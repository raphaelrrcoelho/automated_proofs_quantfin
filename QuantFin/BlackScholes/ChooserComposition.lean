/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Chooser
import QuantFin.BlackScholes.PDE
import QuantFin.BlackScholes.PutGreeks

/-!
# Chooser option as call-plus-put portfolio (first-principles composition)

The pre-existing `BlackScholes/Chooser.lean` derives the algebraic identity
`max(C, P) = C + max(0, K_disc − S)` from put-call parity. That identity is
the chooser's *static portfolio replication* at the chooser date.

This file completes the chain to actual BS pricing:

1. **Time-0 closed form** for the chooser price as `bsV(K, T) + bsP(K_disc, t_1)`,
   where `K_disc = K · e^{−r(T − t_1)}` is the strike discounted from maturity
   back to the chooser date.

2. **Linearity-of-expectation identity**: any random call value `C(ω)` and put
   value `P(ω)` at the chooser date satisfying PCP pointwise yields, under
   linearity of integration,
   `∫ max(C, P) dQ = ∫ C dQ + ∫ max(0, K_disc − S) dQ`. Discounting both sides
   by `e^{−r·t_1}` recovers the time-0 chooser price as `call + put`.

The non-trivial *pricing* step (`E_Q[e^{−r·t_1} · C_{t_1}]` = time-0 call
price) requires the Q-martingale property of the discounted call price,
which would need intermediate-time BS infrastructure not yet formalised
here. The algebra (PCP decomposition) and the linearity identity are both
proved in full.

## Results

* `chooserPrice`: definition `bsV K r σ S_0 T + bsP (K e^{−r(T−t_1)}) r σ S_0 t_1`.
* `chooserPayoff_decompose_BS`: specialisation of `chooser_via_pcp` with the
  BS-style discounted strike.
* `chooser_integral_decomp`: the linearity-of-expectation step.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Chooser option closed-form price** under BS: long call (strike `K`,
maturity `T`) + long put (strike `K · e^{−r(T − t_1)}`, maturity `t_1`).

Derivation rationale: at chooser date `t_1`, the holder picks `max(C_{t_1},
P_{t_1})`. By PCP at `t_1`, this equals `C_{t_1} + max(0, K · e^{−r(T −
t_1)} − S_{t_1})`. The first term is the call payoff; the second is the put
payoff with strike `K · e^{−r(T − t_1)}` and maturity `t_1`. Time-0 prices
are then `bsV(K, T)` and `bsP(K · e^{−r(T−t_1)}, t_1)` respectively. -/
noncomputable def chooserPrice (S_0 K r σ T t_1 : ℝ) : ℝ :=
  bsV K r σ S_0 T + bsP (K * Real.exp (-(r * (T - t_1)))) r σ S_0 t_1

/-- **Chooser payoff decomposition with the BS-style discounted strike**:
specialisation of `chooser_via_pcp` to `K_disc = K · e^{−r(T − t_1)}`. -/
theorem chooserPayoff_decompose_BS
    (C P S K r T t_1 : ℝ)
    (hPCP : C - P = S - K * Real.exp (-(r * (T - t_1)))) :
    max C P = C + max 0 (K * Real.exp (-(r * (T - t_1))) - S) :=
  chooser_via_pcp C P S _ hPCP

/-- **Chooser integral decomposition (linearity-of-expectation step)**: for
random call value `C : Ω → ℝ` and put value `P : Ω → ℝ` at the chooser date
satisfying PCP pointwise with discounted strike `K_disc`, the expectation
of the chooser payoff `max(C, P)` decomposes as `E[C] + E[max(0, K_disc − S)]`.

This is the first integration step in the chooser-pricing chain: combined
with risk-neutral pricing of each piece (`E_Q[e^{−r·t_1} · C_{t_1}] =
bsV(K, T)` etc.), it produces `chooserPrice = bsV + bsP`. -/
theorem chooser_integral_decomp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (C P S : Ω → ℝ) (K_disc : ℝ)
    (hPCP : ∀ ω, C ω - P ω = S ω - K_disc)
    (hint_C : Integrable C Q)
    (hint_put : Integrable (fun ω => max 0 (K_disc - S ω)) Q) :
    ∫ ω, max (C ω) (P ω) ∂Q =
      (∫ ω, C ω ∂Q) + ∫ ω, max 0 (K_disc - S ω) ∂Q := by
  have h_pointwise : ∀ ω, max (C ω) (P ω) = C ω + max 0 (K_disc - S ω) :=
    fun ω => chooser_via_pcp (C ω) (P ω) (S ω) K_disc (hPCP ω)
  rw [show (fun ω => max (C ω) (P ω)) =
        (fun ω => C ω + max 0 (K_disc - S ω)) from funext h_pointwise]
  exact integral_add hint_C hint_put

/-- **Chooser price expanded** via the BS pricing formulas `bsV` and `bsP`:
`chooserPrice = S_0 · Φ(d_1^{call}) − K · e^{−rT} · Φ(d_2^{call}) +
                K_disc · e^{−r·t_1} · Φ(−d_2^{put}) − S_0 · Φ(−d_1^{put})`,
where the `^{call}` parameters use strike `K`, maturity `T`, and the
`^{put}` parameters use strike `K_disc = K · e^{−r(T − t_1)}`, maturity
`t_1`. This makes the explicit closed form visible. -/
theorem chooserPrice_expanded (S_0 K r σ T t_1 : ℝ) :
    chooserPrice S_0 K r σ T t_1 =
      (S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K r σ T)) +
      ((K * Real.exp (-(r * (T - t_1)))) * Real.exp (-(r * t_1)) *
          Phi (-(bsd2 S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1)) -
        S_0 * Phi (-(bsd1 S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1))) := by
  unfold chooserPrice bsV bsP
  ring

end QuantFin
