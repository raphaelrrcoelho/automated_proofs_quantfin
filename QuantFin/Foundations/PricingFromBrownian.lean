/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Foundations.BSCallHypFromBrownian
import QuantFin.BlackScholes.Put
import QuantFin.BlackScholes.Forward
import QuantFin.BlackScholes.Digital
import QuantFin.BlackScholes.PowerCall
import QuantFin.BlackScholes.StockNumeraire
import QuantFin.BlackScholes.Dividends
import QuantFin.FixedIncome.KMVMertonStructural

/-!
# Pricing entry points from a pre-Brownian motion (phase 31)

This file demonstrates that the full BS pricing pipeline (call, put,
put-call parity, Bachelier call) is derivable from a *single* primitive:
the existence of a pre-Brownian motion `W : ℝ≥0 → Ω → ℝ` (`IsPreBrownian W
Q` from the `BrownianMotion` package).

Each composite corollary is a *one-line composition*:

  `existing pricing formula ∘ BSCallHyp.of_isPreBrownian`,

with the scaled `Z := W T.toNNReal / √T` discharging the marginal-Gaussian
hypothesis. The proofs are zero-line.

## Why this matters

The pre-existing BS / Bachelier pricing theorems take the marginal `Z ~
N(0, 1)` as hypothesis. The Bridge A scaling lemma
(`scaled_isPreBrownian_eval_law`) shows this marginal is *constructible
from any pre-Brownian motion*, so the entire pricing pipeline now has a
single foundational entry point: "supply a Brownian motion."

## Results

* `bs_call_formula_via_brownian`: BS call price formula from BM.
* `bs_put_formula_via_brownian`: BS put price formula from BM.
* `bs_put_call_parity_via_brownian`: put-call parity from BM.
* `bachelier_call_formula_via_brownian`: Bachelier call price formula from BM.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **BS call pricing formula from a pre-Brownian motion**. Given a pre-
Brownian process `W` under `Q`, the BS call price formula

  `e^{−rT} · E[max(S_T − K, 0)] = S_0 · Φ(d_1) − K · e^{−rT} · Φ(d_2)`

holds for `S_T := bsTerminal S_0 r σ T (W T.toNNReal · / √T)`. -/
theorem bs_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  bs_call_formula (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **BS put pricing formula from a pre-Brownian motion**. -/
theorem bs_put_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (K - bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) 0 ∂Q
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) -
        S_0 * Phi (-(bsd1 S_0 K r σ T)) :=
  bs_put_formula (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **Put-call parity from a pre-Brownian motion**. -/
theorem bs_put_call_parity_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q)
      - (∫ ω, Real.exp (-r * T) *
        max (K - bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) 0 ∂Q)
      = S_0 - K * Real.exp (-r * T) :=
  bs_put_call_parity (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **Bachelier call pricing formula from a pre-Brownian motion**. -/
theorem bachelier_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, max (bachelierTerminal S_0 σ T
        (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = (S_0 - K) * Phi (bachelierD S_0 K σ T) +
        σ * Real.sqrt T *
          gaussianPDFReal 0 1 (bachelierD S_0 K σ T) :=
  bachelier_call_formula (BachelierHyp.of_isPreBrownian Q W hK hσ hT)

/-- **Cash-or-nothing digital from a pre-Brownian motion**. -/
theorem bs_cash_or_nothing_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun _ => (1 : ℝ))
          (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) ∂Q
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  bs_cash_or_nothing_formula (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **Asset-or-nothing digital from a pre-Brownian motion**. -/
theorem bs_asset_or_nothing_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun s => s)
          (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) :=
  bs_asset_or_nothing_formula (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **Powered call from a pre-Brownian motion**. -/
theorem bs_power_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ} (a : ℕ) (ha : 0 < a)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsPowerTerminal S_0 r σ T a
          (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q =
      bsPowerEffectiveSpot S_0 r σ T a *
        Phi (bsd1 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) -
      K * Real.exp (-r * T) *
        Phi (bsd2 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) :=
  bs_power_call_formula a ha hK (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **BS-with-dividends call from a pre-Brownian motion**. The drift used
in the marginal hypothesis is `r − q`. -/
theorem bs_dividends_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r q σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 (r - q) σ T
          (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = S_0 * Real.exp (-(q * T)) * Phi (bsd1 S_0 K (r - q) σ T)
        - K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K (r - q) σ T) :=
  bs_dividends_call_formula
    (BSCallHyp.of_isPreBrownian (r := r - q) Q W hS_0 hK hσ hT)

/-- **Stock-numeraire exercise probability from a pre-Brownian motion**. -/
theorem stockNumeraire_exercise_probability_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ ω, (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
      (fun z => Real.exp (-r * T) * bsTerminal S_0 r σ T z / S_0)
        (W T.toNNReal ω / Real.sqrt T) ∂Q) =
        Phi (bsd1 S_0 K r σ T) :=
  stockNumeraire_exercise_probability
    (BSCallHyp.of_isPreBrownian Q W hS_0 hK hσ hT)

/-- **KMV-Merton default probability from a pre-Brownian motion**. -/
theorem kmvPD_eq_one_sub_survival_probability_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {V_0 F r σ_V T : ℝ}
    (hV : 0 < V_0) (hF : 0 < F) (hσ : 0 < σ_V) (hT : 0 < T) :
    kmvPD V_0 F r σ_V T =
      1 - (Q {ω | bsTerminal V_0 r σ_V T
        (W T.toNNReal ω / Real.sqrt T) > F}).toReal :=
  kmvPD_eq_one_sub_survival_probability hV hF
    (BSCallHyp.of_isPreBrownian Q W hV hF hσ hT)

/-- **Merton equity = call on firm assets, from a pre-Brownian motion**. -/
theorem merton_equity_eq_bs_call_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) [IsPreBrownian W Q]
    {V_0 F r σ_V T : ℝ}
    (hV : 0 < V_0) (hF : 0 < F) (hσ : 0 < σ_V) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal V_0 r σ_V T
          (W T.toNNReal ω / Real.sqrt T) - F) 0 ∂Q =
      V_0 * Phi (bsd1 V_0 F r σ_V T) -
        F * Real.exp (-r * T) * Phi (bsd2 V_0 F r σ_V T) :=
  merton_equity_eq_bs_call (BSCallHyp.of_isPreBrownian Q W hV hF hσ hT)

end QuantFin
