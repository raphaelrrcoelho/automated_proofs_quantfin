/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.Model

/-!
# American option pricing in the binomial tree

For a binomial tree with up-factor `u`, down-factor `d`, per-step rate `r`,
under the no-arbitrage condition `d < e^r < u`, an American option with
intrinsic payoff `g : ℝ → ℝ` (e.g. `S ↦ max(S − K, 0)` for a call) has price

  `V_n(S) = max(g(S), e^{-r} · (p · V_{n-1}(uS) + (1 − p) · V_{n-1}(dS)))`

with `V_0(S) = g(S)`, where `p = crrUpProb u d r`. `n` counts steps remaining.

This file defines `americanPrice` and proves:

* `americanPrice_ge_intrinsic`: the American price dominates the intrinsic payoff,
  `g(S) ≤ V_n(S)` for all `n, S`.
* `americanPrice_supermartingale`: the discounted continuation value at step `n+1`
  is at most the American price, i.e. the discounted price process is a
  supermartingale under the risk-neutral measure.
* `binomialPrice_le_americanPrice`: the American price dominates the European
  price with the same terminal payoff. The American has weakly more optionality
  (early-exercise) — this is the formal expression of that intuition.

No new infrastructure beyond `BinomialModel` is needed.
-/

namespace QuantFin

open Real

/-- American option price in the binomial tree.

Bellman recursion: at each step, take the maximum of immediate exercise (`g S`)
and the discounted expected continuation. `n` counts steps remaining; `g` is
the intrinsic payoff function. -/
noncomputable def americanPrice (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, S => g S
  | n + 1, S => max (g S)
      (binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u))
        (americanPrice u d r g n (S * d)))

/-- At maturity (`n = 0`), the American price equals the intrinsic payoff. -/
@[simp]
lemma americanPrice_zero (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    americanPrice u d r g 0 S = g S := rfl

/-- One-step Bellman: `V_{n+1}(S) = max(g(S), one-period continuation)`. -/
lemma americanPrice_succ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    americanPrice u d r g (n + 1) S = max (g S)
      (binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u))
        (americanPrice u d r g n (S * d))) := rfl

/-- **Intrinsic-value bound**: `g(S) ≤ V_n(S)` for all `n, S`.

Immediate: at step 0 they are equal; at later steps the recursion takes a `max`
that contains `g S` as a candidate. -/
lemma americanPrice_ge_intrinsic (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    g S ≤ americanPrice u d r g n S := by
  cases n with
  | zero => simp
  | succ n => rw [americanPrice_succ]; exact le_max_left _ _

/-- **Supermartingale property** (discrete form): the one-period continuation
value at `V_{n+1}` is bounded above by `V_{n+1}` itself. In other words, the
discounted American price process is a supermartingale under the risk-neutral
measure.

Immediate from the Bellman max: `V_{n+1}(S) = max(g(S), continuation(n+1, S))
≥ continuation(n+1, S)`. -/
lemma americanPrice_supermartingale (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialOptionPriceOnePeriod u d r
      (americanPrice u d r g n (S * u))
      (americanPrice u d r g n (S * d))
        ≤ americanPrice u d r g (n + 1) S := by
  rw [americanPrice_succ]; exact le_max_right _ _

/-- Monotonicity of the one-period continuation: if `V_u ≤ V_u'` and
`V_d ≤ V_d'`, then the one-period prices satisfy the same ordering.
Required for the European → American domination proof. -/
lemma binomialOptionPriceOnePeriod_mono {u d r V_u V_u' V_d V_d' : ℝ}
    (h : BinomialNoArb u d r) (hu : V_u ≤ V_u') (hd : V_d ≤ V_d') :
    binomialOptionPriceOnePeriod u d r V_u V_d
      ≤ binomialOptionPriceOnePeriod u d r V_u' V_d' := by
  have h_p := crrUpProb_mem_Ioo h
  have h_p_pos : 0 < crrUpProb u d r := h_p.1
  have h_p_lt_one : crrUpProb u d r < 1 := h_p.2
  have h_q_pos : 0 < 1 - crrUpProb u d r := by linarith
  have h_exp_pos : 0 < Real.exp (-r) := Real.exp_pos _
  unfold binomialOptionPriceOnePeriod
  have h_sum : crrUpProb u d r * V_u + (1 - crrUpProb u d r) * V_d
            ≤ crrUpProb u d r * V_u' + (1 - crrUpProb u d r) * V_d' := by
    have h1 : crrUpProb u d r * V_u ≤ crrUpProb u d r * V_u' :=
      mul_le_mul_of_nonneg_left hu h_p_pos.le
    have h2 : (1 - crrUpProb u d r) * V_d ≤ (1 - crrUpProb u d r) * V_d' :=
      mul_le_mul_of_nonneg_left hd h_q_pos.le
    linarith
  exact mul_le_mul_of_nonneg_left h_sum h_exp_pos.le

/-- **American ≥ European**: for the same intrinsic payoff `g`, the American
price dominates the European price at every step and every spot.

Proof: induction on the step count. At `n = 0` both equal `g(S)`. The
inductive step uses the supermartingale property (`V_{n+1}^{Am} ≥
continuation^{Am}`), monotonicity of the continuation in its arguments, and
the European recursion `V_{n+1}^{Eu} = continuation^{Eu}`. -/
theorem binomialPrice_le_americanPrice {u d r : ℝ} (h : BinomialNoArb u d r)
    (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g n S ≤ americanPrice u d r g n S := by
  induction n generalizing S with
  | zero => simp [binomialPrice_zero]
  | succ n ih =>
    calc binomialPrice u d r g (n + 1) S
        = binomialOptionPriceOnePeriod u d r
            (binomialPrice u d r g n (S * u))
            (binomialPrice u d r g n (S * d)) := binomialPrice_succ_eq_onePeriod u d r g n S
      _ ≤ binomialOptionPriceOnePeriod u d r
            (americanPrice u d r g n (S * u))
            (americanPrice u d r g n (S * d)) :=
          binomialOptionPriceOnePeriod_mono h (ih (S * u)) (ih (S * d))
      _ ≤ americanPrice u d r g (n + 1) S := americanPrice_supermartingale u d r g n S

end QuantFin
