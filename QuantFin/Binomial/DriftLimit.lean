/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.CRRConvergence

/-!
# CRR drift limit (Phase 3 closeout)

This file proves the second classical-analytic step of the CRR-to-BS
correspondence (the variance step `crr_variance_limit` is already in
`BinomialCRRConvergence.lean`):

  `n · (2 p_n − 1) · σ √(T/n) → (r − σ² / 2) T`  as `n → ∞`.

This combined with `crrProb_tendsto_half` and `crr_variance_limit` pins down
the BS log-return moments matched by the CRR tree. Full distributional
convergence `binomialPrice → bs_call_price` remains upstream-gated on a
triangular-array CLT (Mathlib at the current pin only ships the fixed-iid
CLT).

## Main results

* `tendsto_exp_sym_sub_two_div_sq`: `(e^{σh} + e^{-σh} − 2) / h² → σ²`
  as `h → 0`. Uses the algebraic identity
  `e^{σh} + e^{-σh} − 2 = e^{−σh} · (e^{σh} − 1)²` to reduce to existing
  `tendsto_exp_sub_one_div`.
* `crr_drift_limit`: the headline `n · (2 p_n − 1) · σ √(T/n) → (r − σ²/2) T`.
-/

namespace QuantFin

open Real Filter
open scoped Topology

/-- **The cosh-like difference**: `(e^{σh} + e^{−σh} − 2) / h² → σ²` as `h → 0`.

Algebraic identity `e^{σh} + e^{−σh} − 2 = e^{−σh} · (e^{σh} − 1)²` reduces this
to a product of three existing limits: `e^{−σh} → 1`, `(e^{σh} − 1)/h → σ`,
and squaring is continuous. -/
lemma tendsto_exp_sym_sub_two_div_sq (σ : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (σ * h) + Real.exp (-(σ * h)) - 2) / h^2)
      (𝓝[≠] 0) (𝓝 (σ^2)) := by
  -- Building blocks.
  have h_exp_neg : Tendsto (fun h : ℝ => Real.exp (-(σ * h))) (𝓝[≠] 0) (𝓝 1) := by
    have h_cont : Continuous (fun h : ℝ => Real.exp (-(σ * h))) := by continuity
    have h_at_zero : Real.exp (-(σ * 0)) = 1 := by simp [Real.exp_zero]
    have h_tendsto : Tendsto (fun h : ℝ => Real.exp (-(σ * h))) (𝓝 0) (𝓝 1) := by
      rw [show (1 : ℝ) = Real.exp (-(σ * 0)) from h_at_zero.symm]
      exact h_cont.tendsto 0
    exact h_tendsto.mono_left nhdsWithin_le_nhds
  have h_exp_diff : Tendsto (fun h : ℝ => (Real.exp (σ * h) - 1) / h) (𝓝[≠] 0) (𝓝 σ) :=
    tendsto_exp_sub_one_div σ
  have h_exp_diff_sq : Tendsto (fun h : ℝ => ((Real.exp (σ * h) - 1) / h)^2)
      (𝓝[≠] 0) (𝓝 (σ^2)) := h_exp_diff.pow 2
  have h_prod := h_exp_neg.mul h_exp_diff_sq
  have h_target : (1 : ℝ) * σ^2 = σ^2 := one_mul _
  rw [h_target] at h_prod
  -- Now show pointwise that `e^{-σh} · ((e^{σh}-1)/h)² = (e^{σh} + e^{-σh} - 2)/h²`.
  refine h_prod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh_ne : h ≠ 0 := hh
  have h_sq_ne : h^2 ≠ 0 := pow_ne_zero 2 hh_ne
  have h_exp_id : Real.exp (-(σ * h)) * Real.exp (σ * h) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- (e^{σh}-1)/h squared = (e^{σh}-1)² / h²
  -- Goal: (e^σh + e^{-σh} - 2)/h² = e^{-σh} · ((e^σh - 1)/h)²
  rw [div_pow, mul_div_assoc']
  rw [div_eq_div_iff h_sq_ne h_sq_ne]
  -- Goal after div_eq_div_iff: (e^σh + e^{-σh} - 2) · h² = e^{-σh} · (e^σh - 1)² · h²
  -- The h² factors cancel, leaving the algebraic identity.
  have h_exp_id : Real.exp (-(σ * h)) * Real.exp (σ * h) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- Move h² to one side then linear_combination handles the rest.
  have h_alg : Real.exp (σ * h) + Real.exp (-(σ * h)) - 2
             = Real.exp (-(σ * h)) * (Real.exp (σ * h) - 1)^2 := by
    linear_combination -(Real.exp (σ * h) - 2) * h_exp_id
  rw [h_alg]

/-- **Numerator-of-`2p−1` limit**: `(2 e^{rh²} − e^{σh} − e^{−σh}) / h² → 2r − σ²`.

Combines `tendsto_exp_sq_sub_one_div_sq r` (gives `(e^{rh²}-1)/h² → r`) with
`tendsto_exp_sym_sub_two_div_sq σ` (gives `(e^{σh}+e^{-σh}-2)/h² → σ²`). -/
lemma tendsto_crr_numerator_div_sq (σ r : ℝ) :
    Tendsto (fun h : ℝ =>
        (2 * Real.exp (r * h^2) - Real.exp (σ * h) - Real.exp (-(σ * h))) / h^2)
      (𝓝[≠] 0) (𝓝 (2 * r - σ^2)) := by
  have h_exp_sq := tendsto_exp_sq_sub_one_div_sq r
  -- 2 · (e^{rh²} - 1)/h² → 2r
  have h_2exp_sq : Tendsto (fun h : ℝ => 2 * ((Real.exp (r * h^2) - 1) / h^2))
      (𝓝[≠] 0) (𝓝 (2 * r)) := h_exp_sq.const_mul 2
  have h_sym := tendsto_exp_sym_sub_two_div_sq σ
  have h_diff := h_2exp_sq.sub h_sym
  refine h_diff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh_ne : h ≠ 0 := hh
  have h_sq_ne : h^2 ≠ 0 := pow_ne_zero 2 hh_ne
  field_simp
  ring

/-- **Drift-quotient limit (continuous form)**: as `h → 0` (`h ≠ 0`),
`(2 e^{rh²} − e^{σh} − e^{−σh}) / (h · (e^{σh} − e^{−σh})) → (r − σ²/2) / σ`.

Quotient of `tendsto_crr_numerator_div_sq r` and `tendsto_sinh_div σ`. -/
lemma tendsto_crr_drift_quotient {σ : ℝ} (hσ : σ ≠ 0) (r : ℝ) :
    Tendsto (fun h : ℝ =>
        (2 * Real.exp (r * h^2) - Real.exp (σ * h) - Real.exp (-(σ * h)))
          / (h * (Real.exp (σ * h) - Real.exp (-(σ * h)))))
      (𝓝[≠] 0) (𝓝 ((r - σ^2 / 2) / σ)) := by
  have h_num := tendsto_crr_numerator_div_sq σ r
  have h_den := tendsto_sinh_div σ
  have h_2σ : (2 * σ : ℝ) ≠ 0 := by
    intro h; apply hσ; linarith
  have h_quot := h_num.div h_den h_2σ
  -- h_quot : Tendsto (fun h => (Num/h²) / ((e^{σh}-e^{-σh})/h)) (𝓝[≠] 0) (𝓝 ((2r-σ²)/(2σ)))
  have h_target : (2 * r - σ^2) / (2 * σ) = (r - σ^2 / 2) / σ := by
    field_simp
  rw [h_target] at h_quot
  refine h_quot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh_ne : h ≠ 0 := hh
  have h_sq_ne : h^2 ≠ 0 := pow_ne_zero 2 hh_ne
  -- Goal: ((Num h / h²) / ((sinh-like)/h)) = Num h / (h · (sinh-like))
  show (2 * Real.exp (r * h^2) - Real.exp (σ * h) - Real.exp (-(σ * h))) / h^2
      / ((Real.exp (σ * h) - Real.exp (-(σ * h))) / h)
      = _
  rcases eq_or_ne (Real.exp (σ * h) - Real.exp (-(σ * h))) 0 with hden0 | hden0
  · simp [hden0]
  · field_simp

/-- **CRR drift limit** (continuous form): the substantive analytic content of
the drift correspondence.

For `σ ≠ 0`, as `h → 0` (`h ≠ 0`):
  `(2 e^{r h²} − e^{σh} − e^{−σh}) / (h · (e^{σh} − e^{−σh})) → (r − σ²/2) / σ`.

To extract the textbook `n · (2 p_n − 1) · σ √(T/n) → (r − σ²/2) T` form,
substitute `h = √(T/n)`, multiply by `σT`, and use `n · √(T/n) · √(T/n) = T`.
The substitution step is mechanical but the resulting Lean expression
requires algebraic manipulation through several real arithmetic
identities; this is left as integration work. The analytic content above
captures the substantive limit. -/
theorem crr_drift_limit_h {σ : ℝ} (hσ : σ ≠ 0) (r : ℝ) :
    Tendsto (fun h : ℝ =>
        (2 * Real.exp (r * h^2) - Real.exp (σ * h) - Real.exp (-(σ * h)))
          / (h * (Real.exp (σ * h) - Real.exp (-(σ * h)))))
      (𝓝[≠] 0) (𝓝 ((r - σ^2 / 2) / σ)) :=
  tendsto_crr_drift_quotient hσ r

/-- **CRR drift limit (textbook n-form)**: as `n → ∞`,
`n · (2 p_n − 1) · σ · √(T/n) → (r − σ²/2) · T`.

The substitution `h_n = √(T/n)` reduces this to `crr_drift_limit_h` scaled by
`σ T`, using the algebraic identity `n · (√(T/n))² = T`. -/
theorem crr_drift_limit_n {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
        (n : ℝ) * (2 * crrProb r σ T n - 1) * σ * Real.sqrt (T / n))
      atTop (𝓝 ((r - σ^2 / 2) * T)) := by
  have h_sqrt_step : Tendsto (fun n : ℕ => Real.sqrt (crrStep T n)) atTop (𝓝[≠] 0) := by
    have h_to_zero : Tendsto (fun n : ℕ => Real.sqrt (crrStep T n)) atTop (𝓝 0) :=
      tendsto_sqrt_crrStep_zero T
    refine tendsto_nhdsWithin_iff.mpr ⟨h_to_zero, ?_⟩
    rw [eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have h_step_pos : 0 < crrStep T n := by
      unfold crrStep
      exact div_pos hT (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
    have h_sqrt_pos : 0 < Real.sqrt (crrStep T n) := Real.sqrt_pos.mpr h_step_pos
    exact h_sqrt_pos.ne'
  have h_drift_h := tendsto_crr_drift_quotient (hσ.ne') r
  have h_comp := h_drift_h.comp h_sqrt_step
  have h_σT : Tendsto (fun n : ℕ =>
      σ * T * ((2 * Real.exp (r * (Real.sqrt (crrStep T n))^2)
            - Real.exp (σ * Real.sqrt (crrStep T n))
            - Real.exp (-(σ * Real.sqrt (crrStep T n))))
        / (Real.sqrt (crrStep T n)
          * (Real.exp (σ * Real.sqrt (crrStep T n))
            - Real.exp (-(σ * Real.sqrt (crrStep T n)))))))
      atTop (𝓝 (σ * T * ((r - σ^2 / 2) / σ))) := h_comp.const_mul (σ * T)
  have h_target : σ * T * ((r - σ^2 / 2) / σ) = (r - σ^2 / 2) * T := by
    field_simp
  rw [h_target] at h_σT
  refine h_σT.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h_step_pos : 0 < crrStep T n := div_pos hT hn_pos
  have h_step_eq : crrStep T n = T / n := rfl
  have h_sqrt_sq : Real.sqrt (crrStep T n) ^ 2 = crrStep T n := Real.sq_sqrt h_step_pos.le
  have h_sqrt_pos : 0 < Real.sqrt (crrStep T n) := Real.sqrt_pos.mpr h_step_pos
  have h_sqrt_ne : Real.sqrt (crrStep T n) ≠ 0 := h_sqrt_pos.ne'
  have h_inner_lt : -(σ * Real.sqrt (crrStep T n)) < σ * Real.sqrt (crrStep T n) := by
    have h_pos : 0 < σ * Real.sqrt (crrStep T n) := mul_pos hσ h_sqrt_pos
    linarith
  have hden_pos :
      0 < Real.exp (σ * Real.sqrt (crrStep T n))
            - Real.exp (-(σ * Real.sqrt (crrStep T n))) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr h_inner_lt)
  have hden_ne :
      Real.exp (σ * Real.sqrt (crrStep T n))
        - Real.exp (-(σ * Real.sqrt (crrStep T n))) ≠ 0 := hden_pos.ne'
  have h_sqrt_eq : Real.sqrt (T / n) = Real.sqrt (crrStep T n) := by
    rw [h_step_eq]
  unfold crrProb crrUp crrDown crrPerStepRate
  rw [h_sqrt_eq]
  have h_n_step : (n : ℝ) * crrStep T n = T := by
    rw [h_step_eq]; field_simp
  field_simp
  rw [h_sqrt_sq]
  linear_combination
    -(2 * Real.exp (r * crrStep T n) - Real.exp (σ * Real.sqrt (crrStep T n))
        - Real.exp (-(σ * Real.sqrt (crrStep T n)))) * h_n_step

end QuantFin
