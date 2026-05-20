/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Sharpe ratio and Kelly criterion

Two classical performance and money-management identities:

* **Sharpe ratio** `S(μ, r_f, σ) = (μ - r_f) / σ` measures excess return per unit
  of risk. Under iid time aggregation, `L_T ~ N(T·μ, T·σ²)`, so the Sharpe ratio
  scales as `√T`.
* **Kelly fraction** `f*(p, b) = (p·b - q) / b` (with `q = 1 - p`) maximizes the
  expected log-growth `g(f) = p · log(1 + f·b) + q · log(1 - f)` of a wealth
  process under a binary bet with win-probability `p` and payoff ratio `b`.

Results:

* `sharpeRatio`: definition.
* `sharpeRatio_scale_invariant`: `S(λμ, λr_f, λσ) = S(μ, r_f, σ)` for `λ ≠ 0`.
* `sharpeRatio_scaleT`: `S_T = √T · S_1` for iid time aggregation.
* `kellyFraction`, `kellyGrowth`: definitions.
* `kellyGrowth_deriv_at_kelly`: first-order optimality `g'(f*) = 0`.
-/

namespace HybridVerify

open Real

/-- Sharpe ratio `(μ - r_f) / σ`. -/
noncomputable def sharpeRatio (μ r_f σ : ℝ) : ℝ := (μ - r_f) / σ

/-- **Scale invariance**: the Sharpe ratio is invariant under uniform scaling
of mean, risk-free rate, and volatility. -/
lemma sharpeRatio_scale_invariant {c : ℝ} (hc : c ≠ 0) (μ r_f σ : ℝ) :
    sharpeRatio (c * μ) (c * r_f) (c * σ) = sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  by_cases hσ : σ = 0
  · subst hσ; simp
  · field_simp

/-- **Sharpe `√T`-scaling**: under iid time aggregation, `L_T ~ N(T·μ, T·σ²)`,
so the Sharpe ratio at horizon `T` equals `√T` times the unit-horizon Sharpe
ratio. -/
lemma sharpeRatio_scaleT {μ r_f σ T : ℝ} (hT : 0 < T) (hσ : σ ≠ 0) :
    sharpeRatio (T * μ) (T * r_f) (σ * Real.sqrt T) =
      Real.sqrt T * sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrtT_ne : Real.sqrt T ≠ 0 := h_sqrtT_pos.ne'
  have h_T_eq : T = Real.sqrt T * Real.sqrt T := by
    rw [← Real.sqrt_mul hT.le, Real.sqrt_mul_self hT.le]
  -- Rewrite the LHS numerator using T = √T · √T
  rw [show T * μ - T * r_f =
      Real.sqrt T * Real.sqrt T * (μ - r_f) from by rw [← h_T_eq]; ring]
  field_simp

/-- Kelly fraction `f* = (p·b - q) / b`, where `q = 1 - p`. -/
noncomputable def kellyFraction (p b : ℝ) : ℝ := (p * b - (1 - p)) / b

/-- Expected log-growth of a binary bet at fraction `f`:
`p · log(1 + f·b) + (1 - p) · log(1 - f)`. -/
noncomputable def kellyGrowth (p b f : ℝ) : ℝ :=
  p * Real.log (1 + f * b) + (1 - p) * Real.log (1 - f)

/-- **Kelly first-order condition**: at the Kelly fraction `f* = (p·b − q)/b`,
the derivative of the expected log-growth vanishes. -/
lemma kellyGrowth_deriv_at_kelly {p b : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f => kellyGrowth p b f) 0 (kellyFraction p b) := by
  unfold kellyGrowth kellyFraction
  set f₀ : ℝ := (p * b - (1 - p)) / b with hf₀_def
  have hb_ne : b ≠ 0 := hb.ne'
  -- 1 + f₀·b = p·(b + 1)
  have h_1_add : 1 + f₀ * b = p * (b + 1) := by
    rw [hf₀_def]; field_simp; ring
  -- 1 - f₀ = (1 - p)·(b + 1)/b
  have h_1_sub : 1 - f₀ = (1 - p) * (b + 1) / b := by
    rw [hf₀_def]; field_simp; ring
  have h_b1_pos : 0 < b + 1 := by linarith
  have h_q : 0 < 1 - p := by linarith
  have h_1_add_pos : 0 < 1 + f₀ * b := by rw [h_1_add]; positivity
  have h_1_add_ne : 1 + f₀ * b ≠ 0 := h_1_add_pos.ne'
  have h_1_sub_pos : 0 < 1 - f₀ := by rw [h_1_sub]; positivity
  have h_1_sub_ne : 1 - f₀ ≠ 0 := h_1_sub_pos.ne'
  -- Derivative of f ↦ log(1 + f·b) at f₀: b / (1 + f₀·b)
  have h1 : HasDerivAt (fun f => Real.log (1 + f * b))
      (b / (1 + f₀ * b)) f₀ := by
    have hbase : HasDerivAt (fun f : ℝ => 1 + f * b) b f₀ := by
      have := (hasDerivAt_id f₀).mul_const b
      simpa using this.const_add 1
    simpa [div_eq_mul_inv] using hbase.log h_1_add_ne
  -- Derivative of f ↦ log(1 - f) at f₀: -1 / (1 - f₀)
  have h2 : HasDerivAt (fun f => Real.log (1 - f))
      (-1 / (1 - f₀)) f₀ := by
    have hbase : HasDerivAt (fun f : ℝ => 1 - f) (-1) f₀ := by
      simpa using (hasDerivAt_id f₀).const_sub 1
    simpa [div_eq_mul_inv] using hbase.log h_1_sub_ne
  -- Combine
  have h := (h1.const_mul p).add (h2.const_mul (1 - p))
  convert h using 1
  rw [h_1_add, h_1_sub]
  have h_bp_ne : b + 1 ≠ 0 := h_b1_pos.ne'
  field_simp
  ring

end HybridVerify
