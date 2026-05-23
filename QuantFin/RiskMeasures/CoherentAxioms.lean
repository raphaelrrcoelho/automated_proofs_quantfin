/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.RiskMeasures.Gaussian

/-!
# Coherent risk measure axioms (gaussian case)

For losses `L ~ N(μ, σ²)` and gaussian aggregations, both VaR and CVaR satisfy
the four coherent-risk-measure axioms of Artzner–Delbaen–Eber–Heath (1999):

* **Translation invariance**: `ρ(L + c) = ρ(L) + c`.
* **Positive homogeneity**: `ρ(λ·L) = λ·ρ(L)` for `λ ≥ 0`.
* **Monotonicity (parameter form)**: if `μ₁ ≤ μ₂` and `σ₁ = σ₂`, then
  `ρ(L₁) ≤ ρ(L₂)` for right-tail quantiles `z ≥ 0`.
* **Subadditivity**: for joint-gaussian `L₁ + L₂ ~ N(μ₁ + μ₂, σ₊²)` with
  `σ₊² = σ₁² + 2 ρ σ₁ σ₂ + σ₂²`, `|ρ| ≤ 1`, `σ_i ≥ 0`, and `z ≥ 0`:
  `ρ(L₁ + L₂) ≤ ρ(L₁) + ρ(L₂)`.

In general (non-gaussian) distributions, VaR can fail subadditivity, which is
why CVaR (which is subadditive in all settings) is preferred for capital
adequacy. Within the gaussian family, both work.

Results:

* `gaussianVaR_translation`, `gaussianCVaR_translation`: translation invariance.
* `gaussianVaR_positiveHomogeneity`, `gaussianCVaR_positiveHomogeneity`:
  positive homogeneity.
* `gaussianVaR_monotone_mean`, `gaussianCVaR_monotone_mean`: monotonicity in
  the mean (right-tail).
* `joint_stdev_le`: `√(σ₁² + 2 ρ σ₁ σ₂ + σ₂²) ≤ σ₁ + σ₂` for `|ρ| ≤ 1` and
  `σ_i ≥ 0`. The substantive analytic content of gaussian subadditivity.
* `gaussianVaR_subadditive`, `gaussianCVaR_subadditive`: subadditivity.
-/

namespace QuantFin

open Real ProbabilityTheory

/-- **VaR translation invariance**: `VaR(L + c) = VaR(L) + c`. -/
lemma gaussianVaR_translation (μ σ z c : ℝ) :
    gaussianVaR (μ + c) σ z = gaussianVaR μ σ z + c := by
  unfold gaussianVaR; ring

/-- **CVaR translation invariance**: `CVaR(L + c) = CVaR(L) + c`. -/
lemma gaussianCVaR_translation (μ σ z α c : ℝ) :
    gaussianCVaR (μ + c) σ z α = gaussianCVaR μ σ z α + c := by
  unfold gaussianCVaR; ring

/-- **VaR positive homogeneity**: `VaR(λ·L) = λ·VaR(L)` for `λ ≥ 0`. -/
lemma gaussianVaR_positiveHomogeneity (μ σ z : ℝ) {l : ℝ} (_hl : 0 ≤ l) :
    gaussianVaR (l * μ) (l * σ) z = l * gaussianVaR μ σ z := by
  unfold gaussianVaR; ring

/-- **CVaR positive homogeneity**: `CVaR(λ·L) = λ·CVaR(L)` for `λ ≥ 0`. -/
lemma gaussianCVaR_positiveHomogeneity (μ σ z α : ℝ) {l : ℝ} (_hl : 0 ≤ l) :
    gaussianCVaR (l * μ) (l * σ) z α = l * gaussianCVaR μ σ z α := by
  unfold gaussianCVaR; ring

/-- **VaR monotonicity in mean** at the same volatility and right-tail quantile:
if `μ₁ ≤ μ₂` and `σ ≥ 0`, then `VaR(L₁) ≤ VaR(L₂)`. -/
lemma gaussianVaR_monotone_mean {μ₁ μ₂ σ z : ℝ}
    (hμ : μ₁ ≤ μ₂) :
    gaussianVaR μ₁ σ z ≤ gaussianVaR μ₂ σ z := by
  unfold gaussianVaR
  linarith

/-- **CVaR monotonicity in mean** at the same volatility: if `μ₁ ≤ μ₂`, then
`CVaR(L₁) ≤ CVaR(L₂)`. -/
lemma gaussianCVaR_monotone_mean {μ₁ μ₂ σ z α : ℝ}
    (hμ : μ₁ ≤ μ₂) :
    gaussianCVaR μ₁ σ z α ≤ gaussianCVaR μ₂ σ z α := by
  unfold gaussianCVaR
  linarith

/-- **Joint-standard-deviation triangle inequality**:
`√(σ₁² + 2 ρ σ₁ σ₂ + σ₂²) ≤ σ₁ + σ₂` whenever `|ρ| ≤ 1` and `σ_i ≥ 0`. This is
the substantive inequality behind gaussian subadditivity. -/
lemma joint_stdev_le {σ₁ σ₂ ρ : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) :
    Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ := by
  have h_sum_sq : σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2 ≤ (σ₁ + σ₂) ^ 2 := by
    have h_prod : 0 ≤ σ₁ * σ₂ := mul_nonneg h₁ h₂
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) h_prod]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  have : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤
      Real.sqrt ((σ₁ + σ₂) ^ 2) := Real.sqrt_le_sqrt h_sum_sq
  rwa [Real.sqrt_sq h_sum_nn] at this

/-- **Gaussian VaR subadditivity**: for joint-gaussian `L₁ + L₂ ~ N(μ₁ + μ₂, σ₊²)`
with `σ₊ = √(σ₁² + 2 ρ σ₁ σ₂ + σ₂²)` and `|ρ| ≤ 1`, `σ_i ≥ 0`, `z ≥ 0`:
`VaR(L₁ + L₂) ≤ VaR(L₁) + VaR(L₂)`. -/
lemma gaussianVaR_subadditive {μ₁ μ₂ σ₁ σ₂ ρ z : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) (hz : 0 ≤ z) :
    gaussianVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2)) z ≤
      gaussianVaR μ₁ σ₁ z + gaussianVaR μ₂ σ₂ z := by
  unfold gaussianVaR
  have h_stdev : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ :=
    joint_stdev_le h₁ h₂ hρ
  nlinarith

/-- **Gaussian CVaR subadditivity**: same setup as `gaussianVaR_subadditive`,
plus the level `α < 1`. -/
lemma gaussianCVaR_subadditive {μ₁ μ₂ σ₁ σ₂ ρ z α : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) (hα : α < 1) :
    gaussianCVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2)) z α ≤
      gaussianCVaR μ₁ σ₁ z α + gaussianCVaR μ₂ σ₂ z α := by
  unfold gaussianCVaR
  have h_stdev : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ :=
    joint_stdev_le h₁ h₂ hρ
  have h_one_alpha : 0 < 1 - α := by linarith
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 z := gaussianPDFReal_nonneg _ _ _
  have h_factor_nn : 0 ≤ gaussianPDFReal 0 1 z / (1 - α) :=
    div_nonneg h_pdf_nn h_one_alpha.le
  have h_mul : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) *
        (gaussianPDFReal 0 1 z / (1 - α)) ≤
      (σ₁ + σ₂) * (gaussianPDFReal 0 1 z / (1 - α)) :=
    mul_le_mul_of_nonneg_right h_stdev h_factor_nn
  linarith

end QuantFin
