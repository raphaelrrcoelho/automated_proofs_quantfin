/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Markowitz two-asset portfolio theory

Closed-form results for the two-asset minimum-variance problem. Returns are
modelled by their first two moments only (`σ_1`, `σ_2`, ρ`), not by a probability
space — this is the classical mean-variance setting where the covariance matrix
is the primitive.

For a two-asset portfolio with weight `w` on asset 1 and `1 - w` on asset 2:

  `Var(w) = w² σ_1² + (1 - w)² σ_2² + 2 w (1 - w) ρ σ_1 σ_2`.

The "completing-the-square" identity

  `Var(w) = D · (w − w*)² + V_min`

with `D = σ_1² − 2 ρ σ_1 σ_2 + σ_2²`,
`w* = (σ_2² − ρ σ_1 σ_2) / D`,
`V_min = σ_1² σ_2² (1 − ρ²) / D`,

makes both the location of the minimum (at `w*`) and its value (`V_min`)
immediate, and avoids any explicit calculus.

Results:

* `portfolioVarTwo_eq_quad`: the factorization above.
* `portfolioVarTwo_at_minVarWeight`: `Var(w*) = V_min`.
* `portfolioVarTwo_ge_min`: `Var(w) ≥ V_min` for every `w`, given `D > 0`.
* `minPortfolioVarTwo_eq_zero_iff_perfect_anticorr`: at `ρ = -1` with
  `σ_1, σ_2 > 0`, the minimum variance is exactly zero (perfect hedge).
-/

namespace QuantFin

/-- Portfolio variance for a two-asset mix with weight `w` on asset 1 and
`1 - w` on asset 2. -/
noncomputable def portfolioVarTwo (σ₁ σ₂ ρ : ℝ) (w : ℝ) : ℝ :=
  w ^ 2 * σ₁ ^ 2 + (1 - w) ^ 2 * σ₂ ^ 2 + 2 * w * (1 - w) * ρ * σ₁ * σ₂

/-- Denominator of the min-variance weight: `D = σ_1² − 2 ρ σ_1 σ_2 + σ_2²`. -/
noncomputable def minVarDenom (σ₁ σ₂ ρ : ℝ) : ℝ :=
  σ₁ ^ 2 - 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2

/-- Closed-form minimum-variance weight:
`w* = (σ_2² − ρ σ_1 σ_2) / D`. -/
noncomputable def minVarWeightTwo (σ₁ σ₂ ρ : ℝ) : ℝ :=
  (σ₂ ^ 2 - ρ * σ₁ * σ₂) / minVarDenom σ₁ σ₂ ρ

/-- Minimum portfolio variance: `V_min = σ_1² σ_2² (1 − ρ²) / D`. -/
noncomputable def minPortfolioVarTwo (σ₁ σ₂ ρ : ℝ) : ℝ :=
  σ₁ ^ 2 * σ₂ ^ 2 * (1 - ρ ^ 2) / minVarDenom σ₁ σ₂ ρ

/-- Two-asset portfolio variance has the closed-form factorization
`Var(w) = D · (w − w*)² + V_min`. -/
lemma portfolioVarTwo_eq_quad {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) (w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w =
      minVarDenom σ₁ σ₂ ρ * (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2
      + minPortfolioVarTwo σ₁ σ₂ ρ := by
  unfold portfolioVarTwo minVarWeightTwo minPortfolioVarTwo
  field_simp
  unfold minVarDenom
  ring

/-- Two-asset portfolio variance attains the explicit minimum `V_min` at `w = w*`. -/
lemma portfolioVarTwo_at_minVarWeight {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) :
    portfolioVarTwo σ₁ σ₂ ρ (minVarWeightTwo σ₁ σ₂ ρ) =
      minPortfolioVarTwo σ₁ σ₂ ρ := by
  rw [portfolioVarTwo_eq_quad hD]
  simp [sub_self]

/-- For any weight, the portfolio variance is at least `V_min`, provided the
denominator `D` is positive (the standard non-degeneracy condition). -/
lemma portfolioVarTwo_ge_min {σ₁ σ₂ ρ : ℝ}
    (hD : 0 < minVarDenom σ₁ σ₂ ρ) (w : ℝ) :
    minPortfolioVarTwo σ₁ σ₂ ρ ≤ portfolioVarTwo σ₁ σ₂ ρ w := by
  rw [portfolioVarTwo_eq_quad hD.ne' w]
  have h_sq : 0 ≤ (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2 := sq_nonneg _
  have h_term : 0 ≤ minVarDenom σ₁ σ₂ ρ * (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2 :=
    mul_nonneg hD.le h_sq
  linarith

/-- **Perfect-hedge corollary**: when `ρ = -1` and both volatilities are
positive, the minimum portfolio variance equals zero. -/
lemma minPortfolioVarTwo_perfect_anticorr (σ₁ σ₂ : ℝ) :
    minPortfolioVarTwo σ₁ σ₂ (-1) = 0 := by
  unfold minPortfolioVarTwo
  have h : (1 : ℝ) - (-1) ^ 2 = 0 := by ring
  rw [h]
  ring

end QuantFin
