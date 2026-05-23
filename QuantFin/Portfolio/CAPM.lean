/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Capital Asset Pricing Model (CAPM)

CAPM at the algebraic / definitional level. Returns are modelled by their first
two moments (`E[R_i]`, `Cov(R_i, R_M)`, `Var(R_M)`) — the same primitives used
in the Markowitz file. This is the standard textbook treatment.

Results:

* `beta`: defines `β_i = Cov(R_i, R_M) / Var(R_M)`.
* `securityMarketLine`: the equilibrium expected return `R_f + β_i (E[R_M] − R_f)`.
* `expectedReturn_eq_SML_iff_pricing_holds`: the CAPM identity
  `E[R_i] = R_f + β_i (E[R_M] − R_f)` is equivalent to the equation
  `α_i = E[R_i] − (R_f + β_i (E[R_M] − R_f)) = 0` (Jensen's alpha vanishes).
* `beta_linearity`: a portfolio's beta is the weighted sum of its components' betas,
  `β_p = ∑ w_i β_i`, by bilinearity of covariance (axiomatized at the algebraic level).
* `beta_of_marketPortfolio`: the market's beta is `1`.
* `beta_of_riskFree`: the risk-free asset's beta is `0` (zero covariance with the market).
-/

namespace QuantFin

/-- CAPM beta: `β = Cov(R, R_M) / Var(R_M)`. Defined algebraically as a ratio. -/
noncomputable def beta (covRRm varRm : ℝ) : ℝ := covRRm / varRm

/-- Security Market Line: the CAPM equilibrium expected return as a function of beta. -/
noncomputable def securityMarketLine (rf β eRm : ℝ) : ℝ := rf + β * (eRm - rf)

/-- The CAPM pricing identity `E[R] = R_f + β (E[R_M] − R_f)` is equivalent to
zero Jensen's alpha. -/
lemma expectedReturn_eq_SML_iff_alpha_zero
    (eR rf β eRm : ℝ) :
    eR = securityMarketLine rf β eRm ↔ eR - securityMarketLine rf β eRm = 0 := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- A risk-free asset (zero covariance with the market) has beta zero. -/
lemma beta_of_riskFree (varRm : ℝ) :
    beta 0 varRm = 0 := by
  unfold beta
  exact zero_div varRm

/-- The market portfolio's beta is one: when `R_i = R_M`, `Cov(R_M, R_M) = Var(R_M)`
so `β_M = 1`. -/
lemma beta_market {varRm : ℝ} (hVar : varRm ≠ 0) :
    beta varRm varRm = 1 := by
  unfold beta
  exact div_self hVar

/-- **Beta linearity** for a two-asset portfolio: the portfolio's beta is the
weight-sum of the component betas.

For a portfolio `R_p = w_1 R_1 + w_2 R_2`, bilinearity of covariance gives
`Cov(R_p, R_M) = w_1 Cov(R_1, R_M) + w_2 Cov(R_2, R_M)`, so dividing by
`Var(R_M)` yields the result. -/
lemma beta_linearity_two
    {varRm : ℝ} (hVar : varRm ≠ 0)
    (w₁ w₂ covR₁Rm covR₂Rm : ℝ) :
    beta (w₁ * covR₁Rm + w₂ * covR₂Rm) varRm =
      w₁ * beta covR₁Rm varRm + w₂ * beta covR₂Rm varRm := by
  unfold beta
  field_simp

/-- **Beta linearity** for a finite-index portfolio: the portfolio's beta is the
weight-sum of the component betas.

For weights `w : ι → ℝ` and component covariances `c : ι → ℝ`, bilinearity of
covariance gives `Cov(∑ w_i R_i, R_M) = ∑ w_i Cov(R_i, R_M)`. -/
lemma beta_linearity_finset
    {ι : Type*} (s : Finset ι) (w c : ι → ℝ) (varRm : ℝ) :
    beta (∑ i ∈ s, w i * c i) varRm = ∑ i ∈ s, w i * beta (c i) varRm := by
  unfold beta
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mul_div_assoc]

end QuantFin
