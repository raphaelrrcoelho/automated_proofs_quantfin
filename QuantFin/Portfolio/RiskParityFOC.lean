/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Portfolio.CAPMEquilibrium

/-!
# Risk-parity portfolios from the log-barrier Lagrangian (first-principles)

The pre-existing `Portfolio/RiskParity.lean` states the 2-asset closed form
`w_1^{RP} = σ_2 / (σ_1 + σ_2)` and verifies the equal-risk-contribution
identity algebraically (no derivation from a variational principle).

This file derives the N-asset risk-parity / risk-budget conditions from the
first-order condition of the canonical convex programme used in the
risk-parity literature (Roncalli 2014, Maillard-Roncalli-Teïletche 2010):

  `min_w  (1/2) · w^T Σ w − ∑_i b_i · log(w_i)`,    `w_i > 0`.

The FOC is

  `(Σw)_i = b_i / w_i`,                              for every `i`,

equivalently `w_i · (Σw)_i = b_i` (risk contribution `RC_i` equals the
prescribed risk budget `b_i`). Risk parity is the special case `b_i = c`
constant — all assets contribute equally to variance.

## Why this is "first principles"

Risk parity was previously stated as an algebraic identity at closed-form
weights. This file shows it as the *output of an optimisation*: critical
points of the log-barrier-regularised variance minimisation satisfy the
risk-budget property. The 2-asset closed form `σ_2 / (σ_1 + σ_2)` is a
*solution* of this FOC for `b_i = 1/N` — the algebraic verification in
`RiskParity.lean` becomes a check that this candidate is actually critical.

## Results

* `riskContribution`: `RC_i(w) := w_i · (Σw)_i`.
* `sum_riskContribution_eq_variance`: `∑ RC_i = w^T Σ w`.
* `IsRiskParity`: equal `RC_i` across all assets.
* `IsRiskBudgetPortfolio`: each `RC_i` matches a prescribed budget `b_i`.
* `isRiskBudget_of_log_barrier_FOC` (forward derivation): FOC `(Σw)_i =
  b_i / w_i` ⟹ risk-budget property.
* `isRiskParity_of_uniform_log_barrier_FOC`: specialisation with uniform
  budget ⟹ risk parity.
* `isRiskParity_iff_cross_product`: equivalent cross-product
  characterisation.
-/

namespace QuantFin

open Finset

/-- **Risk contribution of asset `i`** in portfolio `w` under covariance
matrix `Sg`: `RC_i := w_i · (Σw)_i`. The sum of risk contributions equals
the portfolio variance. -/
def riskContribution {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) : ℝ :=
  w i * marginalVariance s Sg w i

/-- **Sum-of-risk-contributions identity**: `∑_i RC_i = Var(w) = w · (Σw)`. -/
lemma sum_riskContribution_eq_variance
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    ∑ i ∈ s, riskContribution s Sg w i = portfolioVariance s Sg w := by
  unfold riskContribution portfolioVariance
  rfl

/-- **Equal-risk-contribution property ("risk parity")**: all assets
contribute the same amount of risk to portfolio variance, i.e., `RC_i = RC_j`
for every pair `(i, j) ∈ s × s`. -/
def IsRiskParity {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s,
    riskContribution s Sg w i = riskContribution s Sg w j

/-- **Risk-budget portfolio**: each asset's risk contribution matches a
prescribed budget `b_i`. Risk parity is the uniform-budget specialisation. -/
def IsRiskBudgetPortfolio {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w b : ι → ℝ) : Prop :=
  ∀ i ∈ s, riskContribution s Sg w i = b i

/-- **Forward derivation: risk-budget property from log-barrier Lagrangian
FOC**. The critical-point condition

  `(Σw)_i = b_i / w_i` for all `i ∈ s` with `w_i ≠ 0`,

(which is the FOC of `(1/2) w^T Σ w − ∑_i b_i log(w_i)`) implies the
risk-budget identity `w_i · (Σw)_i = b_i`. -/
theorem isRiskBudget_of_log_barrier_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w b : ι → ℝ)
    (h_pos : ∀ i ∈ s, w i ≠ 0)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = b i / w i) :
    IsRiskBudgetPortfolio s Sg w b := by
  intro i hi
  unfold riskContribution
  rw [h_FOC i hi, mul_div_assoc', mul_comm, mul_div_assoc, div_self (h_pos i hi), mul_one]

/-- **Risk parity from uniform-budget log-barrier FOC**: if the FOC holds
with the *same* constant `c` for every asset (uniform risk budget), then
the portfolio satisfies the equal-risk-contribution property. -/
theorem isRiskParity_of_uniform_log_barrier_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (c : ℝ)
    (h_pos : ∀ i ∈ s, w i ≠ 0)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = c / w i) :
    IsRiskParity s Sg w := by
  intro i hi j hj
  unfold riskContribution
  rw [h_FOC i hi, h_FOC j hj,
      mul_div_assoc', mul_comm (w i) c, mul_div_assoc, div_self (h_pos i hi), mul_one,
      mul_div_assoc', mul_comm (w j) c, mul_div_assoc, div_self (h_pos j hj), mul_one]

/-- **Cross-product characterisation of risk parity**: `RC_i = RC_j` is
literally `w_i · (Σw)_i = w_j · (Σw)_j`. This is the form used in numerical
solvers (project onto the equal-contribution hyperplane). -/
theorem isRiskParity_iff_cross_product
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    IsRiskParity s Sg w ↔
      ∀ i ∈ s, ∀ j ∈ s,
        w i * marginalVariance s Sg w i = w j * marginalVariance s Sg w j := by
  unfold IsRiskParity riskContribution
  rfl

/-- **Risk parity implies each `RC_i = Var(w) / |s|`**: at a risk-parity
portfolio, every asset contributes `1/N`-th of the total variance. -/
theorem riskContribution_eq_variance_div_card_of_riskParity
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) (hi : i ∈ s) (hs : s.Nonempty)
    (h_RP : IsRiskParity s Sg w) :
    riskContribution s Sg w i =
      portfolioVariance s Sg w / (s.card : ℝ) := by
  have h_card_pos : 0 < (s.card : ℝ) := by exact_mod_cast s.card_pos.mpr hs
  have h_card_ne : (s.card : ℝ) ≠ 0 := h_card_pos.ne'
  -- ∑ RC_j = card · RC_i (since all are equal)
  have h_sum : ∑ j ∈ s, riskContribution s Sg w j =
               (s.card : ℝ) * riskContribution s Sg w i := by
    have h_all_eq : ∀ j ∈ s,
        riskContribution s Sg w j = riskContribution s Sg w i := fun j hj => h_RP j hj i hi
    rw [Finset.sum_congr rfl h_all_eq, Finset.sum_const, nsmul_eq_mul]
  rw [sum_riskContribution_eq_variance] at h_sum
  field_simp
  linarith

end QuantFin
