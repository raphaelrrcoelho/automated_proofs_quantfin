/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.FixedIncome.Immunization

/-!
# Second-order bond portfolio immunization

The first-order immunization in `BondImmunization.lean` only neutralizes
`∂(A - L)/∂r` at the current rate. Larger parallel rate shifts are picked up
by the second-order term `(1/2) ∂²(A - L)/∂r² · (Δr)²`, governed by the
**convexity** of the cash-flow stream.

For each ZCB: `∂² B/∂r² = (T - t)² · B`. For a portfolio:

  `Conv_P · P = ∑_i w_i · (T_i - t)² · exp(-r(T_i - t))`,

and the derivative `∂_r (-Dur_P · P) = Conv_P · P`.

Second-order immunization: matching both duration AND convexity of the asset
portfolio with the liability portfolio gives a quadratic-order-stable hedge.

Results:

* `bondPortfolioConv`: convexity-times-value `Conv_P · P`.
* `hasDerivAt_bondPortfolioDur_r`: `∂_r (Dur_P · P) = −Conv_P · P`.
* `hasDerivAt_neg_bondPortfolioDur_r`: `∂_r (−Dur_P · P) = Conv_P · P` (this
  is the second derivative of the portfolio value).
* `bondPortfolio_immunization_second_order`: matching convexity gives
  `∂² (A − L)/∂r² = 0`.
-/

namespace QuantFin

open Real

/-- Convexity-times-value `Conv_P · P` of the bond portfolio:
`∑_i w_i · (T_i − t)² · exp(−r(T_i − t))`. -/
noncomputable def bondPortfolioConv
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t)))

/-- **Derivative of duration-times-value w.r.t. rate**:
`∂_r (Dur_P · P) = −Conv_P · P`. -/
lemma hasDerivAt_bondPortfolioDur_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' => bondPortfolioDur s w T t r')
      (-bondPortfolioConv s w T t r) r := by
  unfold bondPortfolioDur bondPortfolioConv
  have h_each : ∀ i ∈ s, HasDerivAt
      (fun r' => w i * (T i - t) * Real.exp (-(r' * (T i - t))))
      (-(w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t))))) r := by
    intro i _
    have h_lin : HasDerivAt (fun r' : ℝ => -(r' * (T i - t))) (-(T i - t)) r := by
      have h := (hasDerivAt_id r).mul_const (T i - t)
      simpa using h.neg
    have h_exp := h_lin.exp
    have h_prod := h_exp.const_mul (w i * (T i - t))
    convert h_prod using 1
    ring
  have h_raw := HasDerivAt.sum h_each
  have h_fn_eq :
      (∑ i ∈ s, fun r' : ℝ =>
          w i * (T i - t) * Real.exp (-(r' * (T i - t)))) =
        (fun r' : ℝ =>
          ∑ i ∈ s, w i * (T i - t) * Real.exp (-(r' * (T i - t)))) := by
    funext r'
    rw [Finset.sum_apply]
  rw [h_fn_eq] at h_raw
  rw [Finset.sum_neg_distrib] at h_raw
  exact h_raw

/-- **Second derivative of portfolio value w.r.t. rate**:
`∂²P/∂r² = Conv_P · P` (equivalently `∂_r (−Dur_P · P) = Conv_P · P`). -/
lemma hasDerivAt_neg_bondPortfolioDur_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' => -bondPortfolioDur s w T t r')
      (bondPortfolioConv s w T t r) r := by
  have h := (hasDerivAt_bondPortfolioDur_r s w T t r).neg
  simpa using h

/-- **Single-bond convexity**: a single-bond portfolio's convexity-times-value
equals `w · (T − t)² · exp(−r(T − t))`. -/
lemma bondPortfolio_single_bond_conv
    {ι : Type*} [DecidableEq ι] (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioConv {i} w T t r =
      w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioConv
  simp

/-- **Second-order immunization**: if both the duration-times-value AND the
convexity-times-value of the asset portfolio match those of the liability,
then both the first and second derivatives of `P_A − P_L` vanish at the
current rate. The first-order condition is `bondPortfolio_immunization_first_order`;
this lemma covers the second-order condition. -/
lemma bondPortfolio_immunization_second_order
    {ι κ : Type*}
    (sA : Finset ι) (wA TA : ι → ℝ)
    (sL : Finset κ) (wL TL : κ → ℝ)
    (t r : ℝ)
    (h_match_conv :
      bondPortfolioConv sA wA TA t r = bondPortfolioConv sL wL TL t r) :
    HasDerivAt (fun r' =>
        -bondPortfolioDur sA wA TA t r' -
        (-bondPortfolioDur sL wL TL t r'))
      0 r := by
  have hA := hasDerivAt_neg_bondPortfolioDur_r sA wA TA t r
  have hL := hasDerivAt_neg_bondPortfolioDur_r sL wL TL t r
  have h := hA.sub hL
  convert h using 1
  rw [h_match_conv]
  ring

end QuantFin
