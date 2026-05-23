/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Portfolio.CAPM
import QuantFin.Portfolio.TangentPortfolio

/-!
# CAPM from market equilibrium (first-principles derivation)

The pre-existing `Portfolio.CAPM` defines `β_i = Cov(R_i, R_M) / Var(R_M)`
and the Security Market Line `SML(β) = R_f + β (E[R_M] − R_f)`, and proves
that the CAPM pricing identity `E[R_i] = SML(β_i)` is equivalent to `α_i = 0`.
It treats CAPM as a definitional algebraic statement.

This file closes the equilibrium-derivation gap. CAPM is *derived* from the
fact that the market portfolio satisfies the tangent-portfolio cross-product
FOC (i.e., in equilibrium, every investor holds the tangent portfolio, so
aggregating gives the market portfolio = tangent portfolio).

## Setup

* `s : Finset ι` — assets in the universe.
* `w_M : ι → ℝ` — market portfolio weights.
* `μ_excess : ι → ℝ` — excess expected returns (over the risk-free rate).
* `Sg : ι → ι → ℝ` — covariance matrix.
* `marginalVariance` — `(Σw)_i = ∑_k Sg(i,k) · w(k)` (= `Cov(R_i, R_M)`).
* `portfolioVariance` — `Var(R_M) = w_M · (Σw_M)`.
* `portfolioReturn` — `μ_M = w_M · μ_excess` (market excess return).

## The equilibrium hypothesis

`h_FOC`: `∀ j k ∈ s, μ_excess(k) · (Σw_M)_j = μ_excess(j) · (Σw_M)_k`.

This is exactly the tangent-portfolio cross-product FOC `IsTangentPortfolioN`
from `Portfolio.TangentPortfolio`, evaluated at `w = w_M`. The economic
content: in equilibrium, the market portfolio satisfies the tangent FOC.

## The CAPM identity (derived, not assumed)

`theorem CAPM_from_market_equilibrium`:

  `μ_excess(i) = β_i · μ_excess(M)`,

where `β_i = (Σw_M)_i / Var(R_M)`. This is the *operational* form of CAPM:
an asset's expected excess return is its beta times the market's expected
excess return.

## Why this is "first principles"

Existing CAPM library content stated the SML and proved consistency
relations (`expectedReturn_eq_SML_iff_alpha_zero`, beta linearity). It did
not derive the SML from a market-equilibrium argument. This file does:
given the equilibrium hypothesis (`h_FOC`, which itself follows from
optimal portfolio choice via `Portfolio.TangentPortfolio`), the CAPM
pricing identity is a *consequence*, not a definition.
-/

namespace QuantFin

/-- Marginal variance contribution of asset `i` in portfolio `w` under
covariance matrix `Sg`: `(Σw)_i = ∑_k Sg(i,k) · w(k)`. For the market
portfolio this equals `Cov(R_i, R_M)`. -/
def marginalVariance {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) : ℝ :=
  ∑ k ∈ s, Sg i k * w k

/-- Portfolio variance: `Var(R_w) = w · (Σw) = ∑_i w(i) · (Σw)_i`. -/
def portfolioVariance {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) : ℝ :=
  ∑ k ∈ s, w k * marginalVariance s Sg w k

/-- Portfolio expected return: `μ_w = w · μ = ∑_i w(i) · μ(i)`. -/
def portfolioReturn {ι : Type*} (s : Finset ι) (w μ : ι → ℝ) : ℝ :=
  ∑ k ∈ s, w k * μ k

/-- **CAPM from market equilibrium**: under the equilibrium hypothesis that
the market portfolio satisfies the tangent-portfolio cross-product FOC,
every asset's excess return is its beta times the market excess return.

The proof is a discrete-Lagrangian argument:

1. From `h_FOC i j` (with `i` fixed): `μ_excess(j) · (Σw_M)_i = μ_excess(i) · (Σw_M)_j`.
2. Multiply both sides by `w_M(j)` and sum over `j ∈ s`.
3. LHS becomes `(∑_j w_M(j) μ_excess(j)) · (Σw_M)_i = μ_M · (Σw_M)_i`.
4. RHS becomes `μ_excess(i) · (∑_j w_M(j) (Σw_M)_j) = μ_excess(i) · Var(R_M)`.
5. So `μ_M · (Σw_M)_i = μ_excess(i) · Var(R_M)`, and dividing by `Var(R_M) ≠ 0`
   yields `μ_excess(i) = (Σw_M)_i / Var(R_M) · μ_M = β_i · μ_M`. -/
theorem CAPM_from_market_equilibrium
    {ι : Type*} (s : Finset ι) (w_M : ι → ℝ) (μ_excess : ι → ℝ)
    (Sg : ι → ι → ℝ) (i : ι) (hi : i ∈ s)
    (h_var : portfolioVariance s Sg w_M ≠ 0)
    (h_FOC : ∀ j ∈ s, ∀ k ∈ s,
       μ_excess k * marginalVariance s Sg w_M j =
         μ_excess j * marginalVariance s Sg w_M k) :
    μ_excess i =
      (marginalVariance s Sg w_M i / portfolioVariance s Sg w_M) *
        portfolioReturn s w_M μ_excess := by
  -- Sum w_M(j) · (h_FOC i j) over j ∈ s
  have h_sum :
      ∑ j ∈ s, w_M j * (μ_excess i * marginalVariance s Sg w_M j) =
      ∑ j ∈ s, w_M j * (μ_excess j * marginalVariance s Sg w_M i) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    -- h_FOC i hi j hj: μ_excess j * (Σw_M)_i = μ_excess i * (Σw_M)_j
    rw [h_FOC i hi j hj]
  -- LHS = μ_excess i · Var(R_M)
  have h_LHS :
      ∑ j ∈ s, w_M j * (μ_excess i * marginalVariance s Sg w_M j) =
        μ_excess i * portfolioVariance s Sg w_M := by
    unfold portfolioVariance
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  -- RHS = μ_M · (Σw_M)_i
  have h_RHS :
      ∑ j ∈ s, w_M j * (μ_excess j * marginalVariance s Sg w_M i) =
        portfolioReturn s w_M μ_excess * marginalVariance s Sg w_M i := by
    unfold portfolioReturn
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [h_LHS, h_RHS] at h_sum
  -- h_sum: μ_excess i * Var(R_M) = μ_M * (Σw_M)_i
  -- Divide both sides by Var(R_M)
  rw [div_mul_eq_mul_div, eq_div_iff h_var]
  linarith

/-- **CAPM equilibrium ⟹ Security Market Line**: the equilibrium CAPM
identity in the standard SML form `E[R_i] = R_f + β_i (E[R_M] − R_f)`.

This packages `CAPM_from_market_equilibrium` together with the relations
`μ_excess(i) = E[R_i] − R_f` and `μ_excess(M) = E[R_M] − R_f`. -/
theorem expectedReturn_eq_SML_from_equilibrium
    {ι : Type*} (s : Finset ι) (w_M : ι → ℝ) (μ : ι → ℝ) (rf : ℝ)
    (Sg : ι → ι → ℝ) (i : ι) (hi : i ∈ s)
    (h_weights : ∑ k ∈ s, w_M k = 1)
    (h_var : portfolioVariance s Sg w_M ≠ 0)
    (h_FOC : ∀ j ∈ s, ∀ k ∈ s,
       (μ k - rf) * marginalVariance s Sg w_M j =
         (μ j - rf) * marginalVariance s Sg w_M k) :
    μ i = securityMarketLine rf
      (marginalVariance s Sg w_M i / portfolioVariance s Sg w_M)
      (∑ k ∈ s, w_M k * μ k) := by
  unfold securityMarketLine
  have h := CAPM_from_market_equilibrium s w_M (fun k => μ k - rf) Sg i hi h_var h_FOC
  -- h: μ i - rf = β_i · (∑ k w_M(k) (μ k - rf))
  -- We want: μ i = rf + β_i · ((∑ k w_M(k) μ k) - rf)
  unfold portfolioReturn at h
  have h_mu_M : ∑ k ∈ s, w_M k * (μ k - rf) =
                (∑ k ∈ s, w_M k * μ k) - rf := by
    have h_aux : ∑ k ∈ s, w_M k * (μ k - rf) =
                 (∑ k ∈ s, w_M k * μ k) - (∑ k ∈ s, rf * w_M k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intros k _
      ring
    rw [h_aux, ← Finset.mul_sum, h_weights]
    ring
  rw [h_mu_M] at h
  linarith

end QuantFin
