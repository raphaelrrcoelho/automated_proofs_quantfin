/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.Portfolio.CAPMEquilibrium

/-!
# N-asset Markowitz from constrained-variance Lagrangian (first principles)

The 2-asset version of Markowitz (`Portfolio/SharpeFOCDerivation.lean`,
phase 21) derives the cross-product FOC `r₂(Σw)₁ = r₁(Σw)₂` from
`d(Sh²)/dw = 0`. This file extends the first-principles derivation to N
assets, but for the *constrained variance minimization* formulation —
which is the textbook Markowitz statement and gives the canonical
Lagrangian FOC `Σw = lam_1 · 1 + lam_2 · μ`.

## The problem

Minimize `(1/2) · w^T Σ w` (portfolio variance) subject to

  * `1^T w = 1` (budget constraint),
  * `μ^T w = m` (expected-return target).

## The Lagrangian

`L(w, lam_1, lam_2) := (1/2) · w^T Σ w − lam_1 · (1^T w − 1) − lam_2 · (μ^T w − m)`.

## The FOC (textbook derivation)

`∂L/∂w_i = (Σw)_i − lam_1 − lam_2 · μ_i = 0`,    i.e.,    `Σw = lam_1 · 1 + lam_2 · μ`.

This says the marginal variance vector lies in the 2-d span of the
constraint normals — the canonical "two-fund separation" structural fact.

## Variational characterisation

A portfolio `w` is a **constrained variance critical point** iff for every
admissible perturbation `δw` (orthogonal to budget and expected-return
normals, i.e., `1^T δw = 0` and `μ^T δw = 0`),

  `d/dt [(1/2) (w + t δw)^T Σ (w + t δw)] |_{t=0} = 0`,
  equivalently   `(Σw)^T δw = 0`.

## Results

* `IsConstrainedVarianceCriticalPoint`: the variational definition.
* `isCriticalPoint_of_lagrangian_FOC` (forward direction): if `Σw = lam_1 ·
  1 + lam_2 · μ` componentwise, then `w` is a constrained-variance critical
  point. *Proof*: direct algebra — substitute the FOC, use the
  perturbation's orthogonality to the constraint normals.
* `lagrangian_critical_directional_deriv`: explicit computation of the
  directional derivative of `(1/2) w^T Σ w` at `w` in direction `δw` for
  symmetric `Σ`, equals `(Σw) · δw`. The mathematical content underlying
  the FOC.

## What is *not* in this file (deferred)

The backward direction ("critical point ⟹ Lagrangian FOC") requires
showing `Σw ∈ span{1, μ}`, which by the orthogonal-complement
characterization is equivalent to `Σw ⊥ {δw : 1·δw = 0 ∧ μ·δw = 0}`. In
finite dimensions this needs `Submodule.orthogonalComplement` machinery —
substantial Mathlib linear-algebra infrastructure. The forward direction
already gives the constructive content (every weight satisfying the
Lagrangian equations is a critical point); the backward direction is the
"every critical point arises from some Lagrange multipliers" converse.

## Why this is "first principles"

The pre-existing `Portfolio/Markowitz.lean` / `MarkowitzNAsset.lean` state
the closed-form covariance-inverse weight `w = α · Σ⁻¹(μ − r_f · 1)` and
verify variance/return identities. This file derives *why* such weights
are critical points: they satisfy the Lagrangian first-order condition of
the constrained variance-minimization problem. The 2-asset version
(phase 21) handled Sharpe maximization; this file extends to N assets
with budget + target-return constraints (the standard textbook setup).
-/

namespace HybridVerify

open Finset

/-- **Constrained-variance critical-point property** (variational form):
`w` is a critical point of `(1/2) w^T Σ w` subject to `1^T w = 1` and
`μ^T w = m` if, for every admissible perturbation `δw` (orthogonal to
both constraint normals), the directional derivative `(Σw) · δw` vanishes. -/
def IsConstrainedVarianceCriticalPoint {ι : Type*} (s : Finset ι)
    (Sg : ι → ι → ℝ) (μ w : ι → ℝ) : Prop :=
  ∀ δw : ι → ℝ,
    (∑ i ∈ s, δw i) = 0 →
    (∑ i ∈ s, μ i * δw i) = 0 →
    (∑ i ∈ s, marginalVariance s Sg w i * δw i) = 0

/-- **Forward direction of the Lagrangian FOC characterisation**: if there
exist scalars `lam_1, lam_2` such that `(Σw)_i = lam_1 + lam_2 · μ_i` for every
asset `i ∈ s`, then `w` is a constrained-variance critical point.

The "Lagrangian FOC" `Σw = lam_1 · 1 + lam_2 · μ` is the textbook
characterisation of efficient portfolios — every variance-minimising
portfolio for some target return satisfies this for some `(lam_1, lam_2)`.

Proof: substitute the FOC into the directional-derivative sum and use the
perturbation's orthogonality to the constraint normals (`∑ δw = 0` kills
the `lam_1` term, `∑ μ δw = 0` kills the `lam_2 μ` term). -/
theorem isCriticalPoint_of_lagrangian_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (μ w : ι → ℝ)
    (lam_1 lam_2 : ℝ)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = lam_1 + lam_2 * μ i) :
    IsConstrainedVarianceCriticalPoint s Sg μ w := by
  intro δw h_sum_zero h_mu_zero
  -- ∑ (Σw)_i · δw_i = ∑ (lam_1 + lam_2 μ_i) · δw_i
  --                 = lam_1 · ∑ δw_i + lam_2 · ∑ μ_i δw_i
  --                 = lam_1 · 0 + lam_2 · 0 = 0
  have h_subst : ∑ i ∈ s, marginalVariance s Sg w i * δw i =
                 ∑ i ∈ s, (lam_1 + lam_2 * μ i) * δw i := by
    refine Finset.sum_congr rfl ?_
    intros i hi
    rw [h_FOC i hi]
  rw [h_subst]
  -- ∑ (lam_1 + lam_2 μ i) · δw i = lam_1 · ∑ δw + lam_2 · ∑ μ δw
  have h_split : ∑ i ∈ s, (lam_1 + lam_2 * μ i) * δw i =
                 lam_1 * (∑ i ∈ s, δw i) + lam_2 * (∑ i ∈ s, μ i * δw i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [h_split, h_sum_zero, h_mu_zero]
  ring

/-- **Self-dot identity for the variance objective**: `(1/2) w^T Σ w` (the
variance objective, up to constant 1/2) equals `(1/2) · ∑_i w_i · (Σw)_i`.
This is the same self-dot identity used in `Portfolio/SharpeFOCDerivation.lean`,
restated for N assets. -/
lemma variance_objective_eq_self_dot
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    (1 / 2 : ℝ) * portfolioVariance s Sg w =
      (1 / 2 : ℝ) * ∑ i ∈ s, w i * marginalVariance s Sg w i := by
  unfold portfolioVariance
  rfl

/-- **Directional derivative of the variance objective at `w` in direction
`δw`**, for *symmetric* `Sg`:

  `d/dt [(1/2) (w + t δw)^T Σ (w + t δw)] |_{t=0} = (Σw)^T δw`.

This is the calculus content underlying the FOC. Proof: expand the
quadratic in `t`, the linear coefficient is `(1/2) · [(δw)^T Σ w + w^T Σ δw]`,
which for symmetric `Σ` equals `(Σw)^T δw`.

(The actual `HasDerivAt` statement uses the parameterised path; the
identity below states the polynomial coefficient algebraically.) -/
lemma quadratic_form_perturb_linear_coeff
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w δw : ι → ℝ)
    (h_symm : ∀ i ∈ s, ∀ j ∈ s, Sg i j = Sg j i) :
    (1 / 2 : ℝ) *
      ((∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j) +
       (∑ i ∈ s, ∑ j ∈ s, Sg i j * w i * δw j)) =
      ∑ i ∈ s, marginalVariance s Sg w i * δw i := by
  -- The cross-terms: ∑_{ij} Sg(i,j) (δw_i w_j + w_i δw_j)
  -- By symmetry Sg(i,j) = Sg(j,i), this equals 2 ∑_{ij} Sg(i,j) δw_i w_j
  -- (after relabelling). Then (1/2) · 2 = 1, giving ∑_i δw_i (Σw)_i.
  have h_swap : ∑ i ∈ s, ∑ j ∈ s, Sg i j * w i * δw j =
                ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j := by
    -- Swap the indices using symmetry of Sg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intros i hi
    refine Finset.sum_congr rfl ?_
    intros j hj
    rw [h_symm i hi j hj]
    ring
  rw [h_swap]
  unfold marginalVariance
  rw [show (1 / 2 : ℝ) * ((∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j) +
            (∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j)) =
        ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j from by ring]
  -- ∑_i ∑_j Sg(i,j) δw_i w_j = ∑_i δw_i · (∑_j Sg(i,j) w_j) = ∑_i δw_i · (Σw)_i
  rw [show ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j =
        ∑ i ∈ s, δw i * (∑ j ∈ s, Sg i j * w j) from
      Finset.sum_congr rfl (fun i _ => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => by ring))]
  refine Finset.sum_congr rfl (fun i _ => by ring)

/-- **Sufficient condition for tangency from the Lagrangian FOC**:
specialising to the case `lam_1 = 0` (no budget constraint, only expected-
return constraint), the FOC becomes `Σw = lam_2 · μ`, recovering the
cross-product tangent characterisation `IsTangentPortfolioN` from
`Portfolio/TangentPortfolio.lean`. -/
theorem isTangent_of_lagrangian_no_budget
    {ι : Type*} (s : Finset ι) (μ w : ι → ℝ) (Sg : ι → ι → ℝ)
    (lam_2 : ℝ)
    (h : ∀ i ∈ s, marginalVariance s Sg w i = lam_2 * μ i) :
    IsTangentPortfolioN s μ Sg w := by
  intro i hi j hj
  unfold marginalVariance at h
  rw [h i hi, h j hj]
  ring

end HybridVerify
