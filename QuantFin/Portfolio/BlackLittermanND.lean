/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Portfolio.BlackLitterman

/-!
# N-dimensional Black-Litterman posterior (matrix form, first-principles)

The pre-existing `Portfolio/BlackLitterman.lean` derives the 1-D Bayesian
update for a single asset with a single direct view. This file extends to
the **N-asset / m-view matrix** formulation, the standard form used in
production.

## Setup

* `π : Fin n → ℝ` — prior mean of expected returns.
* `Sg_inv : Matrix (Fin n) (Fin n) ℝ` — prior *precision* (inverse covariance).
* `Q : Fin m → ℝ` — view vector (target values).
* `P : Matrix (Fin m) (Fin n) ℝ` — view-selection matrix (which linear
  combinations of `μ` the views talk about).
* `Om_inv : Matrix (Fin m) (Fin m) ℝ` — view *precision* (inverse covariance
  of view noise).

## Posterior identities

The Bayesian-conjugate update gives

  `posterior_precision = Sg_inv + Pᵀ · Om_inv · P`,             (additive precision)
  `posterior_precision · μ_post = Sg_inv · π + Pᵀ · Om_inv · Q`. (normal equation)

When posterior precision is invertible, the posterior mean has the explicit
form

  `μ_post = (posterior_precision)⁻¹ · (Sg_inv · π + Pᵀ · Om_inv · Q)`.

This file proves: (a) the explicit form satisfies the normal equation, and
(b) the solution to the normal equation is *unique* (when precision is
invertible).

## Why this is "first principles"

The 1-D `BlackLitterman.lean` stated the posterior as a closed form and
verified three equivalent forms (symmetric, precision-weighted, harmonic-
variance). This file derives the N-dim posterior as the **unique solution
of a linear system** — the natural way to characterise it without ad-hoc
inverses, and the way it is used in practice (LU/Cholesky solve rather
than explicit inversion).

## Connection to the 1-D module

Specialising `n = 1`, `m = 1`, `P = (1)`, `Sg_inv = (1/s0sq)`, `Om_inv =
(1/s1sq)` recovers the 1-D posterior `posteriorMean1d` from
`Portfolio/BlackLitterman.lean`.

## Results

* `blPosteriorPrecision`: definition `Sg_inv + Pᵀ · Om_inv · P`.
* `blPrecisionWeightedMean`: definition `Sg_inv · π + Pᵀ · Om_inv · Q`.
* `IsBLPosteriorMean`: variational characterisation as the normal-equation
  solution.
* `blPosteriorMean`: explicit form using `(posterior_precision)⁻¹`.
* `blPosteriorMean_satisfies_normal_eq`: explicit form satisfies the
  normal equation.
* `IsBLPosteriorMean_unique`: solution to the normal equation is unique
  (when posterior precision is invertible).
-/

namespace QuantFin

open Matrix

/-- **N-dim BL posterior precision**: additive Bayesian update of precision.
`posterior_precision = prior_precision + view_precision`, where the view
precision is `Pᵀ · Om_inv · P` (the information about `μ` provided by the
linear views). -/
def blPosteriorPrecision {n m : ℕ}
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Sg_inv + Pᵀ * Om_inv * P

/-- **N-dim BL precision-weighted mean RHS**: `Sg_inv · π + Pᵀ · Om_inv · Q`.
This is the RHS of the BL normal equation. -/
def blPrecisionWeightedMean {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Fin n → ℝ :=
  Sg_inv *ᵥ π + (Pᵀ * Om_inv) *ᵥ Q

/-- **N-dim BL posterior mean as the normal-equation solution** (variational
characterisation). A vector `μ_post : Fin n → ℝ` is a BL posterior mean iff
it satisfies

  `(Sg_inv + Pᵀ · Om_inv · P) · μ_post = Sg_inv · π + Pᵀ · Om_inv · Q`.

This characterisation does not require the precision to be invertible — it
is well-defined for any precision (the existence of a solution requires
the RHS to be in the column span of the LHS; uniqueness requires
invertibility). -/
def IsBLPosteriorMean {n m : ℕ}
    (μ_post π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (blPosteriorPrecision Sg_inv P Om_inv).mulVec μ_post =
    blPrecisionWeightedMean π Q Sg_inv P Om_inv

/-- **Explicit form of the N-dim BL posterior mean** (when posterior
precision is invertible): apply the inverse to the precision-weighted mean. -/
noncomputable def blPosteriorMean {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Fin n → ℝ :=
  (blPosteriorPrecision Sg_inv P Om_inv)⁻¹ *ᵥ
    blPrecisionWeightedMean π Q Sg_inv P Om_inv

/-- **Explicit form satisfies the normal equation** (when posterior precision
is invertible). -/
theorem blPosteriorMean_satisfies_normal_eq {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ)
    [Invertible (blPosteriorPrecision Sg_inv P Om_inv)] :
    IsBLPosteriorMean (blPosteriorMean π Q Sg_inv P Om_inv) π Q Sg_inv P Om_inv := by
  unfold IsBLPosteriorMean blPosteriorMean
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_inv_of_invertible]
  rw [Matrix.one_mulVec]

/-- **Uniqueness of the BL posterior mean** (when posterior precision is
invertible): any solution to the normal equation equals the explicit form. -/
theorem IsBLPosteriorMean_unique {n m : ℕ}
    {μ_post π : Fin n → ℝ} {Q : Fin m → ℝ}
    {Sg_inv : Matrix (Fin n) (Fin n) ℝ}
    {P : Matrix (Fin m) (Fin n) ℝ}
    {Om_inv : Matrix (Fin m) (Fin m) ℝ}
    [Invertible (blPosteriorPrecision Sg_inv P Om_inv)]
    (h : IsBLPosteriorMean μ_post π Q Sg_inv P Om_inv) :
    μ_post = blPosteriorMean π Q Sg_inv P Om_inv := by
  unfold IsBLPosteriorMean at h
  unfold blPosteriorMean
  rw [← h]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.inv_mul_of_invertible]
  rw [Matrix.one_mulVec]

end QuantFin
