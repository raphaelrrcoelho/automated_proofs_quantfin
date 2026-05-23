/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Almgren-Chriss optimal execution (deterministic closed form)

Liquidating `X_0` units of an asset over horizon `T` with linear temporary
impact (coefficient `η`) and price-variance risk aversion (coefficient `λ`),
the optimal trajectory `X(t)` (remaining inventory) minimises the
deterministic cost functional

  `∫_0^T (σ² λ · X(t)² + η · X'(t)²) dt`

subject to `X(0) = X_0` and `X(T) = 0`. The Euler-Lagrange equation reduces
to

  `X''(t) = κ² · X(t)`,    `κ² := σ² λ / η`,

a linear ODE with hyperbolic-cosine/sinh solutions. The boundary-condition-
satisfying solution is

  `X(t) = X_0 · sinh(κ · (T − t)) / sinh(κ · T)`.

We verify the closed form satisfies:
- the initial condition `X(0) = X_0`,
- the terminal condition `X(T) = 0`,
- the EL equation `X''(t) = κ² · X(t)`.

The full minimisation theorem (this closed form is optimal among all
admissible trajectories) is a calculus-of-variations claim that requires
function-space machinery beyond Mathlib's current pin.

## Results

* `almgrenChrissPath`: closed-form trajectory.
* `almgrenChrissPath_at_zero`: `X(0) = X_0`.
* `almgrenChrissPath_at_terminal`: `X(T) = 0`.
* `hasDerivAt_almgrenChrissPath`: first derivative.
* `almgrenChrissPath_satisfies_EL`: `X''(t) = κ² · X(t)`.
-/

namespace QuantFin

open Real

/-- **Almgren-Chriss optimal-execution trajectory**:
`X(t) = X_0 · sinh(κ (T − t)) / sinh(κ T)`. Liquidation rate `−X'(t)` is
slow at the start and accelerates near `T`. -/
noncomputable def almgrenChrissPath (X_0 κ T t : ℝ) : ℝ :=
  X_0 * Real.sinh (κ * (T - t)) / Real.sinh (κ * T)

/-- **Initial condition**: `X(0) = X_0`. -/
theorem almgrenChrissPath_at_zero (X_0 κ T : ℝ) (hT : Real.sinh (κ * T) ≠ 0) :
    almgrenChrissPath X_0 κ T 0 = X_0 := by
  unfold almgrenChrissPath
  rw [sub_zero]
  field_simp

/-- **Terminal condition**: `X(T) = 0`. -/
theorem almgrenChrissPath_at_terminal (X_0 κ T : ℝ) :
    almgrenChrissPath X_0 κ T T = 0 := by
  unfold almgrenChrissPath
  rw [sub_self, mul_zero, Real.sinh_zero]
  simp

/-- **First derivative**: `X'(t) = −X_0 · κ · cosh(κ (T − t)) / sinh(κ T)`. -/
theorem hasDerivAt_almgrenChrissPath (X_0 κ T : ℝ)
    (hT : Real.sinh (κ * T) ≠ 0) (t : ℝ) :
    HasDerivAt (almgrenChrissPath X_0 κ T)
      (-(X_0 * κ * Real.cosh (κ * (T - t)) / Real.sinh (κ * T))) t := by
  unfold almgrenChrissPath
  -- Inner derivative: d/dt (κ (T − t)) = −κ.
  have h_inner : HasDerivAt (fun t : ℝ => κ * (T - t)) (-κ) t := by
    have h_id : HasDerivAt (fun t : ℝ => T - t) (-1) t := by
      have := (hasDerivAt_id t).const_sub T
      simpa using this
    have := h_id.const_mul κ
    convert this using 1
    ring
  have h_sinh : HasDerivAt (fun t => Real.sinh (κ * (T - t)))
                (Real.cosh (κ * (T - t)) * (-κ)) t := h_inner.sinh
  have h_mul := h_sinh.const_mul X_0
  have h_div := h_mul.div_const (Real.sinh (κ * T))
  convert h_div using 1
  field_simp

/-- **Almgren-Chriss EL equation**: the closed-form trajectory satisfies
`X''(t) = κ² · X(t)` (the Euler-Lagrange equation of the cost functional).
The second derivative — obtained by differentiating the first — has the
same `sinh(κ (T − t))` shape multiplied by `κ²`. -/
theorem almgrenChrissPath_satisfies_EL (X_0 κ T : ℝ)
    (hT : Real.sinh (κ * T) ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        -(X_0 * κ * Real.cosh (κ * (T - s)) / Real.sinh (κ * T)))
      (κ^2 * almgrenChrissPath X_0 κ T t) t := by
  unfold almgrenChrissPath
  -- d/dt of cosh(κ (T − t)) = sinh(κ (T − t)) · (−κ).
  have h_inner : HasDerivAt (fun t : ℝ => κ * (T - t)) (-κ) t := by
    have h_id : HasDerivAt (fun t : ℝ => T - t) (-1) t := by
      have := (hasDerivAt_id t).const_sub T
      simpa using this
    have := h_id.const_mul κ
    convert this using 1
    ring
  have h_cosh : HasDerivAt (fun t => Real.cosh (κ * (T - t)))
                (Real.sinh (κ * (T - t)) * (-κ)) t := h_inner.cosh
  have h_const_mul := h_cosh.const_mul (X_0 * κ)
  have h_div := h_const_mul.div_const (Real.sinh (κ * T))
  have h_neg := h_div.neg
  convert h_neg using 1
  field_simp

end QuantFin
