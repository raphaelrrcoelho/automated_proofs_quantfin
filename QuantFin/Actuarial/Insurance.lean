/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Net premium principle (life insurance)

The **net premium principle** sets the periodic premium `P` of an insurance
contract by equating the present value of expected premiums with the
present value of expected benefits:

  `P · annuityFactor = benefitPV`,

so `P = benefitPV / annuityFactor`. Both quantities are deterministic
expectations under the mortality-and-interest joint setup.

Two algebraic results:

* **Annuity-due formula** `ä_n = (1 − v^n) / d` where `v = 1/(1+i)` and
  `d = 1 − v` is the discount rate. (Mirror of the immediate-annuity
  closed form `a_n = (1 − v^n) / i` in `CouponBonds.lean`.)
* **Net premium algebra**: `P · ä_n = benefitPV ⟺ P = benefitPV / ä_n`.

Results:

* `annuityDueValue`: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)` (geometric).
* `net_premium_principle`: equivalent algebraic statement.
-/

namespace QuantFin

open Finset

/-- **Annuity-due geometric closed form**: `Σ_{k=0}^{n-1} v^k = (1 − v^n)/(1 − v)`
for `v ≠ 1`. -/
theorem annuityDueValue (v : ℝ) (n : ℕ) (hv : v ≠ 1) :
    ∑ k ∈ Finset.range n, v ^ k = (1 - v ^ n) / (1 - v) := by
  have h_one_sub_ne : (1 : ℝ) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have h_v_sub_ne : v - 1 ≠ 0 := sub_ne_zero.mpr hv
  rw [geom_sum_eq hv n]
  rw [div_eq_div_iff h_v_sub_ne h_one_sub_ne]
  ring

/-- **Net premium principle**: if both `P · A = B` and `A ≠ 0`, then
`P = B / A`. Restated as a strict equivalence for use in delivery
benchmarks. -/
theorem net_premium_principle (P A B : ℝ) (hA : A ≠ 0) :
    P * A = B ↔ P = B / A := by
  constructor
  · intro h; rw [← h]; field_simp
  · intro h; rw [h]; field_simp

end QuantFin
