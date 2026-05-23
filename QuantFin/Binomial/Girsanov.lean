/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.Model

/-!
# Discrete Girsanov: measure change in the single-period binomial tree

The continuous-time Girsanov theorem has a transparent discrete-time
counterpart in the binomial model.

Given physical up-probability `p` and risk-neutral up-probability `q`, the
**Radon-Nikodym derivative** `dQ/dP` takes only two values:

  `Z_up = q / p`,    `Z_down = (1 − q) / (1 − p)`.

The key invariant: `E^P[Z] = 1` (the change of measure preserves total mass).
Plugging in:

  `p · (q/p) + (1 − p) · ((1 − q)/(1 − p)) = q + (1 − q) = 1`.

This is the *cleanest possible* instance of Girsanov: a finite, two-point
measure change with explicit RN derivative.

## Why this matters

Every continuous-time risk-neutral pricing argument is `E^Q[X] = E^P[Z · X]`
for the appropriate `Z = dQ/dP`. In the binomial model the same identity
holds with `Z` as above, and the risk-neutral pricing formula

  `V_0 = e^{−r} · E^Q[V_T] = e^{−r} · E^P[Z · V_T]`

is just two-state algebra. We make this discrete Girsanov-machinery explicit.

## Results

* `binomialRN`: the two-valued RN derivative.
* `binomialRN_expectation_one`: `E^P[Z] = 1` (RN normalisation).
* `binomial_riskNeutral_via_RN`: discrete pricing identity
  `E^Q[V_T] = E^P[Z · V_T] = p · Z_up · V_u + (1 − p) · Z_down · V_d`.
-/

namespace QuantFin

open Real

/-- **Radon-Nikodym derivative `dQ/dP`** for the single-period binomial measure
change. At the up state it equals `q/p`; at the down state, `(1−q)/(1−p)`. -/
noncomputable def binomialRN (p q : ℝ) : Bool → ℝ
  | true => q / p
  | false => (1 - q) / (1 - p)

/-- **RN normalisation**: `E^P[Z] = 1`, i.e.
`p · (q/p) + (1 − p) · ((1 − q)/(1 − p)) = 1`.

This is the universal "the change of measure preserves total mass"
property, here in two-state form. -/
theorem binomialRN_expectation_one (p q : ℝ)
    (hp : p ≠ 0) (hp1 : p ≠ 1) :
    p * binomialRN p q true + (1 - p) * binomialRN p q false = 1 := by
  unfold binomialRN
  have h_1mp_ne : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  field_simp
  ring

/-- **Discrete Girsanov pricing identity**: under the binomial measure change,
the `Q`-expectation of any payoff equals the `P`-expectation of `Z · payoff`,
where `Z = dQ/dP`:

  `E^Q[V] = q · V_u + (1−q) · V_d = E^P[Z · V] = p · (q/p) · V_u + (1−p) · ((1−q)/(1−p)) · V_d`.

(Both sides simplify to `q · V_u + (1 − q) · V_d`.) -/
theorem binomial_riskNeutral_via_RN (p q V_u V_d : ℝ)
    (hp : p ≠ 0) (hp1 : p ≠ 1) :
    q * V_u + (1 - q) * V_d =
      p * binomialRN p q true * V_u + (1 - p) * binomialRN p q false * V_d := by
  unfold binomialRN
  have h_1mp_ne : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  field_simp

end QuantFin
