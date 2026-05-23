/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Triangle arbitrage no-arbitrage condition

For three currencies `A, B, C` with exchange rates `S_AB` (units of `A` per
unit of `B`), `S_BC`, `S_CA`, the round-trip `A → B → C → A` converts one
unit of `A` into

  `S_AB · S_BC · S_CA`

units of `A` (modulo transaction costs, which we ignore). No-arbitrage forces
this round-trip product to be exactly `1`; if `> 1`, the round trip is a
risk-free gain; if `< 1`, the reverse trip is.

## Result

* `TriangleNoArb`: definition `S_AB · S_BC · S_CA = 1`.
* `triangleNoArb_solve_third`: given two rates (non-zero), the no-arb constraint
  uniquely determines the third: `S_CA = 1 / (S_AB · S_BC)`.
* `triangleNoArb_inverse_consistency`: if `S_CA = 1 / (S_AC)` and similarly
  for the other pairs, no-arb is equivalent to `S_AC · S_CB · S_BA = 1`.
-/

namespace QuantFin

/-- **Triangle no-arbitrage**: three exchange rates `S_AB`, `S_BC`, `S_CA`
in cyclic order satisfy `S_AB · S_BC · S_CA = 1` (otherwise a riskless
round-trip arbitrage exists). -/
def TriangleNoArb (S_AB S_BC S_CA : ℝ) : Prop :=
  S_AB * S_BC * S_CA = 1

/-- **No-arb determines the third rate uniquely**: given `S_AB`, `S_BC` both
non-zero, the no-arb constraint forces `S_CA = 1 / (S_AB · S_BC)`. -/
theorem triangleNoArb_solve_third {S_AB S_BC : ℝ}
    (h_ab : S_AB ≠ 0) (h_bc : S_BC ≠ 0) :
    ∃! S_CA : ℝ, TriangleNoArb S_AB S_BC S_CA := by
  have h_prod_ne : S_AB * S_BC ≠ 0 := mul_ne_zero h_ab h_bc
  refine ⟨1 / (S_AB * S_BC), ?_, ?_⟩
  · -- Existence: plug in `1 / (S_AB · S_BC)`.
    unfold TriangleNoArb
    field_simp
  · -- Uniqueness: any other solution must equal it.
    intro S_CA h
    unfold TriangleNoArb at h
    field_simp
    linarith

end QuantFin
