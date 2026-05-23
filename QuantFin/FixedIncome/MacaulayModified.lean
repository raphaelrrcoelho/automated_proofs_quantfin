/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Macaulay vs modified duration under discrete compounding

For a bond with discrete-compounded yield `y` and cashflows `c_i` at times
`t_i ∈ ℕ`, define the duration numerators

  `MacNum(y) = Σ t_i · c_i / (1 + y)^{t_i}`,
  `ModNum(y) = Σ t_i · c_i / (1 + y)^{t_i + 1}`.

Modified duration is `ModNum / Price`, Macaulay duration is `MacNum / Price`.
The discrete-compounding identity is

`ModNum(y) = MacNum(y) / (1 + y)`,

i.e. modified duration differs from Macaulay duration by exactly one factor of
the discount step. (Under continuous compounding the two coincide, which is
the lemma `bondMacaulay_eq_modified_continuous` in `FixedIncome/ZCB`.)

Result:

* `modifiedNumerator_eq_macaulayNumerator_div`: the algebraic identity.
-/

namespace QuantFin

open Finset

variable {ι : Type*}

/-- Bond price under discrete annual compounding with integer cashflow times. -/
noncomputable def bondPriceDisc (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, c i / (1 + y) ^ t i

/-- Macaulay duration numerator. -/
noncomputable def macaulayNumerator (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (t i : ℝ) * c i / (1 + y) ^ t i

/-- Modified duration numerator. -/
noncomputable def modifiedNumerator (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (t i : ℝ) * c i / (1 + y) ^ (t i + 1)

/-- **Modified = Macaulay / (1 + y)** at the level of numerators, hence at the
level of durations themselves. -/
lemma modifiedNumerator_eq_macaulayNumerator_div
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) (hy : 1 + y ≠ 0) :
    modifiedNumerator s t c y =
      macaulayNumerator s t c y / (1 + y) := by
  unfold modifiedNumerator macaulayNumerator
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_succ]
  field_simp

end QuantFin
