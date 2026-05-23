/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Capped call payoff decomposition

A capped call with strikes `K₁ ≤ K₂` pays `min(max(S − K₁, 0), K₂ − K₁)`. Below
`K₁` the payoff is `0`; between `K₁` and `K₂` it tracks `S − K₁`; above `K₂` it
is capped at `K₂ − K₁`. Algebraically this equals the bull-call spread

`max(S − K₁, 0) − max(S − K₂, 0)`,

so a capped call is replicated by a long call at `K₁` and a short call at `K₂`.

Result:

* `cappedCall_eq_bull_spread`: case-by-case over `S` vs `K₁, K₂`.
-/

namespace QuantFin

/-- **Capped call as a bull call spread**: for `K₁ ≤ K₂`,
`min(max(S − K₁, 0), K₂ − K₁) = max(S − K₁, 0) − max(S − K₂, 0)`. -/
lemma cappedCall_eq_bull_spread (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :
    min (max (S - K₁) 0) (K₂ - K₁) =
      max (S - K₁) 0 - max (S - K₂) 0 := by
  by_cases h1 : S ≤ K₁
  · have e1 : max (S - K₁) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : (0:ℝ) ≤ K₂ - K₁)]; ring
  push_neg at h1
  by_cases h2 : S ≤ K₂
  · have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : S - K₁ ≤ K₂ - K₁)]; ring
  · push_neg at h2
    have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = S - K₂ := max_eq_left (by linarith)
    rw [e1, e2]
    rw [min_eq_right (by linarith : K₂ - K₁ ≤ S - K₁)]; ring

end QuantFin
