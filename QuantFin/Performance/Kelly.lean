/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Performance.Ratios

/-!
# Multi-period Kelly criterion and Kelly fraction bounds

For `T` periods of iid binary bets at the same fraction `f`, the expected
log-growth aggregates linearly:

  `T · g(f) = T · (p log(1 + f·b) + q log(1 - f))`.

Maximizing this over `f` is the same single-period problem, so the multi-period
Kelly fraction equals the single-period one — Kelly is myopic.

Additionally:

* **`kellyFraction < 1`**: the Kelly fraction is always strictly less than 1 for
  proper probabilities `p < 1` and positive payoffs `b > 0` (no all-in bet
  except in the degenerate `p = 1` case).
* **`kellyFraction = 0 iff break-even`**: `f* = 0` iff `p(b+1) = 1`.
* **`kellyFraction > 0 iff favorable bet`**: `f* > 0` iff `p(b+1) > 1`.

Results:

* `kellyGrowth_n_periods`: multi-period log-growth at fraction `f` equals
  `T · kellyGrowth p b f`.
* `kelly_n_periods_deriv_at_kelly`: first-order optimality for `T · kellyGrowth`
  vanishes at the single-period `kellyFraction p b`.
* `kellyFraction_lt_one`, `kellyFraction_eq_zero_iff`, `kellyFraction_pos_iff`:
  bounds and sign analysis of the Kelly fraction.
-/

namespace QuantFin

open Real

/-- Multi-period log-growth: at constant fraction `f` over `T` periods of iid
binary bets, the total log-growth equals `T · g(f)`. -/
lemma kellyGrowth_n_periods (T : ℕ) (p b f : ℝ) :
    (T : ℝ) * kellyGrowth p b f =
      (T : ℝ) * (p * Real.log (1 + f * b) + (1 - p) * Real.log (1 - f)) := rfl

/-- **Multi-period Kelly first-order condition**: the optimal fraction is
independent of the horizon `T`. -/
lemma kelly_n_periods_deriv_at_kelly (T : ℕ) {p b : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f => (T : ℝ) * kellyGrowth p b f) 0 (kellyFraction p b) := by
  have h := kellyGrowth_deriv_at_kelly hp hp1 hb
  have h_mul := h.const_mul (T : ℝ)
  simpa using h_mul

/-- **Kelly fraction < 1** for proper probabilities and positive payoff. -/
lemma kellyFraction_lt_one {p b : ℝ} (hp : p < 1) (hb : 0 < b) :
    kellyFraction p b < 1 := by
  unfold kellyFraction
  rw [div_lt_one hb]
  nlinarith

/-- **Kelly fraction = 0 iff break-even bet** (`p · (b + 1) = 1`). -/
lemma kellyFraction_eq_zero_iff (p : ℝ) {b : ℝ} (hb : b ≠ 0) :
    kellyFraction p b = 0 ↔ p * (b + 1) = 1 := by
  unfold kellyFraction
  rw [div_eq_zero_iff]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · linarith
    · exact absurd h hb
  · intro h; left; linarith

/-- **Kelly fraction > 0 iff favorable bet** (`p · (b + 1) > 1`). -/
lemma kellyFraction_pos_iff (p : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < kellyFraction p b ↔ 1 < p * (b + 1) := by
  unfold kellyFraction
  rw [lt_div_iff₀ hb]
  refine ⟨?_, ?_⟩ <;> intro h <;> linarith

end QuantFin
