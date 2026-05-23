/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Lookback call lower bound

The lookback call's payoff `max(M − K, 0)` (with `M = max_{t ∈ [0,T]} S_t`)
dominates the vanilla call payoff `max(S_T − K, 0)` because `S_T ≤ M`.
Discounted to today, this gives the static lower bound:

`lookbackCall ≥ vanillaCall`.

Result:

* `lookback_payoff_ge_vanilla`: `max(S − K, 0) ≤ max(M − K, 0)` when `S ≤ M`.
-/

namespace QuantFin

/-- **Lookback call payoff lower bound**: if `S ≤ M` (the running max), then
`max(S − K, 0) ≤ max(M − K, 0)`. -/
lemma lookback_payoff_ge_vanilla (M S K : ℝ) (h : S ≤ M) :
    max (S - K) 0 ≤ max (M - K) 0 :=
  max_le_max (by linarith) le_rfl

end QuantFin
