/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.FixedIncome.Vasicek

/-!
# Mean-reversion half-life — re-export

The Vasicek/OU half-life `t_{1/2} = log 2 / κ` and the verification that
`r(t_{1/2}) − θ = (r₀ − θ) / 2` are properties of the Vasicek deterministic
trajectory, not a separate model. The two lemmas have been folded into
`FixedIncome/Vasicek.lean` next to the trajectory definition.

This file is retained as an import path; the namespace `QuantFin`
exposes `meanReversionHalfLife` and `vasicekDeterministic_at_halfLife`
through the transitive import.
-/
