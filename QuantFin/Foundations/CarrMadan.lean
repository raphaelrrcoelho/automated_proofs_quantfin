/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.VarianceSwap

/-!
# Carr-Madan static replication — stub / acknowledgement

The full Carr-Madan identity

  `g(S) = g(F) + g'(F)(S − F) + ∫₀^F g''(K)(K − S)⁺ dK + ∫_F^∞ g''(K)(S − K)⁺ dK`

is a Taylor-with-integral-remainder application that requires Mathlib's
intervalIntegral machinery. The algebraic core (the log-payoff identity
`log(S) − log(F) = log(S/F)`) is literally `Real.log_div`, and the
*log-payoff variance-swap connection* is already realised in
`BlackScholes/VarianceSwap.lean` (the `varianceSwap_log_contribution`
theorem there is the substantive Carr-Madan-style result we have).

This file records `carrMadan_log_payoff_algebra` as a thin alias for
`Real.log_div`, retained only for the benchmark-import API. The substantive
Carr-Madan-style log-payoff replication is formalised in
`BlackScholes/VarianceSwap.lean` (`varianceSwap_log_contribution`).
-/

namespace QuantFin

/-- **Carr-Madan log-payoff algebra**: `log(S) − log(F) = log(S/F)`. Recorded
as an alias for `Real.log_div` for the benchmark-import API. -/
theorem carrMadan_log_payoff_algebra (S F : ℝ) (hS : 0 < S) (hF : 0 < F) :
    Real.log S - Real.log F = Real.log (S / F) := by
  rw [Real.log_div hS.ne' hF.ne']

end QuantFin
