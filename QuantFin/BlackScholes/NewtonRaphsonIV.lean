/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.BlackScholes.ImpliedVolatility

/-!
# Newton-Raphson iteration — re-export

The Newton iteration step `σ_{n+1} = σ_n − f(σ_n)/f'(σ_n)`, fixed-point-at-
root, and error-decomposition lemmas have been folded into
`BlackScholes/ImpliedVolatility.lean`, where they sit next to the
implied-vol uniqueness machinery.

The namespace `QuantFin` exposes `newtonStep`, `newtonStep_fixed_at_root`,
and `newtonStep_error_via_root` through the transitive import.
-/
