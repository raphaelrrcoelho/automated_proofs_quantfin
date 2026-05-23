/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Actuarial.Mortality

/-!
# Compound Poisson MGF — re-export

The compound Poisson MGF identity `e^{−λ} · e^{λ M} = e^{λ(M − 1)}` and the
Lundberg adjustment-coefficient equation have been folded into
`Actuarial/Mortality.lean`, alongside the force-of-mortality machinery —
both live in the same actuarial family.

The namespace `QuantFin` exposes `compoundPoisson_mgf_identity`,
`isLundbergAdjustmentCoefficient`, and `lundberg_zero_at_zero` through the
transitive import.
-/
