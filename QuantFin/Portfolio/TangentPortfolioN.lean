/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Portfolio.TangentPortfolio

/-!
# N-asset tangent portfolio — re-export

The N-asset tangent FOC has been folded into
`Portfolio/TangentPortfolio.lean`, where it sits next to the two-asset
closed form (of which it is the natural generalisation).

The namespace `QuantFin` exposes `IsTangentPortfolioN` and
`isTangent_of_proportional` through the transitive import.
-/
