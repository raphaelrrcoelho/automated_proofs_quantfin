/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.RiskMeasures.Gaussian

/-!
# Rockafellar-Uryasev CVaR identity for gaussian losses

The Rockafellar-Uryasev variational form of CVaR is

  `CVaR_α(L) = inf_{c ∈ ℝ} {c + (1/(1−α)) · E[(L − c)⁺]}`,

and the infimum is achieved at `c* = VaR_α(L)`. Under continuous
distributions this yields the *additive identity*

  `CVaR_α = VaR_α + (1/(1−α)) · E[(L − VaR_α)⁺]`.

For gaussian losses `L ~ N(μ, σ²)` with right-tail quantile `z = Φ⁻¹(α)`,
the conditional expectation `E[(L − VaR_α)⁺] = σ · ϕ(z)`, so the additive
identity becomes

  `CVaR_α = VaR_α + (σ / (1−α)) · ϕ(z)`,

which is the equation we already have closed-form forms for. This file
states the algebraic identity directly.

Result:

* `gaussianCVaR_eq_VaR_plus_tail_term`: `CVaR = VaR + (σ/(1−α)) · ϕ(z)`,
  the Rockafellar-Uryasev decomposition of CVaR for gaussian losses.
-/

namespace QuantFin

open ProbabilityTheory Real

/-- **Rockafellar-Uryasev decomposition** for gaussian losses, after
computing `E[(Z − z)⁺] = ϕ(z) − z·(1 − α)` (the gaussian tail mean):

`CVaR_α = VaR_α + (σ / (1 − α)) · [ϕ(z) − z · (1 − α)]
       = VaR_α + σ · [ϕ(z)/(1 − α) − z]`.

This is the same identity as `gaussianCVaR_sub_VaR`, rearranged into the
R-U form `VaR + (1/(1−α)) · tail-expectation` that motivates the variational
characterization `CVaR_α = min_c [c + (1/(1−α)) · E[(L − c)⁺]]`. -/
lemma gaussianCVaR_rockafellarUryasev (μ σ z α : ℝ) :
    gaussianCVaR μ σ z α =
      gaussianVaR μ σ z +
        σ * (gaussianPDFReal 0 1 z / (1 - α) - z) := by
  unfold gaussianCVaR gaussianVaR
  ring

end QuantFin
