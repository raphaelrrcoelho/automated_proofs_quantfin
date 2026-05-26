/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Gaussian VaR and CVaR closed forms

For a loss `L ~ N(μ, σ²)`, Value-at-Risk and Conditional Value-at-Risk at level
`α` admit the closed forms

  `VaR_α(L) = μ + σ · z`,    where `z = Φ⁻¹(α)`,
  `CVaR_α(L) = μ + σ · ϕ(z) / (1 − α)`.

We parametrize on the quantile `z` rather than on `α` directly, since Mathlib
at the current pin does not ship a clean `Φ⁻¹` API. All identities below are
algebraic; the only Mathlib facts used are `gaussianPDFReal` and the field /
ring tactics.

Results:

* `gaussianVaR_affine`: `VaR(a·L + b) = a · VaR(L) + b` for `a ≥ 0`.
* `gaussianCVaR_affine`: `CVaR(a·L + b) = a · CVaR(L) + b` for `a ≥ 0`.
* `gaussianVaR_standard`: `VaR(N(0,1)) = z`.
* `gaussianCVaR_standard`: `CVaR(N(0,1)) = ϕ(z) / (1 − α)`.
* `gaussianCVaR_sub_VaR`: `CVaR − VaR = σ · (ϕ(z)/(1−α) − z)`.
* `gaussianVaR_volatility_scaling`: under iid time aggregation
  (`σ_T = σ · √T`), `VaR_α(L_T) = T · μ + σ · √T · z`.
-/

namespace QuantFin

open ProbabilityTheory Real

/-- Gaussian VaR at quantile `z = Φ⁻¹(α)` for a loss `L ~ N(μ, σ²)`. -/
noncomputable def gaussianVaR (μ σ z : ℝ) : ℝ := μ + σ * z

/-- Gaussian CVaR at quantile `z` and level `α` for a loss `L ~ N(μ, σ²)`. -/
noncomputable def gaussianCVaR (μ σ z α : ℝ) : ℝ :=
  μ + σ * (gaussianPDFReal 0 1 z / (1 - α))

/-- **VaR affine invariance**: `VaR(a·L + b) = a · VaR(L) + b` for `a ≥ 0`. The
volatility scales by the genuine standard deviation `|a|·σ` of `a·L + b`, so the
hypothesis `0 ≤ a` is load-bearing — it discharges `|a| = a`. -/
lemma gaussianVaR_affine (μ σ z a b : ℝ) (ha : 0 ≤ a) :
    gaussianVaR (a * μ + b) (|a| * σ) z = a * gaussianVaR μ σ z + b := by
  unfold gaussianVaR
  rw [abs_of_nonneg ha]; ring

/-- **CVaR affine invariance**: `CVaR(a·L + b) = a · CVaR(L) + b` for `a ≥ 0`
(volatility scales by `|a|·σ`, so `0 ≤ a` is load-bearing). -/
lemma gaussianCVaR_affine (μ σ z α a b : ℝ) (ha : 0 ≤ a) :
    gaussianCVaR (a * μ + b) (|a| * σ) z α = a * gaussianCVaR μ σ z α + b := by
  unfold gaussianCVaR
  rw [abs_of_nonneg ha]; ring

/-- Standard normal VaR collapses to the quantile itself. -/
lemma gaussianVaR_standard (z : ℝ) : gaussianVaR 0 1 z = z := by
  unfold gaussianVaR; ring

/-- Standard normal CVaR equals `ϕ(z) / (1 − α)`. -/
lemma gaussianCVaR_standard (z α : ℝ) :
    gaussianCVaR 0 1 z α = gaussianPDFReal 0 1 z / (1 - α) := by
  unfold gaussianCVaR; ring

/-- **CVaR/VaR difference**: `CVaR − VaR = σ · (ϕ(z)/(1−α) − z)`. -/
lemma gaussianCVaR_sub_VaR (μ σ z α : ℝ) :
    gaussianCVaR μ σ z α - gaussianVaR μ σ z =
      σ * (gaussianPDFReal 0 1 z / (1 - α) - z) := by
  unfold gaussianCVaR gaussianVaR
  ring

/-- **Volatility scaling under iid time aggregation**: for `L_T = ∑_{i=1}^T L_i`
with each `L_i ~ N(μ, σ²)` iid, `L_T ~ N(T·μ, T·σ²)`, so
`VaR_α(L_T) = T·μ + σ·√T · z`. The identity is purely algebraic. -/
lemma gaussianVaR_volatility_scaling (μ σ z T : ℝ) :
    gaussianVaR (T * μ) (σ * Real.sqrt T) z = T * μ + σ * Real.sqrt T * z := by
  unfold gaussianVaR
  ring

end QuantFin
