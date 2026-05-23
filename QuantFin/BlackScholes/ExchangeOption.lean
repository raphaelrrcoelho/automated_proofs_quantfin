/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.GarmanNormalForm

/-!
# Margrabe's exchange option: a two-asset option that is a one-asset BS problem

The **exchange option** pays `max(S¹_T − S²_T, 0)` — the right to exchange
asset 2 for asset 1 at maturity. Its defining structural fact (Margrabe 1978)
is that it depends only on the *ratio* `S¹/S²`, which is itself lognormal
with an **effective volatility**

  `σ² = σ₁² + σ₂² − 2 ρ σ₁ σ₂`,

so the two-asset problem collapses to a one-asset Black-Scholes problem at
that effective vol. This is the first genuinely multivariate result in the
library, and it reuses (rather than re-derives) the 1-D machinery — the same
"structural reduction" discipline as `PowerCall`.

This file establishes the two pieces of the reduction:

* `margrabe_variance_sub` / `margrabe_effective_variance` — the effective
  variance of the log-spread, from covariance bilinearity. This is the first
  consumer of the covariance machinery that `Foundations/BivariateGaussian`
  also uses, making that machinery load-bearing.
* `exchange_payoff_eq_ratio` — the payoff reduction `max(S¹ − S², 0) = S² ·
  max(S¹/S² − 1, 0)`, exhibiting the exchange option as a (numeraire-scaled)
  vanilla call on the ratio.

The price-level Margrabe formula combines these with a change of numeraire to
the `S²`-measure (composing with `Foundations/GaussianGirsanov` and
`BlackScholes/StockNumeraire`) and is the next increment.

## Results

* `margrabe_variance_sub`: `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁, L₂)`.
* `margrabe_effective_variance`: substituting `σ₁²T, σ₂²T, ρσ₁σ₂T` gives the
  effective variance `(σ₁² + σ₂² − 2ρσ₁σ₂)·T`.
* `exchange_payoff_eq_ratio`: `max(a − b, 0) = b · max(a/b − 1, 0)` for `b > 0`.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory

/-- **Variance of a spread** via covariance bilinearity: for two L²
random variables, `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁, L₂)`. The
cross term carries the correlation — this is where the `−2ρσ₁σ₂` of the
Margrabe effective volatility comes from. -/
theorem margrabe_variance_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {L₁ L₂ : Ω → ℝ} (h₁ : MemLp L₁ 2 P) (h₂ : MemLp L₂ 2 P) :
    Var[L₁ - L₂; P] = Var[L₁; P] + Var[L₂; P] - 2 * cov[L₁, L₂; P] := by
  rw [← covariance_self (h₁.sub h₂).aemeasurable,
      covariance_sub_left h₁ h₂ (h₁.sub h₂),
      covariance_sub_right h₁ h₁ h₂, covariance_sub_right h₂ h₁ h₂,
      covariance_self h₁.aemeasurable, covariance_self h₂.aemeasurable,
      covariance_comm L₂ L₁]
  ring

/-- **Margrabe effective variance**: with `Var L₁ = σ₁²T`, `Var L₂ = σ₂²T`,
and `cov(L₁, L₂) = ρσ₁σ₂T`, the log-spread variance is
`(σ₁² + σ₂² − 2ρσ₁σ₂)·T` — the effective variance at which the exchange
option prices as a one-asset Black-Scholes call. -/
theorem margrabe_effective_variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {L₁ L₂ : Ω → ℝ} {σ₁ σ₂ ρ T : ℝ}
    (h₁ : MemLp L₁ 2 P) (h₂ : MemLp L₂ 2 P)
    (hV₁ : Var[L₁; P] = σ₁ ^ 2 * T) (hV₂ : Var[L₂; P] = σ₂ ^ 2 * T)
    (hcov : cov[L₁, L₂; P] = ρ * σ₁ * σ₂ * T) :
    Var[L₁ - L₂; P] = (σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) * T := by
  rw [margrabe_variance_sub h₁ h₂, hV₁, hV₂, hcov]
  ring

/-- **Exchange-option payoff reduction**: `max(a − b, 0) = b · max(a/b − 1, 0)`
for `b > 0`. The exchange payoff `max(S¹_T − S²_T, 0)` is `S²_T` times a
vanilla call payoff on the ratio `S¹_T/S²_T` struck at `1` — the algebraic
form of "use `S²` as numeraire." -/
theorem exchange_payoff_eq_ratio (a b : ℝ) (hb : 0 < b) :
    max (a - b) 0 = b * max (a / b - 1) 0 := by
  rw [mul_max_of_nonneg _ _ hb.le, mul_zero,
      show b * (a / b - 1) = a - b from by field_simp]

/-! ## Margrabe price is a Garman-normal-form instance

The exchange-option closed form is the *one* BS-family formula
`V = A·Φ(d₁) − K·DF·Φ(d₂)` at `A = S¹₀`, `K = S²₀`, `DF = 1` (the
S²-numeraire / forward measure carries no discounting), and effective vol
`σ = √(σ₁² + σ₂² − 2ρσ₁σ₂)`. So Margrabe joins Black-Scholes, Black-76,
BS-Merton, Garman-Kohlhagen, and KMV-Merton as instances of `bsVGarman`. -/

/-- **Margrabe `d₁`**: `(log(S¹₀/S²₀) + σ²T/2) / (σ√T)`, with `σ` the
effective volatility of the log-spread. -/
noncomputable def margrabeD1 (S1 S2 σ T : ℝ) : ℝ :=
  (Real.log (S1 / S2) + σ ^ 2 * T / 2) / (σ * Real.sqrt T)

/-- **Margrabe `d₂`**: `d₁ − σ√T`. -/
noncomputable def margrabeD2 (S1 S2 σ T : ℝ) : ℝ :=
  margrabeD1 S1 S2 σ T - σ * Real.sqrt T

/-- **Margrabe exchange-option price**: `S¹₀·Φ(d₁) − S²₀·Φ(d₂)`. -/
noncomputable def margrabePrice (S1 S2 σ T : ℝ) : ℝ :=
  S1 * Phi (margrabeD1 S1 S2 σ T) - S2 * Phi (margrabeD2 S1 S2 σ T)

/-- **Margrabe is a Garman-normal-form instance**: the exchange-option price
equals `bsVGarman` at `A = S¹₀`, `K = S²₀`, `DF = 1`, effective vol `σ`. The
second asset plays the role of the discounted strike and `DF = 1` because the
S²-numeraire measure carries no discounting. So a *multivariate* option is the
same closed form `V = A·Φ(d₁) − K·DF·Φ(d₂)` as every BS-family price — one
more consumer of the `GarmanNormalForm` principle. -/
theorem margrabe_eq_bsVGarman (S1 S2 σ T : ℝ) :
    margrabePrice S1 S2 σ T = bsVGarman S1 S2 1 σ T := by
  have hd1 : margrabeD1 S1 S2 σ T = gbsd1 S1 S2 1 σ T := by
    unfold margrabeD1 gbsd1; rw [mul_one]
  unfold margrabePrice bsVGarman margrabeD2 gbsd2
  rw [hd1, mul_one]

end QuantFin
