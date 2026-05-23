/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin

/-!
# Examples — a curated tour of five representative results

Five proofs chosen to span the project's techniques and topics. Each is a
direct re-export of a theorem already proved in the corresponding section;
this file exists to give a single high-density entry point for visitors.

1. **BS call delta** via the magic identity (`BlackScholes.PDE.hasDerivAt_bsV_S`).
2. **Markowitz min-variance** via completing-the-square
   (`Portfolio.Markowitz.portfolioVarTwo_eq_quad` + the lower bound).
3. **Gaussian VaR subadditivity** from the joint-stdev triangle inequality
   (`RiskMeasures.CoherentAxioms.gaussianVaR_subadditive`).
4. **Kelly criterion first-order optimality**
   (`Performance.Ratios.kellyGrowth_deriv_at_kelly`).
5. **Variance swap fair strike (log-payoff piece)**
   `(2/T)·E[log(F/S_T)] = σ²` (`BlackScholes.VarianceSwap.varianceSwap_log_contribution`).
-/

namespace QuantFin.Examples

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open QuantFin

/-! ### 1. Black-Scholes call delta `∂_S V = Φ(d₁)` -/

/-- The Black-Scholes call delta equals `Φ(d₁)`. The magic identity
`S·ϕ(d₁) = K·e^{-rτ}·ϕ(d₂)` makes the surviving `∂_S d_i` terms cancel,
leaving only `Φ(d₁)`. -/
example {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S :=
  hasDerivAt_bsV_S hK hσ hS hτ

/-! ### 2. Markowitz two-asset minimum variance via completing-the-square -/

/-- The two-asset portfolio variance factorizes as `D·(w − w*)² + V_min` (so the
minimum at `w = w*` is immediate and the value `V_min = σ₁²σ₂²(1 − ρ²)/D`
is closed form). -/
example {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) (w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w =
      minVarDenom σ₁ σ₂ ρ * (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2
      + minPortfolioVarTwo σ₁ σ₂ ρ :=
  portfolioVarTwo_eq_quad hD w

/-- Lower-bound property: every weight gives variance ≥ `V_min`. -/
example {σ₁ σ₂ ρ : ℝ}
    (hD : 0 < minVarDenom σ₁ σ₂ ρ) (w : ℝ) :
    minPortfolioVarTwo σ₁ σ₂ ρ ≤ portfolioVarTwo σ₁ σ₂ ρ w :=
  portfolioVarTwo_ge_min hD w

/-! ### 3. Gaussian VaR subadditivity (coherent risk measure axiom) -/

/-- For joint-gaussian losses with `|ρ| ≤ 1` and right-tail quantile `z ≥ 0`,
`VaR(L₁ + L₂) ≤ VaR(L₁) + VaR(L₂)`. The substantive inequality is the
joint-stdev triangle bound `√(σ₁² + 2ρσ₁σ₂ + σ₂²) ≤ σ₁ + σ₂`. -/
example {μ₁ μ₂ σ₁ σ₂ ρ z : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) (hz : 0 ≤ z) :
    gaussianVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2)) z ≤
      gaussianVaR μ₁ σ₁ z + gaussianVaR μ₂ σ₂ z :=
  gaussianVaR_subadditive h₁ h₂ hρ hz

/-! ### 4. Kelly criterion: first-order optimality at `f* = (pb − q)/b` -/

/-- At the Kelly fraction, the derivative of the expected log-growth vanishes —
this characterizes `f*` as the (interior) optimum. -/
example {p b : ℝ} (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f => kellyGrowth p b f) 0 (kellyFraction p b) :=
  kellyGrowth_deriv_at_kelly hp hp1 hb

/-! ### 5. Variance swap fair strike (Demeterfi-Derman-Kamal log-payoff piece) -/

/-- Under the BS lognormal hypothesis (gaussian `Z`, `S_T = S_0 exp((r-σ²/2)T +
σ√T Z)`), the log-payoff piece of the variance swap replication identity gives
`(2/T) · E[log(F/S_T)] = σ²` where `F = S_0 e^{rT}`. -/
example {S_0 : ℝ} (hS : 0 < S_0) (r σ T : ℝ) (hT : T ≠ 0) :
    (2 / T) *
      (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
            (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        ∂(gaussianReal 0 1)) = σ^2 :=
  varianceSwap_log_contribution hS r σ T hT

end QuantFin.Examples
