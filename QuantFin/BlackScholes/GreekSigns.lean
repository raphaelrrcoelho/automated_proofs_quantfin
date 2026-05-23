/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.PDE
import QuantFin.BlackScholes.PriceBounds

/-!
# Black-Scholes Greek sign constraints

The signs of the BS Greeks are determined by the structure of the call
price formula and the positivity of the standard-normal PDF/CDF. They are
collected here as named lemmas — the library has the individual derivatives
scattered across `PDE.lean`, `StrikeGreeks.lean`, and `HigherGreeks.lean`,
but the sign constraints are not explicitly stated.

The sign constraints are the *qualitative* content of the BS Greeks: a
trader can read each sign off the formula and the table below.

| Greek | Sign for call | Reason |
|---|---|---|
| δ = ∂_S V    | ≥ 0    | `Φ(d_1) ∈ [0, 1]` |
| γ = ∂²_S V   | > 0    | `ϕ(d_1) > 0`, positive denominator |
| ν = ∂_σ V    | > 0    | `S · ϕ(d_1) · √τ > 0` (already in ImpliedVolatility.lean) |
| ρ = ∂_r V    | ≥ 0    | `K · τ · e^{−rτ} · Φ(d_2) ≥ 0` |
| ∂_K V        | ≤ 0    | `−e^{−rτ} · Φ(d_2) ≤ 0` (call decreases in strike) |
| ∂²_K V       | ≥ 0    | `e^{−rτ} · ϕ(d_2)/(K σ √τ) ≥ 0` (Breeden-Litzenberger) |

These signs are the *qualitative* expression of: a call is increasing
and convex in spot, increasing in vol, decreasing and convex in strike,
increasing in rate, decreasing in dividends.

## Results

* `bsV_delta_nonneg`, `bsV_delta_le_one`: `Φ(d_1) ∈ [0, 1]`.
* `bsV_gamma_pos`: `∂²_S V > 0` (call strictly convex in spot).
* `bsV_rho_nonneg`: `∂_r V ≥ 0` (call increasing in rate).
* `bsV_partial_K_nonpos`: `∂_K V ≤ 0` (call decreasing in strike).
* `bsV_partial_KK_nonneg`: `∂²_K V ≥ 0` (call convex in strike).
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ## Delta sign constraints -/

/-- **Call delta is non-negative**: `0 ≤ Φ(d_1)`. -/
theorem bsV_delta_nonneg (S K r σ τ : ℝ) : 0 ≤ Phi (bsd1 S K r σ τ) :=
  Phi_nonneg _

/-- **Call delta is at most 1**: `Φ(d_1) ≤ 1`. -/
theorem bsV_delta_le_one (S K r σ τ : ℝ) : Phi (bsd1 S K r σ τ) ≤ 1 :=
  Phi_le_one _

/-! ## Gamma sign constraint -/

/-- **Call gamma is strictly positive**: `∂²_S V = ϕ(d_1) / (S σ √τ) > 0`
for `S, σ, τ > 0`. The call price is strictly convex in spot. -/
theorem bsV_gamma_pos {K r σ : ℝ} (_hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    0 < gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ) := by
  have h_pdf_pos : 0 < gaussianPDFReal 0 1 (bsd1 S K r σ τ) :=
    gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  have h_den_pos : 0 < S * σ * Real.sqrt τ :=
    mul_pos (mul_pos hS hσ) (Real.sqrt_pos.mpr hτ)
  exact div_pos h_pdf_pos h_den_pos

/-! ## Rho sign constraint -/

/-- **Call rho is non-negative**: `∂_r V = K · τ · e^{−rτ} · Φ(d_2) ≥ 0`
for `K ≥ 0` and `τ ≥ 0`. The call price increases in the risk-free rate. -/
theorem bsV_rho_nonneg {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (S r σ : ℝ) :
    0 ≤ K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_Phi_nn : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg hK hτ) h_exp_nn) h_Phi_nn

/-! ## Strike-direction sign constraints -/

/-- **Partial in strike is non-positive**: `∂_K V = −e^{−rτ} · Φ(d_2) ≤ 0`.
The call price decreases in the strike (a more out-of-the-money option
is worth less). -/
theorem bsV_partial_K_nonpos (S K r σ τ : ℝ) :
    -(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) ≤ 0 := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_Phi_nn : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  have := mul_nonneg h_exp_nn h_Phi_nn
  linarith

/-- **Second partial in strike is non-negative**: `∂²_K V = e^{−rτ} · ϕ(d_2) /
(K · σ · √τ) ≥ 0` for `K, σ, τ > 0`. This is the *infinitesimal* face of
butterfly non-negativity (`butterfly_payoff_nonneg`); via Breeden-Litzenberger
it equals `e^{−rτ}` times the implied PDF, which must be non-negative because
it *is* a probability density. -/
theorem bsV_partial_KK_nonneg {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    (S r : ℝ) :
    0 ≤ Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
          (K * σ * Real.sqrt τ) := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S K r σ τ) :=
    gaussianPDFReal_nonneg _ _ _
  have h_num_nn : 0 ≤ Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) :=
    mul_nonneg h_exp_nn h_pdf_nn
  have h_den_pos : 0 < K * σ * Real.sqrt τ :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hτ)
  exact div_nonneg h_num_nn h_den_pos.le

end QuantFin
