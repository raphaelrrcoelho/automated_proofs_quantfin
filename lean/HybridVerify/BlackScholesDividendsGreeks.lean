/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholesPDE

/-!
# Black-Scholes-Merton (continuous dividends) Greeks

For the dividends-adjusted call price `V_q(S, σ, T) = S e^{-qT} Φ(d₁') − K e^{-rT} Φ(d₂')`
with `d_i' = bsdi S K (r-q) σ T`, we identify `V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`
and derive the Greeks via existing call Greeks at effective drift `r − q`.

## Main results

* `bsVDiv` — the dividend-adjusted call price, expressed via the identity.
* `hasDerivAt_bsVDiv_S` — δ_q = e^{-qT} · Φ(d₁').
* `hasDerivAt_bsVDiv_SS` — γ_q = e^{-qT} · ϕ(d₁') / (S σ √τ).
* `hasDerivAt_bsVDiv_sigma` — vega_q = e^{-qT} · S · ϕ(d₁') · √τ.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- Dividends-adjusted BS call price. Identity: `V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`. -/
noncomputable def bsVDiv (K r q σ : ℝ) (S τ : ℝ) : ℝ :=
  Real.exp (-(q * τ)) * bsV K (r - q) σ S τ

/-- **BS-Merton delta**: `∂_S V_q = e^{-qT} · Φ(d₁')` where `d₁' = bsd1 S K (r-q) σ T`. -/
lemma hasDerivAt_bsVDiv_S {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsVDiv K r q σ s τ)
      (Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ)) S := by
  have h_bs := hasDerivAt_bsV_S (r := r - q) hK hσ hS hτ
  exact h_bs.const_mul (Real.exp (-(q * τ)))

/-- **BS-Merton gamma**: `∂²_S V_q = e^{-qT} · ϕ(d₁') / (S σ √τ)`. -/
lemma hasDerivAt_bsVDiv_SS {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => Real.exp (-(q * τ)) * Phi (bsd1 s K (r - q) σ τ))
      (Real.exp (-(q * τ)) * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
        / (S * σ * Real.sqrt τ)) S := by
  have h_bs := hasDerivAt_bsV_SS (r := r - q) hK hσ hS hτ
  have h := h_bs.const_mul (Real.exp (-(q * τ)))
  convert h using 1; ring

/-- **BS-Merton vega**: `∂_σ V_q = e^{-qT} · S · ϕ(d₁') · √τ`. -/
lemma hasDerivAt_bsVDiv_sigma {K r q : ℝ} (hK : 0 < K)
    {S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsVDiv K r q s S τ)
      (Real.exp (-(q * τ)) * S * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
        * Real.sqrt τ) σ := by
  have h_bs := hasDerivAt_bsV_sigma (r := r - q) hK hS hσ hτ
  have h := h_bs.const_mul (Real.exp (-(q * τ)))
  convert h using 1; ring

end HybridVerify
