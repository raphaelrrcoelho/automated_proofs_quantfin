/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.PDE

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

namespace QuantFin

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

/-- **BS-Merton rho**: `∂_r V_q = K · τ · e^{-rτ} · Φ(d₂')`.

`V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`. Chain rule on `r-q` gives
`∂_r V_q = e^{-qT} · bsV_rho(K, r-q, σ, S, T) = e^{-qT} · K·τ·e^{-(r-q)τ}·Φ(d₂')`,
and `e^{-qT} · e^{-(r-q)τ} = e^{-rτ}`. -/
lemma hasDerivAt_bsVDiv_r {K q σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (r : ℝ) :
    HasDerivAt (fun r' => bsVDiv K r' q σ S τ)
      (K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K (r - q) σ τ)) r := by
  -- Chain rule on r' ↦ r' - q.
  have h_sub_q : HasDerivAt (fun r' : ℝ => r' - q) 1 r := by
    simpa using (hasDerivAt_id r).sub_const q
  have h_bsV_rho := hasDerivAt_bsV_r (σ := σ) (τ := τ) hK hσ hτ hS (r - q)
  have h_comp := h_bsV_rho.comp r h_sub_q
  have h_full := h_comp.const_mul (Real.exp (-(q * τ)))
  unfold bsVDiv
  convert h_full using 1
  -- Value: e^{-qτ} · (K·τ·e^{-(r-q)τ}·Φ(d_2) · 1) = K·τ·e^{-rτ}·Φ(d_2)
  have h_exp_combine :
      Real.exp (-(q * τ)) * Real.exp (-((r - q) * τ)) = Real.exp (-(r * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination
    -(K * τ * Phi (bsd2 S K (r - q) σ τ)) * h_exp_combine

/-- **BS-Merton psi** (dividend Greek): `∂_q V_q = -S · τ · e^{-qτ} · Φ(d₁')`.

`V_q = e^{-qτ} · bsV(K, r-q, σ, S, τ)`. Product rule:
* `∂_q [e^{-qτ}] = -τ · e^{-qτ}`
* `∂_q [bsV(K, r-q, σ, S, τ)] = -bsV_rho(K, r-q, σ, S, τ) = -K·τ·e^{-(r-q)τ}·Φ(d₂')`

Combining and using `S · e^{-qτ} · Φ(d₁') − K · e^{-rτ} · Φ(d₂') = V_q`,
the result collapses to `-S · τ · e^{-qτ} · Φ(d₁')`. -/
lemma hasDerivAt_bsVDiv_q {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (q : ℝ) :
    HasDerivAt (fun q' => bsVDiv K r q' σ S τ)
      (-(S * τ * Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ))) q := by
  -- Setup: f(q') = e^{-q'τ}, g(q') = bsV(K, r-q', σ, S, τ). V_q = f·g.
  -- ∂_q' f = -τ · e^{-q'τ}
  have h_f : HasDerivAt (fun q' : ℝ => Real.exp (-(q' * τ)))
      (-τ * Real.exp (-(q * τ))) q := by
    have h_neg : HasDerivAt (fun q' : ℝ => -(q' * τ)) (-τ) q := by
      have := (hasDerivAt_id q).mul_const τ; simpa using this.neg
    have h := h_neg.exp
    convert h using 1; ring
  -- ∂_q' [bsV(K, r-q', σ, S, τ)] via chain rule on (r - q').
  have h_sub : HasDerivAt (fun q' : ℝ => r - q') (-1) q := by
    have := (hasDerivAt_id q).const_sub r
    simpa using this
  have h_bsV_rho := hasDerivAt_bsV_r (σ := σ) (τ := τ) hK hσ hτ hS (r - q)
  have h_g := h_bsV_rho.comp q h_sub
  -- h_g : HasDerivAt (fun q' => bsV K (r - q') σ S τ) (K·τ·e^{-(r-q)τ}·Φ(d_2) · -1) q
  -- Product: V_q' = f(q') · g(q'), derivative = f'(q)·g(q) + f(q)·g'(q).
  have h_full := h_f.mul h_g
  unfold bsVDiv
  convert h_full using 1
  simp only [Function.comp_apply]
  unfold bsV
  ring

/-- **BS-Merton theta** (`∂_τ` form): `∂_τ V_q = -q · V_q + e^{-qτ} · (call_theta_at_drift_{r-q})`.

Product rule on `V_q = e^{-qτ} · bsV(K, r-q, σ, S, τ)`. -/
lemma hasDerivAt_bsVDiv_tau {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t => bsVDiv K r q σ S t)
      (-(q * bsVDiv K r q σ S τ) +
        Real.exp (-(q * τ)) *
          (σ * S * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ) / (2 * Real.sqrt τ)
            + (r - q) * K * Real.exp (-((r - q) * τ)) * Phi (bsd2 S K (r - q) σ τ))) τ := by
  -- f(t) = e^{-qt}, derivative -q · e^{-qt}
  have h_f : HasDerivAt (fun t : ℝ => Real.exp (-(q * t))) (-q * Real.exp (-(q * τ))) τ := by
    have h_neg : HasDerivAt (fun t : ℝ => -(q * t)) (-q) τ := by
      have := (hasDerivAt_id τ).const_mul q
      simpa using this.neg
    have h := h_neg.exp
    convert h using 1; ring
  -- g(t) = bsV K (r-q) σ S t, derivative from hasDerivAt_bsV_tau
  have h_g := hasDerivAt_bsV_tau (r := r - q) hK hσ hS hτ
  -- Product
  have h_full := h_f.mul h_g
  unfold bsVDiv
  convert h_full using 1
  ring

end QuantFin
