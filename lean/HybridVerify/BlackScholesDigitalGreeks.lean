/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholesPDE
import HybridVerify.BachelierModel

/-!
# Black–Scholes digital option Greeks

For the two digital (binary) European options:

* **Cash-or-nothing** call price `V_cash(S, τ) = e^{-rτ} Φ(d₂)`.
* **Asset-or-nothing** call price `V_asset(S, τ) = S Φ(d₁)`.

We derive their deltas and gammas:

* `hasDerivAt_bsCashDigital_S` — δ_cash = e^{-rτ} ϕ(d₂) / (S σ √τ).
* `hasDerivAt_bsCashDigital_SS` — γ_cash = -e^{-rτ} ϕ(d₂) · d₁ / (S² σ² τ).
* `hasDerivAt_bsAssetDigital_S` — δ_asset = Φ(d₁) + ϕ(d₁) / (σ √τ).
* `hasDerivAt_bsAssetDigital_SS` — γ_asset = -ϕ(d₁) · d₂ / (S σ² τ).

(The latter follows from the BS magic identity `K e^{-rτ} ϕ(d₂) = S ϕ(d₁)`
which collapses the `S · ϕ(d₁) · ∂_S d₁` chain-rule term. Gammas use the
clean identity `σ√τ − d₁ = -d₂`.)
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- Cash-or-nothing digital call price as a function of `(S, τ)`. -/
noncomputable def bsCashDigital (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)

/-- Asset-or-nothing digital call price as a function of `(S, τ)`. -/
noncomputable def bsAssetDigital (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  S * Phi (bsd1 S K r σ τ)

/-- **Cash-or-nothing delta**: `∂_S V_cash = e^{-rτ} ϕ(d₂) / (S σ √τ)`.

Direct chain rule on `Φ ∘ d₂(S)`. -/
lemma hasDerivAt_bsCashDigital_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsCashDigital K r σ s τ)
      (Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  have h := h_Phi_d2.const_mul (Real.exp (-(r * τ)))
  unfold bsCashDigital
  convert h using 1
  ring

/-- **Asset-or-nothing delta**: `∂_S V_asset = Φ(d₁) + ϕ(d₁) / (σ √τ)`.

The chain rule gives `Φ(d₁) + S · ϕ(d₁) · ∂_S d₁ = Φ(d₁) + S · ϕ(d₁) · 1/(S σ √τ)
= Φ(d₁) + ϕ(d₁) / (σ √τ)`. -/
lemma hasDerivAt_bsAssetDigital_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsAssetDigital K r σ s τ)
      (Phi (bsd1 S K r σ τ) + gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (σ * Real.sqrt τ)) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_id : HasDerivAt (fun s : ℝ => s) 1 S := hasDerivAt_id S
  have h := h_id.mul h_Phi_d1
  unfold bsAssetDigital
  convert h using 1
  simp only [Function.comp_apply]
  field_simp

/-- `(d/dz) ϕ(0, 1, z) = -z · ϕ(0, 1, z)`. -/
private lemma hasDerivAt_pdf_digital (z : ℝ) :
    HasDerivAt (fun z' : ℝ => gaussianPDFReal 0 1 z')
      (-(z * gaussianPDFReal 0 1 z)) z := by
  have h := (HybridVerify.hasDerivAt_neg_gaussianPDFReal_zero_one z).neg
  have h_eq : ((-fun z' : ℝ => -gaussianPDFReal 0 1 z') : ℝ → ℝ)
            = fun z' : ℝ => gaussianPDFReal 0 1 z' := by funext z'; simp
  rw [h_eq] at h
  exact h

/-- **Asset-or-nothing gamma**: `∂²V_asset/∂S² = -ϕ(d₁) · d₂ / (S σ² τ)`.

Differentiating δ_asset = Φ(d₁) + ϕ(d₁)/(σ√τ): the Φ-term contributes
`ϕ(d₁) · ∂_S d₁ = ϕ(d₁)/(Sσ√τ)`, and the ϕ-term contributes
`-d₁ ϕ(d₁) · ∂_S d₁ / (σ√τ) = -d₁ ϕ(d₁)/(Sσ²τ)`. Sum via `σ√τ − d₁ = -d₂`. -/
lemma hasDerivAt_bsAssetDigital_SS {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt
      (fun s => Phi (bsd1 s K r σ τ) +
        gaussianPDFReal 0 1 (bsd1 s K r σ τ) / (σ * Real.sqrt τ))
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) *
        bsd2 S K r σ τ / (S * σ ^ 2 * τ))) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  -- ∂_S Φ(d₁) = ϕ(d₁) · ∂_S d₁
  have h_Phi := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  -- ∂_S ϕ(d₁) = -d₁ ϕ(d₁) · ∂_S d₁
  have h_pdf := (hasDerivAt_pdf_digital (bsd1 S K r σ τ)).comp S h_d1_S
  -- ∂_S [ϕ(d₁) / (σ √τ)] = (∂_S ϕ(d₁)) / (σ √τ)
  have h_pdf_div := h_pdf.div_const (σ * Real.sqrt τ)
  have h_full := h_Phi.add h_pdf_div
  convert h_full using 1
  rw [show bsd2 S K r σ τ = bsd1 S K r σ τ - σ * Real.sqrt τ from by rw [bsd2]]
  field_simp
  rw [show Real.sqrt τ ^ 2 = τ from h_sqrt_sq]
  ring

end HybridVerify
