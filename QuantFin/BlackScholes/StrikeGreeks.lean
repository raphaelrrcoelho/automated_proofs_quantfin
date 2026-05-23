/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.PDE
import QuantFin.BlackScholes.PutGreeks

/-!
# Black-Scholes price monotonicity and convexity in the strike `K`

Standard derivative-Greek identities in the strike direction:

* `∂_K bsV = -e^{-rτ} · Φ(d₂)` (call price strictly decreasing in `K`).
* `∂_K bsP = e^{-rτ} · Φ(-d₂)` (put price strictly increasing in `K`),
  via put-call parity `bsP = bsV - S + K · e^{-rτ}`.
* `∂²_K bsV = e^{-rτ} · ϕ(d₂) / (K σ √τ) ≥ 0` (call price convex in `K` —
  equivalent to butterfly-spread non-negativity).

The clean closed forms come from the magic identity
`S · ϕ(d₁) = K · e^{-rτ} · ϕ(d₂)` (`bs_identity`) which collapses the
`d₁`-derivative contribution.

Results:

* `hasDerivAt_bsd1_K`, `hasDerivAt_bsd2_K`: `∂_K d_i = −1/(K σ √τ)`.
* `hasDerivAt_bsV_K`: `∂_K bsV = −e^{-rτ} · Φ(d₂)`.
* `hasDerivAt_bsP_K`: `∂_K bsP = e^{-rτ} · Φ(-d₂)`.
* `hasDerivAt_bsV_KK`: `∂²_K bsV = e^{-rτ} · ϕ(d₂) / (K σ √τ)` (convexity in K).
-/

namespace QuantFin

open Real ProbabilityTheory

/-- `∂_K d₁(S, K, r, σ, τ) = −1 / (K · σ · √τ)`. Mirror of `hasDerivAt_bsd1_S`. -/
lemma hasDerivAt_bsd1_K (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ)
    {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => bsd1 S k r σ τ) (-(1 / (K * σ * Real.sqrt τ))) K := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  -- k ↦ log k has derivative 1/K at K.
  have h_log : HasDerivAt Real.log (1 / K) K := by
    rw [one_div]; exact Real.hasDerivAt_log hK_ne
  -- k ↦ log S - log k has derivative -(1/K) at K.
  have h_minus_log : HasDerivAt
      (fun k : ℝ => Real.log S - Real.log k) (-(1 / K)) K := by
    have h_neg := h_log.neg
    have h_add := h_neg.const_add (Real.log S)
    convert h_add using 1
  -- log(S/k) =ᶠ[𝓝 K] log S - log k (since K ≠ 0 in a nbhd).
  have h_eventually : (fun k : ℝ => Real.log (S / k)) =ᶠ[nhds K]
                       (fun k => Real.log S - Real.log k) := by
    filter_upwards [eventually_ne_nhds hK_ne] with k hk
    exact Real.log_div hS.ne' hk
  have h_log_div : HasDerivAt (fun k : ℝ => Real.log (S / k)) (-(1 / K)) K :=
    h_minus_log.congr_of_eventuallyEq h_eventually
  -- Add the constant `(r + σ²/2)τ`.
  have h_num : HasDerivAt
      (fun k : ℝ => Real.log (S / k) + (r + σ ^ 2 / 2) * τ) (-(1 / K)) K := by
    simpa using h_log_div.add_const ((r + σ ^ 2 / 2) * τ)
  -- Divide by σ√τ.
  have h_div_στ : HasDerivAt
      (fun k : ℝ => (Real.log (S / k) + (r + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      (-(1 / K) / (σ * Real.sqrt τ)) K :=
    h_num.div_const (σ * Real.sqrt τ)
  have h_val_eq :
      -(1 / K) / (σ * Real.sqrt τ) = -(1 / (K * σ * Real.sqrt τ)) := by
    field_simp
  rw [h_val_eq] at h_div_στ
  exact h_div_στ

/-- `∂_K d₂(S, K, r, σ, τ) = −1 / (K · σ · √τ)` (same as `∂_K d_1` since `d_2 − d_1`
is `K`-independent). -/
lemma hasDerivAt_bsd2_K (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ)
    {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => bsd2 S k r σ τ) (-(1 / (K * σ * Real.sqrt τ))) K := by
  have h_d1 := hasDerivAt_bsd1_K S r σ τ hS hσ hτ hK
  have h_const : HasDerivAt (fun _ : ℝ => σ * Real.sqrt τ) 0 K := hasDerivAt_const K _
  have h_diff := h_d1.sub h_const
  have h_fun_eq : (fun k : ℝ => bsd1 S k r σ τ - σ * Real.sqrt τ)
        = (fun k : ℝ => bsd2 S k r σ τ) := by
    funext k; rw [bsd2]
  rw [show -(1 / (K * σ * Real.sqrt τ)) =
      -(1 / (K * σ * Real.sqrt τ)) - 0 from by ring]
  rw [← h_fun_eq]
  exact h_diff

/-- **Strike-derivative of the call price**: `∂_K bsV = −e^{-rτ} · Φ(d₂)`.
The magic identity `S · ϕ(d₁) = K · e^{-rτ} · ϕ(d₂)` collapses the `d_1`
contribution. -/
lemma hasDerivAt_bsV_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k => bsV k r σ S τ)
      (-(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ))) K := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  -- Pieces
  have h_d1_K := hasDerivAt_bsd1_K S r σ τ hS hσ hτ hK
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp K h_d1_K
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp K h_d2_K
  -- d/dK [S · Phi(d_1(K))] = S · ϕ(d_1) · ∂_K d_1
  have h_S_Phi_d1 := h_Phi_d1.const_mul S
  -- d/dK [K · exp(-rτ) · Phi(d_2(K))] = exp(-rτ)·Phi(d_2) + K·exp(-rτ)·ϕ(d_2)·∂_K d_2
  have h_id : HasDerivAt (fun k : ℝ => k) 1 K := hasDerivAt_id K
  have h_K_Phi_d2 := h_id.mul h_Phi_d2
  have h_K_exp_Phi_d2 := h_K_Phi_d2.const_mul (Real.exp (-(r * τ)))
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun k : ℝ =>
        S * Phi (bsd1 S k r σ τ) -
        Real.exp (-(r * τ)) * (k * Phi (bsd2 S k r σ τ))) =
      (fun k : ℝ => bsV k r σ S τ) := by
    funext k
    show S * Phi (bsd1 S k r σ τ) -
          Real.exp (-(r * τ)) * (k * Phi (bsd2 S k r σ τ)) =
        bsV k r σ S τ
    unfold bsV
    ring
  rw [← h_fun_eq]
  convert h_V using 1
  -- Value side: collapse via magic identity
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  simp only [Function.comp_apply]
  field_simp
  linarith [h_bs]

/-- **Strike-derivative of the put price**: `∂_K bsP = e^{-rτ} · Φ(-d₂)`. Follows
from put-call parity `bsP = bsV − S + K · e^{-rτ}`. -/
lemma hasDerivAt_bsP_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k => bsP k r σ S τ)
      (Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ)) K := by
  have h_eq : (fun k : ℝ => bsP k r σ S τ) =
        fun k => bsV k r σ S τ - S + k * Real.exp (-(r * τ)) := by
    funext k; rw [bsP_eq_bsV k r σ S τ]
  rw [h_eq]
  have h_V := hasDerivAt_bsV_K (S := S) (r := r) (σ := σ) hS hσ hK hτ
  have h_const : HasDerivAt (fun _ : ℝ => S) 0 K := hasDerivAt_const K S
  have h_lin : HasDerivAt (fun k : ℝ => k * Real.exp (-(r * τ)))
      (Real.exp (-(r * τ))) K := by
    have := (hasDerivAt_id K).mul_const (Real.exp (-(r * τ)))
    simpa using this
  have h := (h_V.sub h_const).add h_lin
  convert h using 1
  -- Value: e^{-rτ}·Φ(-d_2) = -(e^{-rτ}·Φ(d_2)) - 0 + e^{-rτ}
  --                      = e^{-rτ}·(1 - Φ(d_2))
  --                      = e^{-rτ}·Φ(-d_2)  by Phi_neg
  have h_Phi := Phi_neg (bsd2 S K r σ τ)
  linear_combination Real.exp (-(r * τ)) * h_Phi

/-- **Convexity of the call price in `K`** (Greek `∂²_K bsV`):
`∂²_K bsV = e^{-rτ} · ϕ(d₂) / (K σ √τ) ≥ 0`. This is butterfly-spread
non-negativity in differential form. -/
lemma hasDerivAt_bsV_KK {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k => -(Real.exp (-(r * τ)) * Phi (bsd2 S k r σ τ)))
      (Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
        (K * σ * Real.sqrt τ)) K := by
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp K h_d2_K
  have h := (h_Phi_d2.const_mul (Real.exp (-(r * τ)))).neg
  convert h using 1
  -- value: e^{-rτ}·ϕ(d_2)/(K·σ·√τ) = -(e^{-rτ}·(ϕ(d_2)·(-1/(K·σ·√τ))))
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  field_simp

end QuantFin
