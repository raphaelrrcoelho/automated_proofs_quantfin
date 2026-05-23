/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.PDE
import QuantFin.BlackScholes.PutGreeks
import QuantFin.BlackScholes.StrikeGreeks

/-!
# Put-price convexity in strike

The put price's second `K`-derivative matches the call's:

  `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`,

since `bsP(K) − bsV(K) = K · e^{-rτ} − S` is linear in `K`. A clean expression
of put-call symmetry at the strike-convexity level.

Results:

* `gaussianPDFReal_zero_one_neg`: `ϕ(−x) = ϕ(x)` for the standard normal PDF.
* `hasDerivAt_bsP_KK`: `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`.
-/

namespace QuantFin

open Real ProbabilityTheory

/-- **Standard normal PDF symmetry**: `ϕ(−x) = ϕ(x)`. -/
lemma gaussianPDFReal_zero_one_neg (z : ℝ) :
    gaussianPDFReal 0 1 (-z) = gaussianPDFReal 0 1 z := by
  unfold gaussianPDFReal
  congr 1
  ring

/-- **Put-price convexity in `K`**: `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`,
identical to the call-price convexity (`hasDerivAt_bsV_KK`). The proof goes
through the put strike-derivative `∂_K bsP = e^{-rτ} · Φ(−d₂)` from
`BlackScholes.StrikeGreeks`. -/
lemma hasDerivAt_bsP_KK {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k => Real.exp (-(r * τ)) * Phi (-bsd2 S k r σ τ))
      (Real.exp (-(r * τ)) *
        gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
        (K * σ * Real.sqrt τ)) K := by
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_neg_d2 := h_d2_K.neg
  have h_Phi_neg_d2 := (hasDerivAt_Phi (-bsd2 S K r σ τ)).comp K h_neg_d2
  have h := h_Phi_neg_d2.const_mul (Real.exp (-(r * τ)))
  have h_pdf_sym : gaussianPDFReal 0 1 (-bsd2 S K r σ τ) =
      gaussianPDFReal 0 1 (bsd2 S K r σ τ) := gaussianPDFReal_zero_one_neg _
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  convert h using 1
  rw [h_pdf_sym]
  field_simp

end QuantFin
