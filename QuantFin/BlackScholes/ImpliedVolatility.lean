/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.PDE

/-!
# Implied volatility uniqueness

The **implied volatility** of a market option price `c` is the value of `σ`
for which the Black–Scholes price equals `c`. Existence requires the option
price to lie in the no-arbitrage range; **uniqueness** follows from strict
monotonicity of the BS call price in `σ`.

Strict monotonicity in `σ` follows from **positive vega**: by
`hasDerivAt_bsV_sigma`, `∂_σ V = S · ϕ(d_1) · √τ`. For `S > 0, T > 0`, this
is strictly positive (since `ϕ > 0`). A function with positive derivative
on an interval is strictly monotone there, hence injective.

## Main result

* `bsV_strictMonoOn_sigma`: the BS call price `σ ↦ V(K, r, σ, S, T)` is
  strictly monotone on `(0, ∞)` for `K, S, T > 0`.
* `implied_volatility_unique`: as a corollary, the implied volatility is
  unique whenever it exists.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Topology

/-- **Vega is strictly positive** for `S > 0, T > 0` and any `σ > 0`. -/
lemma bsV_vega_pos {K r : ℝ} (hK : 0 < K)
    {S σ T : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hT : 0 < T) :
    0 < S * gaussianPDFReal 0 1 (bsd1 S K r σ T) * Real.sqrt T := by
  have h_pdf_pos : 0 < gaussianPDFReal 0 1 (bsd1 S K r σ T) :=
    gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  positivity

/-- **The BS call price is strictly monotone in `σ`** on `(0, ∞)`.

A direct consequence of positive vega (`hasDerivAt_bsV_sigma` + `bsV_vega_pos`)
and the mean-value theorem (`strictMonoOn_of_deriv_pos`). -/
theorem bsV_strictMonoOn_sigma {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S : ℝ} (hS : 0 < S) :
    StrictMonoOn (fun σ => bsV K r σ S T) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · -- ContinuousOn (fun σ => bsV K r σ S T) (Set.Ioi 0)
    intro σ hσ
    have hσ_pos : 0 < σ := hσ
    exact ((hasDerivAt_bsV_sigma (r := r) hK hS hσ_pos hT).continuousAt).continuousWithinAt
  · intro σ hσ_int
    rw [interior_Ioi] at hσ_int
    have hσ_pos : 0 < σ := hσ_int
    have h_deriv := hasDerivAt_bsV_sigma (r := r) hK hS hσ_pos hT
    rw [h_deriv.deriv]
    exact bsV_vega_pos hK hS hσ_pos hT

/-- **Uniqueness of implied volatility.** If two volatilities `σ₁, σ₂ ∈ (0, ∞)`
give the same BS call price, then `σ₁ = σ₂`. Direct consequence of strict
monotonicity. -/
theorem implied_volatility_unique {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S : ℝ} (hS : 0 < S) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (h_eq : bsV K r σ₁ S T = bsV K r σ₂ S T) :
    σ₁ = σ₂ := by
  exact (bsV_strictMonoOn_sigma hK hT hS).injOn hσ₁ hσ₂ h_eq

/-! ## Newton-Raphson iteration (folded from `NewtonRaphsonIV.lean`)

The Newton iteration `σ_{n+1} = σ_n − f(σ_n)/f'(σ_n)` for root-finding. In
the BS implied-vol setting, `f(σ) = bsV(σ) − C_obs` and `f'(σ) = vega(σ) > 0`
(positive by `bsV_vega_pos`), so the iteration is well-defined for `σ > 0`.

Quadratic convergence requires bounding the residual via Taylor with
remainder; we record only the fixed-point-at-root and error-decomposition
identities. -/

/-- **Newton-Raphson iteration step**: `σ_{n+1} = σ_n − f(σ_n) / f'(σ_n)`. -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (σ : ℝ) : ℝ := σ - f σ / f' σ

/-- **A root is a fixed point of the Newton iteration**. -/
theorem newtonStep_fixed_at_root (f f' : ℝ → ℝ) {σ : ℝ} (h_root : f σ = 0) :
    newtonStep f f' σ = σ := by
  unfold newtonStep
  rw [h_root, zero_div, sub_zero]

/-- **Error decomposition for one Newton step** when `σ_*` is a root of `f`. -/
theorem newtonStep_error_via_root
    (f f' : ℝ → ℝ) {σ_star σ : ℝ} (_h_root : f σ_star = 0) :
    newtonStep f f' σ - σ_star = (σ - σ_star) - f σ / f' σ := by
  unfold newtonStep
  ring

end QuantFin
