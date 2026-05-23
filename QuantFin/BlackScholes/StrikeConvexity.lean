/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.StrikeGreeks

/-!
# Strike-direction convexity at every scale

The European call satisfies *the same* convexity-in-`K` fact at three
different scales of resolution:

1. **Payoff level**, `K ↦ max(S − K, 0)`. Convex because the positive
   part of an affine function is convex (`ConvexOn.sup` on `(S − ·)` and
   `0`).
2. **Finite-state price level**, `K ↦ Σ q_i · max(S_i − K, 0)`. Convex
   because non-negative linear combinations of convex functions are convex
   (`ConvexPricingFunctional.callPrice_finiteState_convexOn_K`).
3. **Continuous BS price level**, `K ↦ bsV K r σ S τ`. Convex on `(0, ∞)`
   because its second `K`-derivative is non-negative
   (`hasDerivAt_bsV_KK` + `convexOn_of_deriv2_nonneg'`).

The three scales are not three theorems; they are one principle realised at
three different levels of integration. This file packages all three so the
hierarchy is visible.

## Downstream consequences (one principle, many faces)

* **Bull spread** `V(K₁) ≥ V(K₂)` for `K₁ ≤ K₂` — `Antitone`-payoff after
  pricing-functional preservation of monotonicity.
* **Butterfly non-negativity at payoff** (`butterfly_payoff_nonneg`) —
  convex-payoff second-difference inequality.
* **Butterfly non-negativity at price** (`callPrice_finiteState_butterfly_nonneg`) —
  pricing functional preserves convexity, hence the same second-difference
  is non-negative at the price level.
* **Breeden-Litzenberger PDF positivity** (`lognormalTerminalPDF_nonneg`) —
  the infinitesimal manifestation of price-level convexity, by
  `bsV_strike_convexOn` below + `convexOn_iff_deriv2_nonneg`.

## Results

* `convexOn_sub_const_id`: `K ↦ a − K` is convex.
* `convexOn_call_payoff`: `K ↦ max(S − K, 0)` is convex in K (payoff level).
* `antitone_call_payoff`: `K ↦ max(S − K, 0)` is antitone in K.
* `bsV_strike_convexOn`: `K ↦ bsV K r σ S τ` is convex on `(0, ∞)`
  (continuous BS price level).
-/

namespace QuantFin

open Set Real ProbabilityTheory

/-- The affine function `K ↦ a − K` is convex on `Set.univ`. Affine
functions are simultaneously convex and concave; the inequality holds
with equality. -/
lemma convexOn_sub_const_id (a : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ => a - K) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ s t _ _ hst => ?_⟩
  show a - (s • K₁ + t • K₂) ≤ s • (a - K₁) + t • (a - K₂)
  simp only [smul_eq_mul]
  -- Equality (affine functions are tight): `s·a + t·a = a` via `s + t = 1`.
  have h_sa_ta : s * a + t * a = a := by linear_combination a * hst
  linarith

/-- **Call payoff is convex in the strike**: `K ↦ max(S − K, 0)` is convex.

This is the structural spine of static option-price no-arbitrage relations.
Butterfly non-negativity and Breeden-Litzenberger PDF positivity are
discrete and infinitesimal consequences (respectively) of this single fact,
after passing through risk-neutral expectation. -/
lemma convexOn_call_payoff (S : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ => max (S - K) 0) :=
  (convexOn_sub_const_id S).sup (convexOn_const (0 : ℝ) convex_univ)

/-- **Call payoff is antitone in the strike**: higher strikes pay less.

Equivalent to monotonicity of `max(·, 0)` composed with `K ↦ S − K` (which
is itself antitone). The single-line consequence of monotonicity of `max`. -/
lemma antitone_call_payoff (S : ℝ) :
    Antitone (fun K : ℝ => max (S - K) 0) :=
  fun _ _ h => max_le_max (by linarith) le_rfl

/-! ## The continuous-price face

Beyond the payoff (`convexOn_call_payoff`), the *price itself* is convex
in the strike. The proof is the second-derivative test:

* `hasDerivAt_bsV_K`: `∂_K bsV = −e^{-rτ} · Φ(d_2)` exists at every `K > 0`.
* `hasDerivAt_bsV_KK`: `∂²_K bsV = e^{-rτ} · ϕ(d_2) / (K σ √τ)` exists and
  is non-negative for every `K > 0`.

We feed these to Mathlib's `convexOn_of_deriv2_nonneg'`. The only delicate
step is identifying `deriv (fun K' => bsV K' r σ S τ)` with the explicit
first derivative in a neighborhood of each interior point so the second
derivative inherits the closed form — handled below with
`HasDerivAt.congr_of_eventuallyEq`. -/

/-- **First-derivative identification on `(0, ∞)`**: the closed form for
`∂_K bsV` from `hasDerivAt_bsV_K` agrees with `deriv` on the whole positive
half-line. Used to bridge `hasDerivAt_bsV_KK` to a second-derivative
statement on `deriv` itself. -/
private lemma deriv_bsV_eq_on_Ioi (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ)
    (hτ : 0 < τ) {K : ℝ} (hK : K ∈ Set.Ioi (0 : ℝ)) :
    deriv (fun k => bsV k r σ S τ) K =
      -(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) :=
  (hasDerivAt_bsV_K (S := S) (r := r) (σ := σ) hS hσ hK hτ).deriv

/-- **Local equality of derivatives on `(0, ∞)`**: in a neighbourhood of any
`K > 0`, `deriv (fun K' => bsV K' r σ S τ)` agrees with the explicit closed
form, so derivative facts about the closed form transfer to `deriv`. -/
private lemma deriv_bsV_eventuallyEq (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ)
    (hτ : 0 < τ) {K : ℝ} (hK : 0 < K) :
    (fun K' => deriv (fun k => bsV k r σ S τ) K') =ᶠ[nhds K]
      (fun K' => -(Real.exp (-(r * τ)) * Phi (bsd2 S K' r σ τ))) := by
  filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hK)] with K' hK'
  exact deriv_bsV_eq_on_Ioi S r σ τ hS hσ hτ hK'

/-- **BS call price is convex in the strike on `(0, ∞)`** — the continuous-
price face of the K-convexity principle.

This is the second-derivative test applied to BS: at every `K > 0`,
`∂²_K bsV = e^{-rτ} · ϕ(d_2)/(K σ √τ) ≥ 0`. The hypotheses of
`convexOn_of_deriv2_nonneg'` are the differentiability of `bsV` and of its
first derivative on `Ioi 0`, both of which we have in closed form from
`hasDerivAt_bsV_K` and `hasDerivAt_bsV_KK`. -/
theorem bsV_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K => bsV K r σ S τ) := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioi 0) ?_ ?_ ?_
  -- (1) bsV is differentiable on Ioi 0 (from hasDerivAt_bsV_K).
  · intro K hK
    exact ((hasDerivAt_bsV_K (S := S) (r := r) (σ := σ) hS hσ hK hτ).differentiableAt
      ).differentiableWithinAt
  -- (2) deriv bsV is differentiable on Ioi 0 (from hasDerivAt_bsV_KK, transported via h_ev).
  · intro K hK
    have h_pos : 0 < K := hK
    have h_KK := hasDerivAt_bsV_KK (S := S) (r := r) (σ := σ) hS hσ h_pos hτ
    have h_ev := deriv_bsV_eventuallyEq S r σ τ hS hσ hτ h_pos
    exact ((h_KK.congr_of_eventuallyEq h_ev).differentiableAt).differentiableWithinAt
  -- (3) deriv^[2] bsV K ≥ 0 for K > 0.
  · intro K hK
    have h_pos : 0 < K := hK
    have h_KK := hasDerivAt_bsV_KK (S := S) (r := r) (σ := σ) hS hσ h_pos hτ
    have h_ev := deriv_bsV_eventuallyEq S r σ τ hS hσ hτ h_pos
    have h_d2 : deriv^[2] (fun k => bsV k r σ S τ) K =
        Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
          (K * σ * Real.sqrt τ) :=
      (h_KK.congr_of_eventuallyEq h_ev).deriv
    rw [h_d2]
    have h_exp_pos : 0 < Real.exp (-(r * τ)) := Real.exp_pos _
    have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S K r σ τ) :=
      gaussianPDFReal_nonneg _ _ _
    have h_den_pos : 0 < K * σ * Real.sqrt τ :=
      mul_pos (mul_pos h_pos hσ) (Real.sqrt_pos.mpr hτ)
    exact div_nonneg (mul_nonneg h_exp_pos.le h_pdf_nn) h_den_pos.le

end QuantFin
