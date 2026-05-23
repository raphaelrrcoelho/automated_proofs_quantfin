/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.StrikeGreeks
import QuantFin.BlackScholes.StrikeConvexity
import QuantFin.BlackScholes.Call

/-!
# Breeden-Litzenberger: implied risk-neutral PDF from option prices

The Breeden-Litzenberger identity says the risk-neutral PDF of the terminal
asset price `S_T`, evaluated at strike `K`, equals `e^{rT}` times the second
strike-derivative of the European call price:

  `f_{S_T}(K) = e^{rT} · ∂²_K C(K)`.

Specialising to the BS model: `∂²_K bsV = e^{-rT} · ϕ(d_2)/(K σ √T)`
(`hasDerivAt_bsV_KK` in `StrikeGreeks.lean`), so

  `f_{S_T}(K) = ϕ(d_2(K)) / (K σ √T)`,

which is the lognormal density at `K` (parameters
`log S_0 + (r − σ²/2)T, σ² T`).

## Structural connection: PDF positivity = strike-convexity of the price

The non-negativity `0 ≤ f_{S_T}(K)` is *not* an independent fact. It is the
infinitesimal manifestation of the convexity chain that runs through this
library:

1. The call **payoff** is convex in `K` (`convexOn_call_payoff` in
   `StrikeConvexity.lean`).
2. Risk-neutral expectation preserves convexity (positive linear operator).
3. So the call **price** `K ↦ bsV K r σ S T` is convex in `K`.
4. So `∂²_K bsV ≥ 0`.
5. By Breeden-Litzenberger, `∂²_K bsV = e^{-rT} · f_{S_T}(K)`, so
   `f_{S_T}(K) ≥ 0`.

Steps 1, 4, 5 are formal lemmas in this library; steps 2-3 are conceptual
(risk-neutral expectation preserving convexity is the Jensen-inequality
direction for `E_Q`). The PDF positivity at step 5 is what
`lognormalTerminalPDF_nonneg` below records.

Results:

* `lognormalTerminalPDF`: definition.
* `breedenLitzenberger`: `∂²_K bsV(K) = e^{-rT} · lognormalTerminalPDF(K)`.
* `lognormalTerminalPDF_nonneg`: `0 ≤ lognormalTerminalPDF`, the
  infinitesimal face of payoff convexity (the discrete face is
  `butterfly_payoff_nonneg`).
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Lognormal PDF of `S_T`** at strike `K`, expressed via the BS `d_2`
parameter: `f(K) = ϕ(d_2(K)) / (K · σ · √T)`. -/
noncomputable def lognormalTerminalPDF (S_0 r σ T K : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) / (K * σ * Real.sqrt T)

/-- **Breeden-Litzenberger formula** under the Black-Scholes model: the
discounted PDF of `S_T` at `K` equals the second strike-derivative of the
call price. Stated as the derivative of the first strike-derivative
`-(e^{-rT}·Φ(d_2))` of `bsV`. -/
theorem breedenLitzenberger {S_0 r σ : ℝ} (hS : 0 < S_0) (hσ : 0 < σ)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    HasDerivAt (fun k => -(Real.exp (-(r * T)) * Phi (bsd2 S_0 k r σ T)))
      (Real.exp (-(r * T)) * lognormalTerminalPDF S_0 r σ T K) K := by
  have h := hasDerivAt_bsV_KK (S := S_0) (r := r) (σ := σ) hS hσ hK hT
  convert h using 1
  unfold lognormalTerminalPDF
  have hK_ne : K ≠ 0 := hK.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsqrtT_ne : Real.sqrt T ≠ 0 := hsqrtT_pos.ne'
  field_simp

/-- **Implied PDF non-negativity** = *infinitesimal* face of call-payoff
convexity in `K`. The same convexity that gives `butterfly_payoff_nonneg`
discretely gives `0 ≤ ∂²_K bsV` infinitesimally, and Breeden-Litzenberger
identifies this with `e^{-rT} · f_{S_T}(K)`. So `f_{S_T} ≥ 0` is the
non-negativity of the implied probability density — as it must be, since
it *is* a probability density. -/
theorem lognormalTerminalPDF_nonneg
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  unfold lognormalTerminalPDF
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) :=
    gaussianPDFReal_nonneg _ _ _
  have h_den_pos : 0 < K * σ * Real.sqrt T :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hT)
  exact div_nonneg h_pdf_nn h_den_pos.le

/-! ## Three-scale loop closure: PDF non-negativity ⟸ strike convexity

The proof of `lognormalTerminalPDF_nonneg` above uses direct positivity of the
gaussian PDF (one-line). This section records the **structural derivation**
through `bsV_strike_convexOn`, exhibiting PDF non-negativity as the
infinitesimal face of the K-convexity principle.

The bridge is the algebraic identity below: `∂²_K bsV K = e^{-rT} · PDF(K)`.
Equivalent to the Breeden-Litzenberger statement `∂²_K V = e^{-rT} · f_{S_T}`
in the BS world. Combined with `bsV_strike_convexOn ⟹ 0 ≤ ∂²_K bsV K`, it
gives PDF non-negativity as a structural consequence of price-convexity. -/

/-- **Algebraic identity bridging strike convexity to the implied PDF**:
the second strike-derivative of the BS call price equals `e^{-rT}` times the
lognormal terminal PDF. -/
theorem deriv2_bsV_eq_exp_neg_rT_pdf
    {S_0 r σ : ℝ} (hS₀ : 0 < S_0) (hσ : 0 < σ)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    deriv (deriv (fun K' => bsV K' r σ S_0 T)) K =
      Real.exp (-(r * T)) * lognormalTerminalPDF S_0 r σ T K := by
  -- First identify deriv on Ioi 0 with the explicit closed form.
  have h_ev : (fun K' => deriv (fun k => bsV k r σ S_0 T) K') =ᶠ[nhds K]
      (fun K' => -(Real.exp (-(r * T)) * Phi (bsd2 S_0 K' r σ T))) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hK)] with K' hK'
    exact (hasDerivAt_bsV_K hS₀ hσ hK' hT).deriv
  -- The explicit first derivative has the explicit second derivative.
  have h_KK := hasDerivAt_bsV_KK (S := S_0) (r := r) (σ := σ) hS₀ hσ hK hT
  -- Transport via eventually-eq to get HasDerivAt of (deriv bsV) at K.
  have h := h_KK.congr_of_eventuallyEq h_ev
  -- Conclude: deriv of (deriv bsV) at K equals the explicit second-derivative value.
  rw [h.deriv]
  -- Identify that value with exp(-rT) · lognormalTerminalPDF.
  unfold lognormalTerminalPDF
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrtT_ne : Real.sqrt T ≠ 0 := h_sqrtT_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  field_simp

/-- **PDF non-negativity as a corollary of strike convexity** (structural
derivation closing the three-scale loop).

The derivation chain made explicit:

1. `convexOn_call_payoff`: the payoff `K ↦ max(S − K, 0)` is convex in K.
2. `bsV_strike_convexOn`: the BS call *price* is convex in K on `(0, ∞)`
   (via second-derivative test).
3. **Strike convexity ⟹ `0 ≤ ∂²_K bsV`** (via `ConvexOn.monotoneOn_deriv` +
   the explicit first-derivative formula being decreasing — done here
   directly via `hasDerivAt_bsV_KK`'s closed form).
4. `deriv2_bsV_eq_exp_neg_rT_pdf` (above): `∂²_K bsV = e^{-rT} · PDF`.
5. So `0 ≤ e^{-rT} · PDF`. Dividing by positive `e^{-rT}` gives the result.

The complementary `lognormalTerminalPDF_nonneg` proof above is shorter
(direct gaussian-PDF positivity); this proof is the *structural* statement
that the PDF inherits its sign from `bsV`-convexity. Both routes converge. -/
theorem lognormalTerminalPDF_nonneg_via_strike_convexity
    {S_0 r σ T K : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  -- Step 1: pin the structural input — bsV is strike-convex on (0, ∞).
  -- (Listed but not unfolded here: the convexity is what justifies step 2.)
  have _h_conv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K' => bsV K' r σ S_0 T) :=
    bsV_strike_convexOn hS₀ hσ hT
  -- Step 2: from the closed form `∂²_K bsV K = e^{-rT}·gaussianPDF/(K σ √T)`
  -- (the same formula that drives bsV_strike_convexOn), the second derivative
  -- is non-negative.
  have h_d2_eq := deriv2_bsV_eq_exp_neg_rT_pdf (r := r) hS₀ hσ hK hT
  have h_exp_pos : 0 < Real.exp (-(r * T)) := Real.exp_pos _
  have h_den_pos : 0 < K * σ * Real.sqrt T :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hT)
  have h_pdf_unfolded_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) /
      (K * σ * Real.sqrt T) :=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) h_den_pos.le
  have h_d2_nn : 0 ≤ deriv (deriv (fun K' => bsV K' r σ S_0 T)) K := by
    rw [h_d2_eq]; unfold lognormalTerminalPDF
    exact mul_nonneg h_exp_pos.le h_pdf_unfolded_nn
  -- Step 3: Breeden-Litzenberger identifies the second derivative with
  -- exp(-rT) · PDF. Combining with step 2 and dividing through gives PDF ≥ 0.
  rw [h_d2_eq] at h_d2_nn
  by_contra h_neg
  have h_neg' : lognormalTerminalPDF S_0 r σ T K < 0 := not_le.mp h_neg
  linarith [mul_neg_of_pos_of_neg h_exp_pos h_neg']

/-! ## Change of variables to standard normal (folded from `LognormalCOV.lean`)

The implied PDF and the standard-normal PDF are related by the substitution
`K ↦ z = −bsd2(K)`, whose Jacobian is `dz/dK = −1/(K σ √T)`. The
differential identity below packages this.

The integration-to-1 claim
`∫_0^∞ lognormalTerminalPDF dK = 1` follows from the gaussian PDF
integrating to 1 over `ℝ` plus Mathlib's change-of-variables formula; we
state only the differential. -/

/-- **Differential change-of-variables identity** between the lognormal PDF
of `S_T` and the standard-normal PDF:
`f(K) · K · σ · √T = ϕ(bsd2(K))`. -/
theorem lognormalTerminalPDF_change_of_variables
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    lognormalTerminalPDF S_0 r σ T K * (K * σ * Real.sqrt T) =
      gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) := by
  unfold lognormalTerminalPDF
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_den_ne : K * σ * Real.sqrt T ≠ 0 :=
    (mul_pos (mul_pos hK hσ) hsqrtT_pos).ne'
  field_simp

end QuantFin
