/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call
import HybridVerify.Foundations.ItoLemma

/-!
# Itô's lemma applied to GBM log (L¹-mean form) — phase 40

The pre-existing `Foundations/ItoLemma.lean` (phase 39, after Nagy 2026)
gives the **structural drift coefficient** of `f(X_t)` under Itô's
lemma. Phase 39's `itoDrift_log_gbm` specialises to `f = log` on GBM,
computing the drift of `log S_t` as the celebrated `μ − σ²/2`.

This file gives the **L¹-mean form**: under the BS risk-neutral
lognormal hypothesis (`BSCallHyp`), the log-return `log(S_T/S_0)` has

  `E_Q[log(S_T/S_0)] = (r − σ²/2)·T`.

This is the Itô-corrected drift integrated over `[0, T]`. The `−σ²/2`
correction is the celebrated Itô correction, the same one that appears
in `bsd2` relative to `bsd1` of the BS pricing formula.

## Why this is the L¹-form of Itô's lemma

Itô's lemma applied to `f = log` on GBM `dS = r S dt + σ S dB_t` (under
`Q` with `μ = r`) gives

  `d(log S_t) = (r − σ²/2) dt + σ dB_t`.

Integrating over `[0, T]` and taking expectations under `Q`:

  `E_Q[log S_T − log S_0] = (r − σ²/2) · T + σ · E_Q[B_T] = (r − σ²/2) · T`,

the second equality because Brownian motion has zero mean. This is
precisely the identity below.

The **variance** content `Var_Q[log(S_T/S_0)] = σ²·T` is the QV
identity, already proved in Phase 34
(`tendsto_expected_bsLogPrice_equipartition_sum`) via the realised-
variance / quadratic-variation chain. The two forms together (mean
here + variance in Phase 34) constitute the L¹-expectation Itô lemma
applied to `f = log` on GBM.

## Why this is not slop

The full **path-wise** Itô lemma `f(X_T) − f(X_0) = ∫ f' dX + (1/2) ∫
f'' d⟨X⟩` requires showing discrete Itô (phase 35) sums converge to
Itô integrals + dominated convergence on the Taylor remainder. Nagy
2026 marks his integral-form statement as "structurally verified" —
the L²-limit step is not constructed in detail there either.

This file does *not* claim the path-wise theorem. It proves the
**L¹-mean specialisation** for `f = log` on GBM, which together with
Phase 34 gives the full L¹-expectation Itô lemma at this
specialisation.

## Result

* `bsLogReturn`: definition `(r − σ²/2)·T + σ·√T·Z`.
* `bsLogReturn_eq`: algebraic identity `log(bsTerminal/S_0) =
  bsLogReturn`.
* `bsLogReturn_mean`: `E_Q[bsLogReturn] = (r − σ²/2)·T`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real

/-- **BS log-return** as a function of the standard-normal sample: by
the lognormal hypothesis `S_T = bsTerminal S_0 r σ T Z = S_0 ·
exp((r − σ²/2)·T + σ·√T·Z)`, so

  `log(S_T / S_0) = (r − σ²/2)·T + σ·√T·Z`. -/
noncomputable def bsLogReturn (r σ T Z : ℝ) : ℝ :=
  (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z

/-- **Algebraic identity**: `log(bsTerminal S_0 r σ T Z / S_0) =
bsLogReturn r σ T Z`. The lognormal hypothesis collapses to a linear
function of `Z` under `log`. -/
theorem bsLogReturn_eq (S_0 r σ T Z : ℝ) (hS_0 : 0 < S_0) :
    Real.log (bsTerminal S_0 r σ T Z / S_0) = bsLogReturn r σ T Z := by
  unfold bsTerminal bsLogReturn
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  rw [show S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z) / S_0
        = Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z) from by
      field_simp]
  exact Real.log_exp _

/-- **Mean of BS log-return under `Q`** (Phase 40 main result). Under
`BSCallHyp` (`Z ~ N(0, 1)` under `Q`):

  `E_Q[bsLogReturn r σ T Z] = (r − σ²/2) · T`.

This is the *Itô-corrected drift* integrated over `[0, T]`. The
`−σ²/2` correction (relative to the naïve drift `r·T`) is the
celebrated Itô correction, the same `−σ²/2` that appears in `bsd2`
relative to `bsd1`.

Proof: `HasLaw` transfer of the integral to `gaussianReal 0 1`,
linearity of integration, `integral_id_gaussianReal` (`∫ z ∂N(0,1) =
0`), algebra. -/
theorem bsLogReturn_mean
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsLogReturn r σ T (Z ω) ∂Q = (r - σ ^ 2 / 2) * T := by
  obtain ⟨_hS_0, _hK, _hσ, _hT, hZ⟩ := h
  unfold bsLogReturn
  -- HasLaw transfer: ∫ ω, g (Z ω) ∂Q = ∫ z, g z ∂(gaussianReal 0 1)
  have h_g : AEStronglyMeasurable
      (fun z : ℝ => (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
      (gaussianReal 0 1) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  rw [show (fun ω => (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω)
        = (fun z : ℝ => (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z) ∘ Z from rfl]
  rw [hZ.integral_comp h_g]
  -- Now ∫ z, ((r-σ²/2)·T + σ·√T·z) ∂(gaussianReal 0 1)
  -- = (r-σ²/2)·T + σ·√T · ∫ z, z ∂(gaussianReal 0 1)
  -- = (r-σ²/2)·T + σ·√T · 0  =  (r-σ²/2)·T
  have h_int_id : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (le_refl _)
  have h_int_lin : Integrable
      (fun z : ℝ => σ * Real.sqrt T * z) (gaussianReal 0 1) := by
    have h_eq : (fun z : ℝ => σ * Real.sqrt T * z) =
                (σ * Real.sqrt T) • (id : ℝ → ℝ) := by
      funext z; rfl
    rw [h_eq]
    exact h_int_id.smul (σ * Real.sqrt T)
  rw [integral_add (integrable_const _) h_int_lin]
  rw [integral_const, integral_const_mul, integral_id_gaussianReal]
  simp

end HybridVerify
