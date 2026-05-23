/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.Forward
import QuantFin.Foundations.StandardGaussianMGF

/-!
# Power options under the BS lognormal hypothesis

The `n`-th moment of `S_T` under `BSCallHyp` is

  `E_Q[S_T^n] = S_0^n · exp(n · r · T + n(n−1)/2 · σ²T)`,

and its discounted form is the *power-forward price*

  `e^{−rT} · E_Q[S_T^n] = S_0^n · exp((n−1) · r · T + n(n−1)/2 · σ²T)`.

Both are direct instances of the **affine-shifted standard-normal MGF**
`∫ exp(α + β · z) · pdf(0, 1, z) dz = exp(α + β²/2)` (proved in
`StandardGaussianMGF.lean`), with `α = n · (r − σ²/2) · T` and `β = n · σ · √T`.
The identity `α + β²/2 = n · r · T + n(n−1)/2 · σ²T` is the algebraic core; the
rest is the standard HasLaw transfer from `Z` to `gaussianReal 0 1`.

This file demonstrates the use of the affine MGF master: the proof body
factors `(bsTerminal z)^n = S_0^n · exp(α + β·z)` and applies the master in a
single rewrite. No manual constant-pulling. Compare to the earlier
`secondMoment_terminal` (which is now derivable as `nthMoment_terminal 2`).

Results:

* `nthMoment_terminal`: the `n`-th moment of `S_T` under `BSCallHyp`.
* `powerForward_price`: discounted power-forward price.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **`n`-th moment of the terminal asset price** under `BSCallHyp`:
`E_Q[S_T^n] = S_0^n · exp(n · r · T + n(n−1)/2 · σ²T)`.

Direct instance of the affine-shifted standard-normal MGF: with
`α = n(r − σ²/2)T` and `β = nσ√T`, the integrand `(bsTerminal z)^n` equals
`S_0^n · exp(α + β·z)`, so `E[(bsTerminal)^n] = S_0^n · exp(α + β²/2)`.
The algebraic identity `α + β²/2 = nrT + n(n−1)/2 σ²T` finishes. -/
theorem nthMoment_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q =
      S_0^n *
        Real.exp ((n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  obtain ⟨_hS_0, _hK, _hσ, hT, hZ⟩ := h
  set α : ℝ := (n : ℝ) * (r - σ^2 / 2) * T with α_def
  set β : ℝ := (n : ℝ) * σ * Real.sqrt T with β_def
  -- The two algebraic facts that drive the proof:
  have h_β_sq : β^2 = (n : ℝ)^2 * σ^2 * T := by
    rw [β_def]; ring_nf; rw [Real.sq_sqrt hT.le]
  have h_algebra :
      α + β^2 / 2 =
        (n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T := by
    rw [h_β_sq]; ring
  -- Pointwise: `(S_0 · exp(...))^n = S_0^n · exp(α + β·z)`.
  have h_pow : ∀ z : ℝ,
      (bsTerminal S_0 r σ T z)^n = S_0^n * Real.exp (α + β * z) := by
    intro z
    unfold bsTerminal
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    rw [α_def, β_def]; ring
  -- HasLaw transfer + change to `pdf`-against-Lebesgue form.
  have h_meas : Measurable fun z : ℝ => (bsTerminal S_0 r σ T z)^n := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω => (bsTerminal S_0 r σ T (Z ω))^n) =
        (fun z => (bsTerminal S_0 r σ T z)^n) ∘ Z from rfl,
      hZ.integral_comp h_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Substitute the pointwise factorisation and reorder.
  simp_rw [smul_eq_mul, h_pow]
  rw [show
        (fun z : ℝ => gaussianPDFReal 0 1 z * (S_0^n * Real.exp (α + β * z)))
        =
        (fun z => S_0^n * (Real.exp (α + β * z) * gaussianPDFReal 0 1 z))
      from funext (fun z => by ring)]
  -- Apply the affine MGF master directly: the heart of the proof.
  rw [integral_const_mul, integral_exp_affine_gaussianPDFReal_univ]
  rw [h_algebra]

/-- **Power-forward price**: discounted `n`-th moment equals
`S_0^n · exp((n−1) · r · T + n(n−1)/2 · σ²T)`. Specialises to:
* `n = 0`: `e^{−rT}` (a unit-payoff at maturity is a zero-coupon bond).
* `n = 1`: `S_0` (discounted spot is a martingale: `e^{−rT} · E[S_T] = S_0`).
* `n = 2`: `S_0² · exp(rT + σ²T)` (the variance-relevant moment after
  subtracting the squared forward). -/
theorem powerForward_price
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    Real.exp (-(r * T)) *
        (∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q) =
      S_0^n *
        Real.exp (((n : ℝ) - 1) * r * T +
                  (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  rw [nthMoment_terminal n h, ← mul_assoc, mul_comm (Real.exp _) (S_0^n),
      mul_assoc, ← Real.exp_add]
  congr 2
  ring

end QuantFin
