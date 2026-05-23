/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call

/-!
# Forward and futures pricing under the BS lognormal hypothesis

Under `BSCallHyp` (risk-neutral lognormal model), the risk-neutral
expectation of the terminal asset price equals the no-arbitrage forward
price:

    E_Q[S_T] = S_0 · e^{rT}.

This is the classical no-arbitrage relation `F = S_0 · e^{rT}` derived as
a direct consequence of the Gaussian MGF identity. The discounted asset
price is automatically a Q-martingale (at maturity):

    E_Q[e^{-rT} · S_T] = S_0.

No Itô calculus is required — pure Gaussian integration.

## Interpretation as a no-arbitrage price

A long forward contract pays `S_T − F` at maturity. The **forward price**
`F` is conventionally defined as the unique value making the contract
worth zero at inception. Under any risk-neutral measure `Q`, the zero-value
condition is

    0 = E_Q[e^{-rT}(S_T − F)] = e^{-rT}(E_Q[S_T] − F),

so `F = E_Q[S_T]`. Combined with `expected_terminal_eq_forward`, this gives
`F = S_0 · e^{rT}`.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Standard-normal moment generating function -/

/-- **MGF of the standard normal**: `∫ z, exp(c·z) · pdf(0,1,z) dz = exp(c²/2)`.

Combines `exp_mul_gaussianPDFReal_zero_one` (completing-the-square) with
Mathlib's `integral_gaussianPDFReal_eq_one`. -/
lemma integral_exp_mul_gaussianPDFReal_univ (c : ℝ) :
    ∫ z, Real.exp (c * z) * gaussianPDFReal 0 1 z = Real.exp (c^2 / 2) := by
  rw [show (fun z => Real.exp (c * z) * gaussianPDFReal 0 1 z)
        = (fun z => Real.exp (c^2 / 2) * gaussianPDFReal c 1 z) from
      funext (exp_mul_gaussianPDFReal_zero_one c),
      integral_const_mul,
      integral_gaussianPDFReal_eq_one c (one_ne_zero : (1 : ℝ≥0) ≠ 0), mul_one]

/-! ### Risk-neutral expectation of terminal asset price -/

/-- **No-arbitrage forward price**: under `BSCallHyp`,
    `E_Q[S_T] = S_0 · e^{rT}`.

This is the risk-neutral expectation of the terminal asset price, which is
the no-arbitrage forward price `F` for delivery at time `T`. Derivation:
HasLaw transfer to standard normal + `integral_exp_mul_gaussianPDFReal_univ`
(Gaussian MGF) + BS algebra `(r - σ²/2)T + σ²T/2 = rT`. -/
theorem expected_terminal_eq_forward
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsTerminal S_0 r σ T (Z ω) ∂Q = S_0 * Real.exp (r * T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set μ_log : ℝ := (r - σ^2 / 2) * T with μ_log_def
  set ν_log : ℝ := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_sq : ν_log^2 = σ^2 * T := by rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_algebra : μ_log + ν_log^2 / 2 = r * T := by rw [hν_log_sq]; ring
  have h_term_meas : Measurable fun z : ℝ => bsTerminal S_0 r σ T z := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω => bsTerminal S_0 r σ T (Z ω))
        = (fun z => bsTerminal S_0 r σ T z) ∘ Z from rfl,
      hZ.integral_comp h_term_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Rewrite pdf · S_T(z) = S_0 · exp(μ_log) · (exp(ν_log · z) · pdf)
  have h_factor : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • bsTerminal S_0 r σ T z
        = S_0 * Real.exp μ_log * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    have h_exp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
                = Real.exp μ_log * Real.exp (ν_log * z) := by
      show Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
            = Real.exp ((r - σ^2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
      exact Real.exp_add _ _
    rw [smul_eq_mul, h_exp]; ring
  rw [show (fun z => gaussianPDFReal 0 1 z • bsTerminal S_0 r σ T z)
        = (fun z => S_0 * Real.exp μ_log *
            (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)) from funext h_factor]
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_univ]
  rw [show S_0 * Real.exp μ_log * Real.exp (ν_log^2 / 2)
        = S_0 * (Real.exp μ_log * Real.exp (ν_log^2 / 2)) from by ring,
      ← Real.exp_add, h_algebra]

/-! ### Discounted asset is a Q-martingale at maturity -/

/-- **Discounted terminal price equals spot**: under `BSCallHyp`,
    `E_Q[e^{-rT} S_T] = S_0`. This is the integrated form of the
    risk-neutral martingale property at maturity. -/
theorem discounted_terminal_eq_S0
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-(r * T)) * bsTerminal S_0 r σ T (Z ω) ∂Q = S_0 := by
  rw [integral_const_mul, expected_terminal_eq_forward h]
  rw [show Real.exp (-(r * T)) * (S_0 * Real.exp (r * T))
        = S_0 * (Real.exp (-(r * T)) * Real.exp (r * T)) from by ring,
      ← Real.exp_add,
      show -(r * T) + r * T = 0 from by ring, Real.exp_zero, mul_one]

end QuantFin
