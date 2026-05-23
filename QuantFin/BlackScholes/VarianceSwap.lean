/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.Forward

/-!
# Variance swap fair strike (Demeterfi-Derman-Kamal)

Under the BS lognormal hypothesis, the fair strike of a variance swap with
log-payoff replication

  `(2/T) · E_Q[log(F/S_T) + (S_T - F)/F] = σ²`,

where `F = S_0 · e^{rT}` is the forward price. The two terms are:

* `E_Q[log(F/S_T)] = σ² T / 2`: the log-moment of the discount factor `F/S_T`.
  Comes from `log(F/S_T) = σ² T / 2 − σ √T · Z` (after the `S_0` cancellation)
  and `E_Q[Z] = 0`.
* `E_Q[(S_T - F)/F] = 0`: zero by `expected_terminal_eq_forward` (`E_Q[S_T] = F`).

The result `(2/T)·σ²T/2 = σ²` says: under BS lognormal dynamics, the fair
variance swap rate equals the squared volatility — exactly the relationship
that makes BS implied volatility a "risk-neutral expected variance".

Results:

* `log_forward_div_bsTerminal_eq`: `log(F/S_T) = σ² T / 2 − σ √T · z`.
* `integral_log_forward_div_bsTerminal_eq`:
  `E_Q[log(F/S_T)] = σ² T / 2`.
* `integral_excess_return_eq_zero`: `E_Q[(S_T − F)/F] = 0`.
* `varianceSwap_fairStrike`: the headline `(2/T) · E_Q[...] = σ²`.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Log-moment integrand identity**: after the `S_0` cancellation,
`log((S_0 · e^{rT}) / (S_0 · exp((r − σ²/2)T + σ√T·z))) = σ²T/2 − σ√T·z`. -/
lemma log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0) (r σ T z : ℝ) :
    Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      = σ^2 * T / 2 - σ * Real.sqrt T * z := by
  have hS_ne : S_0 ≠ 0 := hS.ne'
  rw [mul_div_mul_left _ _ hS_ne]
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- **Log-moment integral identity**: `∫ z, log(F/S_T(z)) ∂(gaussianReal 0 1)
= σ² T / 2`. -/
lemma integral_log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) :
    ∫ z, Real.log ((S_0 * Real.exp (r * T)) /
                  (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      ∂(gaussianReal 0 1) = σ^2 * T / 2 := by
  have h_integrand_eq : ∀ z : ℝ,
      Real.log ((S_0 * Real.exp (r * T)) /
                (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        = σ^2 * T / 2 - σ * Real.sqrt T * z :=
    fun z => log_forward_div_bsTerminal_eq hS r σ T z
  rw [show (fun z => Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))))
        = (fun z => σ^2 * T / 2 - σ * Real.sqrt T * z) from funext h_integrand_eq]
  have h_const_integrable :
      Integrable (fun _ : ℝ => σ^2 * T / 2) (gaussianReal 0 1) :=
    integrable_const _
  have h_id_basic : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_cast)
  have h_id_integrable :
      Integrable (fun z : ℝ => σ * Real.sqrt T * z) (gaussianReal 0 1) :=
    h_id_basic.const_mul (σ * Real.sqrt T)
  rw [integral_sub h_const_integrable h_id_integrable]
  rw [integral_const, integral_const_mul, integral_id_gaussianReal]
  simp

/-- **Variance swap fair strike (log-payoff contribution)**: the log-payoff
replication piece scales to give the squared volatility.

`(2/T) · E[log(F/S_T)] = σ²` under the BS lognormal hypothesis (with
`F = S_0 · e^{rT}`). Combined with the zero excess-return moment
`E[(S_T − F)/F] = 0` (from `expected_terminal_eq_forward`), this gives the
full Demeterfi-Derman-Kamal log-replication identity for the variance swap
fair strike. -/
theorem varianceSwap_log_contribution {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT : T ≠ 0) :
    (2 / T) *
      (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
            (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        ∂(gaussianReal 0 1)) = σ^2 := by
  rw [integral_log_forward_div_bsTerminal_eq hS]
  field_simp

end QuantFin
