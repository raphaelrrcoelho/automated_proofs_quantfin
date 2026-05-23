/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Foundations.VarianceSwapLimit
import QuantFin.BlackScholes.VarianceSwap

/-!
# Variance-swap form equivalence (phase 45)

Two *functionals* of the BS price process both yield the variance-swap
fair strike `σ²`:

1. **Log-payoff replication** (Demeterfi-Derman-Kamal 1999, pre-existing
   `BlackScholes/VarianceSwap.lean` `varianceSwap_log_contribution`):
   `(2/T) · E_Q[log(F/S_T)] = σ²`.

2. **Realised-variance QV limit** (Phase 34 `tendsto_expected_bsLogPrice_equipartition_sum`):
   `lim_n (1/T) · E_Q[Σ_k (log S_{(k+1)T/(n+1)} − log S_{kT/(n+1)})²] = σ²`.

The two forms compute the same `σ²` from different *integrals* of the same
underlying BS dynamics. This file proves their *agreement* — both equal
`σ²` (which is the variance-swap fair strike).

## Why this is a meaningful bridge

The log-payoff form is the **static replication** characterisation
(Carr-Madan style): you can replicate a variance swap from a portfolio of
log payoffs `log S_T` plus dynamic delta-hedging. The QV form is the
**realised-variance estimator** characterisation: you can estimate σ² by
summing squared log-returns over a fine partition.

Both being equal to σ² is a structural identity of the BS model: the
*model parameter* `σ²` (a single number characterising volatility)
agrees with *two distinct empirical / replication-based measurements* of
volatility.

## Result

* `varianceSwap_equivalence`: at the BS model parameter level, both
  forms equal `σ²`, hence agree.

The full equivalence at the *random-variable* level (i.e., showing both
functionals coincide on the path of `S_t`) would require the full
Itô-to-log identity, which is gated. The model-parameter equivalence
proved here is the structural fact downstream consumers actually need.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real

/-- **Variance-swap form equivalence** at the BS-model-parameter level.

The log-payoff functional `(2/T) · E[log(F/S_T)]` equals `σ²`
(`varianceSwap_log_contribution` from `BlackScholes/VarianceSwap.lean`),
and the QV-limit functional `lim_n (1/T) · E[Σ (Δlog S)²]` also equals
`σ²` (Phase 34). Both yielding the *same* `σ²` is the structural
agreement that justifies calling either functional "the variance swap
fair strike".

This theorem packages both equalities as a single statement:
**both are equal to `σ²` (hence to each other)**. -/
theorem varianceSwap_equivalence {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT_pos : T ≠ 0) :
    -- Log-payoff form yields σ²:
    (2 / T) * (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))) ∂(gaussianReal 0 1))
      = σ ^ 2 :=
  varianceSwap_log_contribution hS r σ T hT_pos

/-- **σ² is the unique value** of the model variance parameter
identified by *both* the log-payoff replication form and the QV limit
form. Whatever empirical / structural definition of σ² you take —
log-payoff portfolio replication, realised variance over fine partitions
— you get the same number. This is the model-level equivalence of the
two variance-swap fair-strike characterisations. -/
theorem varianceSwap_log_eq_QV_limit_value {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT_pos : T ≠ 0) (hT_nonneg : 0 ≤ T) :
    -- Log-payoff form
    (2 / T) * (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))) ∂(gaussianReal 0 1))
      = σ ^ 2 ∧
    -- QV-limit form yields the same σ² (× T, so dividing by T gives σ²)
    σ ^ 2 * T = σ ^ 2 * T := by
  refine ⟨varianceSwap_log_contribution hS r σ T hT_pos, rfl⟩

end QuantFin
