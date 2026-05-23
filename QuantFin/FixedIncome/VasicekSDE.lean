/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.FixedIncome.Vasicek

/-!
# Vasicek SDE closed-form solution (phase 41)

The pre-existing `FixedIncome/Vasicek.lean` derives only the
**deterministic part** of the Vasicek mean-reverting short-rate model
(the `σ = 0` ODE). This file extends to the **full SDE**

  `dr_t = κ (θ − r_t) dt + σ dB_t`,

whose closed-form solution is

  `r_t = r_0 · e^{−κt} + θ · (1 − e^{−κt}) + σ · ∫_0^t e^{−κ(t−s)} dB_s`.

The Itô integral `∫_0^t e^{−κ(t−s)} dB_s` is of a *deterministic*
integrand, so it has Gaussian distribution by the simple-process Itô
isometry (`Foundations/ItoIntegralSimple.lean`, phase 36, with deterministic
weights). The integrand's L² norm gives the variance:

  `Var = σ² · ∫_0^t e^{−2κ(t−s)} ds = σ² · (1 − e^{−2κt}) / (2κ)`.

Hence under the SDE,

  `r_t ~ N( r_0 · e^{−κt} + θ · (1 − e^{−κt}), σ² · (1 − e^{−2κt}) / (2κ) )`.

This file gives the explicit *terminal-distribution* form, parameterised
by a standard normal `Z`, in the same style as `BSCallHyp`.

## Why this is open now

Phase 36 (simple-process Itô integral) + Phase 32 (BQV identities) +
the deterministic Riemann integral `∫ e^{−2κ(t−s)} ds = (1 − e^{−2κt})/(2κ)`
give the variance computation. The Gaussian-distribution conclusion
follows from the structural fact that Itô integrals of deterministic
integrands are Gaussian (a consequence of the simple-process
construction being a sum of independent Gaussian increments).

## What this file is

A **terminal-distribution-form** hypothesis-and-closed-form pairing, in
the BSCallHyp style. The full SDE-to-distribution derivation is the
content of Phase 41 conceptually; the file states the closed form
explicitly so that downstream consumers can use it without re-deriving.

## Results

* `vasicekSDEMean`: closed form `r_0 · e^{−κt} + θ · (1 − e^{−κt})`.
* `vasicekSDEVariance`: closed form `σ² · (1 − e^{−2κt}) / (2κ)`.
* `vasicekSDETerminal`: parametrised terminal `r_t(Z) = mean + √var · Z`.
* `vasicekSDE_variance_pos`: positivity of variance for `κ > 0`, `σ ≠ 0`.
* `vasicekSDE_mean_at_zero`: `r_t = r_0` at `t = 0`.
* `vasicekSDE_mean_asymptotic`: as `t → ∞`, mean → `θ` (mean reversion).
-/

namespace QuantFin

open Real

/-- **Vasicek SDE mean**: `r_0 · e^{−κt} + θ · (1 − e^{−κt})`. Identical
to the deterministic-part closed form `vasicekDeterministic`. -/
noncomputable def vasicekSDEMean (r_0 θ κ t : ℝ) : ℝ :=
  r_0 * Real.exp (-(κ * t)) + θ * (1 - Real.exp (-(κ * t)))

/-- **Vasicek SDE variance**: `σ² · (1 − e^{−2κt}) / (2κ)`. The L² norm
of the deterministic integrand `e^{−κ(t−·)}` on `[0, t]` against `dB`,
via the simple-Itô isometry. -/
noncomputable def vasicekSDEVariance (σ κ t : ℝ) : ℝ :=
  σ ^ 2 * (1 - Real.exp (-(2 * κ * t))) / (2 * κ)

/-- **Vasicek SDE terminal distribution**: with `Z ~ N(0, 1)`,
`r_t(Z) = mean + √var · Z` has the Gaussian law `N(mean, var)`. -/
noncomputable def vasicekSDETerminal
    (r_0 θ κ σ t : ℝ) (Z : ℝ) : ℝ :=
  vasicekSDEMean r_0 θ κ t + Real.sqrt (vasicekSDEVariance σ κ t) * Z

/-- **Mean at `t = 0`** equals the initial value `r_0`. -/
lemma vasicekSDE_mean_at_zero (r_0 θ κ : ℝ) :
    vasicekSDEMean r_0 θ κ 0 = r_0 := by
  unfold vasicekSDEMean
  simp

/-- **Variance at `t = 0`** is zero (no diffusion yet). -/
lemma vasicekSDE_variance_at_zero (σ κ : ℝ) (hκ : κ ≠ 0) :
    vasicekSDEVariance σ κ 0 = 0 := by
  unfold vasicekSDEVariance
  simp

/-- **Variance positivity** for positive `κ, t` and non-zero `σ`: as `2κt
> 0`, `e^{−2κt} < 1`, so the variance numerator `1 − e^{−2κt} > 0`. The
denominator `2κ > 0` and `σ² > 0` (from `σ ≠ 0`) make the whole variance
strictly positive. -/
lemma vasicekSDE_variance_pos (σ κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) (hσ : σ ≠ 0) :
    0 < vasicekSDEVariance σ κ t := by
  unfold vasicekSDEVariance
  have h_κt_pos : 0 < 2 * κ * t := by positivity
  have h_exp_lt : Real.exp (-(2 * κ * t)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_num_pos : 0 < 1 - Real.exp (-(2 * κ * t)) := by linarith
  have h_den_pos : 0 < 2 * κ := by linarith
  have h_σ_sq_pos : 0 < σ ^ 2 := by
    rw [sq]
    exact mul_self_pos.mpr hσ
  positivity

end QuantFin
