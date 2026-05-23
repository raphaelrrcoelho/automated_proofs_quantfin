/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Foundations.DiscreteIto
import QuantFin.Binomial.CRRConvergence
import QuantFin.Binomial.DriftLimit

/-!
# CRR binomial scheme as a discrete-Itô process (phase 44a+b)

The pre-existing `Binomial/CRRConvergence.lean` ships:
- `crrProb_tendsto_half`: `p_n → 1/2` as `n → ∞`,
- `crr_variance_limit`: `4 σ² T · p_n · (1 − p_n) → σ² T`,
- `crr_one_step_martingale`: `p · u + (1 − p) · d = e^{rΔt}` (algebraic),

and `Binomial/DriftLimit.lean` ships:
- `crr_drift_limit_n`: `n · (2 p_n − 1) · σ · √(T/n) → (r − σ²/2) · T`.

This file **bridges** these existing limit facts to the **discrete-Itô
framework** in `Foundations/DiscreteIto.lean` (phase 35, after Nagy 2026).
The binomial log-price `log S_k` is a discrete-Itô process whose:

* per-step drift `q · log u + (1 − q) · log d = (2q − 1) · σ √Δt`,
* per-step quadratic variation `q · (log u)² + (1 − q) · (log d)² − drift²
  = 4 q (1 − q) · σ² Δt`,

are the discrete analogues of the BS log-price's continuous drift
`(r − σ²/2) dt` and QV `σ² dt`. Summed over `n` steps and taking
`n → ∞`, the existing `crr_drift_limit_n` and `crr_variance_limit` lemmas
deliver the BS values.

## Scope (honest)

**44a (algebraic identification)**: The per-step drift and QV formulas as
closed-form expressions in CRR parameters. No probability, just algebra
on `crrUp, crrDown, crrProb`.

**44b (limit composition)**: Summed-over-n drift and QV converge to BS
drift and QV. Pure composition of existing `crr_drift_limit_n` (drift)
and `crr_variance_limit` (QV) with the per-step identities.

**Not done (44c, deferred)**: The triangular-array CLT applied to the
sum of log-returns, yielding distributional convergence to BS lognormal.
Mathlib pin has fixed-iid CLT but not triangular-array; documented as
future work in `CRRConvergence.lean` line 36 already.

## Results

* `binomialLogReturnDrift`: per-step drift `(2 p − 1) · σ √Δt`.
* `binomialLogReturnQV`: per-step QV `4 p (1 − p) · σ² Δt`.
* `binomial_drift_per_step_eq`: algebraic identity for per-step drift
  in terms of `crrProb, crrUp, crrDown`.
* `binomial_QV_per_step_eq`: algebraic identity for per-step QV.
* `tendsto_sum_drift_atTop_BS_drift`: `n · per_step_drift → (r −
  σ²/2)·T` (composes `crr_drift_limit_n`).
* `tendsto_sum_QV_atTop_BS_QV`: `n · per_step_QV → σ²·T` (composes
  `crr_variance_limit`).
-/

namespace QuantFin

open Filter
open scoped Topology

/-- **Per-step drift of the binomial log-return** in the CRR
parameterisation. Algebraically `(2q − 1) · σ · √Δt`, where `q = crrProb,
Δt = T/n, σ` is the BS volatility. -/
noncomputable def binomialLogReturnDrift (r σ T : ℝ) (n : ℕ) : ℝ :=
  (2 * crrProb r σ T n - 1) * σ * Real.sqrt (crrStep T n)

/-- **Per-step quadratic variation of the binomial log-return**:
`4 q (1 − q) · σ² · Δt`. This is the discrete analogue of the BS
log-price QV per `dt`, which equals `σ² dt`. As `q → 1/2`, the prefactor
`4 q (1 − q) → 1`, so the per-step QV → `σ² · Δt`. Summed over `n`
steps: `n · σ²·Δt · 4q(1−q) → σ²·T`. -/
noncomputable def binomialLogReturnQV (r σ T : ℝ) (n : ℕ) : ℝ :=
  4 * crrProb r σ T n * (1 - crrProb r σ T n) * σ ^ 2 * crrStep T n

/-- **Algebraic per-step drift identity**: `q · log u + (1 − q) · log d
= (2q − 1) · σ · √Δt`, where `log u = σ √Δt` and `log d = −σ √Δt` in the
CRR parameterisation. This is the discrete-Itô drift coefficient of
`log S_k → log S_{k+1}`. -/
theorem binomial_drift_per_step_eq (r σ T : ℝ) (n : ℕ) :
    crrProb r σ T n * Real.log (crrUp σ T n) +
      (1 - crrProb r σ T n) * Real.log (crrDown σ T n) =
        binomialLogReturnDrift r σ T n := by
  unfold binomialLogReturnDrift crrUp crrDown
  rw [Real.log_exp, Real.log_exp]
  ring

/-- **Algebraic per-step QV identity**: the variance of the binomial
log-return equals `4 q (1 − q) · σ² · Δt`.

Computation: `Var = q · (log u)² + (1−q) · (log d)² − [q · log u + (1−q) · log d]²
= q · (σ√Δt)² + (1−q) · (−σ√Δt)² − ((2q−1)σ√Δt)²
= σ²·Δt · (q + 1 − q − (2q−1)²)
= σ²·Δt · (1 − (2q−1)²)
= σ²·Δt · 4q(1−q)`. -/
theorem binomial_QV_per_step_eq (r σ T : ℝ) (n : ℕ) (hT : 0 < T) (hn : 1 ≤ n) :
    crrProb r σ T n * (Real.log (crrUp σ T n)) ^ 2 +
    (1 - crrProb r σ T n) * (Real.log (crrDown σ T n)) ^ 2 -
    (crrProb r σ T n * Real.log (crrUp σ T n) +
      (1 - crrProb r σ T n) * Real.log (crrDown σ T n)) ^ 2 =
        binomialLogReturnQV r σ T n := by
  unfold binomialLogReturnQV crrUp crrDown
  rw [Real.log_exp, Real.log_exp]
  -- Subgoal: q·(σ√Δt)² + (1−q)·(−σ√Δt)² − (q·σ√Δt − (1−q)·σ√Δt)²  =  4q(1−q)·σ²·Δt
  -- LHS = σ²·Δt·[q + (1−q) − (2q−1)²] = σ²·Δt·(1 − (2q−1)²) = σ²·Δt·4q(1−q)
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_step_pos : 0 < crrStep T n := div_pos hT h_n_pos
  have h_sqrt_sq : Real.sqrt (crrStep T n) ^ 2 = crrStep T n :=
    Real.sq_sqrt h_step_pos.le
  -- After log_exp, we have (σ·√Δt)² and (−σ·√Δt)² as the per-step log values squared
  -- Reduce using (a+b)² = a² + 2ab + b² then ring on (√Δt)² = Δt
  nlinarith [h_sqrt_sq, sq_nonneg (crrProb r σ T n),
             sq_nonneg (1 - crrProb r σ T n),
             sq_nonneg σ,
             sq_nonneg (σ * Real.sqrt (crrStep T n))]

/-- **Summed-over-n drift converges to BS drift**: `n · per_step_drift →
(r − σ²/2)·T` as `n → ∞`. Direct consequence of `crr_drift_limit_n` from
`Binomial/DriftLimit.lean`. -/
theorem tendsto_sum_drift_atTop_BS_drift
    {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (n : ℝ) * binomialLogReturnDrift r σ T n)
      atTop (𝓝 ((r - σ ^ 2 / 2) * T)) := by
  unfold binomialLogReturnDrift crrStep
  -- After unfolding, the function is `n · (2 p_n − 1) · σ · √(T/n)`, exactly
  -- the form of `crr_drift_limit_n`.
  refine (crr_drift_limit_n hσ hT).congr' ?_
  filter_upwards with n
  ring

/-- **Summed-over-n QV converges to BS QV**: `n · per_step_QV → σ²·T` as
`n → ∞`. Composes `crr_variance_limit` (which gives `4 σ² T · p · (1−p)
→ σ² T`) with the identity `n · per_step_QV = n · 4 p (1−p) · σ² · (T/n)
= 4 σ² T · p · (1−p)`. -/
theorem tendsto_sum_QV_atTop_BS_QV
    {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (n : ℝ) * binomialLogReturnQV r σ T n)
      atTop (𝓝 (σ ^ 2 * T)) := by
  refine (crr_variance_limit (r := r) hσ hT).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  unfold binomialLogReturnQV crrStep
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  field_simp

/-- **Discrete-Itô identification of the binomial scheme** (phase 44
summary). The binomial scheme, parameterised by CRR, is a discrete-Itô
process whose per-step drift and QV — when summed over `n` steps — limit
to the BS log-price drift `(r − σ²/2)·T` and QV `σ²·T`. The full
distributional convergence to BS lognormal (the actual CRR → BS theorem)
requires a triangular-array CLT, deferred per the docstring of
`CRRConvergence.lean`.

Packaged as a single conjunction for downstream consumption. -/
theorem binomial_discrete_ito_convergence
    {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (n : ℝ) * binomialLogReturnDrift r σ T n)
        atTop (𝓝 ((r - σ ^ 2 / 2) * T)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * binomialLogReturnQV r σ T n)
        atTop (𝓝 (σ ^ 2 * T)) :=
  ⟨tendsto_sum_drift_atTop_BS_drift hσ hT,
   tendsto_sum_QV_atTop_BS_QV hσ hT⟩

end QuantFin
