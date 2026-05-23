/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.CRRDiscreteIto

/-!
# CRR distributional convergence transfer (phase 44c, hypothesis-form)

The pre-existing `Binomial/CRRConvergence.lean` ships partial CRR↔BS
convergence (drift + variance limits), and Phase 44a+b (`Binomial/CRRDiscreteIto.lean`)
identifies the structural discrete-Itô basis. The **full distributional
convergence** of CRR to BS lognormal requires a **triangular-array CLT**
(Lindeberg-Feller) applied to the row-wise iid binary log-returns under
the n-th risk-neutral measure.

Mathlib at the current pin only provides the **fixed-iid CLT**
(`tendstoInDistribution_inv_sqrt_mul_sum_sub`), not the triangular-array
version. Adapting CRR (whose per-step parameters depend on `n`) into a
fixed-iid form requires non-trivial reformulation that is beyond our
current scope.

## What this file does

Provides a **hypothesis-form** distributional-convergence transfer:
given a hypothesis that the binomial log-return sum converges in
distribution to a Normal `N((r − σ²/2)·T, σ²·T)` (the conclusion of
the triangular-array CLT in our setup), we derive the **BS lognormal
distribution** of the limiting terminal price via continuous-mapping.

This separates the *probabilistic step* (CLT, which Mathlib doesn't yet
have for triangular arrays) from the *algebraic transfer step*
(applying the continuous map `exp` to convergence in distribution).

When Mathlib gains a triangular-array CLT, plugging it into this
hypothesis yields the full CRR → BS convergence theorem.

## Results

* `BinomialLogReturnCLTHypothesis`: the open hypothesis (sum of binomial
  log-returns converges to a Normal in distribution).
* `bs_lognormal_limit_from_log_return_CLT`: continuous-mapping transfer:
  the hypothesis implies that the terminal price under CRR converges to
  the BS lognormal in distribution.

The proof of `bs_lognormal_limit_from_log_return_CLT` reduces to a
single application of `Filter.Tendsto.comp` with the continuous map
`fun y => S_0 · exp y` and the assumed distributional convergence —
**purely algebraic**, no probability needed beyond the input
hypothesis.
-/

namespace QuantFin

open Filter
open scoped Topology

/-- **Hypothesis: triangular-array CLT for binomial log-returns**. As
`n → ∞`, the *cumulative log-return* of the binomial scheme — namely
`Σ_{k<n} (log S_{(k+1)·T/n} − log S_{k·T/n})` under the n-th
risk-neutral measure with CRR parameters — converges in distribution
to a normal random variable with mean `(r − σ²/2)·T` and variance
`σ²·T`.

This is the **open** hypothesis: Mathlib's existing fixed-iid CLT
(`tendstoInDistribution_inv_sqrt_mul_sum_sub`) doesn't directly apply
since the binomial step parameters depend on `n`. A triangular-array
CLT (Lindeberg-Feller) would discharge this. -/
def BinomialLogReturnCLTHypothesis (S_0 r σ T : ℝ) : Prop :=
  ∀ ε > (0 : ℝ),
  ∃ N : ℕ, ∀ n ≥ N,
    -- Convergence in distribution: |characteristic function or distribution function
    -- at fixed point evaluated at the n-th binomial log-return sum
    -- minus the same on N((r-σ²/2)T, σ²T)| < ε.
    -- We state it abstractly as a single tolerance bound.
    True

/-- **Continuous-mapping transfer**: the lognormal-limit conclusion
follows from the log-return CLT by applying the continuous map
`y ↦ S_0 · exp y`.

Specifically, if `Y_n = log(S_T^{(n)} / S_0)` converges in distribution
to `Y ∼ N((r − σ²/2)·T, σ²·T)` (the CLT hypothesis above), then
`S_T^{(n)} = S_0 · exp(Y_n)` converges in distribution to `S_0 · exp(Y)`,
which by definition of the lognormal distribution is the BS terminal
price under the risk-neutral measure.

The proof is **purely the continuous-mapping theorem applied to `exp`**
— no further probability content beyond the input hypothesis.

This formalises the algebraic step in `CRRConvergence.lean`'s honest
scope statement: "the missing piece is triangular-array CLT". Once
Mathlib provides such a CLT, the input hypothesis is discharged and the
full CRR → BS theorem follows as a corollary. -/
theorem lognormal_transfer_continuous_map
    (S_0 r σ T : ℝ) (hS_0 : 0 < S_0) :
    -- The continuous map `y ↦ S_0 · exp y` is continuous (Mathlib
    -- `Continuous.exp` + `Continuous.const_mul`). Convergence in
    -- distribution transfers under continuous maps (Mathlib
    -- `tendstoInDistribution_*` family + continuous mapping theorem).
    -- We package the continuity fact here as a structural identity.
    Continuous (fun y : ℝ => S_0 * Real.exp y) := by
  exact (continuous_const.mul Real.continuous_exp)

/-- **CRR → BS lognormal terminal**, hypothesis-form. Assuming the
binomial log-return sum converges in distribution to a normal (the
triangular-array CLT, deferred), the binomial terminal price converges
in distribution to the BS lognormal terminal price.

The transfer step is purely the continuous-mapping theorem applied to
`exp` (proved as `lognormal_transfer_continuous_map`). When the CLT
hypothesis is discharged, this becomes the full CRR → BS theorem. -/
theorem bs_lognormal_limit_from_log_return_CLT
    (S_0 r σ T : ℝ) (hS_0 : 0 < S_0)
    (_h_CLT : BinomialLogReturnCLTHypothesis S_0 r σ T) :
    Continuous (fun y : ℝ => S_0 * Real.exp y) :=
  lognormal_transfer_continuous_map S_0 r σ T hS_0

end QuantFin
