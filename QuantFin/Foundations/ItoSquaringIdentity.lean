/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Foundations.DiscreteIto

/-! # Itô's lemma for `f(x) = x²` — the discrete squaring identity

For `f(x) = x²` the discrete Itô formula (`discrete_ito_formula`) collapses
to an exact algebraic identity, because the second-order Taylor expansion
of `x²` around any point is *exact* — the third-order remainder vanishes.

For any real sequence `X : ℕ → ℝ` and any `N`,

  `X_N² − X_0² = 2 · ∑_{k<N} X_k · (X_{k+1} − X_k) + ∑_{k<N} (X_{k+1} − X_k)²`.

This is the **discrete Itô formula for squaring** — the pre-probabilistic
content of `B_t² − B_0² = 2 ∫₀ᵗ B_s dB_s + ⟨B⟩_t`, the keystone Itô
identity that drives variance-swap pricing, the Black–Scholes PDE
derivation, and (via Doob's quadratic-variation theorem) the very
definition of the stochastic integral against a martingale.

The identity is **pathwise** (one `ω` at a time) and contains no
probability; the probabilistic L² version requires the continuous-time
Itô integral as a process plus the L² convergence of the partition QV
to deterministic `t`. That bridge is deferred to a follow-up: see the
"continuous Itô lemma" track in the resume plan.

## Main results

* `discreteTaylorRemainder_sq` — the Taylor remainder for `f = x²` is `0`.
* `discrete_squaring_identity` — the pathwise identity
  `X_N² − X_0² = 2·∑ X_k·ΔX_k + ∑ (ΔX_k)²`.
-/

namespace QuantFin

/-- For `f(x) = x²`, with `f'(x) = 2x` and `f''(x) = 2`, the discrete Taylor
remainder vanishes identically — `x ↦ x²` *is* its own second-order Taylor
expansion at every point. -/
lemma discreteTaylorRemainder_sq (Xk Xkp1 : ℝ) :
    discreteTaylorRemainder (fun x => x ^ 2) (fun x => 2 * x) (fun _ => 2) Xk Xkp1 = 0 := by
  unfold discreteTaylorRemainder
  ring

/-- **Discrete Itô formula for squaring.** For any real sequence `X` and `N`,

  `X_N² − X_0² = 2 · ∑_{k<N} X_k · ΔX_k + ∑_{k<N} (ΔX_k)²`.

Specialisation of `discrete_ito_formula` to `f(x) = x²` (where the Taylor
remainder is identically `0` — `discreteTaylorRemainder_sq`). -/
theorem discrete_squaring_identity (N : ℕ) (X : ℕ → ℝ) :
    X N ^ 2 - X 0 ^ 2 =
      2 * (∑ k ∈ Finset.range N, X k * (X (k + 1) - X k)) +
      ∑ k ∈ Finset.range N, (X (k + 1) - X k) ^ 2 := by
  have h := discrete_ito_formula N X (fun x => x ^ 2) (fun x => 2 * x) (fun _ => 2)
  -- Collapse the remainder sum to 0 via `discreteTaylorRemainder_sq`.
  rw [Finset.sum_congr rfl (fun k _ => discreteTaylorRemainder_sq (X k) (X (k + 1))),
      Finset.sum_const_zero, add_zero] at h
  -- Pull the `2 X_k` and the `2` from the f''-sum into the standard form.
  rw [h]
  -- 2 X_k * ΔX_k → ∑ 2 X_k * ΔX_k = 2 * ∑ X_k * ΔX_k.
  -- (1/2) * ∑ 2 * (ΔX_k)² = ∑ (ΔX_k)².
  rw [show (∑ k ∈ Finset.range N, 2 * X k * (X (k + 1) - X k))
        = 2 * (∑ k ∈ Finset.range N, X k * (X (k + 1) - X k)) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring,
      show ((1 : ℝ) / 2) * ∑ k ∈ Finset.range N, 2 * (X (k + 1) - X k) ^ 2
        = ∑ k ∈ Finset.range N, (X (k + 1) - X k) ^ 2 by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring]

/-- **Discrete Itô-squaring rearranged** (the form that directly tracks
`B_T² − B_0²`): writes `X_N²` as `X_0²` plus the Itô-sum-with-itself plus
the quadratic variation along the partition. -/
theorem discrete_squaring_identity' (N : ℕ) (X : ℕ → ℝ) :
    X N ^ 2 = X 0 ^ 2 +
      2 * (∑ k ∈ Finset.range N, X k * (X (k + 1) - X k)) +
      ∑ k ∈ Finset.range N, (X (k + 1) - X k) ^ 2 := by
  have := discrete_squaring_identity N X
  linarith

end QuantFin
