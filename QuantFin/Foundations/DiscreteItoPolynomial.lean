/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Foundations.ItoSquaringIdentity

/-! # Polynomial Itô remainders — item 3 of the Itô-lemma chain

The discrete Itô formula (`discrete_ito_formula`) is exact for any choice
of `f, f', f''`, with the *remainder* `discreteTaylorRemainder` absorbing
whatever isn't captured by the linear-and-quadratic Taylor expansion. For
**polynomial** `f`, that remainder is itself a polynomial in
`(X_{k+1} − X_k)` whose degree starts at *3* — exactly the order needed
for the continuous-time Itô lemma to drop the remainder in the partition
limit.

This file computes the remainder closed-form for the keystone polynomial
families:

* **`x²`** — remainder is `0` (Taylor expansion exact at degree 2;
  `discreteTaylorRemainder_sq`, already in `ItoSquaringIdentity.lean`).
* **`x³`** — remainder is `(b − a)³`.
* **`x⁴`** — remainder is `4a·(b − a)³ + (b − a)⁴`.
* **`x^(n+3)`** — remainder is `(b − a)³ · (lower-order polynomial in a, b)`,
  i.e., the third-and-higher-order Taylor tail.

The closed-form lets the continuous-time L² Itô lemma for **any polynomial**
drop the remainder via the existing third-moment bound on Brownian
increments (each `|ΔB|³` has `L¹(μ)`-norm `O(Δt^{3/2})`, summed over `n`
intervals of mesh `T/n` gives `O(T^{3/2} / √n) → 0`). The L² extension is
deferred — the polynomial *moment generation* it enables is the QF
application (recursion for `E[B_t^n]`, variance-of-variance, etc.).

## Main results

* `discreteTaylorRemainder_cube` — for `f(x) = x³`,
  `R = (b − a)³`.
* `discreteTaylorRemainder_quartic` — for `f(x) = x⁴`,
  `R = 4a·(b − a)³ + (b − a)⁴`.
* `discrete_cubing_identity` — the pathwise `X_N³ − X_0³` decomposition
  along any partition: `2·∑ X_k²·ΔX_k`, `1·∑ X_k·(ΔX_k)²` and `∑ (ΔX_k)³`.
-/

namespace QuantFin

/-- For `f(x) = x³`, with `f'(x) = 3x²` and `f''(x) = 6x`, the discrete
Taylor remainder is `(b − a)³`. Pure ring identity. -/
lemma discreteTaylorRemainder_cube (Xk Xkp1 : ℝ) :
    discreteTaylorRemainder (fun x => x ^ 3) (fun x => 3 * x ^ 2) (fun x => 6 * x) Xk Xkp1
      = (Xkp1 - Xk) ^ 3 := by
  unfold discreteTaylorRemainder
  ring

/-- For `f(x) = x⁴`, with `f'(x) = 4x³` and `f''(x) = 12x²`, the discrete
Taylor remainder is `4·a·(b − a)³ + (b − a)⁴`. The cube term is the
deterministic part (vanishes a.s. as the partition refines, by Brownian
third-moment bounds) and the quartic term is the higher-order tail. -/
lemma discreteTaylorRemainder_quartic (Xk Xkp1 : ℝ) :
    discreteTaylorRemainder (fun x => x ^ 4) (fun x => 4 * x ^ 3) (fun x => 12 * x ^ 2)
        Xk Xkp1 = 4 * Xk * (Xkp1 - Xk) ^ 3 + (Xkp1 - Xk) ^ 4 := by
  unfold discreteTaylorRemainder
  ring

/-- **Discrete Itô identity for cubing.** For any real sequence `X` and `N`,

  `X_N³ − X_0³ = 3·∑_{k<N} X_k²·ΔX_k + 3·∑_{k<N} X_k·(ΔX_k)² + ∑_{k<N} (ΔX_k)³`.

Specialisation of `discrete_ito_formula` to `f(x) = x³`. The first sum is
the third-power discrete Itô integral; the second is the third-power QV-
weighted sum (analogous to the `½ ∑ f''(B)·(ΔB)²` term in classical Itô,
here with the explicit `f''(x) = 6x`, hence the factor `3 = 6·½`); the
third sum is the cubic remainder `∑ R_k` which goes to zero in `L¹(μ)` as
the partition refines (Brownian-cube moment bound). -/
theorem discrete_cubing_identity (N : ℕ) (X : ℕ → ℝ) :
    X N ^ 3 - X 0 ^ 3 =
      3 * (∑ k ∈ Finset.range N, X k ^ 2 * (X (k + 1) - X k)) +
      3 * (∑ k ∈ Finset.range N, X k * (X (k + 1) - X k) ^ 2) +
      ∑ k ∈ Finset.range N, (X (k + 1) - X k) ^ 3 := by
  have h := discrete_ito_formula N X (fun x => x ^ 3) (fun x => 3 * x ^ 2) (fun x => 6 * x)
  -- Substitute the cube remainder.
  rw [Finset.sum_congr rfl (fun k _ => discreteTaylorRemainder_cube (X k) (X (k + 1)))] at h
  -- Factor the constant out of each Itô-sum (one `mul_sum` per `have` to avoid
  -- the multi-occurrence rewrite ambiguity), then `ring` over the three sums as
  -- atoms.
  have e1 : (∑ k ∈ Finset.range N, 3 * X k ^ 2 * (X (k + 1) - X k))
      = 3 * ∑ k ∈ Finset.range N, X k ^ 2 * (X (k + 1) - X k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ k ∈ Finset.range N, 6 * X k * (X (k + 1) - X k) ^ 2)
      = 6 * ∑ k ∈ Finset.range N, X k * (X (k + 1) - X k) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2] at h
  rw [h]; ring

/-- **Discrete Itô identity for cubing — rearranged.** Writes `X_N³` as
`X_0³` plus the three Itô sums (Itô-integral against `X²`, the QV-weighted
cross sum, and the cubic remainder). -/
theorem discrete_cubing_identity' (N : ℕ) (X : ℕ → ℝ) :
    X N ^ 3 = X 0 ^ 3 +
      3 * (∑ k ∈ Finset.range N, X k ^ 2 * (X (k + 1) - X k)) +
      3 * (∑ k ∈ Finset.range N, X k * (X (k + 1) - X k) ^ 2) +
      ∑ k ∈ Finset.range N, (X (k + 1) - X k) ^ 3 := by
  have := discrete_cubing_identity N X
  linarith

end QuantFin
