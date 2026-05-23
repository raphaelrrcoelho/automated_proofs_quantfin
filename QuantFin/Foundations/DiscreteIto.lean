/-
This file is a **Lean 4 derivative work** based on the Lean source snippet
published in Section 3 ("The Discrete Itô Formula") of:

  Tamás Nagy, "From Itô to Black–Scholes: A Machine-Verified Derivation in
  Lean 4", SSRN Working Paper 6336503, March 2026.
  <https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503>

The theorem statement and proof skeleton (telescoping via
`Finset.sum_range_sub` + per-summand Taylor decomposition +
`Finset.sum_add_distrib`) are adapted directly from Nagy's published Lean
code. Modifications: renamed `taylor_remainder` → `discreteTaylorRemainder`
(camelCase convention), factored `(1/2)` out of the second sum, added
type ascription, restructured the proof to use `Finset.sum_congr` for the
per-summand rewrite. Mathematical content is unchanged.

Author of this QuantFin Lean 4 adaptation: Raphael Coelho.
Original Lean derivation: Tamás Nagy (SSRN 6336503, 2026).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content and original Lean code © Tamás Nagy 2026, used here
under academic fair use for derivative work with attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Discrete Itô formula (phase 35, after Nagy 2026)

The discrete Itô formula is an **exact algebraic identity** — no
approximation, no limit, no probability. For any real-valued sequence
`X : ℕ → ℝ` and any (formal) `f, f', f''`, the telescoped difference
factorises as

  `f(X_N) − f(X_0) = Σ_{k<N} f'(X_k) · ΔX_k
                     + (1/2) · Σ_{k<N} f''(X_k) · (ΔX_k)²
                     + Σ_{k<N} R_k`,

where `ΔX_k := X_{k+1} − X_k` and `R_k` is the **discrete Taylor
remainder**, *defined* here so that the identity is tautological-by-
construction (the substantive content is the *bound* on `R_k` under the
continuous limit, which is deferred).

## Why this matters for quant finance

The "Itô correction" `(1/2) f''(X_k)·(ΔX_k)²` appears here as a purely
algebraic structural fact — no probability assumed. The Itô correction
becomes *probabilistically* meaningful only in the continuous limit, when
`(ΔX_k)² ≈ ΔW_k² ≈ Δt_k` (the L¹ quadratic-variation identity proved in
`Foundations/BrownianQuadraticVariation.lean`). Then the discrete formula
becomes Itô's lemma `df(X_t) = f'(X_t) dX_t + (1/2) f''(X_t) σ²(X_t) dt`.

This file establishes the algebraic backbone; the QV identity (phase 32)
provides the probabilistic content needed for the limit.

## Results

* `discreteTaylorRemainder`: definition of the per-step remainder.
* `discrete_ito_formula`: the main identity.
-/

namespace QuantFin

/-- **Discrete Taylor remainder** at sub-interval `[X_k, X_{k+1}]`: the
deviation of `f(X_{k+1}) − f(X_k)` from its second-order Taylor expansion
around `X_k`. *Defined* as

  `R_k(f, X_k, X_{k+1}) := f(X_{k+1}) − f(X_k) − f'(X_k)·ΔX_k − (1/2)·f''(X_k)·(ΔX_k)²`,

making the discrete Itô formula a definitional identity. The substantive
content lies in the **third-order bound** on `R_k` under `f ∈ C³` (the
classical Taylor remainder estimate); that bound governs the limit-to-
continuous step and is deferred. -/
noncomputable def discreteTaylorRemainder
    (f f' f'' : ℝ → ℝ) (Xk Xkp1 : ℝ) : ℝ :=
  f Xkp1 - f Xk -
    f' Xk * (Xkp1 - Xk) -
    (1 / 2) * (f'' Xk * (Xkp1 - Xk) ^ 2)

/-- **Discrete Itô formula** (Nagy 2026, Theorem 3.1). For any real-valued
sequence `X : ℕ → ℝ` and any (formal) `f, f', f''`,

  `f(X_N) − f(X_0) = Σ_{k<N} f'(X_k) · ΔX_k
                     + (1/2) · Σ_{k<N} f''(X_k) · (ΔX_k)²
                     + Σ_{k<N} R_k`,

where `R_k = discreteTaylorRemainder f f' f'' (X k) (X (k+1))`.

Proof: telescoping `f(X_N) − f(X_0) = Σ (f(X_{k+1}) − f(X_k))` via
`Finset.sum_range_sub`, then substituting the definition of `R_k` into
each summand, then `Finset.sum_add_distrib` + `Finset.mul_sum`. No
probabilistic content; the Itô correction `(1/2) f''(X_k)·(ΔX_k)²`
appears purely algebraically. -/
theorem discrete_ito_formula
    (N : ℕ) (X : ℕ → ℝ) (f f' f'' : ℝ → ℝ) :
    f (X N) - f (X 0) =
      (∑ k ∈ Finset.range N, f' (X k) * (X (k + 1) - X k)) +
      (1 / 2) *
        (∑ k ∈ Finset.range N, f'' (X k) * (X (k + 1) - X k) ^ 2) +
      ∑ k ∈ Finset.range N,
        discreteTaylorRemainder f f' f'' (X k) (X (k + 1)) := by
  -- Telescoping: f(X N) - f(X 0) = Σ (f(X (k+1)) - f(X k))
  have h_tele : f (X N) - f (X 0) =
      ∑ k ∈ Finset.range N, (f (X (k + 1)) - f (X k)) :=
    (Finset.sum_range_sub (fun n => f (X n)) N).symm
  rw [h_tele]
  -- Per-summand Taylor decomposition
  have h_summand : ∀ k,
      f (X (k + 1)) - f (X k) =
        f' (X k) * (X (k + 1) - X k) +
        (1 / 2) * (f'' (X k) * (X (k + 1) - X k) ^ 2) +
        discreteTaylorRemainder f f' f'' (X k) (X (k + 1)) := by
    intro k
    unfold discreteTaylorRemainder
    ring
  rw [Finset.sum_congr rfl (fun k _ => h_summand k)]
  -- Distribute the three-term sum and pull the (1/2) constant out
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

end QuantFin
