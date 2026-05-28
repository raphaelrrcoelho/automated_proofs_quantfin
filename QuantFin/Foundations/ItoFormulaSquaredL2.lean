/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion
import QuantFin.Foundations.ItoSquaringIdentity
import QuantFin.Foundations.QuadraticVariationL2

/-! # Itô's lemma for `f(x) = x²` — the L² continuous-time form

This is the **continuous-time L² Itô formula** for the squaring function. For
Brownian motion `B : ℝ≥0 → Ω → ℝ` and time `T : ℝ≥0`, the Riemann sums
`∑_{k<n} B_{t_k} · (B_{t_{k+1}} − B_{t_k})` along the uniform partition of `[0,T]`
converge **in L²(μ)** to `½ · (B_T² − B_0² − T)`. Equivalently,

  `2 · ∑_{k<n} B_{t_k} · ΔB_k − (B_T² − B_0² − T) → 0`  in `L²(μ)`.

This is the **keystone Itô identity** behind variance-swap pricing, the
Doob definition of the Itô integral, and the BS-PDE-from-Itô derivation:
*the* L² limit of the discrete-Itô sum is `½(B_T² − B_0² − T)` — no
existence theorem for the limit needed, the formula *names* it.

## The proof in one line

The discrete pathwise identity (`discrete_squaring_identity`) says
`B_T² − B_0² = 2·∑ B_{t_k}·ΔB_k + ∑ (ΔB_k)²`. Subtracting `T` and dividing
by `2`,

  `½·(B_T² − B_0² − T) − ∑ B_{t_k}·ΔB_k = ½·(∑ (ΔB_k)² − T)`.

By `tendsto_qv` (L² QV of BM), the RHS L²-norm goes to zero with mesh.
That is the entire content.

## Two equivalent statements

* `itoSquared_L2_tendsto`: the L²-norm of the difference between
  `2·∑ B·ΔB` and `B_T² − B_0² − T` tends to zero, along the uniform
  partition of `[0, T]`. Pure-quantitative form: an integral.
* `itoSquared_L2_tendsto_div2`: the symmetric one-half form,
  `∑ B·ΔB → ½(B_T² − B_0² − T)` in `L²`.

The first form is what the proof produces directly (no division); the
second is the canonical Itô-lemma statement. Both are derived; pick the
shape that downstream proofs find more convenient.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Filter QuantFin.QuadraticVariationL2
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  [hB : IsPreBrownian B μ]

/-- **L² Itô formula for the squaring function — quantitative form.** Along
the uniform partition of `[0, T]` into `n` pieces, the integrated squared
difference between `2 · ∑ B_{kT/n} · ΔB_k` and `B_T² − B_0² − T` tends to
zero. The proof is one algebraic step from the pathwise discrete identity
(`discrete_squaring_identity`) plus `tendsto_qv` (the L² QV of BM). -/
theorem itoSquared_L2_tendsto (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (2 * (∑ k ∈ Finset.range n,
                      B (unifPart T n k) ω *
                        (B (unifPart T n (k + 1)) ω
                          - B (unifPart T n k) ω))
              - (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  -- Rewrite the squared integrand pointwise using `discrete_squaring_identity`.
  -- The identity needs `n > 0` so that `unifPart T n n = T` (at `n = 0` the
  -- partition is degenerate and the endpoints collapse to `0`, not `T`).
  have h_id : ∀ n : ℕ, 0 < n → ∀ ω,
      2 * (∑ k ∈ Finset.range n,
              B (unifPart T n k) ω *
                (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
        - (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))
      = (T : ℝ)
        - ∑ k ∈ Finset.range n, (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
    intro n hn ω
    have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hsn : unifPart T n n = T := by simp only [unifPart, div_self hn0, one_mul]
    have hs0 : unifPart T n 0 = 0 := by simp [unifPart]
    have h := discrete_squaring_identity n (fun k => B (unifPart T n k) ω)
    rw [hsn, hs0] at h
    linarith
  -- Replace the integrand and use `tendsto_qv` (filter out the trivial n=0 case).
  refine (tendsto_qv (μ := μ) (B := B) hBmeas T).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply integral_congr_ae
  filter_upwards with ω
  rw [h_id n hn]
  ring

/-- **L² Itô formula for the squaring function — half-form.** The Riemann sums
`∑_{k<n} B_{kT/n} · (B_{(k+1)T/n} − B_{kT/n})` along the uniform partition of
`[0, T]` tend to `½·(B_T² − B_0² − T)` in `L²(μ)`. The canonical statement of
"the Itô integral of `s ↦ B_s` against `dB_s` equals `½(B_T² − B_0² − T)`",
extracted from the `factor-of-2` form `itoSquared_L2_tendsto`. -/
theorem itoSquared_L2_tendsto_div2 (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
        ∫ ω, ((∑ k ∈ Finset.range n,
                  B (unifPart T n k) ω *
                    (B (unifPart T n (k + 1)) ω
                      - B (unifPart T n k) ω))
              - (1 / 2) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  -- The half-form is (factor-of-2 form) / 4, by `(2A − B)² = 4(A − B/2)²`.
  have h := itoSquared_L2_tendsto (μ := μ) (B := B) hBmeas T
  -- Substitute `(2A − B)² = 4(A − B/2)²` pointwise, then divide-by-4 limit.
  have h_eq : ∀ n : ℕ,
      ∫ ω, (2 * (∑ k ∈ Finset.range n,
                B (unifPart T n k) ω *
                  (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
            - (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) ^ 2 ∂μ
        = 4 * ∫ ω, ((∑ k ∈ Finset.range n,
                B (unifPart T n k) ω *
                  (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
              - (1 / 2) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) ^ 2 ∂μ := by
    intro n
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    ring
  simp_rw [h_eq] at h
  -- `4 · I_n → 0` ⇔ `I_n → 0`.
  have h4 := h.const_mul (1/4 : ℝ)
  simpa using h4

end QuantFin
