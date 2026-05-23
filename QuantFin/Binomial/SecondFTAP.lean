/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.Model

/-!
# Second Fundamental Theorem of Asset Pricing (single-period binomial form)

The First FTAP (existence of an equivalent martingale measure ⟺ no-arbitrage)
has a corresponding **Second FTAP**: the EMM is *unique* if and only if the
market is *complete*.

In the single-period binomial model the second FTAP collapses to a clean
algebraic fact:

* **Completeness is automatic**: every contingent claim `(V_u, V_d)` is
  replicated by an explicit Δ/B portfolio (`replicating_portfolio_cost` in
  `Binomial.Model`).
* **Uniqueness of the EMM**: the martingale condition `q·u + (1−q)·d = e^r`
  is a single linear equation in `q`, uniquely solvable when `u ≠ d`. Under
  no-arbitrage (`d < e^r < u`), the unique solution is the risk-neutral
  up-probability `crrUpProb u d r = (e^r − d) / (u − d)`.

So in the single-period binomial: **no-arbitrage ⟹ unique EMM ⟺ completeness**.

## Result

* `second_FTAP_single_period`: under `BinomialNoArb u d r`, the risk-neutral
  up-probability `q` is uniquely determined.
-/

namespace QuantFin

open Real

/-- **Second FTAP (single-period binomial form)**: under no-arbitrage
(`d < e^r < u`), the risk-neutral measure is uniquely characterised by the
martingale condition `q · u + (1 − q) · d = e^r`. The unique solution is
`crrUpProb u d r = (e^r − d) / (u − d)`. -/
theorem second_FTAP_single_period {u d r : ℝ} (h : BinomialNoArb u d r) :
    ∃! q : ℝ, q * u + (1 - q) * d = Real.exp r := by
  have h_ud : 0 < u - d := sub_pos.mpr h.d_lt_u
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  refine ⟨crrUpProb u d r, ?_, ?_⟩
  · -- Existence: `crrUpProb` solves the equation.
    unfold crrUpProb
    field_simp
    ring
  · -- Uniqueness: any solution must equal `crrUpProb`.
    intro q hq
    -- `hq : q · u + (1−q) · d = e^r`  ⟺  `q · (u − d) = e^r − d`  ⟺  `q = (e^r − d)/(u − d)`.
    have h_solve : q * (u - d) = Real.exp r - d := by linarith
    unfold crrUpProb
    rw [eq_div_iff h_ud_ne]
    exact h_solve

/-! ## Multi-period FTAP (marginal-uniqueness form)

In the multi-period binomial tree on path space `Fin n → Bool`, an Equivalent
Martingale Measure (EMM) for the discounted asset must satisfy the
one-step martingale condition `q_k · u + (1 − q_k) · d = e^r` at every
step `k`. By the single-period Second FTAP (above), each `q_k` is uniquely
determined to be `crrUpProb u d r`. So the **marginal step-probabilities of
any multi-period EMM are constant**, equal to `crrUpProb u d r`.

The full path-measure characterization (every multi-period EMM is the
product `μ(ω) = ∏ k, q_k^{ω_k} · (1 − q_k)^{1 − ω_k}` with `q_k = crrUpProb`)
follows from this marginal-uniqueness fact plus a Markov-property argument
on `Fin n → Bool`. We record the marginal-uniqueness form here as the
direct lift of the single-period Second FTAP; the full path-measure form
is downstream work.

## Result

* `multi_period_FTAP_marginals`: under no-arbitrage, the only sequence
  `q : Fin n → ℝ` of per-step risk-neutral probabilities consistent with
  the one-step martingale condition is the constant sequence `crrUpProb u d r`.
-/

/-- **Multi-period First/Second FTAP (marginal form)**: under no-arbitrage,
the unique sequence `q : Fin n → ℝ` of per-step risk-neutral probabilities
satisfying the one-step martingale condition `q_k · u + (1 − q_k) · d = e^r`
at every `k ∈ Fin n` is the constant sequence `q_k ≡ crrUpProb u d r`.

Direct chained application of `second_FTAP_single_period` at each `k`. -/
theorem multi_period_FTAP_marginals {u d r : ℝ} (h : BinomialNoArb u d r) (n : ℕ) :
    ∃! (q : Fin n → ℝ), ∀ k : Fin n, q k * u + (1 - q k) * d = Real.exp r := by
  have h_p : crrUpProb u d r * u + (1 - crrUpProb u d r) * d = Real.exp r := by
    have h_ud_ne : u - d ≠ 0 := (sub_pos.mpr h.d_lt_u).ne'
    unfold crrUpProb; field_simp; ring
  refine ⟨fun _ => crrUpProb u d r, fun _ => h_p, ?_⟩
  intro q hq
  funext k
  exact ExistsUnique.unique (second_FTAP_single_period h) (hq k) h_p

end QuantFin
