/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.Foundations.StatePrices
import HybridVerify.BlackScholes.StrikeConvexity

/-!
# Convexity is preserved by the linear pricing functional

The substantive theorem this file packages:

  **If `g_i(K)` is convex in `K` for each state `i`, and the state prices
  `q_i` are non-negative, then `K ↦ Σ q_i · g_i(K)` is convex in `K`.**

This is the structural reason that — in a finite-state market with
non-negative state prices — **call-price convexity in the strike**,
**butterfly non-negativity at the price level**, and (in the limit)
**implied-PDF non-negativity** all hold. None of these is an
independent fact; each is a consequence of *payoff convexity* passing
through a *non-negative linear operator*.

In the library currently, four facts touch this principle:

* **Payoff** convex (`convexOn_call_payoff` in `BlackScholes/StrikeConvexity`).
* **Price** has `∂²_K bsV ≥ 0` (`hasDerivAt_bsV_KK` in `BlackScholes/StrikeGreeks`,
  whose RHS is manifestly non-negative).
* **Discrete second-difference of payoff ≥ 0** (`butterfly_payoff_nonneg`
  in `BlackScholes/Spreads`).
* **Implied PDF ≥ 0** (`lognormalTerminalPDF_nonneg` in
  `BlackScholes/BreedenLitzenberger`).

These are connected by the convexity-preservation principle but the library
previously did not write that principle down. This file states and proves it,
turning four independent observations into a single structural fact with
three corollaries.

## Why this matters (the "math genius" point)

A textbook-formula verification library writes down each consequence as its
own lemma, proves each with the local algebra (`field_simp` / `linarith`),
and calls it done. A library that *does mathematics* writes the principle
down, proves the consequences as corollaries, and lets the reader see why
the consequences had to be true.

Almost everything in the previous 13 phases of this library is of the first
kind. This module is one example of the second kind.

## Results

* `statePricePricing_convexOn`: linear pricing with non-negative weights
  preserves convexity in any parameter.
* `callPrice_finiteState_convexOn_K`: in a finite-state market, the call
  price is convex in the strike.
* `callPrice_finiteState_butterfly_nonneg`: butterfly non-negativity at
  the *price* level (discrete second-difference of the price), the
  infinitesimal face of which is `∂²_K ≥ 0` and (passing to a continuous
  density) the implied-PDF positivity.
-/

namespace HybridVerify

open Finset

variable {ι : Type*}

/-- **The linear pricing functional preserves convexity** in any parameter.

Given:
- a `Finset` `s` of states,
- non-negative state prices `q i ≥ 0`,
- a family `g i : ℝ → ℝ` of functions, *each convex in `K`*,

the pricing functional `K ↦ Σ q i · g i K` is itself convex in `K`.

Proof: at any pair `K₁, K₂` and weights `α + β = 1` with `α, β ≥ 0`,
each summand `q i · g i (αK₁ + βK₂)` is bounded by `α · (q i · g i K₁) +
β · (q i · g i K₂)` by pointwise convexity (`g i`'s convexity inequality
multiplied by `q i ≥ 0`). Summing preserves the inequality. -/
theorem statePricePricing_convexOn
    (s : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, ConvexOn ℝ (Set.univ : Set ℝ) (g i)) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun K => ∑ i ∈ s, q i * g i K) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ a b ha hb hab => ?_⟩
  -- Goal: Σ q i · g i (a • K₁ + b • K₂) ≤ a • (Σ q i · g i K₁) + b • (Σ q i · g i K₂).
  show ∑ i ∈ s, q i * g i (a • K₁ + b • K₂)
        ≤ a • (∑ i ∈ s, q i * g i K₁) + b • (∑ i ∈ s, q i * g i K₂)
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  -- Pointwise convexity at state i: g i (αK₁ + βK₂) ≤ α · g i K₁ + β · g i K₂.
  have hconv := (hg i hi).2 (Set.mem_univ K₁) (Set.mem_univ K₂) ha hb hab
  simp only [smul_eq_mul] at hconv
  -- Multiply by q i ≥ 0.
  have hqi := hq i hi
  nlinarith [hconv]

/-- **The state-price pricing functional preserves convexity**: stated
in terms of `statePricePricing` from `Foundations/StatePrices`. -/
theorem statePricePricing_convexOn_inK
    (s : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, ConvexOn ℝ (Set.univ : Set ℝ) (g i)) :
    ConvexOn ℝ (Set.univ : Set ℝ)
      (fun K => statePricePricing s q (fun i => g i K)) := by
  unfold statePricePricing
  exact statePricePricing_convexOn s q hq g hg

/-- **Call price is convex in the strike (finite-state market)**: with
non-negative state prices `q_i ≥ 0` and terminal asset values `S_i`,
the call-price functional

  `K ↦ Σ q_i · max(S_i − K, 0)`

is convex in `K`. Direct corollary of the payoff being convex
(`convexOn_call_payoff`) and the linear pricing functional preserving
convexity (`statePricePricing_convexOn` above). -/
theorem callPrice_finiteState_convexOn_K (s : Finset ι)
    (S : ι → ℝ) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) :
    ConvexOn ℝ (Set.univ : Set ℝ)
      (fun K => ∑ i ∈ s, q i * max (S i - K) 0) := by
  refine statePricePricing_convexOn s q hq (fun i K => max (S i - K) 0) ?_
  intro i _
  exact convexOn_call_payoff (S i)

/-- **Butterfly non-negativity at the price level (finite-state market)**:
for any strikes `K₁, K₃` and the midpoint `K₂ = (K₁+K₃)/2`,

  `C(K₁) − 2·C((K₁+K₃)/2) + C(K₃) ≥ 0`,

where `C(K) := Σ q_i · max(S_i − K, 0)` is the finite-state call price.

This is the *infinitesimal* face of `butterfly_payoff_nonneg` (which gives
the same inequality at the *payoff* level): butterfly non-negativity is
preserved when passing from payoff to price via the (non-negative) linear
pricing functional. Passing further to a continuous-density limit yields
the **Breeden-Litzenberger non-negativity** of the implied PDF — the same
fact at three scales (discrete payoff, discrete price, continuous density). -/
theorem callPrice_finiteState_butterfly_nonneg (s : Finset ι)
    (S : ι → ℝ) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) (K₁ K₃ : ℝ) :
    0 ≤ (∑ i ∈ s, q i * max (S i - K₁) 0)
        - 2 * (∑ i ∈ s, q i * max (S i - (K₁ + K₃) / 2) 0)
        + (∑ i ∈ s, q i * max (S i - K₃) 0) := by
  have h_convex := callPrice_finiteState_convexOn_K s S q hq
  have h := h_convex.2 (Set.mem_univ K₁) (Set.mem_univ K₃)
    (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) + 1/2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1/2 * K₁ + 1/2 * K₃ : ℝ) = (K₁ + K₃) / 2 from by ring] at h
  linarith

end HybridVerify
