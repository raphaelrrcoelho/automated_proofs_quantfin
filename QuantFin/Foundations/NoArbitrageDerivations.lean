/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Core quant-finance results derived from no-arbitrage (first principles)

This file derives the canonical static no-arbitrage relations — **put-call
parity** and the **forward price** — from a single structural object: a
non-negative linear pricing functional on payoffs.

The pattern: a "market" is parameterised by

* a finite state space `s : Finset ι`,
* non-negative state prices `q : ι → ℝ` (`hq : 0 ≤ q i`),
* terminal asset values `S : ι → ℝ`,

with two structural constraints:

* **Bond pricing**: `∑ q i = DF`, where `DF` is the time-0 price of a
  contract paying `1` at maturity in every state.
* **Stock pricing**: `∑ q i · S i = S_0`, where `S_0` is the time-0 spot
  price of the asset.

A general claim with payoff `g : ι → ℝ` has time-0 price `Λ(g) := ∑ q i · g i`.
This `Λ` is a non-negative linear functional.

## Why this is "first principles"

The pre-existing `bsP_eq_bsV` (in `BlackScholes.PutGreeks`) is an *algebraic*
verification: starting from the closed forms `bsV` and `bsP`, prove they
differ by `S - K · e^{-rτ}`. The proof is `unfold` + `linear_combination`
on the gaussian-CDF identity `Φ(x) + Φ(-x) = 1`.

The *first-principles* version below — `putCall_parity_from_no_arbitrage` —
makes no reference to `bsV`, `bsP`, the BS formula, or any closed form. It
says: whenever a market admits a non-negative linear pricing functional
with the bond and stock constraints, *any* call and put prices satisfy
parity. The proof is two lines:

1. Pointwise: `max(S - K, 0) - max(K - S, 0) = S - K`.
2. Linearity of `Λ`: `Λ(C-payoff) - Λ(P-payoff) = Λ(S - K) = S_0 - K · DF`.

The same template gives the forward price `F = S_0 / DF`.

## Results

* `max_sub_max_neg`: `max x 0 - max (-x) 0 = x` (the payoff identity).
* `putCall_parity_from_no_arbitrage`: the parity derivation.
* `forward_price_from_no_arbitrage`: the forward price characterisation.
-/

namespace QuantFin

open Finset

/-- **Payoff identity**: `max(x, 0) - max(-x, 0) = x`.

This is the pointwise algebraic fact that turns into put-call parity when
passed through a linear pricing functional. -/
lemma max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    rw [max_eq_right (by linarith : -x ≤ 0)]
    ring
  · have hx' : x < 0 := not_le.mp hx
    rw [max_eq_right hx'.le]
    rw [max_eq_left (by linarith : 0 ≤ -x)]
    ring

/-- **Put-call parity from no-arbitrage** (first-principles derivation).

In a finite-state market with non-negative state prices `q : ι → ℝ`,
terminal asset values `S : ι → ℝ`, discount factor `DF = ∑ q i`, and spot
price `S_0 = ∑ q i · S i`, the call price `C(K) = ∑ q i · max(S i − K, 0)`
and the put price `P(K) = ∑ q i · max(K − S i, 0)` satisfy

  `C(K) − P(K) = S_0 − K · DF`.

The proof has *no reference to the Black-Scholes formula*. It uses only:
* linearity of the pricing functional `Λ(g) := ∑ q i · g i`,
* the pointwise payoff identity `max(S - K, 0) - max(K - S, 0) = S - K`
  (`max_sub_max_neg`),
* the bond and stock pricing constraints.

Specialisation to the BS model recovers `bsP_eq_bsV` (currently proved
algebraically); the algebraic proof there can now be seen as
"the BS closed forms are realised by some such pricing functional." -/
theorem putCall_parity_from_no_arbitrage
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ K : ℝ)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : ∑ i ∈ s, q i * S i = S₀) :
    (∑ i ∈ s, q i * max (S i - K) 0) - (∑ i ∈ s, q i * max (K - S i) 0)
      = S₀ - K * DF := by
  -- Pointwise: q i · max(S i − K, 0) − q i · max(K − S i, 0) = q i · (S i − K).
  have h_pointwise : ∀ i ∈ s,
      q i * max (S i - K) 0 - q i * max (K - S i) 0 = q i * (S i - K) := by
    intros i _
    have h_identity : max (S i - K) 0 - max (K - S i) 0 = S i - K := by
      have h := max_sub_max_neg (S i - K)
      rwa [show -(S i - K) = K - S i from by ring] at h
    linear_combination q i * h_identity
  calc (∑ i ∈ s, q i * max (S i - K) 0) - (∑ i ∈ s, q i * max (K - S i) 0)
      = ∑ i ∈ s, (q i * max (S i - K) 0 - q i * max (K - S i) 0) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ i ∈ s, q i * (S i - K) := Finset.sum_congr rfl h_pointwise
    _ = ∑ i ∈ s, (q i * S i - K * q i) := Finset.sum_congr rfl (fun i _ => by ring)
    _ = (∑ i ∈ s, q i * S i) - K * (∑ i ∈ s, q i) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = S₀ - K * DF := by rw [h_bond, h_stock]

/-- **Forward price from no-arbitrage** (first-principles derivation).

The fair forward price `F` — the strike at which the forward contract
with terminal payoff `S_T − F` has zero time-0 price — is

  `F = S_0 / DF`.

With continuous compounding (`DF = e^{−rT}`), this is the classical
`F = S_0 · e^{rT}` cash-and-carry formula.

The proof: by linearity, `Λ(S_T − F) = Λ(S_T) − F · Λ(1) = S_0 − F · DF`.
Setting this equal to zero and solving gives `F = S_0 / DF`. -/
theorem forward_price_from_no_arbitrage
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ F : ℝ) (hDF : DF ≠ 0)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : ∑ i ∈ s, q i * S i = S₀) :
    (∑ i ∈ s, q i * (S i - F) = 0) ↔ F = S₀ / DF := by
  -- Λ(S - F) = Λ(S) - F · Λ(1) = S_0 - F · DF.
  have h_eval : ∑ i ∈ s, q i * (S i - F) = S₀ - F * DF := by
    calc ∑ i ∈ s, q i * (S i - F)
        = ∑ i ∈ s, (q i * S i - F * q i) := Finset.sum_congr rfl (fun i _ => by ring)
      _ = (∑ i ∈ s, q i * S i) - F * (∑ i ∈ s, q i) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = S₀ - F * DF := by rw [h_bond, h_stock]
  rw [h_eval]
  constructor
  · intro h
    have : F * DF = S₀ := by linarith
    field_simp
    linarith
  · intro hF
    rw [hF]; field_simp; ring

/-- **Forward price (closed form)**: the unique fair forward is `F = S_0 / DF`. -/
theorem forward_price_eq_spot_div_discount
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ : ℝ) (hDF : DF ≠ 0)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : ∑ i ∈ s, q i * S i = S₀) :
    ∃! F : ℝ, ∑ i ∈ s, q i * (S i - F) = 0 := by
  refine ⟨S₀ / DF, ?_, ?_⟩
  · exact (forward_price_from_no_arbitrage s q S DF S₀ (S₀ / DF) hDF h_bond h_stock).mpr rfl
  · intro F hF
    exact (forward_price_from_no_arbitrage s q S DF S₀ F hDF h_bond h_stock).mp hF

end QuantFin
