/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.American

/-!
# Snell envelope characterization of `americanPrice`

In the discrete-time binomial tree, the American option price is the **Snell
envelope** of the payoff `g`: the *smallest* function `V : ℕ × ℝ → ℝ`
satisfying:

1. **Intrinsic dominance**: `V n S ≥ g S` at every step `n` and spot `S`.
2. **One-step supermartingale**: for every `n, S`,
   `V (n+1) S ≥ e^{-r}·(q·V n (uS) + (1−q)·V n (dS))`
   (i.e., the discounted Q-expectation of `V n` evaluated at the children
   is bounded above by `V (n+1) S` — the supermartingale property).

This is the optimal-stopping-theoretic characterization of `americanPrice`.
It is equivalent — via standard discrete-time martingale-theory arguments —
to the more familiar form

  `americanPrice n S = sup over stopping rules τ of E^Q[e^{−rτ} g(S_τ)]`

but the Snell envelope form avoids defining stopping rules as path
functions, so it is significantly tighter to formalise. The "sup over
stopping rules" form is downstream work, requiring stopping-time machinery
on the binomial path space `Fin n → Bool`.

## Why this matters

The Snell envelope characterization separates the *definitional* content of
`americanPrice` (a backward Bellman recursion) from its *operational*
content (the smallest supermartingale dominating the payoff). Three
existing results combine to give the full Snell theorem:

* `americanPrice_ge_intrinsic` (Binomial.American): `g S ≤ americanPrice n S`.
* `americanPrice_supermartingale` (Binomial.American): the discounted
  one-step continuation is bounded above by `americanPrice (n+1) S`.
* `americanPrice_le_of_supermartingale_dominating` (this file): any `V`
  satisfying (1) and (2) is bounded below by `americanPrice`.

Together: `americanPrice` is *the* smallest supermartingale dominating `g`.

## Result

* `americanPrice_le_of_supermartingale_dominating`: the upper-bound
  characterization. Combined with the existing dominance and supermartingale
  lemmas in `Binomial.American`, gives the Snell envelope theorem.
-/

namespace QuantFin

/-- **Snell envelope upper bound**: any function `V : ℕ → ℝ → ℝ` that
dominates the payoff (`hV_g`) and satisfies the one-step supermartingale
condition (`hV_super`) is bounded below by `americanPrice` at every step
and spot.

Combined with `americanPrice_ge_intrinsic` and `americanPrice_supermartingale`
(which show `americanPrice` itself satisfies both conditions), this gives
the **Snell envelope characterization**: `americanPrice` is the smallest
such `V`.

Proof: induction on `n`. The base case `n = 0` uses `hV_g 0 S`. The
inductive step uses (a) `hV_g (n+1) S` to bound the intrinsic side of the
Bellman `max`, and (b) `hV_super n S` plus monotonicity of the one-step
operator (`binomialOptionPriceOnePeriod_mono`) plus the IH to bound the
continuation side. -/
theorem americanPrice_le_of_supermartingale_dominating
    {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ) (V : ℕ → ℝ → ℝ)
    (hV_g : ∀ n S, g S ≤ V n S)
    (hV_super : ∀ n S,
      binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
        V (n + 1) S) :
    ∀ n S, americanPrice u d r g n S ≤ V n S := by
  intro n
  induction n with
  | zero =>
    intro S
    rw [americanPrice_zero]
    exact hV_g 0 S
  | succ n ih =>
    intro S
    rw [americanPrice_succ]
    refine max_le (hV_g (n + 1) S) ?_
    calc binomialOptionPriceOnePeriod u d r
          (americanPrice u d r g n (S * u)) (americanPrice u d r g n (S * d))
        ≤ binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) :=
          binomialOptionPriceOnePeriod_mono h (ih (S * u)) (ih (S * d))
      _ ≤ V (n + 1) S := hV_super n S

/-- **Snell envelope theorem (packaged form)**: `americanPrice u d r g` is
the smallest function `V : ℕ → ℝ → ℝ` that simultaneously dominates the
payoff and satisfies the one-step supermartingale property.

The statement makes the universal characterization visible: for *any* V
satisfying the two properties, `americanPrice ≤ V`. -/
theorem americanPrice_is_snell_envelope
    {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ) :
    (∀ n S, g S ≤ americanPrice u d r g n S) ∧
    (∀ n S,
      binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u)) (americanPrice u d r g n (S * d)) ≤
      americanPrice u d r g (n + 1) S) ∧
    (∀ (V : ℕ → ℝ → ℝ),
      (∀ n S, g S ≤ V n S) →
      (∀ n S,
        binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
          V (n + 1) S) →
      ∀ n S, americanPrice u d r g n S ≤ V n S) :=
  ⟨americanPrice_ge_intrinsic u d r g,
   americanPrice_supermartingale u d r g,
   americanPrice_le_of_supermartingale_dominating h g⟩

end QuantFin
