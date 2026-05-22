# Math depth roadmap

This document captures the strategic discussion from 2026-05-22 on what
"ultimate Lean/Mathlib quant finance repo" actually means, why depth beats
breadth at this stage, and what the concrete next round would look like.

## The honest distinction

There are three different things people mean by "high-quality formal
math library":

* **Coverage**: most textbook results in the field are formalised.
  Measured by theorem count.
* **Structural depth**: the library organises results around a small
  number of *principles* whose consequences flow as one- to three-line
  corollaries. The hierarchy is visible in the file structure.
* **Original mathematics**: theorems in the library are *contributions* to
  mathematics, not formalisations of textbook material. Mathlib's
  reputation rests largely on this (sphere eversion, Polynomial
  Freiman-Ruzsa, etc.).

Our library is at *medium coverage + partial structural depth + no
original mathematics*. The third tier is out of reach: original quant-
finance mathematics either needs Mathlib's stochastic calculus (Itô,
Girsanov continuous-time, BSDEs — all upstream-gated) or is research-
grade work (Föllmer-Schied dual, robust price bounds under model
uncertainty, Lee 2004 moment formula at full rigor).

What's *in reach* is more structural depth, which is what the next
round should pursue.

## Why depth beats breadth

* **Diminishing returns on breadth.** 250+ theorems is enough. Adding
  another 20 textbook verifications takes the count to 270 but doesn't
  change what the library *is*. The proof shape (`unfold; field_simp;
  ring`) tells the reader what the additions are.

* **Coverage gaps are mostly upstream-gated.** The missing items —
  Itô calculus, Margrabe via change of numéraire, Heston, local vol,
  SABR — need Mathlib's stochastic-calculus layer, which isn't there
  yet. We can't fix that with more `field_simp`.

* **The slop ratio sharpens with more breadth.** Of the 211 "full"
  derivations, roughly 30 are genuinely non-trivial (Doob L^p,
  Wiener L² isometry, joint-stdev triangle, Kelly FOC, Sharpe √T,
  second-order immunization, Asian AM-GM, Merton-tree one-period
  dominance, etc.). The other ~180 are closed-form verifications.
  Adding 20 more closed-form checks moves the ratio from 30:180 to
  30:200 — the wrong direction.

* **Depth additions are multiplicative.** A reflection principle for
  binomial walks unlocks barrier-option pricing as a whole category.
  A continuous-convexity bridge collapses K-direction reasoning across
  the library. A discrete martingale representation makes hedging
  discussions tractable. Each depth theorem leverages future ones.

## What "ultimate Lean/Mathlib quant finance" looks like

Concretely:

1. **A small set of named structural principles** that *generate*
   the consequences. We have nine (Garman normal form, strike
   convexity, price bounds rectangle, Greek signs, convex pricing
   functional, gaussian MGF, exponential discount, Merton-tree
   one-period, replicating uniqueness). Target ~15.

2. **At least one genuinely-non-trivial theorem per category** —
   not just a definition + ring. Currently ~8 (listed above). Target
   ~15–20.

3. **An honest hierarchy** between foundational math, principles, and
   verifications. README now distinguishes the three tiers; file
   organisation could enforce it more strongly.

4. **Eventual upstream contributions to Mathlib** — when Itô lands,
   the deepest quant results become possible. The library's structure
   should be ready to accommodate them.

What it explicitly is *not*:

* The largest theorem count.
* The broadest textbook-chapter coverage.
* Original mathematics. Tao level is original mathematics; that's a
  different game.

## Concrete next-round candidates

Three depth theorems, ranked by leverage:

1. **Multi-step Merton 1973 in the binomial tree** (~150 LOC).
   Combines the one-period dominance shipped in `MertonAmericanCallTree`
   with induction on `n`. Result: `americanPrice = binomialPrice` for
   the non-dividend call at any horizon. Completes the Merton 1973
   story in discrete time. Real theorem (induction + lower-bound
   lemma + dominance).

2. **Continuous convexity of `K ↦ bsV K r σ S τ` on `(0, ∞)`**
   (~150 LOC). Bridges `ConvexPricingFunctional` (finite-state) to
   the actual BS formula via `convexOn_of_deriv2_nonneg` +
   `hasDerivAt_bsV_KK`. After this, four scales (payoff convex /
   discrete price convex / continuous price convex / PDF positive)
   are visibly one fact.

3. **Discrete reflection principle for binomial paths** (~300 LOC).
   Bijection on `Fin n → Bool`. Independently beautiful; unlocks
   barrier-option pricing as a follow-on category.

Total ~600 LOC across three modules. Each ships a theorem whose
statement is non-trivial and whose proof is real math.

## Larger, multi-session candidates

If the project continues beyond the next round:

4. **Variance-optimal hedging in finite-state markets** (~250 LOC).
   Given a contingent claim `X` and a tradable subspace, the
   variance-optimal hedge is the `L²(q)`-orthogonal projection.
   Finite-dimensional Hilbert space.

5. **Discrete-time martingale representation in binomial** (~500 LOC).
   Every Q-martingale is the discrete stochastic integral of a
   predictable process w.r.t. the discounted asset. Constructive.

6. **Optimal-stopping characterisation** (~400 LOC). Snell envelope
   equals `sup_{τ stopping time} E^Q[e^{−rτ} g(S_τ)]`. Requires
   defining stopping times on the binomial path space.

7. **Carr-Madan full integral identity** (~400 LOC). Taylor with
   integral remainder for the log-payoff, expressed as static
   portfolio of OTM puts + calls. Requires `intervalIntegral`
   calculus.

8. **Carr-Lee moment formula** (~600 LOC). Existence of `E[S_T^p]`
   bounded by wing-decay rate of implied vol `σ²(K) · T`. Real-
   analytic, genuinely surprising.

## What this library can *not* become without Mathlib upstream

Honest scope statement:

* **Continuous-time Itô calculus**: Mathlib does not ship the Itô
  integral at the current pin. Until it does, results that *require*
  it (Itô's lemma, Girsanov continuous-time, Margrabe, Heston, local
  volatility, SABR, BSDEs) are out of reach.

* **Continuous Poisson processes**: Mathlib has the discrete
  `PoissonPMF`; continuous-time Poisson processes (interarrival
  exponential, superposition, thinning, Lévy processes) are
  upstream-gated.

* **Fine Brownian path machinery**: reflection principle for BM,
  nowhere-differentiability of BM paths, law of iterated logarithm —
  these need path-level machinery beyond what's currently in
  Mathlib's `BrownianMotion`.

The library can be excellent without these. It cannot be "complete"
quant finance without them.

## Conclusion

The path to "the formalization library that defines what quant finance
looks like in Lean/Mathlib" runs through structural depth, not theorem
count. Three depth theorems plus continued slop-folding plus honest
documentation get us a coherent library that a quant practitioner would
respect. They do not get us to Tao level — that requires original
mathematics, which is a different project.
