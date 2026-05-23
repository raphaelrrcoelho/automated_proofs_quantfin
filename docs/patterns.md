# Learnings

Notes from the 2026-05-22 session that pushed `docs/roadmap.md`'s
three depth-theorem candidates to completion (continuous K-convexity bridge,
multi-step Merton tree, full reflection-principle bijection — Phases 15
and 16). This document captures what worked, what was harder than expected,
and patterns worth reusing.

It is *not* a reference for what's in the library — that's `README.md`,
`docs/coverage.md`, and the source itself. It is a record of the
*how*: idioms, traps, and structural intuitions.

## Structural patterns

### Three-scale unification

A single mathematical principle often manifests at multiple scales of
resolution: payoff (discrete combinatorial), finite-state price (discrete
linear combination), continuous price (calculus). The cleanliness payoff of
formalisation is naming the principle once and writing the three scales as
corollaries.

Example: **K-convexity** of the call now lives at three scales in
`BlackScholes/StrikeConvexity.lean`:

* `convexOn_call_payoff` — payoff `K ↦ max(S − K, 0)` convex (combinatorial:
  `sup` of an affine function and zero).
* `callPrice_finiteState_convexOn_K` (in `ConvexPricingFunctional.lean`) —
  pricing under non-negative state prices preserves convexity.
* `bsV_strike_convexOn` — continuous BS price convex on `(0, ∞)` via
  `convexOn_of_deriv2_nonneg'` and the closed-form second derivative.

Before this session, the three lived as essentially independent claims.
Now the second-derivative computation in `BreedenLitzenberger.lean`
(`lognormalTerminalPDF_nonneg`) reads as "the infinitesimal face of the
same convexity," and `Spreads.lean` reads it as "the discrete face."

The pattern generalises. Wherever a property holds at a payoff level and
is preserved by a non-negative pricing functional, three scales suffice.

### One-period inequality + induction → multi-step theorem

Discrete dynamic-programming arguments lift from one period to `n` periods
by induction *if and only if* you have a monotonicity lemma for the
one-period operator. The structure:

1. Prove the substantive content as a one-period inequality
   (`call_one_period_continuation_dominates_intrinsic`).
2. Prove monotonicity of the one-period operator
   (`binomialOptionPriceOnePeriod_mono`).
3. The multi-step result is induction: at step `n+1`, the European recursion
   gives `one-period(binomialPrice n at daughters)`. By IH, the daughter
   values are bounded; by monotonicity, the bound lifts; the one-period
   inequality closes the step.

Used in `americanCallPrice_le_binomialPrice`. The Bellman-`max` structure
of `americanPrice` makes both intrinsic and continuation bounds visible.

### Algebraic-identity / counting-bijection decoupling

For combinatorial-bijection theorems, separate the *algebraic identity* on
the path level from the *counting* statement at the cardinality level. The
algebraic identity has no decidability or hitting-time prerequisites and
proves cleanly by sum decomposition. The counting bijection then uses the
identity as one ingredient and adds first-hitting-time machinery
(`Finset.min'`) for the other.

Used in `Binomial/PathReflection.lean`:

* `walkPos_reflectAfter_ge` — algebraic identity, no hitting-time anywhere.
* `firstHit`, `HitsLevel`, `reflectAtFirstHit`, `reflectionPrincipleEquiv` —
  counting layer, built on top.

The algebraic identity is what generalises. The counting layer is a clean
application; if a different reflection-style theorem needs a different
counting structure (e.g. ballot problem), the identity remains the same.

## Lean / Mathlib technical idioms

### Type-inference traps with coerced lambdas

```lean
-- WRONG (in a Finset (Fin n) context):
(Finset.univ : Finset (Fin n)).filter (fun i => (i : ℕ) < k)
-- Error: Lean picks i : ℕ from the (i : ℕ) annotation, then Finset.univ
-- has wrong type.

-- RIGHT (option 1): annotate the lambda argument
(Finset.univ : Finset (Fin n)).filter (fun (i : Fin n) => (i : ℕ) < k)

-- RIGHT (option 2): use `.val` to avoid coercion ambiguity
(Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
```

Pattern: whenever a lambda is passed to a polymorphic function and the
argument type is ambiguous, explicit annotation or `.val` resolves it.
Cost the reflection-principle file ~20 minutes of debugging until the
fix landed in one shot. Worth catching early.

### `abbrev` vs `def` for Decidable propagation

```lean
-- WRONG: blocks typeclass synthesis from seeing through.
def HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop :=
  (hittingSet ω a).Nonempty
-- Then: `if h : HitsLevel a ω then ...` fails Decidable synthesis.

-- RIGHT:
abbrev HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop :=
  (hittingSet ω a).Nonempty
-- Now `Decidable (HitsLevel a ω)` is found via `Decidable ((...).Nonempty)`.
```

`abbrev` is `@[reducible] def` — Lean's typeclass system sees through it
during instance search. `def` is opaque to the elaborator. Use `abbrev`
for predicates whose decidability comes from an underlying construction.

### `omega` and the `set` tactic

`set x := expr with x_def` introduces an alias and rewrites occurrences,
but `omega` *does not always* see through the resulting hypotheses. When
omega's counterexample-display shows two different opaque variables that
ought to be the same, the culprit is often a `set` alias not being
unfolded.

Fix: avoid `set` for the variables that flow into omega's hypotheses.
Write out the long expressions or introduce `have` lemmas first.

### `convexOn_of_deriv2_nonneg'` for open intervals

Mathlib has two variants:

* `convexOn_of_deriv2_nonneg` — wants `ContinuousOn` and differentiability
  on the *interior*. For closed intervals.
* `convexOn_of_deriv2_nonneg'` — wants differentiability on the set
  itself. For *open* sets like `Set.Ioi 0`.

`bsV_strike_convexOn` uses the `'` variant since BS is only defined for
`K > 0`. Choose the variant by domain openness.

### `HasDerivAt.congr_of_eventuallyEq` for `deriv f` identification

To prove that `deriv f` has a specific value at a point, when `f` has a
known closed-form derivative, the pattern is:

```lean
-- Local equality of derivatives in a neighborhood:
have h_ev : (fun K' => deriv f K') =ᶠ[nhds K] explicit_first_deriv := by
  filter_upwards [open_set.mem_nhds h_K_pos] with K' hK'
  exact (hasDerivAt_f hK').deriv

-- Transport HasDerivAt of the explicit form to HasDerivAt of `deriv f`:
have h_KK_for_deriv_f : HasDerivAt (deriv f) (second_deriv K) K :=
  h_KK.congr_of_eventuallyEq h_ev
```

Used in `deriv_bsV_eventuallyEq` and the third hypothesis of
`bsV_strike_convexOn`. This is *the* idiom for "second derivative via
intermediate explicit first derivative."

### `Subtype.ext` for `Equiv.left_inv` / `Equiv.right_inv`

When proving `left_inv` / `right_inv` of an `Equiv` between subtypes, a
naive `ext` may peel into pointwise function equality (since the underlying
type may be a function type), which is the wrong granularity.

```lean
-- Use:
left_inv ω := Subtype.ext (by ...)  -- the (by ...) proves val equality
```

Peels exactly one layer (Subtype to underlying value), leaving the
function-level equality to be discharged by the involution.

Used in `reflectionPrincipleEquiv`.

## Workflow patterns

### Daemon-first, lake-build-last

The Lean REPL daemon (`./scripts/lean-check.sh`) checks a single file in
5–30 s by reusing pre-loaded Mathlib oleans. Full `lake build` re-elaborates
the changed module's transitive dependents (often 5–15 minutes).

Workflow:

1. Edit a file.
2. Daemon-check it.
3. Iterate on errors until daemon green.
4. Run `lake build` once at the end (or before committing) to confirm
   cross-file integrity.

The reflection-principle file went through ~6 daemon-check iterations
before reaching `success: true`. Each iteration ~30s. Equivalent
lake-build iterations would have been ~30 minutes total instead of 3.

Caveats: the daemon doesn't write `.olean`s for downstream imports. After
the daemon green-lights a file, the umbrella import won't pick up changes
until a full `lake build` (or daemon restart). For multi-file refactors,
prefer one daemon-check per file plus a final lake build.

### Concrete LOC estimates calibrate

The roadmap predicted:

* Multi-step Merton: ~150 LOC. Actual: ~105.
* Continuous convexity: ~150 LOC. Actual: ~80 (file extension).
* Reflection principle full: ~300 LOC. Actual algebraic core ~180,
  bijection ~190 — ~370 total.

The roadmap was within ~20%. This kind of estimation matters when
deciding between "one focused session" and "spread across multiple
sessions." A 600-LOC roadmap is plausibly one session of focused work;
a 1500-LOC one is not.

### Cleanup-as-you-go beats cleanup-pass-later

The push-neg deprecation warnings in `MertonAmericanCallTree.lean` had
been pending across sessions. Folding the two replacements
(`push_neg at h` → `have h := not_le.mp h`) into the same commit as the
Phase 16-B work added ~5 lines of diff but eliminated the warnings
permanently. A dedicated cleanup pass would have been larger and harder
to motivate.

Apply: when you touch a file, fix the inline warnings if they're trivial
(< 5-minute effort each). Don't accumulate a backlog of "cleanup later"
items.

## Open opportunities

Notes on what would extend this session's work, with rough scope estimates.

### Discrete IVT for ±1 walks (~50 LOC)

The reflection-principle bijection currently requires `HitsLevel a ω` as
a hypothesis on both sides. With a discrete intermediate-value theorem
(`walkPos ω n ≥ a ⟹ HitsLevel a ω`), the right-hand side simplifies to
`{ω : walkPos ω n = 2a − b}` (no hitting condition). This unblocks the
classical **maximal-distribution theorem**

> `|{ω : max_k walkPos ω k ≥ a}| = 2 · |{ω : walkPos ω n ≥ a}| − |{ω : walkPos ω n = a}|`

which is the formula barrier-option pricers actually use.

IVT proof: induction on `n`, using `walkPos_succ` (step changes by ±1).
Likely ~50 LOC.

### Variance-optimal hedging in finite-state markets (~250 LOC)

Given a contingent claim `X : ι → ℝ` on a finite probability space and a
tradable subspace, the variance-optimal hedge is the orthogonal projection
in `L²(q)`. Concretely: minimise `E^q[(X − Δ · S)²]` over deltas in some
linear span. The minimiser is the projection.

This uses real linear algebra (orthogonal projection in inner product
space) and would establish the foundational version of the "quadratic
hedging" toolkit. Mathlib has `InnerProductSpace`, `orthogonalProjection`,
etc. — should slot in cleanly.

### First-hit on the upcrossing side (~80 LOC)

Currently `firstHit` requires `HitsLevel a ω` as a proof argument
(`(hittingSet ω a).min' h`). An alternative: define
`firstHit? ω a : Option ℕ` returning `none` for non-hit paths. This is
more ergonomic for computational reasoning and matches the typical
mathematical narrative ("the first hit, if it exists").

Could refactor `firstHit` into `firstHit?` and provide convenience
helpers. Mostly notation work, but unlocks cleaner downstream theorems.

## Anti-patterns to avoid

### "Just unfold the def" without checking what gets exposed

`unfold X at hyp` rewrites the *occurrence in `hyp`* but not in the goal.
If the goal also contains `X`, the hypothesis and goal will mention
different terms — and `omega`/`linarith` won't unify them.

Pattern that bit the `firstHit_le` proof: I had

```lean
have h_mem := (...).min'_mem h
unfold hittingSet at h_mem
-- Now h_mem talks about `(Finset.range (n+1)).filter (...)`
-- Goal still talks about `firstHit ω a h`
-- omega sees these as different opaque variables.
```

Fix: keep the hypothesis at the level of the goal's terms, and extract the
needed numeric facts via cleaner predicates.

### Multiple `set` calls in a proof passed to `omega`

`set` introduces local aliases, but their definitional unfolding is
fragile under tactics that work with hypothesis context. If a proof needs
to compare two terms that are *definitionally equal* via a `set` alias,
write out the terms explicitly rather than relying on the aliases.

### Over-folding small lemmas

The temptation when refactoring is to fold small modules into parent
files. This can hurt clarity when the small module names a distinct
principle. `BlackScholes/StrikeConvexity.lean` was *not* folded into
`StrikeGreeks.lean` despite their proximity — because K-convexity is a
*principle*, while strike Greeks are *computations*. Naming wins out
over collocation.

Conversely, the original Phase-13 modules (Quanto, CDS, etc.) *were*
folded into their parents because each was a one-shot algebraic check, not
a principle.

Rule: fold when the file is one algebraic check. Don't fold when the file
names a principle that downstream code cites.
