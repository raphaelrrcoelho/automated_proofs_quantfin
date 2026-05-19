# Formalization Status

This project distinguishes two claims:

1. **Backend verification coverage:** active Lean/Isabelle code checks successfully.
2. **Faithful theorem formalization:** the checked statement closely matches the course theorem AND the proof is a real derivation, not a structural projection from an axiomatized conclusion.

The first claim is useful engineering evidence. The second is the academic claim. Do not collapse them.

## Status Vocabulary

- `full`: a faithful formal **derivation** of the textbook theorem from its hypotheses. The hypotheses must be encoded honestly (not the conclusion in disguise) and the proof must do real work — `ring`/`simp`/`rfl` on a structure-projection target does NOT qualify.
- `library_wrapper`: the active code directly invokes a named Lean/Isabelle library theorem whose statement matches the benchmark theorem. The library does the real work.
- `reduced_core`: the active code is honest but narrower than the textbook theorem. This includes:
  - Algebraic / analytic / distributional core checks (e.g., a constant-θ MGF identity behind Wald's exponential).
  - Lean specifications where the textbook conclusion is encoded as a structure field and the proof reads it off via projection. The structure pins down the textbook STATEMENT but does not derive the conclusion.
- `placeholder`: active prover code verifies but does not yet encode a meaningful formal statement of the textbook theorem.

For delivery claims, count only:

```text
full + library_wrapper
```

Report `reduced_core` and `placeholder` separately. **Spec-with-axiomatized-conclusion is `reduced_core`, not `full`.**

## Current Audit

Refresh with:

```bash
python3 -m python.coverage_report
```

Coverage as of 2026-05-19 (extended quant-finance pass: put greeks, higher-order BS greeks, Bachelier greeks, digital greeks, BS-Merton with dividends, Garman-Kohlhagen FX, Black-76 greeks; second pass: Bachelier γ/θ, asset-or-nothing γ, BS-Merton δ/γ/vega, American options in binomial tree):
**88 / 104 delivery-ready** (64 full + 24 library wrappers), 16 reduced cores, 0 placeholders.

The `mathematical_finance.json` benchmark now has 39 theorems (all `full`). Original 14 + 16 from the first 2026-05-19 pass + 9 from the second 2026-05-19 pass:

| ID | name | new module |
|---|---|---|
| `mf-bs-put-formula` | BS put formula | `BlackScholesPut.lean` |
| `mf-put-call-parity` | put-call parity | `BlackScholesPut.lean` |
| `mf-cash-or-nothing` | cash-or-nothing digital | `BlackScholesDigital.lean` |
| `mf-asset-or-nothing` | asset-or-nothing digital | `BlackScholesDigital.lean` |
| `mf-forward-price` | forward / futures pricing | `BlackScholesForward.lean` |
| `mf-vega` | BS vega | `BlackScholesPDE.lean` (extended) |
| `mf-rho` | BS rho | `BlackScholesPDE.lean` (extended) |
| `mf-bachelier-call` | Bachelier model call | `BachelierModel.lean` |
| `mf-implied-vol-unique` | implied volatility uniqueness | `ImpliedVolatility.lean` |
| `mf-black-futures` | Black-76 futures call | `BlackFutures.lean` |
| `mf-binomial-replication` | single-period binomial replication | `BinomialModel.lean` |
| `mf-crr-one-step-martingale` | CRR one-step risk-neutral martingale | `BinomialCRRConvergence.lean` |
| `mf-crr-prob-half` | CRR risk-neutral prob → 1/2 | `BinomialCRRConvergence.lean` |
| `mf-crr-variance-limit` | CRR variance → σ²T | `BinomialCRRConvergence.lean` |
| `mf-bs-put-delta` | BS put delta | `BlackScholesPutGreeks.lean` |
| `mf-bs-put-gamma` | BS put gamma | `BlackScholesPutGreeks.lean` |
| `mf-bs-put-theta` | BS put theta | `BlackScholesPutGreeks.lean` |
| `mf-bs-put-vega` | BS put vega | `BlackScholesPutGreeks.lean` |
| `mf-bs-put-rho` | BS put rho | `BlackScholesPutGreeks.lean` |
| `mf-bs-vanna` | BS vanna | `BlackScholesHigherGreeks.lean` |
| `mf-bs-volga` | BS volga | `BlackScholesHigherGreeks.lean` |
| `mf-bachelier-delta` | Bachelier delta | `BachelierGreeks.lean` |
| `mf-bachelier-vega` | Bachelier vega | `BachelierGreeks.lean` |
| `mf-cash-digital-delta` | cash-or-nothing digital delta | `BlackScholesDigitalGreeks.lean` |
| `mf-asset-digital-delta` | asset-or-nothing digital delta | `BlackScholesDigitalGreeks.lean` |
| `mf-bs-dividends-call` | BS-Merton call with dividends | `BlackScholesDividends.lean` |
| `mf-garman-kohlhagen` | Garman-Kohlhagen FX call | `BlackScholesDividends.lean` |
| `mf-black76-delta` | Black-76 delta | `BlackFuturesGreeks.lean` |
| `mf-black76-gamma` | Black-76 gamma | `BlackFuturesGreeks.lean` |
| `mf-black76-vega` | Black-76 vega | `BlackFuturesGreeks.lean` |
| `mf-bachelier-gamma` | Bachelier gamma | `BachelierGreeks.lean` |
| `mf-bachelier-theta` | Bachelier theta | `BachelierGreeks.lean` |
| `mf-asset-digital-gamma` | asset-or-nothing digital gamma | `BlackScholesDigitalGreeks.lean` |
| `mf-bs-merton-delta` | BS-Merton (dividends) delta | `BlackScholesDividendsGreeks.lean` |
| `mf-bs-merton-gamma` | BS-Merton (dividends) gamma | `BlackScholesDividendsGreeks.lean` |
| `mf-bs-merton-vega` | BS-Merton (dividends) vega | `BlackScholesDividendsGreeks.lean` |
| `mf-american-intrinsic-bound` | American option ≥ intrinsic | `AmericanBinomial.lean` |
| `mf-american-supermartingale` | American discounted price is supermartingale | `AmericanBinomial.lean` |
| `mf-american-ge-european` | American ≥ European (same payoff) | `AmericanBinomial.lean` |

All 39 are `full`, axioms-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

### Quality / structural improvements (2026-05-16 → 2026-05-17 sessions)

These do not change coverage numbers but improve the project's structural alignment with upstream and reduce slop:

- **`*Hyp` wrapper structures removed.** Project-specific bundling structures that gated every major theorem (`ConditionalJensen`, `MartingaleTransform`-as-structure, `FundamentalTheoremOfAssetPricing`, `IndependentExponentialMinimum`, `ContinuousLpMartingaleHyp`, `StoppedContinuousMartingaleHyp`) are gone. Each theorem now takes its hypotheses inline as Mathlib does. Benchmark JSON re-exports pass unpacked hypotheses through.
- **`DoobLp.lean` deleted** (`MathlibLp.lean` was a strict superset; the benchmark now invokes `MeasureTheory.maximal_ineq_Lp` directly). −946 lines.
- **File consolidation.** `StoppedContinuousMartingale.lean` deleted (one-line trivial wrap inlined in benchmark JSON); `HittingTimeOpen.lean` merged into `BrownianMartingale.lean`. Build went 8326 → 8312 jobs.
- **`WienerIntegral.lean` migrated** from a custom `BrownianIncrementSpec` structure (predating discovery of Degenne's repo) to Degenne's `IsPreBrownian` (NNReal time). All five increment helpers now derive in 1–3 lines from `HasLaw.{integral,variance}_eq` and `IsPreBrownian.{hasLaw_sub,hasIndepIncrements}`. −88 lines (218 → 130).
- **`LpContinuousMartingaleConvergence.lean` step 5 proved.** New `lp_continuous_martingale_tendsto_eLpNorm_at_naturals`: for `p > 1`, an `L^p`-bounded continuous martingale converges in `L^p` along natural times to its limit. Proof uses Doob's `L^p` maximal inequality (from `MathlibLp`) + monotone convergence to build a single `L^p`-dominator, then Degenne's `uniformIntegrable_of_dominated_singleton` + Mathlib's Vitali (`tendsto_Lp_finite_of_tendsto_ae`). The full continuous-time bridge (`t → ∞` along reals, not just along ℕ) remains as documented follow-on.
- **`BrownianMartingale.lean` deduplicated.** Extracted `condExp_func_increment` helper used by both `squareSubTime_isMartingale` and `waldExponential_isMartingale` — captures the "function of an increment has cond exp equal to its overall integral, by independence" pattern.
- **New `WienerIntegralL2.lean`** (522 lines, `lake build` clean, 0 sorries) — Itô isometry, fully proved end-to-end:
  - Indexes step intervals by `StepIndex T := { (s, t) : ℝ≥0 × ℝ≥0 // s ≤ t ∧ t ≤ T }`.
  - Defines `stepAssembly`, `wienerAssembly : (StepIndex T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 _` as formal-combination linear maps into the step-function and Wiener-integral sides respectively.
  - Proves the BM covariance identity `∫ ω, (B t ω − B s ω)(B v ω − B u ω) ∂μ = max 0 (min t v − max s u)` via Degenne's `IsPreBrownian.covariance_eval` + zero-mean + the bilinear expansion.
  - Proves the **assembly isometry** `‖wienerAssembly B T f‖ = ‖stepAssembly T f‖` for every `f : StepIndex T →₀ ℝ` (the L²-form of `wiener_finset_isometry`, generalized to arbitrary formal combinations of half-open intervals — no monotonicity needed) by matching both squared norms term-by-term through the inner product `⟨·, ·⟩_ℝ`, the BM covariance identity, and the L² inner-product-of-indicators formula.
  - Proves **density of step indicators** in `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))` via the orthogonal-complement route: for any `g ∈ range(stepAssembly)ᗮ`, the set-integral `∫ x in s, g x ∂(volume.restrict (Ioc 0 T)) = 0` for every measurable `s` (π-system induction on `borel_eq_generateFrom_Ioc_le` + `induction_on_inter`, with the base case for half-open intervals handled by truncating endpoints to `[0, T]` and applying the orthogonality hypothesis). Then `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero` gives `g =ᵐ 0`, hence the orthogonal complement is `⊥` and the range is dense.
  - Defines `wienerIntegralLp : Lp ℝ 2 (volume.restrict (Set.Ioc 0 T)) →L[ℝ] Lp ℝ 2 μ` via `LinearMap.extendOfNorm`.
  - Proves `wienerIntegralLp_norm` (`‖wienerIntegralLp f‖ = ‖f‖`) and `wienerIntegralLp_integral_sq` (`∫ ω, (I f ω)² ∂μ = ∫ s in (0, T], (f s)² ∂volume`) **unconditionally**.
  - Benchmark `sc-thm-6.2.5` (Itô Isometry, Chapter 6.2.5) is now `full`: the JSON wraps `wienerIntegralLp_integral_sq` as a direct named-lemma re-export. Axioms-clean.
- **New `BlackScholesCall.lean`** (~340 lines, `lake build` clean, 0 sorries) — Black-Scholes European call pricing formula, fully proved end-to-end:
  - Defines `Phi (x : ℝ) := (gaussianReal 0 1 (Set.Iic x)).toReal` (standard normal CDF) with `Phi_neg : Φ(-x) = 1 - Φ(x)` via `gaussianReal_map_neg` + `NoAtoms`.
  - Proves `exp_mul_gaussianPDFReal_zero_one`: the completing-the-square identity `exp(c·z) · pdf(0,1,z) = exp(c²/2) · pdf(c,1,z)`.
  - Proves `integral_exp_mul_gaussianPDFReal_Ioi`: `∫ z in Ioi a, exp(c·z) · pdf(0,1,z) dz = exp(c²/2) · Φ(c − a)` — the **shifted-tail Gaussian integral**, the core computational primitive for BS that Mathlib does not have.
  - Defines `BSCallHyp` (risk-neutral lognormal: `S_0>0, K>0, σ>0, T>0, HasLaw Z (gaussianReal 0 1) Q`), `bsd1`, `bsd2`, `bsTerminal`.
  - Proves `bsTerminal_gt_K_iff`: exercise-region identification `S_T(z) > K ↔ z > -d_2`.
  - Proves `max_payoff_eq_indicator`: `max(S_T(z) - K, 0) = (Ioi(-d_2)).indicator (· − K) z`.
  - Main theorem `bs_call_formula`: `∫ ω, e^{-rT} max(S_T(ω) - K, 0) ∂Q = S_0 · Φ(d_1) − K · e^{-rT} · Φ(d_2)`. Proof assembles: `integral_const_mul` → `HasLaw.integral_comp` (transfer ∫_Q to ∫_(gaussianReal 0 1)) → `integral_gaussianReal_eq_integral_smul` (convert to ∫ with pdf factor) → max-to-indicator → `integral_indicator` (restrict to Ioi(-d_2)) → `integral_sub` (split linear combination) → `integral_const_mul` (pull out constants) → apply `integral_exp_mul_gaussianPDFReal_Ioi` for the S_0 term and `gaussianReal_Ioi_toReal` for the K term → final algebraic identity `(r − σ²/2)T + σ²T/2 = rT`.
  - **Triple-checked**: `#print axioms bs_call_formula` reports only `[propext, Classical.choice, Quot.sound]`. Formula matches Hull (Eq. 15.20), Shreve (Theorem 4.5.1), Karatzas-Shreve (Ch 5.8), Saporito (Ch 9.4 at `t=0`). Numerical sanity for `S_0=K=100, r=5%, σ=20%, T=1y` gives `C = 10.4506` USD, matching Hull/Shreve published references to 5 decimal places.
  - Benchmark `gir-bs-call-formula` (Black-Scholes Call Pricing Formula, Chapter 9.4) is now `full`: the JSON wraps `bs_call_formula` as a direct named-theorem re-export. **No upstream Itô calculus / Girsanov machinery required**; pure Gaussian integration. This is the first `girsanov_finance.json` benchmark to reach `full`.

### Current audit (2026-05-17)

```text
theorems: 65
active Lean-only: 40
active Isabelle-only: 0
active Lean+Isabelle: 25
Lean code entries: 65
Isabelle code entries: 25
quarantined SymPy references: 55

full theorem statements: 22
library theorem wrappers: 24
reduced formal cores: 19
placeholders/stubs: 0
delivery-claim ready: 46
```

**Sorry-aware audit (2026-05-09)**: every Degenne-derived `library_wrapper`
is `#print axioms`-checked to ensure it does not transitively depend on
`sorryAx`. Confirmed clean (axioms = `[propext, Classical.choice, Quot.sound]`):
`IsGaussianProcess.isPreBrownian_of_covariance`, `IsPreBrownian.memHolder_mk`,
`HasIndepIncrements.indepFun_eval_sub`, `maximal_ineq_nonneg`. Rejected
candidate: `MeasureTheory.isStoppingTime_hittingAfter'` from
`Choquet/Debut.lean` — `#print axioms` revealed transitive dependence on
`sorryAx` through `Choquet/CompactSystem.lean` (which has 5 unsolved sorries).
`cm-prop-4.3.6` therefore stays `reduced_core`.

**Promotion update (2026-05-13)**: After restructuring the cm-thm-4.3.7
benchmark entry to NNReal-indexed filtration (so Degenne's `Approximable`
instance fires automatically), one additional library_wrapper promotion
lands:
- `cm-thm-4.3.7` — stopped continuous-time martingale. Wraps
  `MeasureTheory.Martingale.stoppedProcess_indicator` from Degenne
  `BrownianMotion/StochasticIntegral/LocalMartingale.lean`. Sorry-free.
  `#print axioms` confirmed clean:
  `[propext, Classical.choice, Quot.sound]`. Lives at
  `lean/HybridVerify/StoppedContinuousMartingale.lean`.

A second NNReal-restructure candidate `cm-prop-4.3.6` (hitting time of an
open set) was scoped but did NOT promote: the Degenne wrap
`isStoppingTime_hittingAfter'` has `#print axioms` output
`[propext, sorryAx, Classical.choice, Quot.sound]` — transitive `sorryAx`
through `Choquet/CompactSystem.lean` (5 unsolved sorries in Degenne master,
unchanged since the 2026-05-09 audit). Per the project audit policy, the
benchmark entry stays `reduced_core` until Degenne closes those upstream
sorries.

**Doob L^p complete (2026-05-13 session)**: `mart-thm-2.4.6` promoted
from `reduced_core` to `full`. End-to-end formal proof in
`lean/HybridVerify/DoobLp.lean`. `#print axioms` confirms clean:
`[propext, Classical.choice, Quot.sound]`. Coverage **41 → 42**
delivery-ready (18 full + 24 library), 23 reduced.

Components of the proof:

- `fubini_swap` (Stage 1, ✓): bivariate Tonelli swap with joint
  measurability of `{(t,ω) | t ≤ runMax M n ω}`, via
  `lintegral_lintegral_swap`.
- `holder_apply` + `holder_step` (Stage 2, ✓): `ENNReal.lintegral_mul_le_Lp_mul_Lq`
  with `HolderConjugate p (p/(p-1))` + rpow algebra `(x^(p-1))^q = x^p`,
  then combined with the layer-cake bound and Fubini swap into the
  master inequality `A ≤ ofReal(p/(p-1)) · B^(1/p) · A^((p-1)/p)` where
  `A = ∫⁻ Mstar^p`, `B = ∫⁻ M_n^p`.
- `eLpNorm_eq_lintegral_ofReal_pow` (Stage 4, ✓): converts
  `eLpNorm f (ofReal p) μ` to `(∫⁻ ofReal(f^p))^(1/p)` for non-negative f.
- Truncated chain (`inner_t_integral_truncated`, `fubini_swap_truncated`,
  `A_K_le_layer_integral`, `holder_step_truncated`): re-proves the
  chain for `min (runMax M n) K`, used in the `A = ∞, B < ∞` corner.
- Main theorem `doob_lp_maximal_inequality`: handles all four cases
  (`A = 0`, `A = B = ∞`, `0 < A < ∞`, `A = ∞ ∧ B < ∞`). The last case
  derives a contradiction via the truncated chain: for each K, the
  truncated A_K is finite and bounded by `(C · B^(1/p))^p` after rpow
  inversion + monotonicity. Then `A = ⨆ A_K` (monotone convergence
  via `lintegral_iSup` on the family `min(runMax M n, K+1)`) so
  `A ≤ (C · B^(1/p))^p < ∞`, contradicting `A = ∞`.

Benchmark entry `mart-thm-2.4.6` promoted to `full`. martingales.json
is now fully delivery-ready (3 full + 6 library, 0 reduced).

**Zero placeholders.** The 3 prior Degenne BM placeholders (`bm-thm-5.1.4`, `bm-thm-5.3.2`, `bm-prop-5.1.2`) were ported on 2026-05-09 — `bm-thm-5.1.4` to a real Mathlib `library_wrapper` (using upstream `HasIndepIncrements.indepFun_eval_sub`), and `bm-thm-5.3.2`, `bm-prop-5.1.2` to honest `reduced_core` structural encodings. See "BM port (2026-05-09)" below for details. Mathlib at pin `f23306121184` ships the relevant scaffolding (`HasIndepIncrements`, `IsGaussianProcess`, `IsKolmogorovProcess`, `multivariateGaussian`) upstream, eliminating the need for the Degenne Lake dependency that lean-interact's `TempRequireProject` could not reliably load.

**Validation note:** `mart-thm-2.6.7` had additional `Adapted → StronglyAdapted` renames applied at lines 124 (S_adapted) and 143 (hφ_pred) on top of the original Adapted/StronglyAdapted + Finset.stronglyMeasurable_fun_sum + Integrable.bdd_mul cascade fix. End-to-end docker validation of this final patch is pending the in-flight `verify` image rebuild (Dockerfile change to add `[dev]` extras invalidated downstream Isabelle/AFP layers). `mart-thm-2.2.9` was confirmed passing in the prior stretch sweep.

Guardrail tests:

```bash
python3 -m pytest tests/test_router.py
```

Result: 7 passed.

## v4.30.0-rc1 Validation Sweep (2026-05-08)

After the v4.18 → v4.30 toolchain migration, a fresh end-to-end sweep against current Mathlib master surfaced 10 regressions that the migration commits had not retested under the new toolchain. Outcomes by file (50 sweep theorems + 5 separately-fixed `distributions.json` theorems):

```text
markov_chains.json:           9 verified, 0 partial, 0 failed
poisson_processes.json:       5 verified, 0 partial, 0 failed
brownian_motion.json:         7 verified, 0 partial, 3 failed (Degenne wrappers)
martingales.json:             4 verified, 0 partial, 5 failed (Adapted/StronglyAdapted, IsStoppingTime/WithTop, Finset rename)
conditional_expectation.json: 5 verified, 0 partial, 0 failed (Lean side has 1 break, Isabelle rescues)
continuous_martingales.json:  2 verified, 0 partial, 2 failed (IsStoppingTime/WithTop)
girsanov_finance.json:        4 verified, 0 partial, 0 failed
stochastic_calculus.json:     11 verified, 0 partial, 0 failed
cross_validated.json:         3 verified, 0 partial, 0 failed (Lean side has 2 breaks, Isabelle rescues)
distributions.json:           3 fixes applied (HasLaw form for affine, cdf_expMeasure_eq for memoryless/min) — pending re-validation
```

Resolution applied 2026-05-08:

- **Fixed in place** (5 entries that compile cleanly under the v4.30 API):
  - `dist-thm-B.1.2-affine`: rewritten in the new `HasLaw X (gaussianReal μ v) P` form for `gaussianReal_const_mul` / `gaussianReal_add_const` (no longer the `Measure.map` form).
  - `dist-exp-memoryless`, `dist-exp-min`: rewritten using `cdf (expMeasure r)` + `cdf_expMeasure_eq` and the renamed `isProbabilityMeasure_expMeasure`. The textbook claims (memoryless property and min-of-independents survival function) are unchanged.
  - `mart-thm-2.4.3`, `mart-thm-2.4.6`: mechanical rename `Finset.nonempty_range_succ` → `Finset.nonempty_range_add_one`.
- **Mathlib pin added** (`hybrid_verify.toml` → `mathlib_rev = "f23306121184"`):
  - `python.config.LeanConfig` and `python.lean_backend.LeanBackend` now accept `mathlib_rev`. When set, lean-interact pulls Mathlib at exactly that commit instead of resolving the bare string `"mathlib"` to whatever master is at fetch time.
  - The pin matches Degenne's `brownian-motion @ 51807683` lake-manifest, which itself targets `leanprover/lean4:v4.30.0-rc1` (matching our `lean-toolchain`). Without this pin, Mathlib master had drifted past Degenne's tested version (master is now on rc2), breaking the transitive Brownian-motion build.
  - The lean-interact temp project log confirms `info: mathlib: checking out revision 'f23306121184...'` after the pin took effect.
- **Recovered** under the Mathlib pin (3 entries):
  - `mart-thm-2.3.6`: `{τ σ : Ω → ℕ}` → `{τ σ : Ω → ℕ∞}` to match the new `IsStoppingTime` / `stoppedValue` signatures that take `Ω → WithTop ι`.
  - `cm-thm-4.3.7`, `cm-prop-4.3.6`: replaced `IsStoppingTime 𝓕 τ` with `IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ))` in both the spec field and the public theorem conclusion. The textbook spec keeps `τ : Ω → ℝ` so semantics stay in real-valued form; only the IsStoppingTime field uses the WithTop coercion.
### Stretch attempts (2026-05-08, after the initial recovery commit)

After committing the conservative recovery (29 delivery-ready, 5 placeholders), two follow-on attempts were made to reclaim the remaining placeholders:

**Stretch A — Degenne transitive pins (failed).** Added subverso (`52b9dfbd2658`), checkdecls (`3d425859e73f`), and kolmogorov_extension4 (`e236e968c2b0`) to `[[hybrid-verify.lean.extra_requires]]`, matching Degenne's lake-manifest exactly. Lean-interact's clone log confirmed all four revisions (Mathlib + the three transitive deps + BrownianMotion) checked out at the manifest commits. Despite this, `BrownianMotion.Gaussian.BrownianMotion` still failed to compile — the wrapper file errored with `unknown namespace MeasureTheory` after a ~180s build attempt, identical symptom to the no-transitive-pin run. Conclusion: the issue is in how lean-interact's `TempRequireProject` synthesises a Lake project from a require list versus how Degenne's `lakefile.toml` is structured, not in transitive-version drift. Reverted: transitive pins removed from `hybrid_verify.toml`; the BrownianMotion entry stays for tree resolution, but the 3 BM wrappers stay `placeholder` until a tracked lake-manifest workflow (mounted Lake project) replaces TempRequireProject for these benchmarks.

**Stretch B — Adapted/StronglyAdapted cascade fixes (partial win).** For `mart-thm-2.2.9` and `mart-thm-2.6.7`, applied a sequence of fixes:
1. Field type rename `Adapted → StronglyAdapted` (struct field + lemma return type + downstream methods on `Martingale`).
2. `Finset.stronglyMeasurable_sum (m := 𝓕 n)` → `Finset.stronglyMeasurable_fun_sum (m := 𝓕 n) (M := ℝ)` to match the goal shape `fun ω => ∑ ...` and unblock `ContinuousAdd ?m.61` typeclass elaboration.
3. `Integrable.bdd_mul ⟨K, fun ω => ...⟩` → `Integrable.bdd_mul (c := K) ... · refine Filter.Eventually.of_forall fun ω => ...` for the new signature with explicit `{c : ℝ}` + AE bound.
4. For `mart-thm-2.6.7` only, two additional `Adapted → StronglyAdapted` renames (struct field `S_adapted` and function param `hφ_pred` in the FTAP machinery surrounding the embedded martingale-transform helper).

Result: `mart-thm-2.2.9` confirmed passing in the docker stretch sweep. `mart-thm-2.6.7` initially failed at the `S_adapted`/`hφ_pred` lines; the additional renames are applied but their end-to-end docker validation is pending the in-flight `verify` image rebuild (Dockerfile change to add `[dev]` extras invalidated downstream Isabelle/AFP layers — see "Docker layering" below).

The two Lean-side-only breaks in `conditional_expectation.json` and `cross_validated.json` (Isabelle rescues) are not blocking validation but are tracked in the per-theorem JSON.

### Docker layering

`docker/Dockerfile.verify` was reorganised so that pip / Python source layers live AFTER the heavy Isabelle (HOL-Probability) and AFP (Ergodic_Theory + Markov_Models + Stochastic_Matrices) heap builds. Future edits to `pyproject.toml` / `python/` invalidate only the ~1-2 min pip layer instead of the ~60 min Isabelle stack. The `verify` image now installs `[all,dev]`, so `pytest` runs inside the container; static lints are documented in `CLAUDE.md` to use `docker compose run --rm --entrypoint python3 verify -m pytest tests/test_router.py` rather than host pytest. `docker/docker-compose.yml` mounts `tests/` for this purpose.

## BM Port (2026-05-09)

The 3 Degenne BM placeholders were initially recovered by leveraging the
substantial Mathlib upstream that landed at pin `f23306121184`. After that
recovery, a follow-on round of Degenne library wraps promoted two of those
three from `reduced_core` to `library_wrapper`. The current state:

- **`bm-thm-5.1.4` (Brownian Markov property → `library_wrapper`).** Direct one-line proof: `hIncr.indepFun_eval_sub h0s hst h0`, where `HasIndepIncrements.indepFun_eval_sub` is upstream in `Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic` (Etienne Marion, Joris van Winden, 2025). Statement: under independent increments and `B 0 = 0` a.s., `B s` is independent of the future increment `B t − B s` for every `0 ≤ s ≤ t`. The textbook joint statement (independence of the entire post-`s` increment process from `F_s`) follows by iterating `HasIndepIncrements.nat`, left as future work. **Mathlib only — does not require Degenne.**
- **`bm-thm-5.3.2` (Hölder continuity → `library_wrapper`).** Wrap of Degenne `IsPreBrownian.memHolder_mk` from `BrownianMotion/Gaussian/BrownianMotion.lean`. The textbook claim "almost every BM path is locally `α`-Hölder for every `α ∈ (0, 1/2)`" follows from Degenne's stronger conclusion that the continuous modification `h.mk B` produced by Kolmogorov-Chentsov is everywhere locally `β`-Hölder for every `β < 1/2`; the modification a.s. equals `B` via `IsPreBrownian.mk_ae_eq`. **Requires Degenne.**
- **`bm-prop-5.1.2` (Gaussian-process characterization → `library_wrapper`).** Wrap of Degenne `IsGaussianProcess.isPreBrownian_of_covariance`. The benchmark hypothesis structure encodes a centered Gaussian process on `ℝ≥0` with covariance kernel `min(s, t)`; the conclusion `IsPreBrownian` packages the BM-defining properties (joint Gaussianity, mean zero, covariance `min s t`, independent increments, continuous modification). **Requires Degenne.**

All 10 BM theorems verify under the docker image (full file run 2026-05-09: 10 verified, 0 partial, 0 failed). The Degenne dependency is now load-bearing for `bm-thm-5.3.2` and `bm-prop-5.1.2`; do not remove the `BrownianMotion` `extra_requires` entry from `hybrid_verify.toml`.

### Degenne build via `TempRequireProject` (2026-05-09)

The prior `FORMALIZATION_STATUS.md` note that "BrownianMotion fails to build under `TempRequireProject` even with manifest pins" is **superseded** — that failure was a 180s timeout cutting off Lake mid-build, not a real build error. With all four transitive deps pinned in `hybrid_verify.toml` (Mathlib `f23306121184`, subverso `52b9dfbd2658`, checkdecls `3d425859e73f`, kolmogorov_extension4 `e236e968c2b0`) — matching Degenne's lake-manifest exactly — `TempRequireProject` produces hash `63469b53...` and Lake builds the BM-specific files (~12 min once Mathlib is cached, 3168 jobs). The compiled BrownianMotion oleans persist in the `lean_interact_cache` Docker volume across runs. Each docker session pays a one-time ~3-minute import cost when the first BM-importing benchmark theorem hits the lean-interact REPL; subsequent BM theorems in the same session are cached.

## Strong Markov AFP wrap (2026-05-09)

`mc-thm-1.2.11` (Strong Markov Property) promoted from `reduced_core` to `library_wrapper` via AFP `Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov`, inside the `discrete_Markov_process` locale. The wrapper file builds cleanly against the pre-built `Markov_Models` heap in the verifier image (`isabelle build -d . StrongMarkov_Check` finished in 1s — the heavy lifting is the `Markov_Models` heap, which the image already has). The Lean side keeps its complementary structural specification for finite-state chains; the AFP statement is the load-bearing formal proof.

## What Changed in the v4.30 Migration

The previous v4.18.0 toolchain pre-dated several Mathlib master modules that
are essential for promoting `reduced_core` entries to real wrappers. Bumping
to v4.30.0-rc2 unblocked:

- `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` —
  `multivariateGaussian`, `measurePreserving_eval_multivariateGaussian`.
- `Mathlib/Probability/Distributions/Gaussian/CharFun.lean`,
  `Mathlib/MeasureTheory/Measure/CharacteristicFunction/*` — characteristic
  functions and `iIndepFun.charFun_sum`.
- `Mathlib/Probability/Process/{Kolmogorov,HittingTime,FiniteDimensionalLaws}.lean`.
- `Mathlib/Probability/Independence/Process/HasIndepIncrements/*`.

In addition, the project now vendors `RemyDegenne/brownian-motion` (pinned
commit `51807683` on `master`) via Lake `require` in `lean/lakefile.lean`
and an `[[hybrid-verify.lean.extra_requires]]` entry in `hybrid_verify.toml`,
which lean-interact's `TempRequireProject` reads. That dependency provides
the concrete `brownian` Brownian-motion construction together with
`isGaussianProcess_brownian`, `hasIndepIncrements_brownian`, and
`memHolder_brownian`.

## Promotions Landed in This Migration

9 entries moved from `reduced_core` to `library_wrapper`:

| ID | Source | Library theorem |
|---|---|---|
| `mc-thm-1.4.25` | AFP `Stochastic_Matrices` | `stationary_distribution_unique` |
| `mc-thm-1.3.12` | AFP `Markov_Models.Classifying_Markov_Chain_States` | `recurrent_iff_G_infinite` |
| `mc-thm-1.4.40` | AFP `Markov_Models.Classifying_Markov_Chain_States` | `stationary_distribution_imp_p_limit` |
| `pp-thm-3.3.8` | HOL-Probability `Distributions` | `prob_space.erlang_distributed_sum` |
| `dist-thm-B.1.2-marginal` | Mathlib `Probability.Distributions.Gaussian.Multivariate` | `measurePreserving_eval_multivariateGaussian` |
| `bm-thm-5.1.4` | Mathlib `Probability.Independence.Process.HasIndepIncrements.Basic` | `HasIndepIncrements.indepFun_eval_sub` |
| `bm-prop-5.1.2` | Degenne `BrownianMotion.Gaussian.BrownianMotion` | `IsGaussianProcess.isPreBrownian_of_covariance` |
| `bm-thm-5.3.2` | Degenne `BrownianMotion.Gaussian.BrownianMotion` | `IsPreBrownian.memHolder_mk` (Kolmogorov-Chentsov) |
| `cm-thm-4.3.9` | Degenne `BrownianMotion.StochasticIntegral.DoobLp` | `maximal_ineq_nonneg` (continuous-time L¹ Doob max ineq, sharp form) |

End-to-end verification of these wrappers via the v4.30 Docker image is the
next step (the AFP-only entries depend on the same image's prebuilt
`Markov_Models` AFP heap; the Degenne entries depend on lean-interact's
first-time build of the Degenne dependency, which adds several minutes to
the first verification run but is then cached).

## Verification Evidence

After the 2026-05-08 v4.30.0-rc1 sweep + Mathlib pin + recovery pass, all 10 benchmark files verify cleanly under the Docker image. The numbers below collapse the per-backend results into per-file totals (any-backend success counts as verified, matching the verifier's `Summary:` line); placeholder demotions verify trivially:

```text
brownian_motion.json:         10 verified, 0 partial, 0 failed   (3 entries placeholder — Degenne build issue)
conditional_expectation.json:  5 verified, 0 partial, 0 failed   (Lean side has 1 break, Isabelle rescues)
continuous_martingales.json:   4 verified, 0 partial, 0 failed   (2 entries recovered via WithTop coercion)
cross_validated.json:          3 verified, 0 partial, 0 failed   (Lean side has 2 breaks, Isabelle rescues)
distributions.json:            5 verified, 0 partial, 0 failed   (3 entries fixed to v4.30 API)
girsanov_finance.json:         4 verified, 0 partial, 0 failed
markov_chains.json:            9 verified, 0 partial, 0 failed
martingales.json:              9 verified, 0 partial, 0 failed*  (3 mechanical/type fixes + 2 cascade-fix recoveries; *2.6.7 final patch awaits docker rebuild)
poisson_processes.json:        5 verified, 0 partial, 0 failed
stochastic_calculus.json:     11 verified, 0 partial, 0 failed
```

## What The 37 Delivery-Claim-Ready Entries Are

13 `full` (real derivation or structural definition):

- `cv-prob-space` — probability axioms via Mathlib `measure_univ` / `measure_empty`.
- `mc-def-1.1.1` — finite-state encoding of the Markov property.
- `mc-prop-1.2.3` — Chapman-Kolmogorov via `pow_add` + `Matrix.mul_apply`.
- `mc-prop-1.4.13` — detailed balance ⇒ stationarity by direct calc proof.
- `bm-def-5.1.1` — structural definition of standard Brownian motion.
- `cv-poisson-def` — structural definition of a homogeneous Poisson process.
- `pp-thm-3.3.5` — derives N_t marginal law from the Poisson-process spec via `simpa [hN.zero_at_zero]`.
- `dist-exp-memoryless` — derives memorylessness via Mathlib `cdf_expMeasure_eq` (rewritten for v4.30 from the prior `exponentialCDFReal_eq` form).
- `mart-thm-2.2.9` — **discrete martingale transform** is a martingale (Tier A.3); recovered for v4.30 via the Adapted/StronglyAdapted + Finset.stronglyMeasurable_fun_sum + Integrable.bdd_mul cascade fixes. Confirmed in stretch sweep.
- `ce-prop-2.1.11-jensen` — **conditional Jensen** (Tier A.1) with the subgradient supplied as an explicit hypothesis (Mathlib has no general subgradient API). Real derivation via `condExp_mono`, `condExp_sub`, `condExp_mul_of_stronglyMeasurable_left`, `condExp_of_stronglyMeasurable`.
- `mart-thm-2.6.7` — **FTAP, ⇒ direction** (Tier A.12); embeds the martingale-transform helper. Recovered for v4.30 with the same cascade fixes plus two additional `Adapted → StronglyAdapted` renames in the FTAP struct (`S_adapted`) and predicate (`hφ_pred`). End-to-end validation pending the in-flight `verify` rebuild.
- `mc-thm-1.1.2` — **Markov-chain path factorization** (Tier A.13); constructive `pathProb` def, theorem is `rfl`.
- `dist-exp-min` — **minimum of independent exponentials** (Tier A.5). Real derivation of the survival-function identity `μ{ω | t < min_i τ_i ω} = exp(-(∑rates) t)` for `t ≥ 0` from joint independence (`iIndepFun.meas_iInter`) + individual exponential laws via `cdf_expMeasure_eq` and `isProbabilityMeasure_expMeasure` (rewritten for v4.30).
- `bm-thm-5.1.5` — **Brownian motion is a martingale w.r.t. its filtration** (real derivation, 2026-05-09 LocalProject spike). Proof in `lean/HybridVerify/BrownianMartingale.lean` (Lake-built library); benchmark snippet imports the compiled lemma and re-exports it. Uses Mathlib `condExp_indep_eq` + `condExp_of_stronglyMeasurable` + `condExp_add` + Degenne `IsPreBrownian.integrable_eval` + `IsPreBrownian.hasLaw_sub`. The hypothesis structure `BrownianMartingaleHyp` is `IsPreBrownian + StronglyAdapted + (B_t − B_s ⊥ 𝓕 s)` — the standard textbook "BM w.r.t. filtration" condition. Three drafts of this proof OOM'd Lean's elaborator under `TempRequireProject` (the inline-snippet model); moving the proof out to a Lake file resolved that. Axioms-clean per `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

23 `library_wrapper` (direct Mathlib / Isabelle / Degenne library invocation):

Pre-existing (12, all Mathlib):

- `mart-thm-2.2.12` — `martingalePart_add_predictablePart`.
- `mart-thm-2.3.6` — `Submartingale.expected_stoppedValue_mono` (recovered for v4.30 with `{τ σ : Ω → ℕ∞}` to match the `IsStoppingTime`/WithTop signature).
- `mart-thm-2.4.3` — `maximal_ineq` (mechanical rename `nonempty_range_succ` → `nonempty_range_add_one` applied for v4.30).
- `mart-thm-2.5.1`, `mart-thm-2.5.3` — `Submartingale.ae_tendsto_limitProcess`.
- `mart-prop-2.5.5` — `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`.
- `dist-thm-B.1.2-affine` — `gaussianReal_const_mul` + `gaussianReal_add_const` (rewritten in the new `HasLaw X (gaussianReal μ v) P` form for v4.30).
- `ce-prop-2.1.5-linearity` — `condExp_add` + `condExp_smul`.
- `ce-prop-2.1.11-tower`, `cv-cond-exp-tower` — `condExp_condExp_of_le`.
- `ce-prop-2.1.11-pull-out` — `condExp_mul_of_stronglyMeasurable_left`.
- `ce-prop-2.1.11-independence` — `condExp_indep_eq`.

Added in the v4.30 migration (5):

- `mc-thm-1.4.25` — AFP `Stochastic_Matrices.stationary_distribution_unique`.
- `mc-thm-1.3.12` — AFP `Markov_Models.recurrent_iff_G_infinite`.
- `mc-thm-1.4.40` — AFP `Markov_Models.stationary_distribution_imp_p_limit`.
- `pp-thm-3.3.8` — HOL-Probability `prob_space.erlang_distributed_sum`.
- `dist-thm-B.1.2-marginal` — Mathlib `measurePreserving_eval_multivariateGaussian`.

Added in the BM-port + Strong-Markov sweep (2):

- `bm-thm-5.1.4` — Mathlib `HasIndepIncrements.indepFun_eval_sub` (upstream, no Degenne dep needed).
- `mc-thm-1.2.11` — AFP `Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov` inside `discrete_Markov_process` locale.

Added in the Degenne BM wraps round (2):

- `bm-prop-5.1.2` — Degenne `BrownianMotion.Gaussian.BrownianMotion.IsGaussianProcess.isPreBrownian_of_covariance` (Gaussian-process characterization).
- `bm-thm-5.3.2` — Degenne `BrownianMotion.Gaussian.BrownianMotion.IsPreBrownian.memHolder_mk` (Hölder regularity via Kolmogorov-Chentsov in `Continuity/KolmogorovChentsov.lean`).

Added in the Degenne Doob L¹ continuous-time wrap (1):

- `cm-thm-4.3.9` — Degenne `BrownianMotion.StochasticIntegral.DoobLp.maximal_ineq_nonneg` (continuous-time Doob L¹ maximal inequality, sharp form: `ε · P({sup_{s ≤ n} Y_s ≥ ε}) ≤ ∫_{set} Y_n dP` for non-negative right-continuous submartingale Y). The textbook form `λ · P(sup ≥ λ) ≤ E[M_t]` is the immediate corollary by bounding the right-side set integral against `E[M_t]` (using `M_t ≥ 0`). Sorry-free per `#print axioms`.

(Note: `cm-prop-4.3.6` is `reduced_core` — its spec field uses the new `IsStoppingTime 𝓕 (fun ω => (τA ω : WithTop ℝ))` form. The textbook continuous-time hitting-time-of-an-open-set theorem still has no direct Mathlib wrap; the `reduced_core` spec pins the statement. The 6 remaining BM `reduced_core` entries — `bm-thm-5.1.5`, `bm-thm-5.1.7`, `bm-cor-5.3.4`, `bm-rmk-5.1.6-square`, `bm-rmk-5.1.6-exp`, `bm-thm-5.3.5` — are not directly wrappable by Degenne: the martingale-property entries would need an `IsPreBrownian → Martingale` derivation (Degenne does not expose this directly), the reflection principle and law-of-iterated-logarithm are not in Degenne yet, and nowhere-differentiability is a research-grade analytical proof not yet formalized.)

## Delivery-Safe Claim

Use wording like:

> We built a reproducible Lean 4 / Isabelle verification artifact covering 65 stochastic-process benchmark statements. All active prover obligations type-check under Mathlib v4.30 / Lean v4.30.0-rc1 with Mathlib pinned to commit `f23306121184` (validated 2026-05-09). Under a strict faithfulness audit, 37 entries are full or direct library-backed theorem formalizations: 14 derive the conclusion from honest hypotheses (or are structural definitions), 23 directly invoke a named Mathlib / Isabelle-AFP / Degenne `brownian-motion` library theorem whose statement matches the benchmark. Every Degenne-derived wrapper has been `#print axioms`-audited to confirm axioms-clean status. Complex Lean derivations that would overrun the REPL elaborator's memory budget live as real files in a Lake-built library (`lean/HybridVerify/`) so `lake build` gives Lean the full incremental-compilation budget per file; benchmark snippets re-export by name. The remaining 28 entries are `reduced_core`: the active code is honest but is either a narrower algebraic/analytic check or a Lean specification structure that pins down the textbook STATEMENT (so any inhabitant satisfies it by construction) without DERIVING the conclusion. There are zero placeholders. The artifact identifies precisely where current Lean/Isabelle libraries support the course material, where a meaningful real proof is achievable in the near term, and where genuine new stochastic-process infrastructure is required (Itô-integral layer, BM reflection principle / nowhere-differentiability / law of iterated logarithm, Doob L^p, conditional Gaussian, continuous-time hitting times of open sets).

Avoid:

> We formally proved all theorems in the course.

That claim is not supported. The honest version is:

> We have faithful Lean STATEMENTS for all 65 textbook theorems, real derivations or library-backed proofs for 33 of them, and explicit `reduced_core` specifications for the remaining 32 documenting what a real proof would need to construct.

## Path Forward

See `QUANTFIN_ROADMAP.md` for the current roadmap.
