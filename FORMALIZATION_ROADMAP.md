# Formalization Roadmap

Goal: move from "active prover obligations type-check on faithful textbook statements" toward "real Lean derivations of textbook theorems."

The current audit is (post v4.30 migration + BM port + Strong Markov AFP wrap + Degenne BM wraps + Degenne Doob L¹ continuous-time wrap + LocalProject spike with bm-thm-5.1.5 → full, 2026-05-09):

```text
65 benchmark statements
37 delivery-claim ready entries: 14 full + 23 library_wrapper
28 reduced formal cores
0 placeholders
0 active SymPy entries
```

**Infrastructure: LocalProject migration (2026-05-09)**. The Lean backend
now exclusively uses `lean-interact.LocalProject` pointing at the `lean/`
Lake project — the `TempRequireProject` branch was removed from
`python/lean_backend.py`, and the now-dead `mathlib`/`mathlib_rev`/
`extra_requires`/`version` fields were stripped from `python/config.py` and
`hybrid_verify.toml`. `lakefile.lean` + `lake-manifest.json` are
authoritative. Four non-trivial proofs that previously lived as inline JSON
strings have been migrated to real Lean files under `lean/HybridVerify/`:
`MartingaleTransform.lean` (Theorem 2.2.9), `FTAP.lean` (Theorem 2.6.7,
imports `MartingaleTransform` instead of duplicating it), `CondExpJensen.lean`
(Proposition 2.1.11(9)), `ExpMin.lean` (Appendix B.2 minimum-of-exponentials).
Each benchmark JSON now imports the module and re-exports the named lemma
in 15–25 lines. Authoring on host (VS Code + Lean LSP) is the intended
path; trivial library wrappers can still stay inline. `Dockerfile.verify`
also gained a `lake exe cache get && lake build` prebuild step so the next
image rebuild bakes Mathlib oleans into the image (saves ~30 min on the
first verify call).

**Sorry-aware audit (2026-05-09)**: every Degenne-derived `library_wrapper`
is checked via `#print axioms` to confirm it does NOT transitively depend on
`sorryAx`. Several Degenne files do contain `sorry` (notably
`Choquet/CompactSystem.lean` with 5 sorries and `StochasticIntegral/{LocalMartingale,
SquareIntegrable, OptionalSampling, Komlos, UniformIntegrable, QuadraticVariation}.lean`),
which transitively pollutes some attractive-looking lemmas — e.g.
`MeasureTheory.isStoppingTime_hittingAfter'` from `Choquet/Debut.lean` was
investigated as a wrap candidate for `cm-prop-4.3.6` (hitting time of an open
set is a stopping time) but was rejected after `#print axioms` showed
`sorryAx` in its dependency closure. The wraps that ARE landed
(`isPreBrownian_of_covariance`, `memHolder_mk`, `HasIndepIncrements.indepFun_eval_sub`,
`maximal_ineq_nonneg`) all show the standard clean axiom set
`[propext, Classical.choice, Quot.sound]`.

Recent promotions (Tier A): `mart-thm-2.2.9` (martingale transform — A.3),
`ce-prop-2.1.11-jensen` (conditional Jensen with explicit subgradient — A.1),
`mart-thm-2.6.7` (FTAP ⇒ direction, leveraging the embedded martingale-transform
helper — A.12), `mc-thm-1.1.2` (Markov-chain path factorization, constructive
def — A.13), `dist-exp-min` (minimum of independent exponentials, survival-
function level — A.5), and `mc-thm-1.4.32` (Birkhoff/ergodic for Markov chains
via AFP `Ergodic_Theory.Ergodicity.birkhoff_theorem_AE` — A.9, library_wrapper).

**BM-martingale extensions (2026-05-09 evening)**: `bm-rmk-5.1.6-square` and
`bm-rmk-5.1.6-exp` both promoted from `reduced_core` to `full` via real Lean
derivations in `lean/HybridVerify/BrownianMartingale.lean`. The square version
uses `condExp_indep_eq` + Mathlib's `variance_id_gaussianReal` for the second-
moment computation; the exponential (Wald) version uses `mgf_id_gaussianReal`
for the MGF computation + `condExp_mul_of_stronglyMeasurable_left` to pull out
the 𝓕_s-measurable factor. Both proofs were authored using the persistent
`lean-repl` daemon (commit 9d19573), which dropped iteration to ~5 sec/check
from ~5-15 min/check. Net audit: 28 → 26 reduced cores; 14 → 16 full;
37 → 39 delivery-claim ready.

**A.7 bivariate Gaussian conditional — sketch only**: a structured proof
attempt for `dist-thm-B.1.3-conditional` (deriving `E[X|σ(Y)] = μ_X +
(ρσ_X/σ_Y)(Y − μ_Y)` from joint-Gaussianity hypotheses) is preserved at
`docs/superpowers/sketches/bivariate_gaussian_v1.lean`. The structure follows
the textbook approach (orthogonal regression + zero-covariance ⇒ independence
for jointly Gaussian, via Mathlib's `HasGaussianLaw.indepFun_of_covariance_eq_zero`).
Four open Lean errors remain at the integral-arithmetic / `condExp_add` /
`show`-tactic-pattern levels — each tractable individually, but the proof
together is ~250 lines and the API signatures need careful work that the
single session could not absorb. Benchmark `dist-thm-B.1.3-conditional`
remains `reduced_core`.

**Degenne BM wraps (2026-05-09)**: confirmed Degenne `RemyDegenne/brownian-motion`
(commit 51807683) builds cleanly under `lean-interact`'s existing `TempRequireProject`
once all four transitive deps are pinned in `hybrid_verify.toml` (Mathlib
`f23306121184`, subverso, checkdecls, kolmogorov_extension4). The prior
"unknown namespace MeasureTheory" failure was a 180s timeout cutoff, not a
genuine build error — the actual build is ~12 min once Mathlib is cached, and
the resulting BrownianMotion oleans persist in the `lean_interact_cache`
Docker volume. Two BM `reduced_core` entries promoted to `library_wrapper`
on this path:
- **`bm-prop-5.1.2`** (Gaussian-process characterization) → wrap of
  `IsGaussianProcess.isPreBrownian_of_covariance` from
  `BrownianMotion/Gaussian/BrownianMotion.lean`. The conclusion `IsPreBrownian`
  packages the BM-defining properties (joint Gaussianity, mean zero, covariance
  `min s t`, independent increments, continuous modification).
- **`bm-thm-5.3.2`** (Hölder continuity) → wrap of
  `IsPreBrownian.memHolder_mk` (i.e. the Kolmogorov-Chentsov continuity
  theorem from `BrownianMotion/Continuity/KolmogorovChentsov.lean`) for every
  Hölder exponent `β ∈ (0, 1/2)`.

**BM port (2026-05-09, earlier in session)**: the 3 Degenne BM placeholders
were first recovered by leveraging upstream Mathlib at pin
`f23306121184`. `bm-thm-5.1.4` was promoted to `library_wrapper` via Mathlib's
`HasIndepIncrements.indepFun_eval_sub` (still applies). `bm-thm-5.3.2` and
`bm-prop-5.1.2` were temporarily `reduced_core` and have now been promoted to
`library_wrapper` via Degenne (see "Degenne BM wraps" above). See
`FORMALIZATION_STATUS.md` § "BM port (2026-05-09)".

**Strong Markov AFP wrap (2026-05-09)**: `mc-thm-1.2.11` promoted from
`reduced_core` to `library_wrapper` via AFP
`Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov` inside
the `discrete_Markov_process` locale. Wrapper builds in 1s against the
pre-built `Markov_Models` heap.

**Infrastructure: AFP install** (2026-05-07/08). `docker/Dockerfile.verify` now
pre-builds AFP `Ergodic_Theory`, `Markov_Models`, and `Stochastic_Matrices`
sessions on top of `HOL-Probability` (image delta ~2.0–2.5 GB,
~30–60 min build). `python/isabelle_backend.py` selects the session per
theorem (auto-detects AFP namespace imports, or set
`metadata.isabelle_session` explicitly). Recognized AFP namespaces:
`Ergodic_Theory`, `Markov_Models`, `Stochastic_Matrices`, `Perron_Frobenius`,
`Jordan_Normal_Form`, `Coinductive`, `Gauss_Jordan_Elim_Fun`. `Stochastic_Matrices`
is wired but **not yet exercised** — the next Docker rebuild lands it. See
`docker/AFP_NOTES.md` for authoring patterns and the full list of probed AFP
lemmas (including `stationary_distribution_unique`).

**Tier A status reconciliation (2026-05-09).** Several Tier A entries that
were tagged "blocked" in the original spec have, in fact, been promoted
to `library_wrapper` since (during the v4.30 migration and AFP install).
The current Tier A board:

- **A.1** `ce-prop-2.1.11-jensen` — DONE (`full`, with explicit-subgradient hyp).
- **A.2** `mart-thm-2.4.6` (Doob L^p) — **library-blocked 2026-05-08** (exhaustive web/AFP/Mathlib audit found NO formal version in Mathlib master, in-flight Mathlib PRs, AFP `Doob_Convergence`, AFP `Martingales`, AFP `DiscretePricing`, HOL-Probability core, or `RemyDegenne/brownian-motion`). The Mathlib `brownian-motion` blueprint outlines `lem:doob_Lp_countable` with the same proof strategy we used (layer cake → L^1 maximal → Fubini → Hölder) but has not formalized it. We have 10 helper lemmas verified against Mathlib v4.18.0 in `docs/superpowers/sketches/doob_lp_v1.lean`; the Fubini swap remains the dominant cost. Status: stays `reduced_core` until Mathlib lands `MeasureTheory.maximal_ineq_Lp` (or Degenne's `lem:doob_Lp_countable` is formalized upstream).
- **A.3** `mart-thm-2.2.9` — DONE (`full`).
- **A.4** `pp-thm-3.3.8` (sum of exponentials → Erlang/Gamma) — **DONE** (`library_wrapper`). Wrapped via Isabelle `HOL-Probability.Distributions.prob_space.erlang_distributed_sum` specialized to k_i = 0; the textbook density λⁿ tⁿ⁻¹ e^{−λt}/(n−1)! is exactly HOL-Probability's `erlang_density (n−1) λ`. The original spec's "no measure convolution / MGF uniqueness" obstruction was sidestepped by going through HOL-Probability instead of Mathlib.
- **A.5** `dist-exp-min` — DONE (`full`, survival-function form).
- **A.6** `dist-thm-B.1.2-marginal` (MV Gaussian marginal) — **DONE** (`library_wrapper`) at v4.30 via Mathlib `Probability.Distributions.Gaussian.Multivariate.measurePreserving_eval_multivariateGaussian`. Mathlib added `multivariateGaussian` between v4.18 and v4.30.
- **A.7** `dist-thm-B.1.3-conditional` (bivariate Gaussian conditional) — **still blocked** (`reduced_core`); even with `multivariateGaussian` in Mathlib, the conditional decomposition `E[X|σ(Y)] = μ_X + (ρσ_X/σ_Y)(Y − μ_Y)` is not packaged. Estimated 1–2 weeks once a Lean proof of this scalar identity from `multivariateGaussian` is written.
- **A.8** `mc-thm-1.4.40` (finite-state convergence to stationary) — **DONE** (`library_wrapper`) via AFP `Markov_Models.Classifying_Markov_Chain_States.stationary_distribution_imp_p_limit` (a slightly different AFP entry point than the spec's anticipated `Stochastic_Matrices` route, which lacked a `lim Pⁿ` theorem).
- **A.9** `mc-thm-1.4.32` — DONE (`library_wrapper`, AFP `Ergodic_Theory.birkhoff_theorem_AE`).
- **A.10** `mc-thm-1.4.25` (stationary uniqueness) — **DONE** (`library_wrapper`) via AFP `Stochastic_Matrices.Stochastic_Matrix_Perron_Frobenius.stationary_distribution_unique`.
- **A.11** `mc-thm-1.3.12` (recurrence criterion) — **DONE** (`library_wrapper`) via AFP `Markov_Models.Classifying_Markov_Chain_States.recurrent_iff_G_infinite`. The textbook ∑Pⁿ(i,i) = ∞ form maps directly onto AFP's `G x x = ∞` (where `G x x = enn_real (∑n. p x x n)`); the gf bridge anticipated in the spec was not needed because AFP packages this equivalence directly.
- **A.12** `mart-thm-2.6.7` — DONE (`full`, ⇒ direction with bounded-strategy hyp).
- **A.13** `mc-thm-1.1.2` — DONE (`full`, constructive).

Net Tier A position: **11 of 13 Tier A entries are at `full` or `library_wrapper`.** Only A.2 (Doob L^p) and A.7 (bivariate Gaussian conditional) remain `reduced_core`, both genuinely upstream-blocked at the current Mathlib pin.

**Full Docker verification 2026-05-08** (post router/backend edits): all
65 benchmark theorems verify, 0 failed, 0 partial. `pytest tests/test_router.py`
green (7/7).

`reduced_core` here means one of two things:

1. **Algebraic / analytic core check.** A narrow real-analytic identity that backs the textbook theorem in spirit (e.g., the Wald exponential constant identity `exp(α²t/2) · exp(-α²t/2) = 1`).
2. **Lean specification structure.** A Lean structure that encodes the textbook hypotheses AND the textbook conclusion as fields. Any inhabitant satisfies the textbook claim by construction, but the structure does NOT derive the conclusion from foundational primitives. The "theorem" reads off the conclusion via `:= h.conclusion_field`.

Both are honest as `reduced_core` and useful as documentation. Neither is `full` — that requires a real derivation.

The next stage of work is to attack the achievable real proofs (Tier A below) and contribute the results upstream where possible.

## Three Tiers

The detailed roadmap is in `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`.
The Tier B/C honest gating audit (what Mathlib infrastructure is missing for
each of those entries) is in `docs/superpowers/specs/2026-05-07-tier-bc-gating-audit.md`.

Summary:

### Tier A — real proofs achievable now, weeks per theorem

These don't need new infrastructure beyond Mathlib `v4.18.0`.

- Conditional Jensen's inequality (Mathlib has it as a TODO).
- Doob's L^p maximal inequality (also a Mathlib TODO).
- Discrete martingale transform.
- Sum of n iid Exp(λ) → Gamma(n, λ).
- Min of independent exponentials → Exp(∑ λ).
- Multivariate Gaussian definition with marginal/affine/conditional theorems.
- Finite-state Markov chain convergence to stationary (Perron–Frobenius), recurrence criterion, ergodic theorem.
- FTAP for finite-state finite-period markets.
- Path-factorization theorem for general (countable-state) Markov chains.

Real Mathlib contributions in scope: conditional Jensen, Doob L^p, multivariate Gaussian.

### Tier B — needs Brownian motion construction first, months of foundational work

These all reduce to "first build a Mathlib-grade Brownian motion."

- BM martingale property, B²−t martingale, Wald exponential.
- Reflection principle, Markov / strong Markov property.
- Hölder regularity (needs Kolmogorov continuity theorem).
- Nowhere differentiability.
- Gaussian-process characterization of BM.
- Quadratic variation of BM.
- Law of the iterated logarithm.

The Mathlib community has been working toward Brownian-motion construction for years. Following / contributing to that work is the realistic path.

### Tier C — needs the stochastic-integral layer (research-grade)

Requires Tier B plus Itô-integral construction (a thesis-level effort each).

- Itô isometry, Itô's formula (1D / time-dependent / 2D).
- Itô process quadratic variation.
- Lévy's martingale characterization of BM.
- Novikov's condition.
- Girsanov's theorem (any version).
- Feynman–Kac for the heat equation.
- SDE existence and uniqueness.
- Martingale representation theorem.
- Black-Scholes PDE / call price formula.

These are not achievable in the near term as Lean derivations. Keep the specifications as documentation of what a future Mathlib-grade construction needs to satisfy.

## Working Rules

- Do not mark `library_wrapper` unless active code invokes or directly wraps a named library theorem close to the benchmark statement.
- Do not mark `full` unless the formal proof is a real derivation. Spec-with-axiomatized-conclusion is `reduced_core`.
- Keep old CAS snippets only under `metadata.cas_reference.sympy`.
- After each promotion attempt, run `python3 -m pytest tests/test_router.py` and `python3 -m python.coverage_report` and Docker-verify the affected file.

## Guardrails

```bash
python3 -m pytest tests/test_router.py
python3 -m python.coverage_report
```

```bash
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json --config hybrid_verify.toml --timeout 240
```

Before any public claim, check `python3 -m python.coverage_report` and use `delivery-claim ready` (i.e., `full + library_wrapper`), not the total theorem count.
