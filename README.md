# automated_proofs_quantfin

formal verification of stochastic-processes textbook theorems via a hybrid lean 4 + isabelle/hol + sympy orchestrator. tracks coverage of saporito's *stochastic processes* at the theorem level, with an honest faithfulness audit.

## status

| | count |
|---|---|
| total theorems | 104 |
| delivery-ready | **88** |
| ↳ full derivations | 64 |
| ↳ library wrappers | 24 |
| reduced cores (upstream-gated) | 16 |
| placeholders | 0 |

every theorem tagged `full` is `#print axioms`-clean: depends only on `[propext, Classical.choice, Quot.sound]` (the three standard mathlib axioms).

see `FORMALIZATION_STATUS.md` for the per-theorem audit and `QUANTFIN_ROADMAP.md` for what's next.

## what makes it different

most lean formalization projects pick one theorem and go deep, or contribute to mathlib directly. this is structured the other way: take a real textbook, audit theorem-by-theorem, distinguish "we proved it" from "we wrapped a library" from "we encoded the statement honestly but haven't derived it yet."

- **honest taxonomy.** every benchmark entry declares `full`, `library_wrapper`, `reduced_core`, or `placeholder`. delivery-claim counts only the first two. the audit policy lives in `FORMALIZATION_STATUS.md`.
- **multi-backend routing.** each theorem can dispatch to lean 4, isabelle/hol, sympy, or several in parallel. the python orchestrator picks based on `domain`. routing table is in `python/router.py`.
- **substantial original derivations**, not in mathlib or in degenne's brownian-motion library at current pins:
  - itô isometry on $L^2(0, T]$ from step-function isometry + π-system density + `LinearMap.extendOfNorm` (`lean/HybridVerify/WienerIntegralL2.lean`, 433 lines)
  - black-scholes call formula from the risk-neutral lognormal hypothesis (`BlackScholesCall.lean`, ~370 lines, no itô used)
  - black-scholes put formula via direct integration on the left tail + put-call parity corollary (`BlackScholesPut.lean`)
  - black-scholes digital options: cash-or-nothing and asset-or-nothing, with call decomposition (`BlackScholesDigital.lean`)
  - black-scholes greeks (call): delta, gamma, theta, **vega** ($\partial_\sigma V = S \phi(d_1) \sqrt{\tau}$), **rho** ($\partial_r V = K \tau e^{-r\tau} \Phi(d_2)$) in `BlackScholesPDE.lean` via magic-identity collapses
  - black-scholes greeks (put): δ, γ, θ, vega, ρ in `BlackScholesPutGreeks.lean` derived from put-call parity + Mathlib derivative rules
  - **higher-order BS greeks**: vanna ($\partial^2 V/\partial \sigma \partial S = -\phi(d_1) d_2 / \sigma$) and volga ($\partial^2 V/\partial \sigma^2 = \text{vega} \cdot d_1 d_2 / \sigma$) via the clean derivative $\partial_\sigma d_1 = -d_2/\sigma$ (`BlackScholesHigherGreeks.lean`)
  - black-scholes PDE forward direction via the magic identity $S \phi(d_1) = K e^{-r\tau} \phi(d_2)$ (`BlackScholesPDE.lean`)
  - **bachelier model** option pricing (arithmetic BM), with the truncated-mean primitive $\int_a^\infty z \phi(z) dz = \phi(a)$ via FTC; full first-order greeks δ, γ, vega, θ in `BachelierGreeks.lean`
  - **digital option deltas + asset-or-nothing gamma** (`BlackScholesDigitalGreeks.lean`)
  - **implied volatility uniqueness** via vega-positivity + `strictMonoOn_of_deriv_pos` (`ImpliedVolatility.lean`)
  - **black-scholes-merton with continuous dividends** $V_q = S e^{-qT} \Phi(d_1) - K e^{-rT} \Phi(d_2)$ and **garman-kohlhagen FX call** (`BlackScholesDividends.lean`); δ, γ, vega via $V_q = e^{-qT} \cdot \mathrm{bsV}(K, r-q, \sigma, S, T)$ identity (`BlackScholesDividendsGreeks.lean`)
  - **black-76 formula + greeks** for futures options (`BlackFutures.lean`, `BlackFuturesGreeks.lean`): formula derived as specialization of the call formula with zero drift; delta/gamma/vega follow directly
  - **american options in binomial tree** (`AmericanBinomial.lean`): Bellman/Snell-envelope definition of `americanPrice`, supermartingale property of the discounted price, intrinsic-value bound, and American ≥ European for the same payoff. No new infrastructure beyond `BinomialModel`.
  - **forward / futures pricing** under no-arbitrage ($F = S_0 e^{rT}$), from the gaussian MGF (`BlackScholesForward.lean`)
  - **single-period binomial replication theorem** + multi-period backward-induction framework (`BinomialModel.lean`)
  - **CRR risk-neutral probability limit** $p_n \to 1/2$ as $n \to \infty$, plus variance limit $4\sigma^2 T \cdot p_n(1-p_n) \to \sigma^2 T$ (`BinomialCRRConvergence.lean`). substantive analytic content of CRR-to-BS correspondence. full distributional convergence is upstream-gated on a triangular-array CLT (mathlib only ships the fixed-iid CLT).
  - feynman-kac formula identification: heat-kernel convolution equals $\mathbb{E}[g(x + B_t)]$ via `Measure.map` transfer + lebesgue translation invariance (`FeynmanKacHeatEquation.lean`)
  - quadratic variation of brownian motion in $L^1$ form (`BrownianQuadraticVariation.lean`)
  - standard normal CDF derivative $\Phi'(x) = \phi(x)$ via FTC on $\text{Iic}$ decomposition (`GaussianCDFDeriv.lean`). mathlib doesn't ship this; it doesn't ship `Real.erf` either.
- **continuous-time martingale L² convergence** (saporito 4.3.10), promoted to `full` via degenne's `Submartingale.rightCont_iSup_ofReal_ne_top` (`LpContinuousMartingaleConvergence.lean`, 703 lines)
- **doob L² for discrete-time martingales** (mart-thm-2.4.6), via mathlib's discrete `pow_norm_le_pow_norm_of_exponent_le`

reproducibility: lean and isabelle versions are pinned in the verify docker image. the lean toolchain is 4.30.0-rc1 with mathlib at commit `f23306121184` and degenne's brownian-motion at `16d15eb4`. isabelle 2025-2 with `HOL-Probability` prebuilt.

## quick start

pull the prebuilt image (3 min) instead of rebuilding (50 min):

```bash
docker compose -f docker/docker-compose.yml pull verify
```

run the verifier on a benchmark file:

```bash
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/stochastic_calculus.json -v --timeout 120
```

static coverage report:

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m python.coverage_report
```

regression tests (router routing, formal-only enforcement, faithfulness-status presence):

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/test_router.py -q
```

## layout

```
python/         orchestrator, backends, router, CLI
  models.py       Domain/Backend/ConfidenceLevel enums, TheoremStatement
  orchestrator.py central coordinator (sequential + parallel dispatch)
  router.py       DEFAULT_ROUTING + PARALLEL_DOMAINS
  cli.py          python -m python.cli benchmarks/file.json
lean/           lake project. mathlib + degenne brownian-motion pinned.
  HybridVerify/   substantial proofs (each > ~50 lines lives here)
benchmarks/     10 json files keyed by saporito chapters
tests/          pytest regression (router + coverage invariants)
docker/         pinned verify image
```

benchmark theorems with non-trivial proofs `import HybridVerify.<Module>` and re-export the named lemma in 5-25 lines. trivial library wrappers stay inline in the json. this split lets `lake build` give each big proof the full incremental-compilation budget while keeping the benchmark snippets short.

## what isn't done

the 16 remaining `reduced_core` theorems all hit one of:

- **itô integral / doleans-dade / girsanov machinery** (4 girsanov + ~8 stochastic-calculus theorems including itô's formula, time-dependent itô, lévy's martingale characterization, SDE existence)
- **continuous-time poisson processes** (3 theorems: interarrival exponential, superposition, thinning). mathlib has only the discrete `PoissonPMF`.
- **fine brownian path machinery** (3 BM pathology theorems: reflection principle, nowhere-differentiability, law of iterated logarithm)

these need upstream work in mathlib or degenne's brownian-motion to unlock. the project will revisit when that lands.

## related upstream work

derived as part of this project, candidates for upstream contribution:

- `gaussianReal_zero_one_Iic_neg`, `gaussianReal_zero_one_Ioi_toReal`, `exp_mul_gaussianPDFReal_zero_one`, `integral_exp_mul_gaussianPDFReal_zero_one_Ioi` (standard normal tail + completing-the-square): drafted as a mathlib PR.
- `IsFilteredPreBrownian.squareSubTime_isMartingale`, `IsFilteredPreBrownian.waldExponential_isMartingale` (the two textbook BM martingales): drafted as a contribution to remy degenne's `brownian-motion` library.

## license

apache 2.0, per the headers on each source file.
