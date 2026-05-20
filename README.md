# automated_proofs_quantfin

formal verification of stochastic-processes textbook theorems via a hybrid lean 4 + isabelle/hol + sympy orchestrator. tracks coverage of saporito's *stochastic processes* at the theorem level, with an honest faithfulness audit.

## status

| | count |
|---|---|
| total theorems | 168 |
| delivery-ready | **152** |
| ↳ full derivations | 128 |
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
  - **CRR drift quotient limit** $(2e^{rh^2} - e^{\sigma h} - e^{-\sigma h})/(h(e^{\sigma h} - e^{-\sigma h})) \to (r - \sigma^2/2)/\sigma$ (`BinomialDriftLimit.lean`). Uses the algebraic identity $e^{\sigma h} + e^{-\sigma h} - 2 = e^{-\sigma h}(e^{\sigma h} - 1)^2$ to reduce the cosh-like difference to existing exp-quotient limits. Plus the textbook n-form $n \cdot (2 p_n - 1) \cdot \sigma \sqrt{T/n} \to (r - \sigma^2/2) T$, closing the analytic content of CRR drift matching.
  - **complete digital options Greek matrix**: cash-or-nothing and asset-or-nothing $\delta, \gamma$, vega, $\rho, \theta$ in `BlackScholesDigitalGreeks.lean`. Vega uses the clean derivative $\partial_\sigma d_1 = -d_2/\sigma$ via `bsd2_eq` + `field_simp + ring`.
  - **Black-76 Greek matrix**: $\delta, \gamma$, vega, $\rho, \theta$ in `BlackFuturesGreeks.lean`. $\rho = -T \cdot V_B$ is clean because the inner $\mathrm{bsV}$ is $r$-independent at zero drift.
  - **fixed income basics** (`FixedIncome.lean`): zero-coupon bond pricing under deterministic short rate $B(t, T) = e^{-r(T - t)}$, yield-to-maturity identity, Macaulay duration $=T-t$, convexity $= (T-t)^2$.
  - **Markowitz two-asset portfolio theory** (`Markowitz.lean`): completing-the-square factorization $\mathrm{Var}(w) = D \cdot (w - w^*)^2 + V_{\min}$ with $D = \sigma_1^2 - 2 \rho \sigma_1 \sigma_2 + \sigma_2^2$, giving the minimum-variance weight $w^*$, minimum variance $V_{\min} = \sigma_1^2 \sigma_2^2 (1 - \rho^2) / D$, lower-bound property, and perfect-hedge corollary $V_{\min} = 0$ at $\rho = -1$.
  - **CAPM** (`CAPM.lean`): $\beta = \mathrm{Cov}(R, R_M)/\mathrm{Var}(R_M)$, $\beta_M = 1$, $\beta_{\text{risk-free}} = 0$, and portfolio beta linearity $\beta_p = \sum w_i \beta_i$ (bilinearity of covariance over a finset-indexed portfolio).
  - **Gaussian risk measures** (`GaussianRiskMeasures.lean`): closed-form Value-at-Risk and Conditional Value-at-Risk for $L \sim \mathcal{N}(\mu, \sigma^2)$ — $\mathrm{VaR}_\alpha = \mu + \sigma z$, $\mathrm{CVaR}_\alpha = \mu + \sigma \phi(z)/(1-\alpha)$ — with affine invariance, standard-normal specializations, the $\mathrm{CVaR} - \mathrm{VaR} = \sigma(\phi(z)/(1-\alpha) - z)$ identity, and the $\sqrt{T}$ time-aggregation rule.
  - **bond portfolio immunization** (`BondImmunization.lean`): Finset-indexed bond portfolio value $P(r) = \sum_i w_i e^{-r(T_i - t)}$, duration-times-value $D_P \cdot P = \sum_i w_i (T_i - t) e^{-r(T_i - t)}$, first-order rate sensitivity $\partial P/\partial r = -D_P \cdot P$, and Redington-style first-order immunization condition (matching $D_A \cdot A = D_L \cdot L$ ⇒ $\partial(A-L)/\partial r = 0$).
  - **N-asset Markowitz** (`MarkowitzNAsset.lean`): portfolio variance as Finset double sum $\sum_{i,j} w_i w_j \sigma_{ij}$, quadratic scaling, diagonal collapse ($\mathrm{Var} = \sum w_i^2 \sigma_{ii}$ under zero cross-covariances), iid diversification ($c^2 n \sigma^2$), positive-semidefinite non-negativity, and explicit two-asset compatibility with `Markowitz.lean`.
  - **performance ratios** (`PerformanceRatios.lean`): Sharpe ratio scale invariance and $\sqrt{T}$ time-aggregation scaling, Kelly criterion first-order optimality $g'(f^*) = 0$ for the expected log-growth $p \log(1 + fb) + q \log(1 - f)$.
  - **coherent risk-measure axioms** (`RiskMeasureAxioms.lean`): gaussian VaR/CVaR satisfy the Artzner-Delbaen-Eber-Heath axioms (translation invariance, positive homogeneity, monotonicity, subadditivity), with the substantive joint-stdev triangle inequality $\sqrt{\sigma_1^2 + 2\rho \sigma_1 \sigma_2 + \sigma_2^2} \le \sigma_1 + \sigma_2$ for $|\rho| \le 1$.
  - **annuity + YTM + forward/spot consistency** (`CouponBondsAndAnnuities.lean`): annuity geometric-series closed form $A_n = c e^{-r\Delta t} (1 - x^n)/(1 - x)$ with $x = e^{-r\Delta t}$, instantaneous forward rate $f(t,T) = r$ under flat curve, coupon-bond strict monotonicity in yield (parameter form of YTM uniqueness).
  - **static option bounds + box-spread identity** (`StaticOptionBounds.lean`): $\Phi \le 1$, BS call price $\le S$, BS put price $\le K e^{-r\tau}$, and the put-call-parity box-spread identity $(bsV(K_1) - bsP(K_1)) - (bsV(K_2) - bsP(K_2)) = (K_2 - K_1) e^{-r\tau}$.
  - **two-fund separation (algebraic)** (`TwoFundSeparation.lean`): Capital Market Line equation $\mu = r_f + \sigma \cdot \mathrm{Sharpe}_t$, Sharpe invariance along the CML, and unique decomposition of any CML portfolio as $\alpha$ tangent + $(1-\alpha)$ risk-free with $\alpha = \sigma_p / \sigma_t$.
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
