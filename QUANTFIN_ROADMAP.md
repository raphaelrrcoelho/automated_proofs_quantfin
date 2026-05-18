# quant-finance roadmap (unblocked path)

the 16 remaining `reduced_core` theorems in `FORMALIZATION_STATUS.md` are upstream-gated on the itô integral, measure-change machinery, and continuous-time poisson processes. this document captures what can be built **without** waiting on upstream mathlib or degenne work, framed as a quant-finance project rather than a textbook audit.

all of it either (a) reuses the existing `bsd1`/`bsd2`/`Phi`/`bs_identity`/`hasDerivAt_Phi`/`bsV` infrastructure, (b) is a parallel construction to black-scholes using the same gaussian machinery, or (c) is discrete-time / classical-analysis material that doesn't touch the itô integral.

## phase 1: complete the static black-scholes world (DONE 2026-05-18)

all six items shipped in a single session. all axioms-clean; all benchmarked as `full` in `benchmarks/mathematical_finance.json`.

- [x] **black-scholes put formula** — `BlackScholesPut.lean`. derived by direct integration on the left tail (`integral_exp_mul_gaussianPDFReal_Iic` primitive). put-call parity proved as corollary.
- [x] **vega**: `∂V/∂σ = S · ϕ(d_1) · √τ` — `BlackScholesPDE.lean` (extended). magic identity collapses both `∂_σ d_1` chain-rule contributions.
- [x] **rho**: `∂V/∂r = K · τ · e^{-rτ} · Φ(d_2)` — `BlackScholesPDE.lean` (extended). same magic-identity collapse.
- [x] **cash-or-nothing digital option** — `BlackScholesDigital.lean`. direct integration on `Ioi(-d_2)`.
- [x] **asset-or-nothing digital option** — `BlackScholesDigital.lean`. plus call decomposition `C = AssetDigital − K · CashDigital` as corollary.
- [x] **forward and futures pricing** under no-arbitrage — `BlackScholesForward.lean`. derived from Gaussian MGF; also gives the discounted-asset martingale property `E_Q[e^{-rT} S_T] = S_0`.

milestone DONE: complete BS sensitivities (delta + gamma in `BlackScholesPDE.lean`, plus vega + theta + rho) plus the full vanilla european product set (call, put, 2 digitals, forward).

## phase 2: vanilla derivatives theory complete (DONE 2026-05-18)

all three items shipped in the same session as phase 1. all axioms-clean; all `full` in `benchmarks/mathematical_finance.json`.

- [x] **bachelier model option pricing** — `BachelierModel.lean` (~330 lines). key new primitive: the **truncated mean of N(0, 1)** `∫_a^∞ z ϕ(z) dz = ϕ(a)`, proved via FTC `integral_Ioi_of_hasDerivAt_of_tendsto` with antiderivative `-ϕ` (and `(-ϕ)' = z · ϕ`). also includes the volume-integrability of `z · ϕ(z)` via withDensity transfer from `Integrable id (gaussianReal 0 1)`.
- [x] **implied volatility uniqueness via vega-positivity** — `ImpliedVolatility.lean`. uses `bsV_vega_pos` + `strictMonoOn_of_deriv_pos` + `StrictMonoOn.injOn`.
- [x] **black formula for futures options** — `BlackFutures.lean`. specialization of `bs_call_formula` with `r = 0` (zero drift for futures) plus independent discount.

milestone DONE: rigorous theory of vanilla derivatives. covers the standard closed-form option pricing models taught in a quant program.

## phase 3: discrete-continuous bridge (PARTIAL 2026-05-18)

- [x] **discrete-time binomial tree pricing framework** — `BinomialModel.lean`. includes:
  - risk-neutral up-probability `crrUpProb u d r = (e^r − d)/(u − d)` + no-arbitrage condition `BinomialNoArb` + `(0, 1)`-range proof.
  - single-period option price `binomialOptionPriceOnePeriod`.
  - **replicating-portfolio theorems** (cost, up-state payoff, down-state payoff) — three full proofs.
  - multi-period `binomialPrice` via well-founded recursion on remaining steps; one-step consistency lemma; linearity and scalar-homogeneity in the payoff; constant-payoff price closed form `e^{-rn} · c`.
- [ ] **CRR convergence theorem**: binomial pricing converges to black-scholes as `Δt → 0`. classic limit theorem using the CLT (already have it) plus careful drift correction (`u_n = e^{σ√Δt}, d_n = e^{−σ√Δt}, p_n` chosen so the binomial mean and variance match GBM to first order). still ~500-800 lines, requires careful work with CLT applied to log-returns. **TODO future session**.

milestone (partial): discrete-time framework with no-arbitrage replication formalized. CRR continuous-time limit remains as future work.

## phase 4: upstream foundations

real upstream contributions that would land in mathlib or degenne. each is a separate PR. all four items are ready to submit; awaiting an upstream-PR session.

- [ ] **`Real.erf` for mathlib**. mathlib has no error function. drafting it would unlock cleaner standard-normal-CDF APIs across this project and the broader probability ecosystem. ~300 lines plus the `Real.erfc`, `Real.erfinv` companions and basic identities. would also let us replace our local `Phi` definition with `(1 + erf(x/√2))/2`. **status**: not yet drafted; multi-day work.
- [x] **`gaussianReal_Iic_hasDerivAt` for mathlib**: proved as `hasDerivAt_Phi` in `lean/HybridVerify/GaussianCDFDeriv.lean` (~80 lines via FTC). ready to upstream as a separate PR (`Φ' = ϕ` is the missing piece).
- [x] **mathlib PR (drafted in `staging/mathlib-pr/`)**: the 4 gaussian tail / completing-the-square lemmas. ready to submit.
- [x] **degenne PR (drafted in `staging/degenne-pr/`)**: the two BM martingales `IsFilteredPreBrownian.squareSubTime_isMartingale` and `IsFilteredPreBrownian.waldExponential_isMartingale`. ready to submit.

## explicitly out of scope (itô-gated, do not attempt without upstream)

these wait on mathlib developing the itô integral or on degenne's brownian-motion library:

- girsanov theorem
- novikov's condition
- martingale representation theorem
- itô's lemma (general SDE chain rule)
- time-dependent itô / 2D itô
- SDE existence/uniqueness
- local martingales / semimartingales
- quadratic variation as a process (we have it as a one-shot at fixed `t`)
- stochastic vol models (heston, SABR)
- jump-diffusion models (merton, kou)
- local volatility (dupire)
- barrier options requiring first-passage time distributions for BM
- quanto / multi-currency options requiring measure change

if mathlib lands an itô integral or degenne extends the brownian-motion library with one, revisit this list.

## stretch goals (technically possible, ergonomically painful)

- **margrabe formula** for exchange options. the rigorous derivation requires a change of numéraire (girsanov). but a "given the right pricing measure, derive the formula" version is achievable using existing gaussian machinery. would need careful scope statement.
- **constant-elasticity-of-variance (CEV) model closed forms**. some special cases have closed forms involving non-central chi-squared distributions. mathlib doesn't have non-central chi-squared yet, so this is gated.

## sequencing recommendation

phases 1 + 2 + phase 3 (basic framework) all landed in a single session on 2026-05-18. remaining work:

1. **CRR convergence to BS** (phase 3 continuation). the big remaining classical-pedagogy artifact. needs CLT applied to log-returns with `u_n = e^{σ√Δt}, d_n = e^{−σ√Δt}` and matching drift correction. ~500-800 lines, multi-session.
2. **upstream PRs** (phase 4). the 3 already-drafted items are ready to submit. the `Real.erf` PR would be a fresh multi-day drafting effort.

## what done looks like (achieved)

end of 2026-05-18 session:
- **76 total theorems** (was 65 — 11 new in `benchmarks/mathematical_finance.json`)
- **60 delivery-ready** (was 49)
  - **36 `full`** (was 25 — +11 from `mathematical_finance.json`)
  - **24 `library_wrapper`** (unchanged)
- **16 `reduced_core`** (unchanged; itô-gated)
- **0 `placeholders`** (unchanged)

the project now contains the most thoroughly formalized treatment of static vanilla derivatives pricing in lean 4 known to the author. it's still niche; the audience is still small. but it's a coherent, complete artifact for the "static" world of black-scholes — call, put, parity, both digitals, forward, vega, rho (delta + gamma + theta were already there), bachelier, implied-vol uniqueness, black-76, and the single-period binomial replication theorem.
