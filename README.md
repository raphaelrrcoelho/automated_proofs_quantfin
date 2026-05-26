# Quant finance, formally verified

A Lean 4 library of machine-checked quant-finance theorems, built on Mathlib
and Degenne's BrownianMotion. 251 theorems across 11 areas — Black-Scholes
with the full Greek matrix and the exotics, binomial trees with American /
Bermudan / Snell envelope, fixed income with hazard credit and Vasicek SDE,
portfolio theory from Markowitz to Black-Litterman, coherent risk measures,
Kelly, mortality, and constant-product AMMs.

The aim is a comprehensive, honest reference for formally-verified
quantitative finance: broad coverage, and — for every result — an exact
statement of what is proved and what is assumed.

|  | count |
|---|---:|
| total theorems | 251 |
| **full derivations** | **211** |
| library wrappers | 24 |
| reduced cores (Mathlib-gated) | 16 |
| placeholders | **0** |

Every `full` derivation is `#print axioms`-clean: it depends only on the
three Mathlib standard axioms `[propext, Classical.choice, Quot.sound]`.

## At a glance

```lean
-- QuantFin/BlackScholes/PDE.lean — BS delta via the magic identity
lemma hasDerivAt_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S := by
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  have h_V := (hasDerivAt_id S).mul h_Phi_d1
              |>.sub (h_Phi_d2.const_mul (K * Real.exp (-(r * τ))))
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  ...; field_simp; linear_combination -h_bs
```

The `bs_identity` magic-identity collapse drives delta, gamma, theta, vega,
rho, vanna, volga, and the BS PDE forward direction. See
[`QuantFin/Examples.lean`](QuantFin/Examples.lean) for a curated
five-proof tour.

## Quick start

```bash
# Pull the pinned image (~3 min) instead of building locally (~15 min)
docker compose -f docker/docker-compose.yml pull verify

# Build the entire library — clean exit means every theorem typechecks
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'

# Run a benchmark chapter
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/mathematical_finance.json
```

Fast authoring loop (5–30s feedback via persistent REPL daemon):

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
./scripts/lean-check.sh QuantFin/<Section>/<Module>.lean
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the full development workflow.

## What's covered

| Area | Headline results |
|---|---|
| **Black-Scholes** | Call, put, digital (cash + asset) + parity; full Greek matrix (δ, γ, vega, θ, ρ, vanna, volga, ψ); BS-Merton with dividends; Garman-Kohlhagen FX; implied vol uniqueness + bisection bracket; PDE forward direction; strike Greeks (∂_K, ∂²_K); static price bounds; box-spread arbitrage; lognormal moments + n-th moment + power forward; variance swap fair strike (closed-form + QV-limit); Breeden-Litzenberger implied risk-neutral PDF. |
| **Exotics** | Chooser via PCP; capped call = bull spread; bull-spread + butterfly non-negativity; lookback ≥ vanilla; two-date geometric ≤ arithmetic Asian; **Margrabe exchange option** (multivariate — effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)`, parity, and the price as a `bs_call_formula` call on the ratio). |
| **Bachelier** | Arithmetic-BM option pricing with the truncated-mean primitive; full first-order Greeks. |
| **Black-76 (Futures)** | Black-76 formula via zero-drift specialisation + full Greek matrix; swaption. |
| **Binomial trees** | Single-period replication + uniqueness; multi-period backward induction; American options (Snell envelope characterisation); CRR convergence; **Bermudan sandwich** (European ≤ Bermudan ≤ American); **Merton 1973** strict dominance bsV > S − K (American = European for non-dividend call); **André's reflection principle** with full bijection. |
| **Fixed income** | ZCB + duration + convexity; coupon bond pricing + YTM monotonicity; annuity geometric-series closed form; flat + non-flat forward/spot rate consistency; Macaulay vs modified duration; first- + second-order Redington immunization; yield-curve bootstrap; reduced-form credit (constant + time-varying hazard); Vasicek deterministic ODE + SDE terminal distribution; **KMV-Merton** structural default. |
| **Portfolio theory** | 2-asset Markowitz (completing-the-square); N-asset Markowitz (Finset double sum, diagonal, iid diversification, PSD bound); **N-asset Lagrangian** FOC characterisation; CAPM (β + portfolio linearity) + **equilibrium derivation**; two-fund separation (CML + Sharpe invariance); **risk parity** equal-contribution (log-barrier FOC); **Black-Litterman** 1-D + **N-dim normal-equation** posterior; tangent portfolio FOC. |
| **Performance ratios** | Sharpe (full affine invariance, √T scaling); Sortino; Treynor; Information ratio; tracking error; Kelly criterion (FOC, horizon myopia, fraction bounds, sign analysis). |
| **Risk measures** | Gaussian VaR / CVaR closed forms; coherent axioms (translation, homogeneity, monotonicity, subadditivity) **verified on the gaussian closed form** (acceptance-set convexity is separately derived from concave utility in `UtilityDerivation.lean`); joint-stdev triangle; VaR/CVaR additivity at ρ=1; **Rockafellar-Uryasev** algebraic form; spectral risk measures; **Herfindahl-Hirschman** with Cauchy-Schwarz lower bound. |
| **Actuarial** | Annuity-due closed form; net premium principle; **Gompertz** cumulative force of mortality. |
| **DeFi** | Constant-product AMM (Uniswap v2) invariants — adapted from Pusceddu-Bartoletti. |
| **Foundations** | **Static Girsanov** — the risk-neutral measure *derived* from the physical measure via an Esscher density, making `BSCallHyp` a theorem and the discounted asset a proven `Q`-martingale ([`docs/leaps.md`](docs/leaps.md)); Brownian motion martingales (square-sub-time, Wald exponential); Wiener integral + L² version; **the adapted Itô isometry** — the genuinely-stochastic `E[(Σ φₖ·ΔBₖ)²]=Σ E[φₖ²]·Δtₖ` for *random adapted* integrands, cross-terms killed by the weak Markov property (`∫B dB` capstone) ([`docs/leaps.md`](docs/leaps.md)); quadratic variation; Doob L^p continuous-time convergence; conditional Jensen; **discrete Itô lemma** (after Nagy); simple Itô integral; FTAP (two-state explicit EMM + multi-state forward); pricing kernels; state prices; Itô structural drift (GBM log-drift, log return mean); BS PDE from Itô + no-arbitrage. |

The library leans on seven **structural-principle modules** where one named
fact generates dozens of one-line corollaries (Garman normal form, price
bounds, K-convexity at three scales, convex pricing functional, standard
gaussian MGF, exponential discount, Snell envelope). See
[`docs/architecture.md`](docs/architecture.md) for the full catalogue.

## Documentation

| File | Contents |
|---|---|
| [`docs/coverage.md`](docs/coverage.md) | Per-theorem audit: faithfulness status (`full` / `library_wrapper` / `reduced_core` / `placeholder`), verification evidence, claim-wording guidance. |
| [`docs/architecture.md`](docs/architecture.md) | Design principles: structural-principle modules, the three-tier honesty model, the Foundations → pricing bridge methodology. |
| [`docs/leaps.md`](docs/leaps.md) | Static Girsanov (EMM derived), the genesis cascade, and Margrabe's multivariate exchange option — the deductive arc that makes the risk-neutral measure a theorem. |
| [`docs/bridges.md`](docs/bridges.md) | Catalogue of bridges from `Foundations/` to pricing modules. |
| [`docs/patterns.md`](docs/patterns.md) | Distilled Lean / Mathlib proof patterns and anti-patterns from prior phases. |
| [`docs/roadmap.md`](docs/roadmap.md) | Strategic depth-vs-breadth framing and the tactical phase log. |
| [`upstream/`](upstream/) | Drafts of contributions to Mathlib, BrownianMotion, and Lean Zulip. |
| [`references/`](references/) | Source PDFs (Saporito notes, cited papers). |

## What's not done (yet)

The 16 remaining `reduced_core` theorems are Mathlib-gated:

- **Itô calculus** (~12 theorems including Itô's lemma path-wise form, time-dependent Itô, Lévy's martingale characterisation, SDE existence + uniqueness, the four Girsanov entries): the deterministic Wiener integral and the **discrete adapted Itô isometry** are now built (`Foundations/ItoIsometryAdapted.lean`, on `IsPreBrownian.hasIndepIncrements`); what remains is the continuous-time L²(adapted) Itô integral — the Cauchy completion over adapted processes.
- **Continuous-time Poisson processes** (3 theorems: interarrival exponential, superposition, thinning): Mathlib has only the discrete `PoissonPMF`.
- **Fine BM path machinery** (3 theorems: reflection principle on Brownian paths, nowhere-differentiability, law of iterated logarithm).

The library will revisit these when the supporting Mathlib infrastructure
lands. Algebraic / structural cores are already in place; only the L²-limit
glue layer is gated. See [`docs/roadmap.md`](docs/roadmap.md).

## Related upstream contributions

Drafted as part of this project (source under [`upstream/`](upstream/)):

- **Mathlib**: `gaussianReal_zero_one_Iic_neg`, `gaussianReal_zero_one_Ioi_toReal`, `exp_mul_gaussianPDFReal_zero_one`, `integral_exp_mul_gaussianPDFReal_zero_one_Ioi` (standard normal tail + completing-the-square primitives).
- **Remy Degenne's `brownian-motion`**: `IsFilteredPreBrownian.squareSubTime_isMartingale`, `IsFilteredPreBrownian.waldExponential_isMartingale` (the two textbook BM martingales).

## Reproducibility

The verify Docker image pins:

- Lean toolchain `4.30.0-rc1`
- Mathlib at commit `f23306121184`
- Remy Degenne's `brownian-motion` library at commit `16d15eb42c`

These are frozen in [`lakefile.lean`](lakefile.lean) + [`lake-manifest.json`](lake-manifest.json) + [`lean-toolchain`](lean-toolchain) at the repo root.

## Acknowledgements

Three modules adapt published Lean 4 formalisations by other authors, with
explicit attribution headers on each file:

- `Foundations/DiscreteIto.lean`, `Foundations/ItoIntegralSimple.lean`, `Foundations/FTAPTwoState.lean` adapt the discretization framework from Tamás Nagy, *"From Itô to Black-Scholes: A Machine-Verified Derivation in Lean 4"*, SSRN [6336503](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503), 2026.
- `DeFi/ConstantProductAMM.lean` adapts Pusceddu & Bartoletti, *"Formalizing Automated Market Makers in the Lean 4 Theorem Prover"*, [OASIcs FMBC 2024.5](https://doi.org/10.4230/OASIcs.FMBC.2024.5) (companion code: <https://github.com/dpusceddu/lean4-amm>); underlying economic theory from Bartoletti, Chiang, Lluch-Lafuente, *"A theory of Automated Market Makers in DeFi"*, LMCS 2022.

Adaptations re-implement these results in this library's framework
(real-valued, `gaussianReal`-based BS hypothesis rather than reconstructed
Itô integral, ℝ-positivity rather than `PReal` subtypes). Mathematical
content is unchanged; copyright on the specific adaptation is Raphael
Coelho (Apache 2.0); academic fair use covers the derivative-work
relationship.

## References

Saporito, *Stochastic Processes* (textbook chapter coverage, primary
source). Hull, *Options, Futures, and Other Derivatives*. Bodie / Kane /
Marcus, *Investments*. Fabozzi, *Fixed Income Mathematics*. McNeil / Frey /
Embrechts, *Quantitative Risk Management*. Demeterfi / Derman / Kamal,
*More Than You Ever Wanted to Know About Volatility Swaps* (1999).
Artzner / Delbaen / Eber / Heath, *Coherent Measures of Risk* (1999).
Kelly, *A New Interpretation of Information Rate* (1956). Tobin,
*Liquidity Preference as Behavior Towards Risk* (1958). Sharpe (1965),
Treynor (1965), Sortino-van der Meer (1991), Grinold-Kahn (1999),
Rockafellar-Uryasev (2000). Black-Scholes (1973), Merton (1973), Black
(1976), Bachelier (1900), Cox-Ross-Rubinstein (1979). Roncalli-Maillard
on risk parity, Black-Litterman (1992).

## License

Apache 2.0, per the header on each source file.
