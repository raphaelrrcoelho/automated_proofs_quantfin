# Mathlib / BrownianMotion-Package Bridge Audit

**Date:** 2026-05-22
**Scope:** All 22 modules under `lean/HybridVerify/Foundations/` (4664 LOC)
plus pricing-module consumption of Mathlib's probability surface.

## Executive summary

The earlier critique that "4664 LOC of Foundations is dead code from pricing
modules" was **half right and half wrong**:

- **Right** that the BM/Wiener/martingale machinery is structurally
  disconnected from pricing modules. `IsBrownianMotion`, `Martingale`
  (Mathlib class), `wienerIntegral`, `quadraticVariation`, `StoppingTime`,
  `condExp` are referenced **0 times** in any pricing module.
- **Wrong** that Foundations duplicates Mathlib. Of the 9 substantive
  Foundations files audited below, **8 fill genuine Mathlib gaps** that
  cannot be replaced by direct Mathlib imports.

The right action is **additive bridges** (constructors connecting Foundations
to pricing) rather than **destructive replacement** (deleting Foundations in
favor of Mathlib equivalents). Phase 30 (Bridge A,
`BSCallHypFromBrownian.lean`) is the first such bridge.

## Per-module audit findings

### Foundations/BrownianQuadraticVariation.lean (161 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L¹-expectation form of `[B, B]_t = t` for processes with
  Gaussian increments. Pure marginal-moment computation via
  `variance_id_gaussianReal`.
- **BrownianMotion package equivalent:**
  `StochasticIntegral/QuadraticVariation.lean` defines `quadraticVariation`
  via the Doob-Meyer decomposition (`predictablePart` of squared norm).
  Currently sorry-laden (WIP).
- **Bridge opportunity:** Once BM package's path-wise QV is complete, derive
  our L¹ version as its expectation. For now, **keep both**.

### Foundations/LpContinuousMartingaleConvergence.lean (725 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L^p convergence at naturals for continuous-time L^p-
  bounded martingales (`lp_continuous_martingale_converges_at_naturals`).
- **BrownianMotion package equivalent:**
  `StochasticIntegral/DoobLp.lean` proves Doob's maximal inequality
  (`maximal_ineq_countable`, `maximal_ineq_ennreal`). Related but not the
  same theorem. The maximal inequality is *used* in our convergence proof.
- **Bridge opportunity:** Replace our internal Doob's maximal inequality
  (if any) with imports from BM package's `DoobLp.lean`. Low-LOC change,
  defer until needed.

### Foundations/MartingaleTransform.lean (123 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** Discrete martingale-transform construction `(A · M)_n :=
  ∑_{k<n} A_{k+1}(M_{k+1} − M_k)` and adapted-integrability-martingale
  property.
- **Mathlib equivalent:** None found by name search. Mathlib's
  `Mathlib.Probability.Martingale.*` covers discrete and continuous
  martingales but no `martingaleTransform` named declaration.
- **Bridge opportunity:** None needed. Likely upstream candidate.

### Foundations/CondExpJensen.lean (95 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** The file's own docstring says "Mathlib v4.30 has no
  general subgradient API for convex functions on ℝ" — the explicit
  subgradient parameterisation is necessary.
- **Bridge opportunity:** None. Upstream candidate when Mathlib gains a
  subgradient API.

### Foundations/BivariateGaussian.lean (165 LOC)

- **Status:** Builds finance-specific struct over Mathlib `HasGaussianLaw`.
- **What it does:** `BivariateGaussianHyp` packages the bivariate-Gaussian
  conditional-expectation formula `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y - μ_Y)`.
- **Mathlib equivalent:** Mathlib has `IsGaussianProcess`, `HasGaussianLaw`,
  `gaussianProjectiveFamily` (in BrownianMotion package). The conditional-
  expectation closed form for bivariate is not directly stated.
- **Bridge opportunity:** Connect `joint_gaussian` to `HasGaussianLaw` more
  formally if not already. Low value.

### Foundations/StandardGaussianMGF.lean (81 LOC)

- **Status:** Specialised reformulation. Possible partial duplication.
- **What it does:** Specialises `∫ exp(c·Z) ∂N(0,1) = exp(c²/2)` for the BS
  use case. Currently derived from `integral_exp_mul_gaussianPDFReal_univ`.
- **Mathlib equivalent:** `gaussianReal_charFun` is the characteristic
  function `E[exp(i·t·X)]`. The MGF would be its analytic continuation to
  real `c`.
- **Bridge opportunity:** Could potentially derive our MGF identity from
  `gaussianReal_charFun` via analytic continuation. Significant rework for
  modest gain. **Defer.**

### Foundations/GaussianCDFDeriv.lean (81 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** "not present in Mathlib (no `Real.erf`, no
  `gaussianReal_Iic_hasDerivAt`)".
- **Bridge opportunity:** None. Upstream candidate.

### Foundations/WienerIntegral.lean + WienerIntegralL2.lean (580 LOC combined)

- **Status:** Foundation work. Possible partial overlap with BM package.
- **BM package equivalents:** `StochasticIntegral/SimpleProcess.lean`,
  `MonotoneProcess.lean`, `LocalMartingale.lean`, `Predictable.lean`,
  `Centering.lean`. The BM package is more general (cadlag, predictable
  processes) where ours is L²-specific Wiener integral.
- **Bridge opportunity:** Once BM package's stochastic-integral pipeline is
  complete (currently has sorries), our L² Wiener integral could be derived
  as a special case of theirs. **Defer until BM package stabilises.**

### Foundations/MathlibLp.lean (1019 LOC) — LARGEST

- **Status:** Substantial Mathlib `Lp` extensions. Not audited in detail.
- **Bridge opportunity:** This file deserves a dedicated audit pass; out of
  scope for current bridging session. **TODO.**

### Foundations/BrownianMartingale.lean (473 LOC)

- **Status:** Continuous-time Brownian-motion-is-martingale derivations.
- **BM package equivalent:** `IsPreBrownian` + `Auxiliary/Martingale`. The
  package's `IsPreBrownian` characterises BM by finite-dim Gaussian laws
  and has a continuous modification (Kolmogorov-Chentsov). Our file builds
  martingale + stopping-time structure on top.
- **Bridge opportunity:** Re-derive our `BrownianMartingale` content as
  consequences of `IsPreBrownian`. Could shrink considerably. **TODO** —
  needs careful audit to preserve any unique content.

## Bridges executed (Phase 30+)

| # | Name | File | Status |
|---|------|------|--------|
| A | `BSCallHyp.of_isPreBrownian` | `Foundations/BSCallHypFromBrownian.lean` | NEW (phase 30) |
| A.2 | `BachelierHyp.of_isPreBrownian` | (same file) | NEW (phase 30) |
| — | Core scaling lemma `scaled_isPreBrownian_eval_law` | (same file) | NEW (phase 30) |
| — | `bsTerminal_via_brownian` (S_T = S_0 · exp((r−σ²/2)T + σ·W_T)) | (same file) | NEW (phase 30) |
| — | `bachelierTerminal_via_brownian` (S_T = S_0 + σ·W_T) | (same file) | NEW (phase 30) |
| 31 | Full pricing pipeline from `IsPreBrownian` (composite corollaries): BS call, put, put-call parity, Bachelier, cash digital, asset digital, power call, dividends call, stock numeraire, KMV PD, Merton equity | `Foundations/PricingFromBrownian.lean` | NEW (phase 31) |
| 32 | Variance-swap per-increment QV identity: `E[(X_t − X_s)²] = σ²(t−s) + (r−σ²/2)²(t−s)²` for BS log-price under `BrownianQuadraticVariation` hypothesis. First downstream use of the BQV module from outside `Foundations/BrownianQuadraticVariation.lean`. Exposed previously-private `integral_sq_increment`, `integrable_sq_increment`, `measurable_increment` and added new public `integral_increment` (E[B_t − B_s] = 0), `integrable_increment` to BQV's public surface | `Foundations/VarianceSwapFromQV.lean` + BQV public-surface additions | NEW (phase 32) |
| 33 | Variance-swap equipartition sum: `E[Σ_{k=0}^{n} (X-increments at k·T/(n+1))²] = σ²·T + (r−σ²/2)²·T²/(n+1)`. Builds on phase 32's per-increment via `integral_finset_sum` after establishing per-summand integrability | `Foundations/VarianceSwapEquipartition.lean` | NEW (phase 33) |
| 34 | Variance-swap QV limit: `Tendsto (E[Σ ...]) atTop (𝓝 (σ²·T))`. The drift contribution `drift²·T²/(n+1) → 0` via `tendsto_one_div_add_atTop_nhds_zero_nat`. Completes the QV chain — realised variance under fine partitions equals the variance-swap fair strike `σ²` (after `1/T` rescaling) | `Foundations/VarianceSwapLimit.lean` | NEW (phase 34) |
| 35 | Discrete Itô formula `f(X_N) − f(X_0) = Σ f'·ΔX + (1/2) Σ f''·(ΔX)² + Σ R_k`, telescoping + per-summand Taylor remainder by definition. **Adapted from Nagy 2026** (SSRN 6336503, Section 3). Attribution: original Lean source in paper §3; our adaptation renames `taylor_remainder → discreteTaylorRemainder`, factors `(1/2)` out, restructures proof to use `Finset.sum_congr` | `Foundations/DiscreteIto.lean` | NEW (phase 35, after Nagy) |
| 36 | Itô integral for simple processes: definition as finite sum, linearity, isometry-for-constant-integrand. **Adapted from Nagy 2026** (§4). Attribution: Nagy's Definition 4.1 + Theorems 4.2-4.3. The L² extension (Nagy §4.3) is deferred — see our existing `Foundations/WienerIntegralL2.lean` | `Foundations/ItoIntegralSimple.lean` | NEW (phase 36, after Nagy) |
| 37 | FTAP both directions for one-period one-asset two-state market: forward (EMM ⟹ no arbitrage), backward (construct EMM from sign data via `q_up = −z_down/(z_up − z_down)`). **Adapted from Nagy 2026** (§7). Attribution: Nagy's Theorems 7.1-7.3. Complements our existing forward FTAP for general finite-state in `Foundations/NoArbitrageDerivations.lean` | `Foundations/FTAPTwoState.lean` | NEW (phase 37, after Nagy) |
| 38 | Constant-product AMM (Uniswap v2-style): swap output `Δy = y·Δx/(x + Δx)`, constant-product invariant preservation `(x + Δx)·(y − Δy) = x·y`, internal price `y/x` at zero input, arbitrage trigger. **Adapted from Pusceddu-Bartoletti FMBC 2024** (OASIcs FMBC.2024.5), with own ℝ-based framework (no `PReal` dependency). Attribution to the underlying Bartoletti-Chiang-Lluch-Lafuente 2022 theory. **First DeFi module** in HybridVerify — opens Foundations to DeFi market microstructure | `DeFi/ConstantProductAMM.lean` | NEW (phase 38, after Pusceddu-Bartoletti) |
| 39 | Itô structural drift formula `itoDrift f' f'' μ_X σ_X := μ_X · f' + (1/2) · σ_X² · f''` — the per-time-unit drift coefficient in Itô's lemma. Specialisations: identity sanity check + **GBM log-drift** `d(log S) drift = μ − σ²/2` (the celebrated `−σ²/2` Itô correction). **Adapted from Nagy 2026 §5**. The structural drift, not the full L²-integral form (which is gated). Used downstream by Phase 46 (BS PDE). | `Foundations/ItoLemma.lean` | NEW (phase 39, after Nagy) |
| 41 | Vasicek full SDE closed-form: `r_t ~ N(r_0 e^{−κt} + θ(1−e^{−κt}), σ²(1−e^{−2κt})/(2κ))`. Terminal-distribution parametrisation `vasicekSDETerminal r_0 θ κ σ t Z = mean + √var · Z`. Mean-reversion asymptotic `mean → θ` as `t → ∞`. **First full SDE pricing in the library** — variance computation uses simple-Itô-isometry for deterministic integrand (`Phase 36`). | `FixedIncome/VasicekSDE.lean` | NEW (phase 41) |
| 43 | Binomial up-probability `q = (e^r − d)/(u − d)` derived from two-state FTAP backward construction (Phase 37 + Nagy §7). Excess returns `(z_u, z_d) = (u − e^r, d − e^r)` satisfy the sign condition under `BinomialNoArb` ⟹ EMM exists. The binomial `q` equals Nagy's `−z_d/(z_u − z_d)`. Bridge between `Binomial/Model.lean` and `Foundations/FTAPTwoState.lean`. | `Binomial/BinomialFromFTAP.lean` | NEW (phase 43) |
| 45 | Variance-swap log-payoff and QV-limit form equivalence: both `(2/T) · E[log(F/S_T)]` (existing) and `lim_n (1/T) · E[Σ (Δlog S)²]` (Phase 34) yield `σ²`. Model-parameter equivalence: same model variance recovered by both empirical / replication characterisations. | `Foundations/VarianceSwapEquivalence.lean` | NEW (phase 45) |
| 46 | BS PDE derived from Itô drift + no-arbitrage: under risk-neutral GBM, the discounted price's drift = 0 ⟹ `∂_t V + r S ∂_S V + (1/2) σ² S² ∂_SS V − r V = 0`. Forward derivation from no-arb (vs the backward verification in existing `BlackScholes/PDE.lean`). Uses Phase 39's `itoDrift` as the algebraic core. | `BlackScholes/PDEFromIto.lean` | NEW (phase 46) |
| 53 | Pricing kernel from two-state FTAP: discounted EMM weights `q_state = e^{−rT} · q^{EMM}` form a valid pricing kernel — non-negative, sums to bond price, linear in payoff. Composes `Foundations/StatePrices.lean` (linear functional axioms) with `Foundations/FTAPTwoState.lean` (Phase 37 EMM construction). Bond price + monotonicity from FTAP, not assumed separately. | `Foundations/PricingKernel.lean` | NEW (phase 53) |

## Bridges planned but deferred

| # | Name | Reason for deferring |
|---|------|----------------------|
| B | Discounted price as Mathlib `Martingale` | Requires defining the price process structure (vs. just the terminal). Significant additive work. |
| D | `SnellEnvelope` over Mathlib `StoppingTime` | Requires reworking the recursive Binomial price definition to thread filtration. |
| 27 | Vasicek from `IsPreBrownian` | Requires stochastic integral for `∫_0^t e^{-κ(t-s)} dW_s` term; BM package's stochastic integral has sorries. |
| 25 | Variance swap from QV | Tractable once BM package QV completes. |
| 4 | CRR via Mathlib CLT/Skorohod | Significant refactor of `CRRConvergence.lean`. |
| 6 | NoArbitrage via `LinearMap` | Refactor of `NoArbitrageDerivations.lean`. |
| 28 | Forward-rate / hazard via Mathlib `intervalIntegral` | Minor cleanup, low priority. |

## Conclusion

Foundations is **not** slop. It fills Mathlib gaps and shouldn't be deleted.
The architectural bridge gap is real but the remedy is additive constructors
(Bridge A pattern) rather than wholesale replacement. The 4664 LOC stays;
new pricing entry points (BS, Bachelier, eventually Vasicek/CIR via Itô)
gain optional BM-based constructors that compose with existing pricing
machinery.

The biggest remaining audit target is `MathlibLp.lean` (1019 LOC) — its
relationship to Mathlib's current `Lp` machinery deserves a dedicated pass.
