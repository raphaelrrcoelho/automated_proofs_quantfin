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

## Concrete next-round candidates — STATUS

Three depth theorems were planned. As of 2026-05-22, **all three cores have
shipped** in `BlackScholes/StrikeConvexity.lean`, `Binomial/MertonAmericanCallTree.lean`,
and `Binomial/PathReflection.lean`:

1. **Multi-step Merton 1973 in the binomial tree** — DONE
   (`Binomial/MertonAmericanCallTree.lean`).
   `americanPrice = binomialPrice` at every horizon `n` for the non-dividend
   call (`r ≥ 0`, `K ≥ 0`). The one-period continuation dominance
   (Jensen + martingale identity + discount shift) extends to multi-step
   via induction on `n` with monotonicity of the one-period operator at
   the inductive step. Three new theorems: `call_intrinsic_le_binomialPrice`,
   `americanCallPrice_le_binomialPrice`, `americanCallPrice_eq_binomialPrice`.

2. **Continuous convexity of `K ↦ bsV K r σ S τ` on `(0, ∞)`** — DONE
   (`BlackScholes/StrikeConvexity.lean`). Bridges `ConvexPricingFunctional`
   (finite-state) to the actual BS formula via
   `convexOn_of_deriv2_nonneg'` + `hasDerivAt_bsV_KK`. K-convexity now
   visible at **three scales** in the library: payoff
   (`convexOn_call_payoff`), finite-state price
   (`callPrice_finiteState_convexOn_K`), continuous BS price
   (`bsV_strike_convexOn`). PDF positivity in `BreedenLitzenberger.lean`
   becomes an actual derivation rather than a standalone fact.

3. **Discrete reflection principle for binomial paths — full**
   — DONE (`Binomial/PathReflection.lean`, ~370 LOC, both halves landed).
   * **Algebraic core**: `walkPos (reflectAfter τ ω) k = 2·walkPos ω τ −
     walkPos ω k` for `τ ≤ k` (via prefix/suffix sum decomposition);
     `reflectAfter_involutive`; endpoint corollary.
   * **Hitting-time bijection**: `firstHit ω a`, invariance under
     reflection (`firstHit_reflectAfter_firstHit`), reflection-at-first-hit
     involution (`reflectAtFirstHit_involutive`), and the full
     **`reflectionPrincipleEquiv a b`** between `{ω : hits a, ends at b}`
     and `{ω : hits a, ends at 2a − b}` as a Mathlib `Equiv`. Both
     directions of the bijection are the same reflection map (involution).

Total ~600 LOC across three modules, all landing in one session. Each
ships a theorem whose statement is non-trivial and whose proof is real
math (calculus / induction / combinatorial sum decomposition,
respectively).

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

---

# quant-finance roadmap (unblocked path)

the 16 remaining `reduced_core` theorems in `docs/coverage.md` are upstream-gated on the itô integral, measure-change machinery, and continuous-time poisson processes. this document captures what can be built **without** waiting on upstream mathlib or degenne work, framed as a quant-finance project rather than a textbook audit.

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

## phase 3: discrete-continuous bridge (PARTIAL 2026-05-18, deeper progress same day)

- [x] **discrete-time binomial tree pricing framework** — `BinomialModel.lean`. includes:
  - risk-neutral up-probability `crrUpProb u d r = (e^r − d)/(u − d)` + no-arbitrage condition `BinomialNoArb` + `(0, 1)`-range proof.
  - single-period option price `binomialOptionPriceOnePeriod`.
  - **replicating-portfolio theorems** (cost, up-state payoff, down-state payoff) — three full proofs.
  - multi-period `binomialPrice` via well-founded recursion on remaining steps; one-step consistency lemma; linearity and scalar-homogeneity in the payoff; constant-payoff price closed form `e^{-rn} · c`.
- [x] **CRR parameterization + classical-analytic limit core** — `BinomialCRRConvergence.lean`.
  - CRR parameterization: `crrUp = e^{σ√Δt}`, `crrDown = e^{−σ√Δt}`, `crrPerStepRate = rΔt`, `crrProb` definitions.
  - one-step risk-neutral martingale identity (exact algebraic): `p_n · u_n + (1 − p_n) · d_n = e^{rΔt}`.
  - exponential difference-quotient limits: `(e^{cx}−1)/x → c`, `(e^{c·h²}−1)/h² → c`, `(e^{c·h²}−1)/h → 0`, `(e^{σh} − e^{−σh})/h → 2σ`. all proved via `HasDerivAt` + `hasDerivAt_iff_tendsto_slope`.
  - **`crrProb_tendsto_half`**: `p_n → 1/2` as `n → ∞`. the substantive analytic step — `p_n` becomes asymptotically symmetric Bernoulli. ~80 lines, uses quotient-of-limits + composition with `h_n = √(T/n)`.
  - **`crr_variance_limit`**: `4 σ² T · p_n (1 − p_n) → σ² T`. direct corollary.
- [ ] **full pricing-convergence theorem**: `binomialPrice → bs_call_price` as `n → ∞`. requires a **triangular-array CLT** (Lindeberg-Feller) — Mathlib at the current pin only ships the **fixed-iid CLT** (`tendstoInDistribution_inv_sqrt_mul_sum_sub`). plus a continuous-mapping + uniform-integrability argument for the call payoff. **TODO future session**: either (a) draft a triangular-array CLT upstream in Mathlib, or (b) prove CRR convergence directly via characteristic functions (Levy's continuity theorem on log-returns).

milestone (still partial): classical-analytic CRR↔BS correspondence is formalized on the variance side (and via `p_n → 1/2`). drift-limit `n · (2 p_n − 1) · σ√Δt → (r − σ²/2) T` needs second-order Taylor on `2 e^{rΔt} − e^{σ√Δt} − e^{−σ√Δt}` and is documented in `BinomialCRRConvergence.lean` as further analytic work. full distributional convergence to BS is upstream-gated.

## phase 4: upstream foundations

real upstream contributions that would land in mathlib or degenne. each is a separate PR. all four items are ready to submit; awaiting an upstream-PR session.

- [ ] **`Real.erf` for mathlib**. mathlib has no error function. drafting it would unlock cleaner standard-normal-CDF APIs across this project and the broader probability ecosystem. ~300 lines plus the `Real.erfc`, `Real.erfinv` companions and basic identities. would also let us replace our local `Phi` definition with `(1 + erf(x/√2))/2`. **status**: not yet drafted; multi-day work.
- [x] **`gaussianReal_Iic_hasDerivAt` for mathlib**: proved as `hasDerivAt_Phi` in `QuantFin/GaussianCDFDeriv.lean` (~80 lines via FTC). ready to upstream as a separate PR (`Φ' = ϕ` is the missing piece).
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
- **79 total theorems** (was 65 — 14 new in `benchmarks/mathematical_finance.json`)
- **63 delivery-ready** (was 49)
  - **39 `full`** (was 25 — +14 from `mathematical_finance.json`)
  - **24 `library_wrapper`** (unchanged)
- **16 `reduced_core`** (unchanged; itô-gated)
- **0 `placeholders`** (unchanged)

the project now contains the most thoroughly formalized treatment of static vanilla derivatives pricing in lean 4 known to the author. it's still niche; the audience is still small. but it's a coherent, complete artifact for the "static" world of black-scholes — call, put, parity, both digitals, forward, vega, rho (delta + gamma + theta were already there), bachelier, implied-vol uniqueness, black-76, and the single-period binomial replication theorem.

## the leaps (2026-05-23) — beyond the static world

three "big leaps" pushed past the static ceiling. full narrative in
[`leaps.md`](leaps.md); per-theorem audit in [`coverage.md`](coverage.md).

- **leap 1 — static Girsanov.** the risk-neutral measure is now *derived* from
  the physical measure via an Esscher density (`GaussianGirsanov.lean`,
  `BSCallHyp.exists_of_physical`). `BSCallHyp` — assumed by 14 pricing files —
  is a theorem. axioms-clean.
- **leap 2 — genesis cascade.** `discounted_terminal_eq_S0_of_physical` proves
  the constructed `Q` is a genuine EMM; `bs_call_formula_of_physical` runs the
  full physical→price chain. additive bridges, `GaussianGirsanov` load-bearing.
- **leap 3 — multivariate (Margrabe).** the exchange option, first multivariate
  result: effective vol, `GarmanNormalForm` slot-in, parity, and the
  price-level reduction (`margrabe_price_via_call`: exchange = `bs_call_formula`
  on the ratio). `ExchangeOption.lean`.

all build-enforced axioms-clean via `QuantFin/AxiomAudit.lean`.

### leap 4 — the adapted Itô isometry (done, discrete) + the continuous frontier

the increment-independence this was long said to wait on is **not** WIP: it is
`IsPreBrownian.hasIndepIncrements` / `IsPreBrownian.indepFun_shift`, fully
proven in Degenne's package. Building directly on it:

- **leap 4 (discrete) — done.** `Foundations/ItoIsometryAdapted.lean`: the Itô
  isometry for *adapted random* simple integrands,
  `E[(Σ φₖ·ΔBₖ)²] = Σ E[φₖ²]·(t_{k+1}−t_k)` (`ito_isometry_discrete`). the
  cross-terms vanish by the weak Markov property (`ΔBₖ ⊥ 𝓕_{tₖ}`), **not** by
  deterministic covariance — that distinction *is* what separates the Itô
  integral from the Wiener integral (`WienerIntegralL2.lean`, deterministic
  integrands). capstone: the fully-discharged `∫₀ᵀ B dB` Riemann-sum isometry
  `ito_isometry_brownian_self`. build-enforced axioms-clean.
- **continuous frontier.** what remains is the L²(adapted) Cauchy completion
  over adapted processes (density of adapted simple integrands in the adapted
  L²), the analogue of `WienerIntegralL2`'s completion for the deterministic
  case. this — *not* increment independence — is the open step, and what would
  clear the remaining itô-gated `reduced_core`s once finished.
- **Margrabe `BSCallHyp`-grounding** — the ratio's risk-neutral lognormality
  from a joint two-GBM model via the numeraire change; uses the same
  gaussian-vector machinery (`IsGaussianProcess.iIndepFun''`). the
  Margrabe-analog of leap 1.

these are honest dedicated builds, not bolt-ons. a hypothesis-form Itô isometry
was drafted and **reverted** earlier precisely because its orthogonality
hypothesis had no available discharge; leap 4 (discrete) is now the genuine
discharge of exactly that orthogonality, via the weak Markov property — the
no-slop line, held.
