/-
  QuantFin (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import QuantFin` to pull
  everything in, or `import QuantFin.<Section>.<Module>` for a
  specific submodule.

  Modules are organized by topic:

  * `Foundations/`   — probability primitives reused across finance.
  * `BlackScholes/`  — BS family (call, put, digitals, Greeks, PDE,
                       Asian / chooser / capped / power / lookback,
                       Breeden-Litzenberger, bisection IV, …).
  * `Futures/`       — Black-76 model.
  * `Binomial/`      — discrete-time tree, CRR convergence, Bermudan
                       sandwich, Merton 1973 American-call dominance.
  * `FixedIncome/`   — ZCB, coupon bonds, duration, convexity, YTM,
                       bootstrap, credit (constant + time-varying hazard),
                       forward-rate non-flat, Vasicek deterministic,
                       Macaulay-vs-modified discrete.
  * `Portfolio/`     — Markowitz, CAPM, two-fund separation, risk parity,
                       Black-Litterman, tangent portfolio FOC.
  * `Performance/`   — Sharpe / Sortino / Treynor / IR / Kelly.
  * `RiskMeasures/`  — VaR/CVaR + coherent-risk axioms, Rockafellar-Uryasev,
                       spectral risk, Herfindahl concentration.
  * `Actuarial/`     — net premium, Gompertz force of mortality.
  * `DeFi/`          — Decentralized-finance market microstructure:
                       constant-product AMMs (Uniswap v2-style), swap
                       output, invariant preservation, internal price.
-/

-- Foundations
import QuantFin.Foundations.GaussianMoments
import QuantFin.Foundations.BivariateGaussian
import QuantFin.Foundations.GaussianCDFDeriv
import QuantFin.Foundations.GaussianGirsanov
import QuantFin.Foundations.FeynmanKacHeatEquation
import QuantFin.Foundations.BrownianMartingale
import QuantFin.Foundations.BrownianQuadraticVariation
import QuantFin.Foundations.CondExpJensen
import QuantFin.Foundations.ExpMin
import QuantFin.Foundations.FTAP
import QuantFin.Foundations.LpContinuousMartingaleConvergence
import QuantFin.Foundations.MartingaleTransform
import QuantFin.Foundations.MathlibLp
import QuantFin.Foundations.WienerIntegral
import QuantFin.Foundations.WienerIntegralL2
-- Structural / principle modules:
import QuantFin.Foundations.StandardGaussianMGF
import QuantFin.Foundations.ExponentialDiscount
-- Phase 13 additions:
import QuantFin.Foundations.StatePrices
import QuantFin.Foundations.TriangleArbitrage
import QuantFin.Foundations.CarrMadan
import QuantFin.Foundations.AlmgrenChriss
import QuantFin.Foundations.ConvexPricingFunctional
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
import QuantFin.Foundations.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
import QuantFin.Foundations.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
import QuantFin.Foundations.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
import QuantFin.Foundations.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
import QuantFin.Foundations.VarianceSwapLimit
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
import QuantFin.Foundations.DiscreteIto
-- Phase 36: Itô integral for simple processes (adapted from Nagy 2026)
import QuantFin.Foundations.ItoIntegralSimple
-- The adapted Itô isometry (increment-independence cornerstone)
import QuantFin.Foundations.ItoIsometryAdapted
-- Stochastic intervals + elementary-predictable-set lemma (Degenne issue #440)
import QuantFin.Foundations.StochasticInterval
-- Continuous L²-adapted Itô integral (construction, anchored on Degenne SimpleProcess)
import QuantFin.Foundations.ItoIntegralL2
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
import QuantFin.Foundations.FTAPTwoState
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
import QuantFin.DeFi.ConstantProductAMM
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
import QuantFin.Foundations.ItoLemma
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
import QuantFin.Foundations.VarianceSwapEquivalence
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
import QuantFin.Foundations.PricingKernel
-- Phase 42: Multi-state FTAP backward (hypothesis-form, forward direction proved)
import QuantFin.Foundations.FTAPMultiState
-- BlackScholes
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.Put
import QuantFin.BlackScholes.PDE
import QuantFin.BlackScholes.PutGreeks
import QuantFin.BlackScholes.Digital
import QuantFin.BlackScholes.DigitalGreeks
import QuantFin.BlackScholes.Dividends
import QuantFin.BlackScholes.DividendsGreeks
import QuantFin.BlackScholes.Forward
import QuantFin.BlackScholes.HigherGreeks
import QuantFin.BlackScholes.StrikeGreeks
import QuantFin.BlackScholes.PutStrikeConvexity
import QuantFin.BlackScholes.StaticBounds
import QuantFin.BlackScholes.AsianInequality
import QuantFin.BlackScholes.ImpliedVolatility
import QuantFin.BlackScholes.LognormalMoments
import QuantFin.BlackScholes.VarianceSwap
import QuantFin.BlackScholes.Bachelier
import QuantFin.BlackScholes.BachelierGreeks
import QuantFin.BlackScholes.Chooser
import QuantFin.BlackScholes.CappedCall
import QuantFin.BlackScholes.Spreads
import QuantFin.BlackScholes.Lookback
import QuantFin.BlackScholes.PowerOption
import QuantFin.BlackScholes.BreedenLitzenberger
import QuantFin.BlackScholes.BisectionIV
-- Structural / principle modules:
import QuantFin.BlackScholes.StrikeConvexity
import QuantFin.BlackScholes.PriceBounds
-- Phase 13 additions:
import QuantFin.BlackScholes.Quanto
import QuantFin.BlackScholes.NewtonRaphsonIV
import QuantFin.BlackScholes.LognormalCOV

-- Futures
import QuantFin.Futures.Black76
import QuantFin.Futures.Black76Greeks
-- Phase 13 additions:
import QuantFin.Futures.Swaption

-- Binomial
import QuantFin.Binomial.Model
import QuantFin.Binomial.American
import QuantFin.Binomial.CRRConvergence
import QuantFin.Binomial.DriftLimit
import QuantFin.Binomial.Bermudan
import QuantFin.Binomial.AmericanCallNoDividend
-- Phase 13 additions:
import QuantFin.Binomial.Girsanov
import QuantFin.Binomial.SecondFTAP
-- Phase 14: real new theorems
import QuantFin.Binomial.MertonAmericanCallTree
import QuantFin.Binomial.ReplicatingUniqueness
import QuantFin.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
import QuantFin.Binomial.PathReflection
-- Phase 19: Snell envelope characterization of americanPrice
import QuantFin.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
import QuantFin.Binomial.BinomialFromFTAP
-- Phase 44: CRR binomial scheme as discrete-Itô process (drift + QV limits)
import QuantFin.Binomial.CRRDiscreteIto
-- Phase 20: first-principles core derivations
import QuantFin.Foundations.NoArbitrageDerivations
import QuantFin.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
import QuantFin.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
import QuantFin.BlackScholes.PowerCall
import QuantFin.BlackScholes.ExchangeOption
-- Margrabe BSCallHyp grounding from a joint two-GBM gaussian model (leap-3 closure)
import QuantFin.BlackScholes.MargrabeGrounding
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
import QuantFin.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
import QuantFin.BlackScholes.PDEFromIto
-- Phase 40: Itô lemma L¹-expectation form applied to GBM log (mean + variance)
import QuantFin.BlackScholes.GBMLogMoments

-- FixedIncome
import QuantFin.FixedIncome.ZCB
import QuantFin.FixedIncome.CouponBonds
import QuantFin.FixedIncome.Immunization
import QuantFin.FixedIncome.ConvexityImmunization
import QuantFin.FixedIncome.YieldCurve
import QuantFin.FixedIncome.Credit
import QuantFin.FixedIncome.MacaulayModified
import QuantFin.FixedIncome.HazardCurve
import QuantFin.FixedIncome.ForwardRate
import QuantFin.FixedIncome.Vasicek
-- Phase 13 additions:
import QuantFin.FixedIncome.KMVMerton
import QuantFin.FixedIncome.MeanReversionHalfLife
import QuantFin.FixedIncome.CDS
-- Phase 21: first-principles duration-as-price-sensitivity
import QuantFin.FixedIncome.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
import QuantFin.FixedIncome.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
import QuantFin.FixedIncome.KMVMertonStructural
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
import QuantFin.FixedIncome.CDSTimeVarying
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
import QuantFin.FixedIncome.VasicekSDE

-- Portfolio
import QuantFin.Portfolio.Markowitz
import QuantFin.Portfolio.MarkowitzNAsset
import QuantFin.Portfolio.CAPM
import QuantFin.Portfolio.TwoFundSeparation
import QuantFin.Portfolio.RiskParity
import QuantFin.Portfolio.BlackLitterman
import QuantFin.Portfolio.TangentPortfolio
-- Phase 13 additions:
import QuantFin.Portfolio.TangentPortfolioN
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
import QuantFin.Portfolio.SharpeFOCDerivation
import QuantFin.Portfolio.CAPMEquilibrium
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
import QuantFin.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
import QuantFin.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
import QuantFin.Portfolio.BlackLittermanND

-- Performance
import QuantFin.Performance.Ratios
import QuantFin.Performance.RatiosExtended
import QuantFin.Performance.Kelly

-- RiskMeasures
import QuantFin.RiskMeasures.Gaussian
import QuantFin.RiskMeasures.CoherentAxioms
import QuantFin.RiskMeasures.Additivity
import QuantFin.RiskMeasures.RockafellarUryasev
import QuantFin.RiskMeasures.Spectral
import QuantFin.RiskMeasures.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
import QuantFin.RiskMeasures.UtilityDerivation

-- Bridges (certified cross-domain unifications)
import QuantFin.Bridges.ConcentrationVariance

-- Actuarial
import QuantFin.Actuarial.Insurance
import QuantFin.Actuarial.Mortality
-- Phase 13 additions:
import QuantFin.Actuarial.CompoundPoisson
