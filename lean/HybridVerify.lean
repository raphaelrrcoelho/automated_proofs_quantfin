/-
  HybridVerify (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import HybridVerify` to pull
  everything in, or `import HybridVerify.<Section>.<Module>` for a
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
import HybridVerify.Foundations.Basic
import HybridVerify.Foundations.BivariateGaussian
import HybridVerify.Foundations.GaussianCDFDeriv
import HybridVerify.Foundations.FeynmanKacHeatEquation
import HybridVerify.Foundations.BrownianMartingale
import HybridVerify.Foundations.BrownianQuadraticVariation
import HybridVerify.Foundations.CondExpJensen
import HybridVerify.Foundations.ExpMin
import HybridVerify.Foundations.FTAP
import HybridVerify.Foundations.LpContinuousMartingaleConvergence
import HybridVerify.Foundations.MartingaleTransform
import HybridVerify.Foundations.MathlibLp
import HybridVerify.Foundations.WienerIntegral
import HybridVerify.Foundations.WienerIntegralL2
-- Structural / principle modules:
import HybridVerify.Foundations.StandardGaussianMGF
import HybridVerify.Foundations.ExponentialDiscount
-- Phase 13 additions:
import HybridVerify.Foundations.StatePrices
import HybridVerify.Foundations.TriangleArbitrage
import HybridVerify.Foundations.CarrMadan
import HybridVerify.Foundations.AlmgrenChriss
import HybridVerify.Foundations.ConvexPricingFunctional
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
import HybridVerify.Foundations.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
import HybridVerify.Foundations.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
import HybridVerify.Foundations.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
import HybridVerify.Foundations.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
import HybridVerify.Foundations.VarianceSwapLimit
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
import HybridVerify.Foundations.DiscreteIto
-- Phase 36: Itô integral for simple processes (adapted from Nagy 2026)
import HybridVerify.Foundations.ItoIntegralSimple
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
import HybridVerify.Foundations.FTAPTwoState
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
import HybridVerify.DeFi.ConstantProductAMM
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
import HybridVerify.Foundations.ItoLemma
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
import HybridVerify.Foundations.VarianceSwapEquivalence
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
import HybridVerify.Foundations.PricingKernel

-- BlackScholes
import HybridVerify.BlackScholes.Call
import HybridVerify.BlackScholes.Put
import HybridVerify.BlackScholes.PDE
import HybridVerify.BlackScholes.PutGreeks
import HybridVerify.BlackScholes.Digital
import HybridVerify.BlackScholes.DigitalGreeks
import HybridVerify.BlackScholes.Dividends
import HybridVerify.BlackScholes.DividendsGreeks
import HybridVerify.BlackScholes.Forward
import HybridVerify.BlackScholes.HigherGreeks
import HybridVerify.BlackScholes.StrikeGreeks
import HybridVerify.BlackScholes.PutStrikeConvexity
import HybridVerify.BlackScholes.StaticBounds
import HybridVerify.BlackScholes.AsianInequality
import HybridVerify.BlackScholes.ImpliedVolatility
import HybridVerify.BlackScholes.LognormalMoments
import HybridVerify.BlackScholes.VarianceSwap
import HybridVerify.BlackScholes.Bachelier
import HybridVerify.BlackScholes.BachelierGreeks
import HybridVerify.BlackScholes.Chooser
import HybridVerify.BlackScholes.CappedCall
import HybridVerify.BlackScholes.Spreads
import HybridVerify.BlackScholes.Lookback
import HybridVerify.BlackScholes.PowerOption
import HybridVerify.BlackScholes.BreedenLitzenberger
import HybridVerify.BlackScholes.BisectionIV
-- Structural / principle modules:
import HybridVerify.BlackScholes.StrikeConvexity
import HybridVerify.BlackScholes.PriceBounds
-- Phase 13 additions:
import HybridVerify.BlackScholes.Quanto
import HybridVerify.BlackScholes.NewtonRaphsonIV
import HybridVerify.BlackScholes.LognormalCOV

-- Futures
import HybridVerify.Futures.Black76
import HybridVerify.Futures.Black76Greeks
-- Phase 13 additions:
import HybridVerify.Futures.Swaption

-- Binomial
import HybridVerify.Binomial.Model
import HybridVerify.Binomial.American
import HybridVerify.Binomial.CRRConvergence
import HybridVerify.Binomial.DriftLimit
import HybridVerify.Binomial.Bermudan
import HybridVerify.Binomial.AmericanCallNoDividend
-- Phase 13 additions:
import HybridVerify.Binomial.Girsanov
import HybridVerify.Binomial.SecondFTAP
-- Phase 14: real new theorems
import HybridVerify.Binomial.MertonAmericanCallTree
import HybridVerify.Binomial.ReplicatingUniqueness
import HybridVerify.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
import HybridVerify.Binomial.PathReflection
-- Phase 19: Snell envelope characterization of americanPrice
import HybridVerify.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
import HybridVerify.Binomial.BinomialFromFTAP
-- Phase 20: first-principles core derivations
import HybridVerify.Foundations.NoArbitrageDerivations
import HybridVerify.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
import HybridVerify.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
import HybridVerify.BlackScholes.PowerCall
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
import HybridVerify.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
import HybridVerify.BlackScholes.PDEFromIto

-- FixedIncome
import HybridVerify.FixedIncome.ZCB
import HybridVerify.FixedIncome.CouponBonds
import HybridVerify.FixedIncome.Immunization
import HybridVerify.FixedIncome.ConvexityImmunization
import HybridVerify.FixedIncome.YieldCurve
import HybridVerify.FixedIncome.Credit
import HybridVerify.FixedIncome.MacaulayModified
import HybridVerify.FixedIncome.HazardCurve
import HybridVerify.FixedIncome.ForwardRate
import HybridVerify.FixedIncome.Vasicek
-- Phase 13 additions:
import HybridVerify.FixedIncome.KMVMerton
import HybridVerify.FixedIncome.MeanReversionHalfLife
import HybridVerify.FixedIncome.CDS
-- Phase 21: first-principles duration-as-price-sensitivity
import HybridVerify.FixedIncome.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
import HybridVerify.FixedIncome.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
import HybridVerify.FixedIncome.KMVMertonStructural
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
import HybridVerify.FixedIncome.CDSTimeVarying
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
import HybridVerify.FixedIncome.VasicekSDE

-- Portfolio
import HybridVerify.Portfolio.Markowitz
import HybridVerify.Portfolio.MarkowitzNAsset
import HybridVerify.Portfolio.CAPM
import HybridVerify.Portfolio.TwoFundSeparation
import HybridVerify.Portfolio.RiskParity
import HybridVerify.Portfolio.BlackLitterman
import HybridVerify.Portfolio.TangentPortfolio
-- Phase 13 additions:
import HybridVerify.Portfolio.TangentPortfolioN
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
import HybridVerify.Portfolio.SharpeFOCDerivation
import HybridVerify.Portfolio.CAPMEquilibrium
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
import HybridVerify.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
import HybridVerify.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
import HybridVerify.Portfolio.BlackLittermanND

-- Performance
import HybridVerify.Performance.Ratios
import HybridVerify.Performance.RatiosExtended
import HybridVerify.Performance.Kelly

-- RiskMeasures
import HybridVerify.RiskMeasures.Gaussian
import HybridVerify.RiskMeasures.CoherentAxioms
import HybridVerify.RiskMeasures.Additivity
import HybridVerify.RiskMeasures.RockafellarUryasev
import HybridVerify.RiskMeasures.Spectral
import HybridVerify.RiskMeasures.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
import HybridVerify.RiskMeasures.UtilityDerivation

-- Actuarial
import HybridVerify.Actuarial.Insurance
import HybridVerify.Actuarial.Mortality
-- Phase 13 additions:
import HybridVerify.Actuarial.CompoundPoisson
