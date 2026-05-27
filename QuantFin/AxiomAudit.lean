/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin

/-!
# Axiom audit — the "axioms-clean" claim, build-enforced

The library's headline claim is that every `full` derivation is
`#print axioms`-clean: it depends only on the three standard Mathlib
axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra
axioms.

This file turns that claim from a docstring assertion (in `docs/coverage.md`)
into a **build-enforced invariant**. Each `#guard_msgs in #print axioms`
block below pins the axiom dependencies of a headline / load-bearing
theorem. If any audited theorem ever picks up `sorryAx` (a `sorry` slipped
in) or a new axiom (a dependency changed), the `#guard_msgs` check fails and
**the build breaks**.

The audited set spans every area of the library — it is representative, not
exhaustive; extend it when a new load-bearing theorem lands. A theorem that
appears here is certified axioms-clean by `lake build`, not by assertion.

Note: pure-algebra theorems (closed by `ring`/`field_simp`) may legitimately
depend on a *subset* of the three (or none); those are pinned to their
actual set below. The invariant we enforce is "no `sorryAx`, no axiom
outside the standard three", which the pinned messages capture exactly.
-/

namespace QuantFin.AxiomAudit

/-! ## Black-Scholes core -/

/-- info: 'QuantFin.bs_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bs_call_formula

/-- info: 'QuantFin.bsP_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bsP_eq_bsV

/-- info: 'QuantFin.hasDerivAt_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.hasDerivAt_bsV_S

/-- info: 'QuantFin.bs_pde_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bs_pde_holds

/-- info: 'QuantFin.expected_terminal_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.expected_terminal_eq_forward

/-! ## Garman normal form + consumer-side corollaries -/

/-- info: 'QuantFin.bsV_eq_bsVGarman_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bsV_eq_bsVGarman_standard

/-- info: 'QuantFin.black_futures_price_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.black_futures_price_eq_bsVGarman

/-- info: 'QuantFin.bs_dividends_price_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bs_dividends_price_eq_bsVGarman

/-! ## Gaussian MGF + lognormal moments -/

/-- info: 'QuantFin.integral_exp_affine_gaussianPDFReal_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.integral_exp_affine_gaussianPDFReal_univ

/-- info: 'QuantFin.nthMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.nthMoment_terminal

/-- info: 'QuantFin.secondMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.secondMoment_terminal

/-- info: 'QuantFin.variance_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.variance_terminal

/-- info: 'QuantFin.bsLogReturn_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bsLogReturn_mean

/-! ## Exponential-discount principle + the rate-recovery retrofits -/

/-- info: 'QuantFin.rate_eq_neg_log_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.rate_eq_neg_log_deriv

/-- info: 'QuantFin.forwardRate_eq_neg_log_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.forwardRate_eq_neg_log_discount

/-- info: 'QuantFin.force_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.force_eq_neg_log_deriv_survival

/-- info: 'QuantFin.hazard_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.hazard_eq_neg_log_deriv_survival

/-! ## Static Girsanov: the risk-neutral measure derived -/

/-- info: 'QuantFin.gaussian_esscher_pdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.gaussian_esscher_pdf

/-- info: 'QuantFin.gaussianReal_withDensity_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.gaussianReal_withDensity_esscher

/-- info: 'QuantFin.BSCallHyp.exists_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.BSCallHyp.exists_of_physical

/-- info: 'QuantFin.bsTerminal_physical_eq_riskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bsTerminal_physical_eq_riskNeutral

/-- info: 'QuantFin.discounted_terminal_eq_S0_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.discounted_terminal_eq_S0_of_physical

/-- info: 'QuantFin.bs_call_formula_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.bs_call_formula_of_physical

/-- info: 'QuantFin.discounted_physical_terminal_eq_S0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.discounted_physical_terminal_eq_S0

/-! ## Margrabe exchange option (first multivariate result) -/

/-- info: 'QuantFin.margrabe_effective_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.margrabe_effective_variance

/-- info: 'QuantFin.exchange_payoff_eq_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.exchange_payoff_eq_ratio

/-- info: 'QuantFin.margrabe_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.margrabe_eq_bsVGarman

/-- info: 'QuantFin.margrabe_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.margrabe_parity

/-- info: 'QuantFin.margrabe_price_via_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.margrabe_price_via_call

/-! ## Convex pricing functional + FTAP / state-price wiring -/

/-- info: 'QuantFin.statePricePricing_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.statePricePricing_convexOn

/-- info: 'QuantFin.callPrice_finiteState_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.callPrice_finiteState_butterfly_nonneg

/-- info: 'QuantFin.stateprice_call_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.stateprice_call_butterfly_nonneg

/-! ## Binomial trees -/

/-- info: 'QuantFin.americanCallPrice_le_binomialPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.americanCallPrice_le_binomialPrice

/-! ## Variance swap (QV limit) -/

/-- info: 'QuantFin.tendsto_expected_bsLogPrice_equipartition_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.tendsto_expected_bsLogPrice_equipartition_sum

/-! ## L² quadratic variation of Brownian motion (Summit 1) + its in-probability corollary -/

/-- info: 'QuantFin.QuadraticVariationL2.tendsto_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.QuadraticVariationL2.tendsto_qv

/-- info: 'QuantFin.QuadraticVariationL2.tendstoInMeasure_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.QuadraticVariationL2.tendstoInMeasure_qv

/-! ## Expectation-form Itô / Feynman–Kac (the QV → ½f″ correction, from first principles) -/

/-- info: 'QuantFin.FeynmanKacHeatEquation.heatConvolution_eq_add_integral_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantFin.FeynmanKacHeatEquation.heatConvolution_eq_add_integral_deriv

/-- info: 'QuantFin.FeynmanKacHeatEquation.expectation_ito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.FeynmanKacHeatEquation.expectation_ito

/-! ## Adapted Itô isometry (increment-independence cornerstone) -/

/-- info: 'QuantFin.ItoIsometryAdapted.integral_adapted_mul_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.ItoIsometryAdapted.integral_adapted_mul_increment

/-- info: 'QuantFin.ItoIsometryAdapted.integral_adapted_sq_mul_increment_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.integral_adapted_sq_mul_increment_sq

/-- info: 'QuantFin.ItoIsometryAdapted.ito_isometry_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.ItoIsometryAdapted.ito_isometry_discrete

/-- info: 'QuantFin.ItoIsometryAdapted.ito_isometry_brownian_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.ItoIsometryAdapted.ito_isometry_brownian_self

/-- info: 'QuantFin.ItoIsometryAdapted.integral_adapted_mul_increment_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.integral_adapted_mul_increment_sq

/-- info: 'QuantFin.ItoIsometryAdapted.ito_isometry_discrete_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.ito_isometry_discrete_bilinear

/-! ## Predictable-rectangle pairing (inner-product core of the continuous Itô integral) -/

/-- info: 'QuantFin.ItoIsometryAdapted.adapted_indepFun_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.adapted_indepFun_forward

/-- info: 'QuantFin.ItoIsometryAdapted.integral_two_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.integral_two_increment

/-- info: 'QuantFin.ItoIsometryAdapted.rect_increment_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIsometryAdapted.rect_increment_pairing

/-! ## Stochastic intervals + elementary-predictable-set lemma (Degenne issue #440) -/

/-- info: 'QuantFin.stochasticIoc.predictable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.stochasticIoc.predictable

/-- info: 'QuantFin.stochasticIoc.elementaryPredictableSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.stochasticIoc.elementaryPredictableSet

/-! ## Continuous Itô integral — foundational bridge (AdaptedAt ↔ natural filtration) -/

/-- info: 'QuantFin.ItoIntegralL2.adaptedAt_of_measurable_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.ItoIntegralL2.adaptedAt_of_measurable_natural

/-! ## Margrabe BSCallHyp grounding (leap-3 closure via gaussian vector) -/

/-- info: 'QuantFin.normalizedSpread_hasLaw_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.normalizedSpread_hasLaw_std

/-- info: 'QuantFin.margrabe_bsCallHyp_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.margrabe_bsCallHyp_of_gaussian

/-- info: 'QuantFin.margrabe_price_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.margrabe_price_of_gaussian

/-! ## Portfolio / risk / performance -/

/-- info: 'QuantFin.portfolioVarTwo_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.portfolioVarTwo_ge_min

/-- info: 'QuantFin.gaussianVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.gaussianVaR_translation

/-- info: 'QuantFin.gaussianCVaR_sub_VaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.gaussianCVaR_sub_VaR

/-- info: 'QuantFin.sharpeRatio_affine_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.sharpeRatio_affine_invariant

/-! ## Certified bridges -/

/-- info: 'QuantFin.portfolioVarN_diag_eq_herfindahl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantFin.portfolioVarN_diag_eq_herfindahl

/-! ## Certified cross-domain bridges -/

/-- info: 'QuantFin.portfolioVarN_diag_eq_herfindahl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantFin.portfolioVarN_diag_eq_herfindahl

end QuantFin.AxiomAudit
