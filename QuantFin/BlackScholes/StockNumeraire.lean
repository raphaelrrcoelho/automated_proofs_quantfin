/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call
import QuantFin.BlackScholes.Forward

/-!
# Delta as stock-numeraire probability: `Φ(d_1) = Q^(S)(S_T > K)`

Under the risk-neutral measure `Q`, `Φ(d_2)` is the exercise probability
(formalised in `BlackScholes.RiskNeutralProbabilities`). The other Φ in the
BS formula, `Φ(d_1)`, has a *different* probabilistic interpretation: it is
the exercise probability **under the stock-numeraire measure** `Q^(S)`,
defined via the Radon-Nikodym density

  `dQ^(S)/dQ := e^{−rT} · S_T / S_0`.

This file derives that identification in three parts.

## Part 1: asset-payoff integral identity

`bsCall_asset_piece_integral`: the Q-integral of `S_T` on the exercise
region equals `S_0 · e^{rT} · Φ(d_1)`. This is the "Φ(d_1) piece" of the
BS formula, extracted as a standalone identity.

  `∫ ω, 1_{S_T(Z ω) > K} · S_T(Z ω) ∂Q = S_0 · e^{rT} · Φ(d_1)`.

The proof mirrors `bs_call_formula`: HasLaw transfer, indicator on the
exercise region `{z > −d_2}`, `integral_exp_mul_gaussianPDFReal_Ioi` for
the completing-the-square step, and the BS algebraic identity
`(r − σ²/2)T + σ²T/2 = rT`.

## Part 2: stock-numeraire measure construction

`stockNumeraireDensity`, `stockNumeraireMeasure`: the Radon-Nikodym
density `e^{−rT} · S_T / S_0` and the resulting measure via
`Measure.withDensity`.

`stockNumeraireMeasure_isProbabilityMeasure`: the density integrates to 1
(this is `discounted_terminal_eq_S0` from `Forward.lean`).

## Part 3: the identification

`stockNumeraire_exercise_probability`: `Q^(S)({ω | S_T(Z ω) > K}) = Φ(d_1)`.

This closes the structural narrative on the BS formula:

  * `bsV = S_0 · Φ(d_1) − K · e^{−rT} · Φ(d_2)`
  * `Φ(d_2) = Q(S_T > K)` (risk-neutral exercise probability)
  * `Φ(d_1) = Q^(S)(S_T > K)` (stock-numeraire exercise probability)

Each Φ is now identified with the exercise probability under one of the
two natural numeraires (money market vs. stock).
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ## Part 1: the asset-payoff integral identity -/

/-- **Asset-payoff integral on the exercise region**: under the risk-neutral
hypothesis `BSCallHyp`,

  `∫ ω, 1_{S_T(Z ω) > K} · S_T(Z ω) ∂Q = S_0 · e^{rT} · Φ(d_1)`.

The integral on the LHS is the Q-expectation of `S_T` restricted to the
exercise region. Combined with `riskNeutralProb_S_T_gt_K`
(`Q(S_T > K) = Φ(d_2)`), this gives the canonical decomposition of the
European call price

  `bsV = e^{−rT} · ∫ ω, max(S_T(Z ω) − K, 0) ∂Q
       = e^{−rT} · ∫ ω, 1_{S_T(Z ω) > K} · S_T(Z ω) ∂Q
         − K · e^{−rT} · Q({S_T > K})
       = S_0 · Φ(d_1) − K · e^{−rT} · Φ(d_2)`. -/
theorem bsCall_asset_piece_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
      (bsTerminal S_0 r σ T) (Z ω) ∂Q =
        S_0 * Real.exp (r * T) * Phi (bsd1 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_1 : ℝ := bsd1 S_0 K r σ T with d_1_def
  set d_2 : ℝ := bsd2 S_0 K r σ T with d_2_def
  set μ_log : ℝ := (r - σ ^ 2 / 2) * T with μ_log_def
  set ν_log : ℝ := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_sq : ν_log ^ 2 = σ ^ 2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_algebra : μ_log + ν_log ^ 2 / 2 = r * T := by rw [hν_log_sq]; ring
  have h_shift_eq : ν_log - (-d_2) = d_1 := by rw [d_1_def, d_2_def, bsd2]; ring
  have h_term_meas : Measurable fun z : ℝ => bsTerminal S_0 r σ T z := by
    unfold bsTerminal; fun_prop
  have h_ind_meas : Measurable fun z : ℝ =>
      (Set.Ioi (-d_2)).indicator (bsTerminal S_0 r σ T) z :=
    h_term_meas.indicator measurableSet_Ioi
  -- Step 1: express as ∘ Z and apply HasLaw transfer
  rw [show (fun ω => (Set.Ioi (-d_2)).indicator (bsTerminal S_0 r σ T) (Z ω)) =
        (fun z => (Set.Ioi (-d_2)).indicator (bsTerminal S_0 r σ T) z) ∘ Z from rfl,
      hZ.integral_comp h_ind_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 2: pdf · indicator (Ioi) bsTerminal = indicator (Ioi) (pdf · bsTerminal)
  rw [show (fun z => gaussianPDFReal 0 1 z •
              (Set.Ioi (-d_2)).indicator (bsTerminal S_0 r σ T) z)
        = (Set.Ioi (-d_2)).indicator
            (fun z => gaussianPDFReal 0 1 z • bsTerminal S_0 r σ T z) from
      funext (fun z => by
        by_cases hz : z ∈ Set.Ioi (-d_2)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, smul_zero])]
  rw [integral_indicator measurableSet_Ioi]
  -- Step 3: rewrite pdf · bsTerminal in factored form
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
    show gaussianPDFReal 0 1 z • bsTerminal S_0 r σ T z =
         S_0 * Real.exp μ_log *
           (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) from by
      unfold bsTerminal
      have h_exp : Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
                  = Real.exp μ_log * Real.exp (ν_log * z) := by
        show Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
              = Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
        exact Real.exp_add _ _
      rw [smul_eq_mul, h_exp]; ring)]
  -- Step 4: pull out S_0 · exp(μ_log) and apply integral_exp_mul_gaussianPDFReal_Ioi
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_Ioi, h_shift_eq]
  -- Step 5: S_0 · exp(μ_log) · exp(ν_log²/2) · Φ(d_1) = S_0 · exp(rT) · Φ(d_1)
  rw [show S_0 * Real.exp μ_log * (Real.exp (ν_log ^ 2 / 2) * Phi d_1) =
      S_0 * (Real.exp μ_log * Real.exp (ν_log ^ 2 / 2)) * Phi d_1 from by ring,
      ← Real.exp_add, h_algebra]

/-! ## Part 2: stock-numeraire measure -/

/-- **Stock-numeraire Radon-Nikodym density**: the density of `Q^(S)` w.r.t.
`Q` is `e^{−rT} · S_T / S_0`. -/
noncomputable def stockNumeraireDensity {Ω : Type*}
    (S_0 r σ T : ℝ) (Z : Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ENNReal.ofReal (Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω) / S_0)

/-- **Stock-numeraire measure**: `Q^(S) := Q.withDensity (e^{−rT} · S_T / S_0)`. -/
noncomputable def stockNumeraireMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) (S_0 r σ T : ℝ) (Z : Ω → ℝ) : Measure Ω :=
  Q.withDensity (stockNumeraireDensity S_0 r σ T Z)

/-- **Stock-numeraire density is non-negative** (as a real). -/
lemma stockNumeraireDensity_real_nonneg
    {Ω : Type*}
    {S_0 r σ T : ℝ} (hS_0 : 0 < S_0) (Z : Ω → ℝ) (ω : Ω) :
    0 ≤ Real.exp (-r * T) * bsTerminal S_0 r σ T (Z ω) / S_0 := by
  apply div_nonneg
  · exact mul_nonneg (Real.exp_nonneg _) (by
      unfold bsTerminal
      exact mul_nonneg hS_0.le (Real.exp_nonneg _))
  · exact hS_0.le

/-! ## Part 3: the identification -/

/-- **Delta as stock-numeraire exercise probability**: under the risk-neutral
hypothesis `BSCallHyp`,

  `Q^(S)({ω | S_T(Z ω) > K}) = Φ(d_1)`,

where `Q^(S) = Q.withDensity (e^{−rT} · S_T / S_0)` is the stock-numeraire
measure.

This is the companion to `riskNeutralProb_S_T_gt_K`
(`Q({S_T > K}) = Φ(d_2)`): under change of numeraire from money market to
stock, the same exercise event has probability `Φ(d_1)`, not `Φ(d_2)`. The
difference `Φ(d_1) − Φ(d_2)` measures the "value of optionality" beyond
pure expected payoff. -/
theorem stockNumeraire_exercise_probability
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    (∫ ω, (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
      (fun z => Real.exp (-r * T) * bsTerminal S_0 r σ T z / S_0) (Z ω) ∂Q) =
        Phi (bsd1 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  -- Rewrite the indicator integrand:
  --   indicator (Ioi) (e^{-rT} · S_T / S_0) z =
  --   e^{-rT} / S_0 · indicator (Ioi) S_T z
  have h_factor : ∀ z : ℝ,
      (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
        (fun z => Real.exp (-r * T) * bsTerminal S_0 r σ T z / S_0) z =
      (Real.exp (-r * T) / S_0) *
        (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
          (bsTerminal S_0 r σ T) z := by
    intro z
    by_cases hz : z ∈ Set.Ioi (-bsd2 S_0 K r σ T)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      field_simp
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  -- Pull the constant outside the integral
  rw [show (fun ω => (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
              (fun z => Real.exp (-r * T) * bsTerminal S_0 r σ T z / S_0) (Z ω)) =
        (fun ω => (Real.exp (-r * T) / S_0) *
          (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
            (bsTerminal S_0 r σ T) (Z ω)) from
    funext (fun ω => h_factor (Z ω))]
  rw [integral_const_mul]
  -- Apply the asset-payoff integral identity
  rw [bsCall_asset_piece_integral
        ⟨hS_0, hK, hσ, hT, hZ⟩]
  -- Combine: (e^{-rT}/S_0) · S_0 · e^{rT} · Phi(d_1) = Phi(d_1)
  have h_exp : Real.exp (-(r * T)) * Real.exp (r * T) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [show Real.exp (-r * T) / S_0 *
        (S_0 * Real.exp (r * T) * Phi (bsd1 S_0 K r σ T)) =
      (Real.exp (-(r * T)) * Real.exp (r * T)) * (S_0 / S_0) *
        Phi (bsd1 S_0 K r σ T) from by
    rw [show Real.exp (-r * T) = Real.exp (-(r * T)) from by congr 1; ring]
    field_simp]
  rw [div_self hS_0.ne', mul_one, h_exp, one_mul]

end QuantFin
