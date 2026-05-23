/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call

/-!
# Bachelier model option pricing

The Bachelier (1900) model is the historical predecessor of Black-Scholes:
asset prices follow an **arithmetic** Brownian motion `S_T = S_0 + σ · W_T`
(no exponential, no log-normality). Used today for short-tenor / negative-rate
markets where lognormality is inappropriate.

Under `BachelierHyp`, the discounted call price is

    V_bach = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`, `Φ` and `ϕ` are the standard normal CDF and
PDF. The proof structure parallels `bs_call_formula`: HasLaw transfer +
indicator decomposition on the exercise region `Ioi(-d)` + a truncated-mean
identity for the Gaussian first moment.

Key new primitive: **truncated mean of `N(0, 1)`** —
`∫ z in Ioi a, z · ϕ(z) dz = ϕ(a)`,
proved via FTC since `(−ϕ)' = z · ϕ`.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

/-! ### Derivative of the standard normal PDF -/

/-- `(−ϕ(0,1,·))' = z · ϕ(0,1,z)`. Algebraic content: `d/dz [exp(-z²/2)] = -z · exp(-z²/2)`. -/
lemma hasDerivAt_neg_gaussianPDFReal_zero_one (z : ℝ) :
    HasDerivAt (fun z' : ℝ => -gaussianPDFReal 0 1 z')
      (z * gaussianPDFReal 0 1 z) z := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  set c := (Real.sqrt (2 * π))⁻¹
  -- d/dz [-z²/2] = -z
  have h_sq : HasDerivAt (fun z' : ℝ => -(z'^2)/2) (-z) z := by
    have h_pow : HasDerivAt (fun z' : ℝ => z'^2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h_div : HasDerivAt (fun z' : ℝ => z'^2 / 2) z z := by
      have := h_pow.div_const 2; simpa using this
    have h_neg : HasDerivAt (fun z' : ℝ => -(z'^2 / 2)) (-z) z := h_div.neg
    have h_eq : (fun z' : ℝ => -(z'^2)/2) = (fun z' : ℝ => -(z'^2 / 2)) := by
      funext z'; ring
    rw [h_eq]; exact h_neg
  -- d/dz [exp(-z²/2)] = exp(-z²/2) · -z
  have h_exp : HasDerivAt (fun z' : ℝ => Real.exp (-(z'^2)/2))
      (Real.exp (-(z^2)/2) * -z) z := h_sq.exp
  -- d/dz [c · exp(-z²/2)] = c · exp(-z²/2) · -z
  have h_const : HasDerivAt (fun z' : ℝ => c * Real.exp (-(z'^2)/2))
      (c * (Real.exp (-(z^2)/2) * -z)) z := h_exp.const_mul c
  -- neg
  have h_neg := h_const.neg
  convert h_neg using 1
  ring

/-! ### Integrability of `z ↦ z · ϕ(0, 1, z)` -/

/-- The function `z ↦ z · ϕ(0, 1, z)` is integrable on `ℝ` (against Lebesgue).
Derived by transferring `Integrable id (gaussianReal 0 1)` (the existence of the
first moment of `N(0, 1)`) through the withDensity identification of
`gaussianReal`. -/
lemma integrable_id_mul_gaussianPDFReal_volume :
    Integrable (fun z : ℝ => z * gaussianPDFReal 0 1 z) volume := by
  have h_id_integrable : Integrable (id : ℝ → ℝ) (gaussianReal (0 : ℝ) 1) := by
    have h_memLp : MemLp (id : ℝ → ℝ) 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal 2
    exact (h_memLp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable le_rfl
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : ℝ≥0) ≠ 0)] at h_id_integrable
  have h_pdf_meas : Measurable (gaussianPDF (0 : ℝ) 1) := by
    unfold gaussianPDF; fun_prop
  have h_pdf_lt_top : ∀ᵐ z ∂(volume : Measure ℝ), gaussianPDF (0 : ℝ) 1 z < ∞ := by
    refine ae_of_all _ (fun z => ?_)
    unfold gaussianPDF; exact ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' h_pdf_meas h_pdf_lt_top] at h_id_integrable
  have h_eq : (fun z : ℝ => (gaussianPDF (0 : ℝ) 1 z).toReal • id z)
            = (fun z : ℝ => z * gaussianPDFReal 0 1 z) := by
    funext z
    show (gaussianPDF (0 : ℝ) 1 z).toReal • z = z * gaussianPDFReal 0 1 z
    unfold gaussianPDF
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp [smul_eq_mul, mul_comm]
  rwa [h_eq] at h_id_integrable

/-! ### Truncated first moment of the standard normal -/

/-- **Truncated mean** of `N(0, 1)` on `(a, ∞)`:
`∫ z in Ioi a, z · ϕ(z) dz = ϕ(a)`.

Proved via FTC for improper integrals (`integral_Ioi_of_hasDerivAt_of_tendsto`)
using the antiderivative `z ↦ -ϕ(z)` of `z ↦ z · ϕ(z)`, and the fact that
`ϕ(z) → 0` as `z → ∞`. -/
lemma integral_id_mul_gaussianPDFReal_Ioi (a : ℝ) :
    ∫ z in Set.Ioi a, z * gaussianPDFReal 0 1 z = gaussianPDFReal 0 1 a := by
  -- Antiderivative of z · ϕ(0,1,z) is -ϕ(0,1,z)
  have h_deriv : ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun z' => -gaussianPDFReal 0 1 z') (x * gaussianPDFReal 0 1 x) x := by
    intro x _; exact hasDerivAt_neg_gaussianPDFReal_zero_one x
  have h_cont : ContinuousWithinAt (fun z' : ℝ => -gaussianPDFReal 0 1 z') (Set.Ici a) a := by
    have : Continuous fun z' : ℝ => -gaussianPDFReal 0 1 z' := by
      unfold gaussianPDFReal; fun_prop
    exact this.continuousWithinAt
  have h_int : IntegrableOn (fun z' : ℝ => z' * gaussianPDFReal 0 1 z') (Set.Ioi a) volume := by
    have h_full : Integrable (fun z' : ℝ => z' * gaussianPDFReal 0 1 z') volume :=
      integrable_id_mul_gaussianPDFReal_volume
    exact h_full.integrableOn
  have h_lim : Tendsto (fun z' : ℝ => -gaussianPDFReal 0 1 z') atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 from neg_zero.symm]
    refine Tendsto.neg ?_
    -- gaussianPDFReal 0 1 z = (sqrt(2π))⁻¹ · exp(-z²/2). Both factors handled separately.
    have h_atBot : Tendsto (fun z : ℝ => -(z - 0)^2/2) atTop atBot := by
      have h_sq : Tendsto (fun z : ℝ => z^2) atTop atTop :=
        tendsto_pow_atTop two_ne_zero
      have h_sub : Tendsto (fun z : ℝ => (z - 0)^2) atTop atTop := by simpa using h_sq
      have h_neg : Tendsto (fun z : ℝ => -((z - 0)^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h_sub
      have h_div := h_neg.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      simpa using h_div
    have h_exp : Tendsto (fun z : ℝ => Real.exp (-(z - 0)^2/2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_atBot
    have h_mul := h_exp.const_mul ((Real.sqrt (2 * π))⁻¹ : ℝ)
    rw [mul_zero] at h_mul
    convert h_mul using 1
    funext z; unfold gaussianPDFReal; simp [NNReal.coe_one]
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_int h_lim
  -- hres : ∫ z in Ioi a, z * pdf z = 0 - (-pdf a) = pdf a
  linarith [hres]

/-! ### Bachelier model hypothesis -/

/-- Bachelier model risk-neutral hypothesis: the terminal price `S_T = S_0 + σ √T · Z`
with `Z ~ N(0, 1)`. The asset follows arithmetic Brownian motion (no exponential). -/
structure BachelierHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S_0 K σ T : ℝ) (Z : Ω → ℝ) : Prop where
  K_pos : 0 < K
  σ_pos : 0 < σ
  T_pos : 0 < T
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- Bachelier `d`: dimensionless distance to the strike. -/
noncomputable def bachelierD (S_0 K σ T : ℝ) : ℝ :=
  (S_0 - K) / (σ * Real.sqrt T)

/-- Bachelier terminal price `S_T(z) = S_0 + σ √T · z`. -/
noncomputable def bachelierTerminal (S_0 σ T : ℝ) (z : ℝ) : ℝ :=
  S_0 + σ * Real.sqrt T * z

/-- Exercise-region identification for the Bachelier model: `S_T(z) > K ↔ z > -d`. -/
private lemma bachelierTerminal_gt_K_iff {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    bachelierTerminal S_0 σ T z > K ↔ z > -bachelierD S_0 K σ T := by
  have h_σsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  unfold bachelierTerminal bachelierD
  have h_neg_eq : -((S_0 - K) / (σ * Real.sqrt T)) = (K - S_0) / (σ * Real.sqrt T) := by
    field_simp; ring
  constructor
  · intro h
    rw [h_neg_eq, gt_iff_lt, div_lt_iff₀ h_σsqT_pos, mul_comm]
    linarith
  · intro h
    rw [h_neg_eq, gt_iff_lt, div_lt_iff₀ h_σsqT_pos, mul_comm] at h
    linarith

/-- `max(S_T(z) - K, 0)` as an indicator on `Ioi(-d)`. -/
private lemma bachelier_max_payoff_eq_indicator {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    max (bachelierTerminal S_0 σ T z - K) 0 =
      (Set.Ioi (-bachelierD S_0 K σ T)).indicator
        (fun z' => bachelierTerminal S_0 σ T z' - K) z := by
  by_cases h : z ∈ Set.Ioi (-bachelierD S_0 K σ T)
  · rw [Set.indicator_of_mem h]
    have hST : bachelierTerminal S_0 σ T z > K :=
      (bachelierTerminal_gt_K_iff hK hσ hT z).mpr h
    exact max_eq_left (sub_nonneg.mpr hST.le)
  · rw [Set.indicator_of_notMem h]
    have hz_le : z ≤ -bachelierD S_0 K σ T := not_lt.mp h
    have hST_le : bachelierTerminal S_0 σ T z ≤ K := by
      by_contra hcontra
      exact h ((bachelierTerminal_gt_K_iff hK hσ hT z).mp (not_le.mp hcontra))
    exact max_eq_right (sub_nonpos.mpr hST_le)

/-! ### Bachelier call pricing formula -/

/-- **Bachelier European call pricing formula.**

For an asset whose risk-neutral dynamics are arithmetic Brownian motion
(`bachelierTerminal(z) = S_0 + σ √T · z` with `Z ~ N(0, 1)`),
the expected payoff of the European call `max(S_T - K, 0)` is

    E_Q[max(S_T - K, 0)] = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`.

Real derivation: HasLaw transfer to standard normal,
`max(S_T - K, 0) = 1_{Ioi(-d)}(z) · σ √T · (z + d)`,
then split into `σ √T · ϕ(d)` (the truncated first moment via FTC) and
`(S_0 - K) · Φ(d)` (the cumulative-tail probability). -/
theorem bachelier_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K σ T : ℝ} {Z : Ω → ℝ}
    (h : BachelierHyp Q S_0 K σ T Z) :
    ∫ ω, max (bachelierTerminal S_0 σ T (Z ω) - K) 0 ∂Q
      = (S_0 - K) * Phi (bachelierD S_0 K σ T) +
        σ * Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S_0 K σ T) := by
  obtain ⟨hK, hσ, hT, hZ⟩ := h
  set d : ℝ := bachelierD S_0 K σ T with d_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_σsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ hsqrT_pos
  have h_σsqT_ne : σ * Real.sqrt T ≠ 0 := h_σsqT_pos.ne'
  have h_payoff_meas : Measurable fun z : ℝ => max (bachelierTerminal S_0 σ T z - K) 0 := by
    unfold bachelierTerminal; fun_prop
  -- HasLaw transfer + convert to volume integral
  rw [show (fun ω => max (bachelierTerminal S_0 σ T (Z ω) - K) 0)
        = (fun z => max (bachelierTerminal S_0 σ T z - K) 0) ∘ Z from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- max → indicator on Ioi(-d)
  rw [show (fun z : ℝ => gaussianPDFReal 0 1 z • max (bachelierTerminal S_0 σ T z - K) 0)
        = (Set.Ioi (-d)).indicator
            (fun z => gaussianPDFReal 0 1 z * (bachelierTerminal S_0 σ T z - K)) from
      funext (fun z => by
        rw [smul_eq_mul, bachelier_max_payoff_eq_indicator hK hσ hT z]
        by_cases hz : z ∈ Set.Ioi (-d)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero])]
  rw [integral_indicator measurableSet_Ioi]
  -- Rewrite pdf · (S_T(z) - K) = pdf · (σ√T · z + (S_0 - K))
  --                            = σ√T · z · pdf + (S_0 - K) · pdf
  have h_split : ∀ z : ℝ,
      gaussianPDFReal 0 1 z * (bachelierTerminal S_0 σ T z - K)
        = σ * Real.sqrt T * (z * gaussianPDFReal 0 1 z) +
          (S_0 - K) * gaussianPDFReal 0 1 z := by
    intro z; unfold bachelierTerminal; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ => h_split z)]
  -- Integrability and split
  have h_int_pdf : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi (-d)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have h_int_z_pdf : IntegrableOn (fun z : ℝ => z * gaussianPDFReal 0 1 z)
      (Set.Ioi (-d)) volume := integrable_id_mul_gaussianPDFReal_volume.integrableOn
  rw [integral_add (h_int_z_pdf.const_mul _) (h_int_pdf.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  -- ∫ pdf on Ioi(-d) = Φ(d), ∫ z·pdf on Ioi(-d) = pdf(0,1,-d) = pdf(0,1,d)
  rw [integral_id_mul_gaussianPDFReal_Ioi]
  have h_pdf_int_eq :
      ∫ z in Set.Ioi (-d), gaussianPDFReal 0 1 z = Phi d := by
    rw [show ∫ z in Set.Ioi (-d), gaussianPDFReal 0 1 z
            = (gaussianReal (0 : ℝ) 1 (Set.Ioi (-d))).toReal by
        rw [gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0) (Set.Ioi (-d))]
        exact (ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
          (fun _ _ => gaussianPDFReal_nonneg _ _ _))).symm,
        gaussianReal_Ioi_toReal, neg_neg]
  rw [h_pdf_int_eq]
  -- Final: σ√T · pdf(0,1,-d) + (S_0 - K) · Φ(d), and pdf(0,1,-d) = pdf(0,1,d)
  have h_pdf_neg : gaussianPDFReal 0 1 (-d) = gaussianPDFReal 0 1 d := by
    unfold gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [show (-d)^2 = d^2 from by ring]
  rw [h_pdf_neg]
  ring

end QuantFin
