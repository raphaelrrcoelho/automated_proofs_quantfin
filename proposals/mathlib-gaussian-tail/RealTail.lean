/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tail probabilities and shifted-tail integrals of real Gaussian measures

This file adds four convenience lemmas about `gaussianReal μ v` on `ℝ`:

* `gaussianReal_Iic_neg`: reflection symmetry of centered Gaussians,
  `P(Z ≤ -x) = 1 − P(Z ≤ x)` for `Z ~ N(0, v)` (any `v ≠ 0`).
* `gaussianReal_Ioi_toReal`: the right-tail identity
  `P(Z > a) = 1 − P(Z ≤ a)` for any `Z ~ N(μ, v)`.
* `exp_mul_gaussianPDFReal`: the completing-the-square identity
  `exp(c · z) · pdf(μ, v, z) = exp(c·μ + c²·v/2) · pdf(μ + c·v, v, z)`.
* `integral_exp_mul_gaussianPDFReal_Ioi`: the shifted-tail integral
  `∫ z in Ioi a, exp(c · z) · pdf(μ, v, z) dz = exp(c·μ + c²·v/2) · P_{N(μ+c·v, v)}(Ioi a)`.

These are Gaussian tail and exponential-tilting identities for real Gaussian
measures.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Total mass of `gaussianReal μ v` on a left-infinite interval is at most one. -/
private lemma gaussianReal_Iic_le_one (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianReal μ v (Set.Iic x) ≤ 1 := by
  rw [show (1 : ℝ≥0∞) = gaussianReal μ v Set.univ from measure_univ.symm]
  exact measure_mono (Set.subset_univ _)

/-- Reflection symmetry of centered real Gaussians: `P(Z ≤ -x) = 1 − P(Z ≤ x)`
for `Z ~ N(0, v)` whenever `v ≠ 0`. -/
lemma gaussianReal_Iic_neg {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal 0 v (Set.Iic (-x))).toReal
      = 1 - (gaussianReal 0 v (Set.Iic x)).toReal := by
  -- Reflection invariance: gaussianReal 0 v is invariant under negation.
  have hmap : (gaussianReal (0 : ℝ) v).map (fun y => -y) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  -- Iic(-x) under negation pulls back to Ici x.
  have h_preimage : (fun y : ℝ => -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, neg_le_neg_iff, Set.mem_Ici]
  have h_eq : gaussianReal (0 : ℝ) v (Set.Iic (-x)) = gaussianReal 0 v (Set.Ici x) := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, h_preimage]
  -- `NoAtoms`: under the (absolutely continuous) Gaussian, `{x}` has measure zero,
  -- so `P(Iic x) = P(Iio x)`, and then `P(Iio x) + P(Ici x) = 1`.
  haveI : NoAtoms (gaussianReal (0 : ℝ) v) := noAtoms_gaussianReal hv
  have h_iio_iic : gaussianReal (0 : ℝ) v (Set.Iic x) = gaussianReal 0 v (Set.Iio x) := by
    have h_decomp : Set.Iic x = Set.Iio x ∪ {x} := by
      ext y
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff,
        le_iff_lt_or_eq, eq_comm]
    have h_disj : Disjoint (Set.Iio x) ({x} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr (lt_irrefl x)
    rw [h_decomp, measure_union h_disj (measurableSet_singleton _),
        measure_singleton, add_zero]
  have h_total :
      gaussianReal (0 : ℝ) v (Set.Iio x) + gaussianReal 0 v (Set.Ici x) = 1 := by
    rw [← measure_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        Set.Iio_union_Ici, measure_univ]
  have h_iic_finite : gaussianReal (0 : ℝ) v (Set.Iic x) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_sum :
      gaussianReal (0 : ℝ) v (Set.Iic x) + gaussianReal 0 v (Set.Ici x) = 1 := by
    rw [h_iio_iic]
    exact h_total
  have h_eq_sub :
      gaussianReal (0 : ℝ) v (Set.Ici x) = 1 - gaussianReal 0 v (Set.Iic x) := by
    refine ENNReal.eq_sub_of_add_eq h_iic_finite ?_
    rw [add_comm]
    exact h_sum
  rw [h_eq, h_eq_sub, ENNReal.toReal_sub_of_le (gaussianReal_Iic_le_one _ _ _) (by simp)]
  rfl

/-- Right tail of a real Gaussian: `P(Z > a) = 1 − P(Z ≤ a)`. -/
lemma gaussianReal_Ioi_toReal (μ : ℝ) (v : ℝ≥0) (a : ℝ) :
    (gaussianReal μ v (Set.Ioi a)).toReal
      = 1 - (gaussianReal μ v (Set.Iic a)).toReal := by
  have h_compl : Set.Ioi a = (Set.Iic a)ᶜ := by
    ext y
    simp
  rw [h_compl, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le (gaussianReal_Iic_le_one _ _ _) (by simp),
      ENNReal.toReal_one]

/-- Completing the square for the Gaussian density:
`exp(c · z) · gaussianPDFReal μ v z = exp(c·μ + c²·v/2) · gaussianPDFReal (μ + c·v) v z`.

This is the algebraic content of the change of variables
`c · z − (z − μ)² / (2v) = c·μ + c²·v/2 − (z − (μ + c·v))² / (2v)`.

Holds for all `v : ℝ≥0`; in the `v = 0` Dirac case both sides are `_ * 0`. -/
lemma exp_mul_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (c z : ℝ) :
    Real.exp (c * z) * gaussianPDFReal μ v z
      = Real.exp (c * μ + c ^ 2 * (v : ℝ) / 2) * gaussianPDFReal (μ + c * v) v z := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianPDFReal_zero_var]
  -- v ≠ 0
  have hv_pos : (0 : ℝ) < (v : ℝ) :=
    lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm (by exact_mod_cast hv))
  unfold gaussianPDFReal
  set P : ℝ := (Real.sqrt (2 * π * (v : ℝ)))⁻¹ with P_def
  have key : c * z + -(z - μ) ^ 2 / (2 * (v : ℝ))
           = (c * μ + c ^ 2 * (v : ℝ) / 2) + -(z - (μ + c * (v : ℝ))) ^ 2 / (2 * (v : ℝ)) := by
    field_simp
    ring
  calc Real.exp (c * z) * (P * Real.exp (-(z - μ) ^ 2 / (2 * (v : ℝ))))
      = P * (Real.exp (c * z) * Real.exp (-(z - μ) ^ 2 / (2 * (v : ℝ)))) := by ring
    _ = P * Real.exp (c * z + -(z - μ) ^ 2 / (2 * (v : ℝ))) := by rw [Real.exp_add]
    _ = P * Real.exp ((c * μ + c ^ 2 * (v : ℝ) / 2) +
          -(z - (μ + c * (v : ℝ))) ^ 2 / (2 * (v : ℝ))) := by rw [key]
    _ = P * (Real.exp (c * μ + c ^ 2 * (v : ℝ) / 2)
          * Real.exp (-(z - (μ + c * (v : ℝ))) ^ 2 / (2 * (v : ℝ)))) := by rw [Real.exp_add]
    _ = Real.exp (c * μ + c ^ 2 * (v : ℝ) / 2)
          * (P * Real.exp (-(z - (μ + c * (v : ℝ))) ^ 2 / (2 * (v : ℝ)))) := by ring

/-- Shifted-tail integral of a real Gaussian density:
`∫ z in Ioi a, exp(c · z) · pdf(μ, v, z) dz = exp(c·μ + c²·v/2) · P_{N(μ+c·v, v)}(Ioi a)`.

Obtained by combining `exp_mul_gaussianPDFReal` (completing the square) with the
defining identity `gaussianReal μ v (Ioi a) = ENNReal.ofReal (∫_{Ioi a} pdf(μ, v, z) dz)`.
Requires `v ≠ 0` because for the Dirac case `v = 0` the LHS is `0` (the PDF vanishes)
but the RHS picks up a contribution `exp(c·μ) · 𝟙_{Ioi a}(μ)`, so the identity fails.

Specialising to `μ = 0`, `v = 1` gives
`exp(c²/2) · P_{N(0,1)}(Ioi (a − c))`, which combined with `gaussianReal_Iic_neg`
and `gaussianReal_Ioi_toReal` yields the standard reflected-tail form
`exp(c²/2) · P_{N(0,1)}(Iic (c − a))`. -/
lemma integral_exp_mul_gaussianPDFReal_Ioi {v : ℝ≥0} (hv : v ≠ 0) (μ a c : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (c * z) * gaussianPDFReal μ v z
      = Real.exp (c * μ + c ^ 2 * (v : ℝ) / 2)
          * (gaussianReal (μ + c * v) v (Set.Ioi a)).toReal := by
  rw [setIntegral_congr_fun measurableSet_Ioi
        (fun z _ => exp_mul_gaussianPDFReal μ v c z), integral_const_mul]
  congr 1
  rw [gaussianReal_apply_eq_integral (μ + c * v) hv (Set.Ioi a)]
  exact (ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
    (fun _ _ => gaussianPDFReal_nonneg _ _ _))).symm

end ProbabilityTheory
