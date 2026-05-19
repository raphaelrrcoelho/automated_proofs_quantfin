/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tail probabilities and shifted-tail integrals of the standard normal

This file adds three convenience lemmas about the standard normal distribution
`gaussianReal 0 1` on `ℝ`:

* `gaussianReal_zero_one_Iic_neg`: the symmetry identity
  `P(Z ≤ -x) = 1 − P(Z ≤ x)` for `Z ~ N(0, 1)`, derived from the reflection
  `gaussianReal_map_neg`.
* `gaussianReal_zero_one_Ioi_toReal`: the right-tail identity
  `P(Z > a) = 1 − P(Z ≤ a)`, the trivial corollary used most often in practice.
* `exp_mul_gaussianPDFReal_zero_one`: the completing-the-square identity
  `exp(c · z) · pdf(0, 1, z) = exp(c² / 2) · pdf(c, 1, z)`. This is the
  algebraic content of the change of variables `c · z − z² / 2 = c² / 2 −
  (z − c)² / 2`.
* `integral_exp_mul_gaussianPDFReal_zero_one_Ioi`: the shifted-tail integral
  `∫ z in Ioi a, exp(c · z) · pdf(0, 1, z) dz = exp(c² / 2) · P(Z ≤ c − a)`,
  obtained by combining the completing-the-square identity with the location-shift
  `gaussianReal_map_add_const`. This is the workhorse identity used in
  derivations of the Black–Scholes formula.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Symmetry of the standard normal around zero: `P(Z ≤ -x) = 1 − P(Z ≤ x)`
for `Z ~ N(0, 1)`. -/
lemma gaussianReal_zero_one_Iic_neg (x : ℝ) :
    (gaussianReal 0 1 (Set.Iic (-x))).toReal
      = 1 - (gaussianReal 0 1 (Set.Iic x)).toReal := by
  -- Reflection invariance: gaussianReal 0 1 is invariant under negation.
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun y => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  -- Iic(-x) under negation pulls back to Ici x.
  have h_preimage : (fun y : ℝ => -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext y; simp only [Set.mem_preimage, Set.mem_Iic, neg_le_neg_iff, Set.mem_Ici]
  have h_eq : gaussianReal (0 : ℝ) 1 (Set.Iic (-x)) = gaussianReal 0 1 (Set.Ici x) := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, h_preimage]
  -- `NoAtoms`: under the (absolutely continuous) Gaussian, `{x}` has measure zero,
  -- so `P(Iic x) = P(Iio x)`, and then `P(Iio x) + P(Ici x) = 1`.
  have h_one_nz : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  haveI : NoAtoms (gaussianReal (0 : ℝ) 1) := noAtoms_gaussianReal h_one_nz
  have h_iio_iic : gaussianReal (0 : ℝ) 1 (Set.Iic x) = gaussianReal 0 1 (Set.Iio x) := by
    have h_decomp : Set.Iic x = Set.Iio x ∪ {x} := by
      ext y
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff,
        le_iff_lt_or_eq, eq_comm]
    have h_disj : Disjoint (Set.Iio x) ({x} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr (lt_irrefl x)
    rw [h_decomp, measure_union h_disj (measurableSet_singleton _),
        measure_singleton, add_zero]
  have h_total :
      gaussianReal (0 : ℝ) 1 (Set.Iio x) + gaussianReal 0 1 (Set.Ici x) = 1 := by
    rw [← measure_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        Set.Iio_union_Ici, measure_univ]
  have h_iic_finite : gaussianReal (0 : ℝ) 1 (Set.Iic x) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_sum :
      gaussianReal (0 : ℝ) 1 (Set.Iic x) + gaussianReal 0 1 (Set.Ici x) = 1 := by
    rw [h_iio_iic]; exact h_total
  have h_eq_sub :
      gaussianReal (0 : ℝ) 1 (Set.Ici x) = 1 - gaussianReal 0 1 (Set.Iic x) := by
    refine ENNReal.eq_sub_of_add_eq h_iic_finite ?_
    rw [add_comm]; exact h_sum
  rw [h_eq, h_eq_sub,
      ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp)]
  rfl

/-- Right tail of the standard normal: `P(Z > a) = 1 − P(Z ≤ a)`. -/
lemma gaussianReal_zero_one_Ioi_toReal (a : ℝ) :
    (gaussianReal 0 1 (Set.Ioi a)).toReal
      = 1 - (gaussianReal 0 1 (Set.Iic a)).toReal := by
  have h_compl : Set.Ioi a = (Set.Iic a)ᶜ := by ext y; simp
  rw [h_compl, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp),
      ENNReal.toReal_one]

/-- The exponential-shift (completing-the-square) identity for the standard
normal density:
`exp(c · z) · gaussianPDFReal 0 1 z = exp(c² / 2) · gaussianPDFReal c 1 z`.

This is the algebraic content of the change of variables
`c · z + (- (z - 0)² / 2) = c² / 2 + (- (z - c)² / 2)`. -/
lemma exp_mul_gaussianPDFReal_zero_one (c z : ℝ) :
    Real.exp (c * z) * gaussianPDFReal 0 1 z
      = Real.exp (c ^ 2 / 2) * gaussianPDFReal c 1 z := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  have key : c * z + -(z - 0) ^ 2 / 2 = c ^ 2 / 2 + -(z - c) ^ 2 / 2 := by ring
  set P : ℝ := (Real.sqrt (2 * π))⁻¹ with P_def
  calc Real.exp (c * z) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - 0) ^ 2 / 2))
      = P * (Real.exp (c * z) * Real.exp (-(z - 0) ^ 2 / 2)) := by rw [P_def]; ring
    _ = P * Real.exp (c * z + -(z - 0) ^ 2 / 2) := by rw [Real.exp_add]
    _ = P * Real.exp (c ^ 2 / 2 + -(z - c) ^ 2 / 2) := by rw [key]
    _ = P * (Real.exp (c ^ 2 / 2) * Real.exp (-(z - c) ^ 2 / 2)) := by rw [Real.exp_add]
    _ = Real.exp (c ^ 2 / 2) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - c) ^ 2 / 2)) := by
        rw [P_def]; ring

/-- Shifted-tail integral of the standard normal:
`∫ z in Ioi a, exp(c · z) · pdf(0, 1, z) dz = exp(c² / 2) · P(Z ≤ c − a)`.

Obtained by combining `exp_mul_gaussianPDFReal_zero_one` (completing the square)
with the location shift `gaussianReal_map_add_const`. This is the workhorse
identity used in derivations of the Black–Scholes call-pricing formula. -/
lemma integral_exp_mul_gaussianPDFReal_zero_one_Ioi (a c : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (c * z) * gaussianPDFReal 0 1 z
      = Real.exp (c ^ 2 / 2) * (gaussianReal 0 1 (Set.Iic (c - a))).toReal := by
  rw [setIntegral_congr_fun measurableSet_Ioi
        (fun z _ => exp_mul_gaussianPDFReal_zero_one c z), integral_const_mul]
  congr 1
  have h_int_eq : ∫ z in Set.Ioi a, gaussianPDFReal c 1 z
      = (gaussianReal c (1 : ℝ≥0) (Set.Ioi a)).toReal := by
    rw [gaussianReal_apply_eq_integral c (one_ne_zero : (1 : ℝ≥0) ≠ 0) (Set.Ioi a)]
    exact (ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
      (fun _ _ => gaussianPDFReal_nonneg _ _ _))).symm
  have h_shift :
      gaussianReal c (1 : ℝ≥0) (Set.Ioi a) = gaussianReal 0 1 (Set.Ioi (a - c)) := by
    have hmap : (gaussianReal (0 : ℝ) 1).map (fun y => y + c) = gaussianReal c 1 := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi, sub_lt_iff_lt_add, add_comm]
  rw [h_int_eq, h_shift, gaussianReal_zero_one_Ioi_toReal,
      ← gaussianReal_zero_one_Iic_neg, neg_sub]

end ProbabilityTheory
