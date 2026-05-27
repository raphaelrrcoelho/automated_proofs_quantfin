/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.Moment

/-!
# Gaussian moments

Small, shared moment facts for real Gaussians used across the Brownian-motion
foundations (`BrownianMartingale`, `BrownianQuadraticVariation`, the L² quadratic
variation). Kept in one place so each identity is proved exactly once.

The fourth moment reuses Degenne's `(2n)`-th central-moment formula
(`ProbabilityTheory.centralMoment_two_mul_gaussianReal`) rather than re-deriving the
Gaussian integral — coherence with the upstream `brownian-motion` package.
-/

@[expose] public section

namespace QuantFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`.
For a mean-zero law the second moment is the variance (`variance_id_gaussianReal`). -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

/-- Fourth moment of a centered real Gaussian: `∫ x, x⁴ ∂(gaussianReal 0 v) = 3 v²`
(the kurtosis identity `E[X⁴] = 3·Var²`, the source of the `2(Δt)²` variance of squared
Brownian increments). Via the `(2n)`-th central-moment formula
`centralMoment_two_mul_gaussianReal` at `n = 2` (`(2·2−1)!! = 3!! = 3`). -/
lemma integral_pow4_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hmean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  have hcm : centralMoment id 4 (gaussianReal 0 v) = ∫ x, x ^ 4 ∂(gaussianReal 0 v) := by
    unfold centralMoment
    simp only [id_eq, hmean, Pi.pow_apply, Pi.sub_apply, sub_zero]
  have key := centralMoment_two_mul_gaussianReal 0 (NNReal.sqrt v) 2
  rw [NNReal.sq_sqrt] at key
  have h4 : ((NNReal.sqrt v : ℝ)) ^ (2 * 2) = (v : ℝ) ^ 2 := by
    rw [pow_mul, ← NNReal.coe_pow, NNReal.sq_sqrt]
  have hdf : (2 * 2 - 1 : ℕ).doubleFactorial = 3 := rfl
  rw [← hcm, key, h4, hdf]
  push_cast
  ring

/-- **Mean-square fluctuation of a squared centered Gaussian**: `∫ (x² − v)² ∂N(0,v) = 2v²`,
i.e. `Var(X²) = 2·Var(X)²` for `X ~ N(0,v)`. This is the kurtosis `E[X⁴] = 3v²` minus
`(E[X²])² = v²`. It is exactly the per-interval term `E[((ΔB)² − Δt)²] = 2(Δt)²` whose sum
gives the `2t²/n` rate of the L² quadratic variation. -/
lemma integral_sq_sub_var_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ^ 2 ∂(gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hint4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow (p := 4) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs] at h
    have hfe : (fun x : ℝ => |x| ^ 4) = fun x : ℝ => x ^ 4 :=
      funext fun x => by rw [pow_abs, abs_of_nonneg (by positivity)]
    rwa [hfe] at h
  have hcm2 : Integrable (fun x : ℝ => 2 * (v : ℝ) * x ^ 2) (gaussianReal 0 v) :=
    hint2.const_mul (2 * (v : ℝ))
  have hdiff : Integrable (fun a : ℝ => a ^ 4 - 2 * (v : ℝ) * a ^ 2) (gaussianReal 0 v) :=
    hint4.sub hcm2
  have hexpand : ∀ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 = x ^ 4 - 2 * (v : ℝ) * x ^ 2 + (v : ℝ) ^ 2 :=
    fun x => by ring
  have huniv : (gaussianReal 0 v).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand),
      integral_add hdiff (integrable_const _),
      integral_sub hint4 hcm2,
      integral_pow4_gaussianReal, integral_const_mul, integral_sq_gaussianReal, integral_const,
      huniv]
  simp only [smul_eq_mul]
  ring

/-- **A centered squared Gaussian has mean zero**: `∫ (x² − v) ∂N(0,v) = 0`, i.e.
`E[X² − Var] = 0` for `X ~ N(0,v)`. (`E[X²] = v`.) -/
lemma integral_sq_sub_var_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ∂(gaussianReal 0 v) = 0 := by
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have huniv : (gaussianReal 0 v).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [integral_sub hint2 (integrable_const _), integral_sq_gaussianReal, integral_const, huniv,
      one_smul, sub_self]

end QuantFin
