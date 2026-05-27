/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion
import QuantFin.Foundations.ItoIsometryAdapted
import QuantFin.Foundations.GaussianMoments

/-!
# The L² quadratic variation of Brownian motion

The keystone behind Itô's lemma: along the uniform partition of `[0, t]` into `n` pieces,
the sum of squared Brownian increments converges to `t` **in L²**,

  `‖∑ₖ (B_{s_{k+1}} − B_{s_k})² − t‖²_{L²} = 2 t² / n → 0`.

This is strictly stronger than the L¹/expectation form (`BrownianQuadraticVariation`,
`E[∑ₖ (ΔB_k)²] → t`), which holds from the marginal second moment alone. The L² statement
is what makes the second-order term in Itô's lemma deterministic: the *fluctuations* of the
squared increments vanish, so `(ΔB_k)² ≈ Δt_k` is exact in the mean-square limit.

## Why the rate is `2 t² / n`

Write `Yₖ = (ΔB_k)² − Δ_k` (centered). The increments over disjoint intervals are
independent (weak Markov), so the cross terms vanish and
`E[(∑ Yₖ)²] = ∑ₖ E[Yₖ²] = ∑ₖ 2 Δ_k²`. Each `E[Yₖ²] = E[(ΔB_k)⁴] − Δ_k² = 3Δ_k² − Δ_k² = 2Δ_k²`
is exactly the **Gaussian kurtosis** `E[X⁴] = 3 Var²` (`integral_pow4_gaussianReal`) — this is
the precise reason the quadratic variation is `t` and not, say, `0`. For the uniform partition
`Δ_k = t/n`, the sum is `n · 2(t/n)² = 2t²/n`.

## Main results

* `integral_increment_pow4` — `E[(B_{t₁} − B_{t₀})⁴] = 3(t₁ − t₀)²`.
-/

namespace QuantFin
namespace QuadraticVariationL2

open MeasureTheory ProbabilityTheory ItoIsometryAdapted
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

/-- **Fourth moment of a Brownian increment**: `E[(B_{t₁} − B_{t₀})⁴] = 3(t₁ − t₀)²`
for `t₀ ≤ t₁`. The increment has law `N(0, t₁ − t₀)`; push the fourth moment through that
law (`HasLaw.integral_comp`) to the Gaussian kurtosis identity `integral_pow4_gaussianReal`.
This is the source of the `2(Δt)²` mean-square fluctuation of a squared increment. -/
theorem integral_increment_pow4 {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 4 ∂μ = 3 * ((t₁ : ℝ) - t₀) ^ 2 := by
  have hmax : ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ) = (t₁ : ℝ) - t₀ := by
    rw [max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le), NNReal.coe_sub ht]
  have hcomp := (hB.hasLaw_sub t₁ t₀).integral_comp (f := fun x : ℝ => x ^ 4)
    (measurable_id.pow_const 4).aestronglyMeasurable
  simp only [Function.comp_def, Pi.sub_apply] at hcomp
  rw [hcomp, integral_pow4_gaussianReal, hmax]

/-- **Mean-square fluctuation of a squared Brownian increment**:
`E[((B_{t₁} − B_{t₀})² − (t₁ − t₀))²] = 2(t₁ − t₀)²` for `t₀ ≤ t₁`. The law-transfer of the
Gaussian identity `integral_sq_sub_var_sq_gaussianReal`. This is the per-interval `2(Δt)²`
that sums to the `2t²/n` quadratic-variation rate. -/
theorem integral_increment_sq_centered {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, ((B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) ^ 2 ∂μ = 2 * ((t₁ : ℝ) - t₀) ^ 2 := by
  have hmax : ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ) = (t₁ : ℝ) - t₀ := by
    rw [max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le), NNReal.coe_sub ht]
  have hcomp := (hB.hasLaw_sub t₁ t₀).integral_comp
    (f := fun y : ℝ => (y ^ 2 - ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ)) ^ 2) (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at hcomp
  rw [integral_sq_sub_var_sq_gaussianReal] at hcomp
  rw [hmax] at hcomp
  exact hcomp

/-- A squared increment over `[a, b] ⊆ [0, c]`, shifted by any constant, is `𝓕_c`-adapted:
it is built from `B a, B b` (`a, b ≤ c`) by difference, square, and subtraction. -/
theorem adaptedAt_increment_sq_sub {a b c : ℝ≥0} (hac : a ≤ c) (hbc : b ≤ c) (r : ℝ) :
    AdaptedAt B c (fun ω => (B b ω - B a ω) ^ 2 - r) := by
  have hincr : AdaptedAt B c (fun ω => B b ω - B a ω) :=
    (adaptedAt_eval hbc).sub (adaptedAt_eval hac)
  have hsq : AdaptedAt B c (fun ω => (B b ω - B a ω) ^ 2) := by
    simpa only [← pow_two] using hincr.mul hincr
  exact hsq.sub ⟨fun _ => r, measurable_const, rfl⟩

/-- **A centered squared Brownian increment has mean zero**: `E[(ΔB)² − (t₁−t₀)] = 0`
for `t₀ ≤ t₁`. The law-transfer of `integral_sq_sub_var_gaussianReal` — i.e. `E[(ΔB)²] = t₁−t₀`.
This is the centering that makes the cross terms vanish. -/
theorem integral_increment_centered_mean {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, ((B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) ∂μ = 0 := by
  have hmax : ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ) = (t₁ : ℝ) - t₀ := by
    rw [max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le), NNReal.coe_sub ht]
  have hcomp := (hB.hasLaw_sub t₁ t₀).integral_comp
    (f := fun y : ℝ => y ^ 2 - ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ)) (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at hcomp
  rw [integral_sq_sub_var_gaussianReal] at hcomp
  rw [hmax] at hcomp
  exact hcomp

/-- **Pairwise orthogonality of centered squared increments** (the vanishing cross terms).
For disjoint ordered intervals `a ≤ b ≤ c ≤ d`,
`E[((ΔB_{a,b})² − (b−a)) · ((ΔB_{c,d})² − (d−c))] = 0`. The two centered squares are functions
of the *independent* increments over `[a,b]` and `[c,d]` (weak Markov), and the second is mean
zero — so the product's expectation factorises to `(…)·0`. This is what makes the quadratic
variation's L² fluctuation a *sum* of the per-interval `2(Δt)²` terms (Pythagoras). -/
theorem integral_increment_sq_centered_cross (hBmeas : ∀ t, Measurable (B t))
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∫ ω, ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a)) * ((B d ω - B c ω) ^ 2 - ((d : ℝ) - c)) ∂μ = 0 := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set χ : Ω → ℝ := fun ω => (B b ω - B a ω) ^ 2 - ((b : ℝ) - a) with hχdef
  have hχ_adapted : AdaptedAt B c χ :=
    adaptedAt_increment_sq_sub (hab.trans hbc) hbc ((b : ℝ) - a)
  have hindep : IndepFun χ (fun ω => (B d ω - B c ω) ^ 2 - ((d : ℝ) - c)) μ := by
    have h := (adapted_indepFun_increment (μ := μ) hBmeas hcd hχ_adapted).comp
      (φ := (id : ℝ → ℝ)) (ψ := fun x => x ^ 2 - ((d : ℝ) - c)) measurable_id (by fun_prop)
    simpa [Function.comp_def] using h
  have hχm : Measurable χ := hχ_adapted.measurable hBmeas
  have hYm : Measurable (fun ω => (B d ω - B c ω) ^ 2 - ((d : ℝ) - c)) := by fun_prop
  rw [hindep.integral_fun_mul_eq_mul_integral hχm.aestronglyMeasurable hYm.aestronglyMeasurable,
      integral_increment_centered_mean hcd, mul_zero]

end QuadraticVariationL2
end QuantFin
