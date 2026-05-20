/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Wiener integral — Itô isometry kernel

Itô isometry for step-function integrands against a pre-Brownian motion
`B : ℝ≥0 → Ω → ℝ` (Degenne's `IsPreBrownian` from
`BrownianMotion.Gaussian.BrownianMotion`):

* `wiener_step_isometry`: for a single step `c · 𝟙_{(s, t]}`,
  `∫ ω, (c · (B_t ω − B_s ω))² ∂μ = c² · (t − s)`.
* `wiener_finset_isometry`: for a monotone partition `p : Fin (n+1) → ℝ≥0`
  and coefficients `c : Fin n → ℝ`,
  `∫ ω, (∑ k, c k · (B (p k.succ) ω − B (p k.castSucc) ω))² ∂μ
      = ∑ k, c k² · (p k.succ − p k.castSucc)`.

This file contains the step-function kernel. The extension to
`Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))` is developed in
`HybridVerify.WienerIntegralL2`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section IsPreBrownian

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

omit [IsProbabilityMeasure μ] in
/-- For `s ≤ t : ℝ≥0`, the increment `B t − B s` has law `gaussianReal 0 (t − s)`. -/
private lemma hasLaw_increment {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (B t - B s) (gaussianReal 0 (t - s)) μ := by
  have hL := IsPreBrownian.hasLaw_sub (X := B) (P := μ) t s
  have hmax : max (t - s) (s - t) = t - s := by
    rw [tsub_eq_zero_iff_le.mpr hst, max_eq_left (zero_le _)]
  rwa [hmax] at hL

omit [IsProbabilityMeasure μ] in
/-- The increment `B t − B s` has mean zero. -/
private lemma integral_increment_eq_zero {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
  have h := (hasLaw_increment (B := B) (μ := μ) hst).integral_eq
  simpa using h.trans integral_id_gaussianReal

omit [IsProbabilityMeasure μ] in
/-- The increment `B t − B s` has variance `t − s`. -/
private lemma variance_increment {s t : ℝ≥0} (hst : s ≤ t) :
    Var[fun ω => B t ω - B s ω; μ] = ((t - s : ℝ≥0) : ℝ) := by
  have h := (hasLaw_increment (B := B) (μ := μ) hst).variance_eq
  simpa using h.trans variance_id_gaussianReal

omit [IsProbabilityMeasure μ] in
/-- The increment `B t − B s` is in `L²`. -/
private lemma memLp_increment_two (s t : ℝ≥0) :
    MemLp (fun ω => B t ω - B s ω) 2 μ :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

omit [IsProbabilityMeasure μ] in
/-- Wiener step-integral isometry. For a pre-Brownian motion `B`, scalar `c`,
and `s ≤ t : ℝ≥0`, the single-step Wiener integral `c · (B_t − B_s)` satisfies

  `∫ ω, (c · (B_t ω − B_s ω))² ∂μ = c² · (t − s)`.

This is the kernel of the Itô isometry: for a step function `f = c · 𝟙_{(s, t]}`,
both `E[(∫ f dB)²] = c² (t − s)` and `∫ f² ds = c² (t − s)`. -/
theorem wiener_step_isometry (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (c * (B t ω - B s ω)) ^ 2 ∂μ = c ^ 2 * ((t - s : ℝ≥0) : ℝ) := by
  simp_rw [mul_pow]
  rw [integral_const_mul]
  congr 1
  rw [show (fun ω => (B t ω - B s ω) ^ 2) = fun ω => (B t - B s) ω ^ 2 from rfl,
      ← variance_of_integral_eq_zero (hasLaw_increment (B := B) hst).aemeasurable
        (by simpa using integral_increment_eq_zero (B := B) hst)]
  simpa using variance_increment (B := B) (μ := μ) hst

/-- Finset Wiener isometry. For a monotone partition `p : Fin (n+1) → ℝ≥0`
and coefficients `c : Fin n → ℝ`, the Wiener step-sum

  `I ω = ∑ k, c k · (B (p k.succ) ω − B (p k.castSucc) ω)`

satisfies the discrete Itô isometry

  `E[I²] = ∑ k, c k² · (p k.succ − p k.castSucc)`. -/
theorem wiener_finset_isometry
    {n : ℕ} (p : Fin (n + 1) → ℝ≥0) (hp : Monotone p) (c : Fin n → ℝ) :
    ∫ ω, (∑ k : Fin n, c k * (B (p k.succ) ω - B (p k.castSucc) ω)) ^ 2 ∂μ
      = ∑ k : Fin n, c k ^ 2 * ((p k.succ - p k.castSucc : ℝ≥0) : ℝ) := by
  set X : Fin n → Ω → ℝ :=
    fun k ω => c k * (B (p k.succ) ω - B (p k.castSucc) ω) with hX
  have hpk : ∀ k : Fin n, p k.castSucc ≤ p k.succ :=
    fun k => hp (Fin.castSucc_le_succ k)
  have h_memLp : ∀ k, MemLp (X k) 2 μ := fun k =>
    (memLp_increment_two (B := B) (μ := μ) (p k.castSucc) (p k.succ)).const_mul (c k)
  have h_pair :
      Set.Pairwise (↑(Finset.univ : Finset (Fin n))) (fun i j => X i ⟂ᵢ[μ] X j) := by
    intro i _ j _ hij
    exact ((IsPreBrownian.hasIndepIncrements (X := B) (P := μ) n p hp).comp
      (fun k x => c k * x) (fun _ => measurable_const.mul measurable_id)).indepFun hij
  have h_mean_sum : ∫ ω, (∑ k : Fin n, X k) ω ∂μ = 0 := by
    simp_rw [Finset.sum_apply, integral_finset_sum _
      (fun k _ => (h_memLp k).integrable one_le_two)]
    exact Finset.sum_eq_zero fun k _ => by
      simp [hX, integral_const_mul, integral_increment_eq_zero (B := B) (hpk k)]
  calc ∫ ω, (∑ k : Fin n, X k ω) ^ 2 ∂μ
      = ∫ ω, ((∑ k : Fin n, X k) ω) ^ 2 ∂μ := by simp_rw [Finset.sum_apply]
    _ = Var[∑ k : Fin n, X k; μ] :=
        (variance_of_integral_eq_zero
          (Finset.aemeasurable_sum _ fun k _ => (h_memLp k).aemeasurable) h_mean_sum).symm
    _ = ∑ k : Fin n, Var[X k; μ] :=
        IndepFun.variance_sum (fun k _ => h_memLp k) h_pair
    _ = ∑ k : Fin n, c k ^ 2 * ((p k.succ - p k.castSucc : ℝ≥0) : ℝ) :=
        Finset.sum_congr rfl fun k _ => by
          simp [hX, variance_const_mul, variance_increment (B := B) (μ := μ) (hpk k)]

end IsPreBrownian

end HybridVerify
