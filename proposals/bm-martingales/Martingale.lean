/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import BrownianMotion.Auxiliary.HasLaw
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Martingale properties of pre-Brownian motion

For a filtered pre-Brownian motion `X`, the following are martingales w.r.t. `𝓕`:

* `X` itself (already provided as `IsPreBrownian.isMartingale` in `Gaussian/BrownianMotion.lean`)
* `t ↦ (X t)² − t`
* `t ↦ exp(α X_t − α² t / 2)` (Wald exponential), for every `α : ℝ`

## Main results

* `IsFilteredPreBrownian.squareSubTime_isMartingale`
* `IsFilteredPreBrownian.waldExponential_isMartingale`
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- For `s ≤ t : ℝ≥0`, `(max (t-s) (s-t) : ℝ) = (t : ℝ) - (s : ℝ)`. -/
private lemma NNReal.max_sub_eq_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  rw [tsub_eq_zero_of_le hst, max_eq_left (zero_le _)]; exact NNReal.coe_sub hst

/-- `∫ x, exp(α x) ∂(gaussianReal 0 v) = exp(α² v / 2)` (Gaussian MGF at mean zero). -/
private lemma integral_exp_mul_gaussianReal_zero (α : ℝ) (v : ℝ≥0) :
    ∫ x, Real.exp (α * x) ∂(gaussianReal 0 v) = Real.exp (α ^ 2 * (v : ℝ) / 2) := by
  have h := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) α
  show mgf id (gaussianReal 0 v) α = _
  rw [h]; ring_nf

/-- Second moment of a centered Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`. -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id integral_id_gaussianReal] at h_var
  exact h_var

/-- `exp(α · Z)` is integrable when `Z` has a Gaussian law. -/
private lemma integrable_exp_mul_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {m : ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal m v) P) (α : ℝ) :
    Integrable (fun ω ↦ Real.exp (α * Z ω)) P := by
  rw [show (fun ω ↦ Real.exp (α * Z ω)) = (fun x ↦ Real.exp (α * x)) ∘ Z from rfl]
  refine Integrable.comp_aemeasurable ?_ hZ_meas.aemeasurable
  rw [hZ.map_eq]; exact integrable_exp_mul_gaussianReal α

namespace IsFilteredPreBrownian

variable [hX : IsFilteredPreBrownian X 𝓕 P] [IsFiniteMeasure P]

/-- For a Borel-measurable `φ : ℝ → ℝ` with `∫ φ (X_t − X_s) ∂P = c`, the conditional
expectation `E[φ ∘ (X_t − X_s) | 𝓕_s] =ᵐ c`. Captures the "increment is independent of
the past, so functions of it have constant conditional expectation" pattern. -/
private lemma condExp_func_increment {s t : ℝ≥0} (hst : s ≤ t)
    (h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ}
    (h_int_eq : ∫ ω, φ (X t ω - X s ω) ∂P = c) :
    P[fun ω ↦ φ (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ c := by
  have h_indep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)) (𝓕 s) P :=
    hX.indep s t hst
  have hφ_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ φ (X t ω - X s ω)) :=
    hφ.comp (Measurable.of_comap_le le_rfl)
  have := condExp_indep_eq h_meas_diff.comap_le (𝓕.le s)
    hφ_comap.stronglyMeasurable h_indep
  rwa [h_int_eq] at this

/-- The "residual" of `X_t² − t` after removing the `𝓕_s`-measurable part `(X_s² − s)`:
`E[2 X_s (X_t − X_s) + ((X_t − X_s)² − (t − s)) | 𝓕_s] =ᵐ 0`.

Cross term: pull-out + zero-mean increment. Squared-increment term: `condExp_func_increment`
with `φ = z² − (t−s)` (the variance integrates to `t − s` so the residual integrates to `0`). -/
private lemma condExp_squareSubTime_residual {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω))
              + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))
        | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
  -- Measurabilities, HasLaws, MemLps.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_Bs_memLp : MemLp (X s) 2 P :=
    ((hL_s.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P))).comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    ((hL_diff.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map h_meas_diff.aemeasurable
  -- Integrabilities.
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P :=
    h_Bs_memLp.integrable_mul h_diff_memLp
  have h_int_2cross : Integrable (fun ω ↦ 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_cross.const_mul 2
  have h_int_diff_sq : Integrable (fun ω ↦ (X t ω - X s ω) ^ 2) P := h_diff_memLp.integrable_sq
  have h_int_diff_sq_sub :
      Integrable (fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))) P :=
    h_int_diff_sq.sub (integrable_const _)
  have h_int_diff : Integrable (fun ω ↦ X t ω - X s ω) P :=
    (hX.integrable_eval t).sub (hX.integrable_eval s)
  -- E[X_t − X_s | 𝓕_s] =ᵐ 0 (centered increment).
  have h_ce_increment :
      P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have h_int_zero : ∫ ω, (X t ω - X s ω) ∂P = 0 := by
      rw [show (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) from rfl,
          hL_diff.integral_eq, integral_id_gaussianReal]
    exact condExp_func_increment hst h_meas_diff measurable_id h_int_zero
  -- E[X_s · diff | 𝓕_s] =ᵐ 0 by pull-out + h_ce_increment.
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_ce_cross :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine (condExp_mul_of_stronglyMeasurable_left h_smeas_s h_int_cross h_int_diff).trans ?_
    filter_upwards [h_ce_increment] with ω hω
    show (X s) ω * _ = 0
    rw [hω]; simp
  -- E[diff² | 𝓕_s] =ᵐ (t − s) via condExp_func_increment with φ = z².
  have h_ce_diff_sq :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
        fun _ ↦ ((t : ℝ) - (s : ℝ)) := by
    have h_var : ∫ ω, (X t ω - X s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
      have h_change : ∫ ω, (X t ω - X s ω) ^ 2 ∂P
          = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
        simpa [Function.comp] using hL_diff.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
      rw [h_change, integral_sq_gaussianReal]; exact NNReal.max_sub_eq_of_le hst
    exact condExp_func_increment hst h_meas_diff (measurable_id.pow_const 2) h_var
  -- Bridge to centered form: E[diff² − (t − s) | 𝓕_s] =ᵐ 0 via condExp_sub + condExp_const.
  have h_ce_diff_sq_sub :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine (condExp_sub h_int_diff_sq (integrable_const _) _).trans ?_
    filter_upwards [h_ce_diff_sq] with ω h
    show P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] ω
          - P[fun _ : Ω ↦ ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)] ω = 0
    rw [h, condExp_const (𝓕.le s)]; simp
  -- Combine via condExp_add + condExp_smul: E[2 cross + diff_sq_sub | 𝓕_s] =ᵐ 2·0 + 0 = 0.
  refine (condExp_add h_int_2cross h_int_diff_sq_sub _).trans ?_
  have h_eq_smul : (fun ω ↦ 2 * (X s ω * (X t ω - X s ω)))
                 = (2 : ℝ) • (fun ω ↦ X s ω * (X t ω - X s ω)) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]
  have h_smul :
      P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
        (2 : ℝ) • P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]; exact condExp_smul (2 : ℝ) _ _
  filter_upwards [h_smul, h_ce_cross, h_ce_diff_sq_sub] with ω hsm hcr hds
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  linarith

/-- For a filtered pre-Brownian motion `X`, `t ↦ (X t)² − t` is a martingale w.r.t. `𝓕`.

Decomposition `X_t² − t = (X_s² − s) + 2 X_s (X_t − X_s) + ((X_t − X_s)² − (t − s))`:
the `𝓕_s`-measurable part survives conditioning; the residual has zero conditional
expectation by `condExp_squareSubTime_residual`. -/
theorem squareSubTime_isMartingale :
    Martingale (fun t ω ↦ (X t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω ↦ (X u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  -- 𝓕_s-measurability + integrability of `(X_s)² − s`.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_Bs_memLp : MemLp (X s) 2 P :=
    ((hL_s.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P))).comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    ((hL_diff.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map
      (h_meas_t.sub h_meas_s).aemeasurable
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_smeas_Bs_sq_sub : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) := by
    have hsq : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2) := by
      simpa [pow_two] using h_smeas_s.mul h_smeas_s
    exact hsq.sub stronglyMeasurable_const
  have h_int_Bs_sq_sub : Integrable (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) P :=
    h_Bs_memLp.integrable_sq.sub (integrable_const _)
  have h_condBs_sq_sub :
      P[fun ω ↦ (X s ω) ^ 2 - (s : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        = fun ω ↦ (X s ω) ^ 2 - (s : ℝ) :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_Bs_sq_sub h_int_Bs_sq_sub
  have h_int_residual : Integrable (fun ω ↦
      2 * (X s ω * (X t ω - X s ω)) + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))) P :=
    ((h_Bs_memLp.integrable_mul h_diff_memLp).const_mul 2).add
      (h_diff_memLp.integrable_sq.sub (integrable_const _))
  -- AE decomposition and combine via a single `condExp_add`.
  have h_decomp_ae :
      (fun ω ↦ (X t ω) ^ 2 - (t : ℝ)) =ᵐ[P] fun ω ↦
        ((X s ω) ^ 2 - (s : ℝ)) +
          (2 * (X s ω * (X t ω - X s ω))
            + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))) :=
    Filter.Eventually.of_forall fun ω ↦ by ring
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  refine (condExp_add h_int_Bs_sq_sub h_int_residual _).trans ?_
  filter_upwards [condExp_squareSubTime_residual (hX := hX) hst] with ω hω
  show P[fun ω ↦ (X s ω) ^ 2 - (s : ℝ) | (𝓕 s : MeasurableSpace Ω)] ω + _ = _
  rw [h_condBs_sq_sub, hω]; simp

/-- For a filtered pre-Brownian motion `X` and `α : ℝ`,
`t ↦ exp(α X_t − α² t / 2)` is a martingale w.r.t. `𝓕`.

Setting `M_s := exp(α X_s − α²s/2)` (𝓕_s-measurable) and
`D_{st} := exp(α(X_t − X_s) − α²(t−s)/2)` (function of the increment, independent of `𝓕_s`),
pointwise `M_t = M_s · D_{st}` and `E[D_{st}] = 1` (Gaussian MGF). Pull-out closes it. -/
theorem waldExponential_isMartingale (α : ℝ) :
    Martingale (fun t ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · refine Real.continuous_exp.comp_stronglyMeasurable ?_
    exact ((hX.stronglyAdapted u).const_mul α).sub stronglyMeasurable_const
  -- Conditional-expectation step.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_int_exp_diff : Integrable (fun ω ↦ Real.exp (α * (X t ω - X s ω))) P :=
    integrable_exp_mul_of_hasLaw h_meas_diff hL_diff α
  -- `M_s := exp(α X_s − α²s/2)` and `D_{st} := exp(α(X_t − X_s) − α²(t−s)/2)`.
  set Ms : Ω → ℝ := fun ω ↦ Real.exp (α * X s ω - α ^ 2 * (s : ℝ) / 2)
  set Dst : Ω → ℝ := fun ω ↦
    Real.exp (α * (X t ω - X s ω) - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
  have hMs_meas : StronglyMeasurable[𝓕 s] Ms :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hX.stronglyAdapted s).const_mul α).sub stronglyMeasurable_const)
  -- Two factorisations used several times (each `funext; show; rw; congr; ring`).
  -- Factored once via `factor_exp` to dedupe.
  have factor_exp : ∀ (a b : ℝ), Real.exp (a + b) = Real.exp a * Real.exp b := Real.exp_add
  have h_decomp : ∀ ω, Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2) = Ms ω * Dst ω := fun ω ↦ by
    show _ = Real.exp _ * Real.exp _; rw [← factor_exp]; congr 1; ring
  have hDst_factor : Dst = fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                              * Real.exp (α * (X t ω - X s ω)) := by
    funext ω; show Real.exp _ = _; rw [← factor_exp]; congr 1; ring
  have hMs_factor : Ms = fun ω ↦ Real.exp (-(α ^ 2 * (s : ℝ) / 2)) * Real.exp (α * X s ω) := by
    funext ω; show Real.exp _ = _; rw [← factor_exp]; congr 1; ring
  -- Integrabilities of `M_s` and `D_{st}` (factored through `exp(α · Gaussian)`).
  have h_int_Dst : Integrable Dst P := hDst_factor ▸ h_int_exp_diff.const_mul _
  have h_int_Ms : Integrable Ms P :=
    hMs_factor ▸ (integrable_exp_mul_of_hasLaw h_meas_s (hX.hasLaw_eval s) α).const_mul _
  -- Mean of `D_{st}` is 1 (Gaussian MGF cancels the `α²(t−s)/2` term).
  have h_int_Dst_eq_one : ∫ ω, Dst ω ∂P = 1 := by
    have h_mgf : ∫ ω, Real.exp (α * (X t ω - X s ω)) ∂P
        = Real.exp (α ^ 2 * ((max (t - s) (s - t) : ℝ≥0) : ℝ) / 2) := by
      have h := hL_diff.integral_comp
        (f := fun x : ℝ ↦ Real.exp (α * x)) (by fun_prop)
      simpa [integral_exp_mul_gaussianReal_zero] using h
    rw [hDst_factor, integral_const_mul, h_mgf, NNReal.max_sub_eq_of_le hst,
        ← factor_exp, neg_add_cancel, Real.exp_zero]
  -- `E[D_{st} | 𝓕_s] =ᵐ 1` (the increment is independent of `𝓕 s`).
  have h_condDst : P[Dst | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) :=
    condExp_func_increment hst h_meas_diff
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub continuous_const)).measurable
      h_int_Dst_eq_one
  -- Pull-out: E[M_s · D_{st} | 𝓕_s] =ᵐ M_s · E[D_{st} | 𝓕_s] =ᵐ M_s · 1 = M_s.
  have h_int_MsDst : Integrable (fun ω ↦ Ms ω * Dst ω) P := by
    rw [← funext h_decomp]
    have h_eq : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
              = fun ω ↦ Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * X t ω) := by
      funext ω; show Real.exp _ = _; rw [← factor_exp]; congr 1; ring
    rw [h_eq]
    exact (integrable_exp_mul_of_hasLaw h_meas_t (hX.hasLaw_eval t) α).const_mul _
  refine (condExp_congr_ae (Filter.Eventually.of_forall h_decomp)).trans ?_
  refine (condExp_mul_of_stronglyMeasurable_left hMs_meas h_int_MsDst h_int_Dst).trans ?_
  filter_upwards [h_condDst] with ω hω
  show (Ms * P[Dst | (𝓕 s : MeasurableSpace Ω)]) ω = Ms ω
  simp only [Pi.mul_apply, hω, mul_one]

end IsFilteredPreBrownian

end ProbabilityTheory
