/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Martingale properties of Brownian motion

For a filtered pre-Brownian motion `X`, the following are martingales w.r.t. the filtration `𝓕`:

* `X` itself (already provided as `IsPreBrownian.isMartingale` in `Gaussian/BrownianMotion.lean`)
* `t ↦ (X t)² − t`
* `t ↦ exp(α X_t − α² t / 2)` (Wald exponential), for any `α : ℝ`

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

/-- For `s ≤ t : ℝ≥0`, the NNReal-valued increment-variance `max (t-s) (s-t)`
coerces to `(t : ℝ) - (s : ℝ)` (since truncated `s - t = 0` when `s ≤ t`). -/
private lemma NNReal.max_sub_eq_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  have hst_zero : s - t = (0 : ℝ≥0) := tsub_eq_zero_of_le hst
  rw [hst_zero, max_eq_left (zero_le _)]
  exact NNReal.coe_sub hst

/-- MGF specialization: for `α : ℝ` and `v : ℝ≥0`,
`∫ x, exp(α x) ∂(gaussianReal 0 v) = exp(α² v / 2)`. -/
private lemma integral_exp_mul_gaussianReal_zero (α : ℝ) (v : ℝ≥0) :
    ∫ x, Real.exp (α * x) ∂(gaussianReal 0 v) = Real.exp (α ^ 2 * (v : ℝ) / 2) := by
  have h := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) α
  show mgf id (gaussianReal 0 v) α = _
  rw [h]
  ring_nf

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`. -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

/-- `Real.exp (α · X) ∘ Z` is integrable when `Z` has a Gaussian law.
Shared helper for `waldExponential_isMartingale` (used 3× there). -/
private lemma integrable_exp_mul_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {m : ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal m v) P) (α : ℝ) :
    Integrable (fun ω ↦ Real.exp (α * Z ω)) P := by
  rw [show (fun ω ↦ Real.exp (α * Z ω)) = (fun x ↦ Real.exp (α * x)) ∘ Z from rfl]
  refine Integrable.comp_aemeasurable ?_ hZ_meas.aemeasurable
  rw [hZ.map_eq]
  exact integrable_exp_mul_gaussianReal α

namespace IsFilteredPreBrownian

variable [hX : IsFilteredPreBrownian X 𝓕 P] [IsFiniteMeasure P]

/-- For a Borel-measurable `φ : ℝ → ℝ` with `∫ φ (X_t ω − X_s ω) ∂P = c`, the
conditional expectation of `φ ∘ (X_t − X_s)` given `𝓕 s` is a.e. the constant
`c`. Captures the "increment is independent of the past, so functions of it
behave like deterministic constants under conditional expectation" pattern. -/
private lemma condExp_func_increment {s t : ℝ≥0} (hst : s ≤ t)
    (h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ}
    (h_int_eq : ∫ ω, φ (X t ω - X s ω) ∂P = c) :
    P[fun ω ↦ φ (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ c := by
  have h_indep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)) (𝓕 s) P := by
    have := hX.indep s t hst
    convert this using 2
  have hφ_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ φ (X t ω - X s ω)) :=
    hφ.comp (Measurable.of_comap_le le_rfl)
  have := condExp_indep_eq h_meas_diff.comap_le (𝓕.le s)
    hφ_comap.stronglyMeasurable h_indep
  rwa [h_int_eq] at this

/-- For a filtered pre-Brownian motion `X`, the process `t ↦ (X t)² − t` is a martingale
w.r.t. `𝓕`.

Decomposition: `(X_t)² = (X_s)² + 2 X_s (X_t − X_s) + (X_t − X_s)²`. The first summand is
`𝓕_s`-measurable; the cross term has zero conditional expectation by pull-out + independence;
the squared increment has conditional expectation `t − s` (its variance). -/
theorem squareSubTime_isMartingale :
    Martingale (fun t ω ↦ (X t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness of `(X u)² − u`.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω ↦ (X u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  -- Conditional-expectation step.
  have h_int_s : Integrable (X s) P := hX.integrable_eval s
  have h_int_t : Integrable (X t) P := hX.integrable_eval t
  have h_int_diff : Integrable (fun ω ↦ X t ω - X s ω) P := h_int_t.sub h_int_s
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have h_eq_diff : (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) := rfl
  -- HasLaws from `IsPreBrownian`.
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  -- L² membership transferred via HasLaw + `memLp_id_gaussianReal`.
  have h_Bs_memLp : MemLp (X s) 2 P :=
    ((hL_s.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P))).comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P := by
    rw [h_eq_diff]
    exact ((hL_diff.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map
      (h_eq_diff ▸ h_meas_diff.aemeasurable)
  -- Integrabilities.
  have h_int_Bs_sq : Integrable (fun ω ↦ (X s ω) ^ 2) P := h_Bs_memLp.integrable_sq
  have h_int_diff_sq : Integrable (fun ω ↦ (X t ω - X s ω) ^ 2) P := h_diff_memLp.integrable_sq
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P := by
    have := h_Bs_memLp.integrable_mul h_diff_memLp
    simpa using this
  -- Mean of increment is 0.
  have h_int_diff_zero : ∫ ω, (X t ω - X s ω) ∂P = 0 := by
    rw [h_eq_diff, hL_diff.integral_eq, integral_id_gaussianReal]
  -- Variance of increment integral: ∫ (X_t − X_s)² ∂P = t − s.
  have h_int_diff_sq_zero : ∫ ω, (X t ω - X s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
    have h_change : ∫ ω, (X t ω - X s ω) ^ 2 ∂P
        = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
      simpa [Function.comp] using hL_diff.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    rw [h_change, integral_sq_gaussianReal]
    exact NNReal.max_sub_eq_of_le hst
  -- `𝓕_s`-measurability of `X_s` and `(X_s)²`.
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_smeas_s_sq : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2) := by
    simpa [pow_two] using h_smeas_s.mul h_smeas_s
  -- `E[(X_s)² | 𝓕_s] = (X_s)²`.
  have h_condBs_sq :
      P[fun ω ↦ (X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] = fun ω ↦ (X s ω) ^ 2 :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_s_sq h_int_Bs_sq
  -- `E[X_t − X_s | 𝓕_s] =ᵐ 0` and `E[(X_t − X_s)² | 𝓕_s] =ᵐ (t − s)`
  -- (the increment is independent of `𝓕 s`).
  have h_condDiff :
      P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) :=
    condExp_func_increment hst h_meas_diff measurable_id h_int_diff_zero
  have h_condDiffSq :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ ((t : ℝ) - (s : ℝ)) :=
    condExp_func_increment hst h_meas_diff (measurable_id.pow_const 2) h_int_diff_sq_zero
  -- Pull-out for the cross term.
  have h_cross_eq :
      (fun ω ↦ X s ω * (X t ω - X s ω)) = (X s) * (fun ω ↦ X t ω - X s ω) := rfl
  have h_pullout :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (X s) * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) := by
    rw [h_cross_eq]
    exact condExp_mul_of_stronglyMeasurable_left h_smeas_s
      (by simpa [h_cross_eq] using h_int_cross) h_int_diff
  have h_cond_cross :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine h_pullout.trans ?_
    filter_upwards [h_condDiff] with ω hω
    change (X s) ω * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) ω = (0 : ℝ)
    rw [hω]; simp
  -- Decomposition of the integrand.
  have h_decomp_ae :
      (fun ω ↦ (X t ω) ^ 2 - (t : ℝ)) =ᵐ[P] fun ω ↦
        ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
          ((X t ω - X s ω) ^ 2 - (t : ℝ)) :=
    Filter.Eventually.of_forall fun ω ↦ by ring
  -- `condExp` respects ae-equality.
  have step1 :
      P[fun ω ↦ (X t ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] P[fun ω ↦
          ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
            ((X t ω - X s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)] :=
    condExp_congr_ae h_decomp_ae
  -- Outer linearity.
  have h_int_inner_left :
      Integrable (fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_Bs_sq.add (h_int_cross.const_mul 2)
  have h_int_inner_right :
      Integrable (fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ)) P :=
    h_int_diff_sq.sub (integrable_const _)
  have step2 :
      P[fun ω ↦
          ((X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))) +
            ((X t ω - X s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
              | (𝓕 s : MeasurableSpace Ω)]) +
            (P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_inner_left h_int_inner_right _
  -- Inner linearity. Use `(2 : ℝ) •` so `condExp_smul` applies.
  have h_eq_smul : (fun ω ↦ 2 * (X s ω * (X t ω - X s ω)))
                 = (2 : ℝ) • (fun ω ↦ X s ω * (X t ω - X s ω)) := by
    funext ω; simp [Pi.smul_apply, smul_eq_mul]
  have h_int_2cross : Integrable (fun ω ↦ 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_cross.const_mul 2
  have step3a :
      P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) +
            (P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_Bs_sq h_int_2cross _
  have step3b :
      P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (2 : ℝ) • P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]; exact condExp_smul (2 : ℝ) _ _
  rw [h_condBs_sq] at step3a
  have step3 :
      P[fun ω ↦ (X s ω) ^ 2 + 2 * (X s ω * (X t ω - X s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (fun ω ↦ (X s ω) ^ 2) +
            (2 : ℝ) • (P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]) := by
    filter_upwards [step3a, step3b] with ω h3a h3b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3a h3b ⊢
    linarith
  -- Inner sub on the right.
  have step4 :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) -
            (fun _ ↦ (t : ℝ)) := by
    have h_const_int : Integrable (fun _ : Ω ↦ (t : ℝ)) P := integrable_const _
    have step4a :
        P[fun ω ↦ (X t ω - X s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
          =ᵐ[P]
            (P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]) -
              P[fun _ : Ω ↦ (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] :=
      condExp_sub h_int_diff_sq h_const_int _
    have step4b :
        P[fun _ : Ω ↦ (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] = fun _ ↦ (t : ℝ) :=
      condExp_const (𝓕.le s) (t : ℝ)
    filter_upwards [step4a] with ω h4a
    rw [h4a, step4b]
  -- Combine via `linear_combination`.
  filter_upwards [step1, step2, step3, step4, h_cond_cross, h_condDiffSq]
    with ω hs1 hs2 hs3 hs4 hcross hdiffsq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs2 hs3 hs4
  linear_combination hs1 + hs2 + hs3 + hs4 + 2 * hcross + hdiffsq

/-- **Wald exponential martingale.** For a filtered pre-Brownian motion `X` and `α : ℝ`,
the process `t ↦ exp(α X_t − α² t / 2)` is a martingale w.r.t. `𝓕`.

Decomposition: `α X_t − α²t/2 = (α X_s − α²s/2) + (α (X_t − X_s) − α²(t−s)/2)`. Setting
`M_s := exp(α X_s − α²s/2)` (which is `𝓕_s`-measurable) and
`D_{st} := exp(α (X_t − X_s) − α²(t−s)/2)` (which is independent of `𝓕_s`),
pointwise `M_t = M_s · D_{st}` and `E[D_{st}] = 1` (Gaussian MGF at `α`). Pull-out yields
`E[M_t | 𝓕_s] = M_s · E[D_{st} | 𝓕_s] = M_s`. -/
theorem waldExponential_isMartingale (α : ℝ) :
    Martingale (fun t ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hinner : StronglyMeasurable[𝓕 u]
        (fun ω ↦ α * X u ω - α ^ 2 * (u : ℝ) / 2) :=
      (hB.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner
  -- Conditional-expectation step.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have h_eq_diff : (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) := rfl
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  -- Integrability of `exp(α (X_t − X_s))`.
  have h_int_exp_diff : Integrable (fun ω ↦ Real.exp (α * (X t ω - X s ω))) P := by
    have := integrable_exp_mul_of_hasLaw h_meas_diff (h_eq_diff ▸ hL_diff) α
    convert this
  -- Mean of `exp(α (X_t − X_s))` (Gaussian MGF at `α`).
  have h_int_exp_diff_eq :
      ∫ ω, Real.exp (α * (X t ω - X s ω)) ∂P
        = Real.exp (α ^ 2 * ((max (t - s) (s - t) : ℝ≥0) : ℝ) / 2) := by
    have hf : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (α * x))
                (gaussianReal 0 (max (t - s) (s - t))) := by fun_prop
    have h := hL_diff.integral_comp hf
    have h_lhs : ((fun x ↦ Real.exp (α * x)) ∘ (X t - X s))
               = (fun ω ↦ Real.exp (α * (X t ω - X s ω))) := rfl
    rw [h_lhs, integral_exp_mul_gaussianReal_zero] at h
    exact h
  -- Define `M_s` (𝓕_s-measurable factor) and the increment exponential `D_{st}`.
  set Ms : Ω → ℝ := fun ω ↦ Real.exp (α * X s ω - α ^ 2 * (s : ℝ) / 2) with hMs_def
  set Dst : Ω → ℝ := fun ω ↦
    Real.exp (α * (X t ω - X s ω) - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) with hDst_def
  have hMs_meas : StronglyMeasurable[𝓕 s] Ms := by
    have hB_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
    have hinner_s : StronglyMeasurable[𝓕 s] (fun ω ↦ α * X s ω - α ^ 2 * (s : ℝ) / 2) :=
      (hB_s.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner_s
  -- Pointwise: `exp(α X_t − α²t/2) = M_s · D_{st}`.
  have h_decomp : ∀ ω, Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2) = Ms ω * Dst ω := by
    intro ω
    change _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  -- Factor `D_{st} = exp(-α²(t−s)/2) · exp(α(X_t−X_s))`.
  have hDst_factor : Dst = (fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                                 * Real.exp (α * (X t ω - X s ω))) := by
    funext ω
    change Real.exp _ = _ * Real.exp _
    rw [← Real.exp_add]; congr 1; ring
  -- Integrability of `D_{st}`.
  have h_int_Dst : Integrable Dst P := hDst_factor ▸ h_int_exp_diff.const_mul _
  -- Mean of `D_{st}` is 1.
  have h_int_Dst_eq_one : ∫ ω, Dst ω ∂P = 1 := by
    rw [hDst_factor, integral_const_mul, h_int_exp_diff_eq, NNReal.max_sub_eq_of_le hst,
        ← Real.exp_add]
    rw [show -(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) + α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2 = 0
        from by ring, Real.exp_zero]
  -- `E[D_{st} | 𝓕_s] =ᵐ 1` (the increment is independent of `𝓕 s`).
  have h_condDst : P[Dst | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) :=
    condExp_func_increment hst h_meas_diff
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub continuous_const)).measurable
      h_int_Dst_eq_one
  -- Pull-out: `E[M_s · D_{st} | 𝓕_s] =ᵐ M_s · E[D_{st} | 𝓕_s] =ᵐ M_s · 1 = M_s`.
  have h_int_Ms : Integrable Ms P := by
    have hMs_factor : Ms = (fun ω ↦ Real.exp (-(α ^ 2 * (s : ℝ) / 2))
                                * Real.exp (α * X s ω)) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [hMs_factor]
    exact (integrable_exp_mul_of_hasLaw h_meas_s (hX.hasLaw_eval s) α).const_mul _
  have h_int_MsDst : Integrable (fun ω ↦ Ms ω * Dst ω) P := by
    rw [← funext h_decomp]
    have h_eq : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
              = (fun ω ↦ Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * X t ω)) := by
      funext ω
      change Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [h_eq]
    exact (integrable_exp_mul_of_hasLaw h_meas_t (hX.hasLaw_eval t) α).const_mul _
  have h_pullout :
      P[fun ω ↦ Ms ω * Dst ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] Ms * (P[Dst | (𝓕 s : MeasurableSpace Ω)]) := by
    have h_eq : (fun ω ↦ Ms ω * Dst ω) = Ms * Dst := rfl
    rw [h_eq]
    exact condExp_mul_of_stronglyMeasurable_left hMs_meas
      (by rw [← h_eq]; exact h_int_MsDst) h_int_Dst
  have h_decomp_ae :
      (fun u ↦ Real.exp (α * X t u - α ^ 2 * (t : ℝ) / 2)) =ᵐ[P] fun ω ↦ Ms ω * Dst ω :=
    Filter.Eventually.of_forall h_decomp
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  refine h_pullout.trans ?_
  filter_upwards [h_condDst] with ω hω
  change (Ms * P[Dst | (𝓕 s : MeasurableSpace Ω)]) ω = Ms ω
  simp [Pi.mul_apply, hω]

end IsFilteredPreBrownian

end ProbabilityTheory

/-! ## Hitting time of an open set is a stopping time

For a continuous adapted process `X` and an open set `A`, the hitting time
`τ_A = inf {t ≥ 0 : X_t ∈ A}` is a stopping time w.r.t. any right-continuous
filtration. The proof reduces `{ω | τ ω < i}` to a countable union of
`{ω | X_q ω ∈ A}` for nonnegative rationals `q < i` (continuity of `X(·, ω)`
upgrades any real witness to a rational witness via `Real.exists_rat_btwn`),
then applies `isStoppingTime_of_measurableSet_lt_of_isRightContinuous`.

The result is generic — applies to any adapted continuous process — but lives
here because the canonical application is to Brownian motion paths.
Corresponds to Saporito Proposition 4.3.6. -/

namespace HybridVerify

open MeasureTheory ProbabilityTheory

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω}

/-- Key set identity: for continuous adapted `X` and open `A`, the set
`{ω | hittingAfter X A 0 ω < i}` equals the countable union over nonnegative
rationals `q < i` of `{ω | X (q : ℝ) ω ∈ A}`. -/
private lemma hittingAfter_lt_eq_iUnion_rationals
    [TopologicalSpace β]
    {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hA_open : IsOpen A)
    (i : ℝ) :
    {ω | hittingAfter X A 0 ω < (i : WithTop ℝ)}
      = ⋃ (q : ℚ) (_ : (0 : ℝ) ≤ (q : ℝ)) (_ : (q : ℝ) < i),
          {ω | X (q : ℝ) ω ∈ A} := by
  ext ω
  rw [Set.mem_setOf_eq, hittingAfter_lt_iff]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Ico, exists_prop]
  constructor
  · rintro ⟨j, ⟨hj_nn, hj_lt⟩, hXj⟩
    have h_pre : (fun t : ℝ => X t ω) ⁻¹' A ∈ nhds j :=
      ((hX_cont ω).continuousAt).preimage_mem_nhds (hA_open.mem_nhds hXj)
    rcases lt_or_eq_of_le hj_nn with hj_pos | hj_zero
    · obtain ⟨δ, hδ_pos, hδ_sub⟩ : ∃ δ > 0,
          Set.Ioo (j - δ) (j + δ) ⊆ (fun t : ℝ => X t ω) ⁻¹' A := by
        have h_nhds := Metric.mem_nhds_iff.mp h_pre
        obtain ⟨ε, hε_pos, hε_sub⟩ := h_nhds
        refine ⟨ε, hε_pos, fun s hs => ?_⟩
        refine hε_sub ?_
        simp only [Metric.mem_ball, Real.dist_eq, Set.mem_Ioo] at hs ⊢
        cases hs with | intro h1 h2 => exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      have h_min_pos : 0 < min δ (min j (i - j)) :=
        lt_min hδ_pos (lt_min hj_pos (by linarith))
      set δ' := min δ (min j (i - j)) / 2 with hδ'_def
      have hδ'_pos : 0 < δ' := half_pos h_min_pos
      have hδ'_lt_min : δ' < min δ (min j (i - j)) := half_lt_self h_min_pos
      have hδ'_le_δ : δ' ≤ δ := hδ'_lt_min.le.trans (min_le_left _ _)
      have hδ'_lt_j : δ' < j :=
        hδ'_lt_min.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hδ'_lt_i_sub_j : δ' < i - j :=
        hδ'_lt_min.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have h_sub_pre : Set.Ioo (j - δ') (j + δ') ⊆ (fun t : ℝ => X t ω) ⁻¹' A := by
        intro s hs
        refine hδ_sub ⟨?_, ?_⟩
        · linarith [hs.1, hδ'_le_δ]
        · linarith [hs.2, hδ'_le_δ]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show j - δ' < j + δ' by linarith)
      refine ⟨q, ?_, ?_, h_sub_pre ⟨hq1, hq2⟩⟩
      · linarith [hδ'_lt_j]
      · linarith [hδ'_lt_i_sub_j]
    · refine ⟨0, ?_, ?_, ?_⟩
      · simp
      · push_cast
        linarith
      · push_cast
        rw [show (0 : ℝ) = j from hj_zero]
        exact hXj
  · rintro ⟨q, hq_nn, hq_lt, hXq⟩
    exact ⟨(q : ℝ), ⟨hq_nn, hq_lt⟩, hXq⟩

private lemma measurableSet_hittingAfter_lt_of_open
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ℝ mΩ} {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hX_adapted : Adapted 𝓕 X)
    (hA_open : IsOpen A) (i : ℝ) :
    MeasurableSet[𝓕 i] {ω | hittingAfter X A 0 ω < (i : WithTop ℝ)} := by
  rw [hittingAfter_lt_eq_iUnion_rationals hX_cont hA_open]
  refine MeasurableSet.iUnion fun q => ?_
  refine MeasurableSet.iUnion fun hq_nn => ?_
  refine MeasurableSet.iUnion fun hq_lt => ?_
  exact 𝓕.mono hq_lt.le _ (hX_adapted (q : ℝ) hA_open.measurableSet)

/-- **Saporito Proposition 4.3.6.** For a continuous adapted process `X` and an
open set `A`, the hitting time `hittingAfter X A 0` is a stopping time w.r.t.
any right-continuous filtration. -/
theorem isStoppingTime_hittingAfter_of_open
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ℝ mΩ} [𝓕.IsRightContinuous]
    {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hX_adapted : Adapted 𝓕 X)
    (hA_open : IsOpen A) :
    IsStoppingTime 𝓕 (hittingAfter X A 0) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i =>
    measurableSet_hittingAfter_lt_of_open hX_cont hX_adapted hA_open i

end HybridVerify
