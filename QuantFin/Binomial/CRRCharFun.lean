/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.DriftLimit

/-!
# CRR characteristic-function convergence (the CLT heart of CRR → Black–Scholes)

The deterministic-analytic correspondence in `CRRConvergence.lean` /
`DriftLimit.lean` (`crrProb_tendsto_half`, `crr_drift_limit_n`) pins down the
mean and variance of one CRR log-return increment. This file converts those
moment limits into the **distributional** statement that drives CRR → BS: the
characteristic function of the `n`-step risk-neutral log-return,

  `φₙ(t)ⁿ`  where  `φₙ(t) = pₙ e^{i (σ√Δt) t} + (1−pₙ) e^{i(−σ√Δt) t}`,

converges pointwise to the Gaussian characteristic function
`exp(i t (r − σ²/2) T − ½ t² σ² T)`, i.e. the charFun of
`N((r − σ²/2)T, σ²T)`.

The crux is `crr_charFun_pow_tendsto`. The argument:

* Since the per-step value `±σ√Δt` is real, `φₙ(t) = cos θₙ + i (2pₙ−1) sin θₙ`
  with `θₙ = σ √(T/n) · t` real (`crrStepCharFun_eq`).
* `n (φₙ − 1) → i t (r−σ²/2)T − ½ t²σ²T =: L`, splitting real/imag parts:
  - real: `n (cos θₙ − 1) = ((cos θₙ−1)/θₙ²)·(n θₙ²) → (−½)·σ²t²T`, since
    `n θₙ² = σ² t² T` exactly and `(cos u−1)/u² → −½`;
  - imag: `n (2pₙ−1) sin θₙ = [n(2pₙ−1)σ√(T/n)]·t·(sin θₙ/θₙ) → (r−σ²/2)T·t`,
    feeding `crr_drift_limit_n` and `sin u/u → 1`.
* `φₙ(t)ⁿ = (1 + (φₙ−1))ⁿ → exp L` via Mathlib's
  `Complex.tendsto_one_add_pow_exp_of_tendsto`.

Both real trig limits reduce to `sin u / u → 1` (the half-angle identity
`1 − cos u = 2 sin²(u/2)` handles the cosine).
-/

namespace QuantFin

open Filter Complex
open scoped Topology

/-! ### Real second-order trig limits at `0` -/

/-- `sin u / u → 1` as `u → 0` (`u ≠ 0`): the slope of `sin` at `0`,
where `sin' 0 = cos 0 = 1`. -/
lemma tendsto_sin_div_one :
    Tendsto (fun u : ℝ => Real.sin u / u) (𝓝[≠] 0) (𝓝 1) := by
  have h_deriv : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have h_slope := h_deriv.tendsto_slope
  refine h_slope.congr' (Eventually.of_forall fun u => ?_)
  rw [slope_def_field]
  simp [Real.sin_zero]

/-- `(1 − cos u)/u² → 1/2` as `u → 0` (`u ≠ 0`), via the half-angle identity
`1 − cos u = 2 sin²(u/2)` and `sin v / v → 1`. -/
lemma tendsto_one_sub_cos_div_sq :
    Tendsto (fun u : ℝ => (1 - Real.cos u) / u ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h_half : Tendsto (fun u : ℝ => u / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun u : ℝ => u / 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_id.div_const (2 : ℝ)).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact div_ne_zero hu (by norm_num)
  have h_s : Tendsto (fun u : ℝ => Real.sin (u / 2) / (u / 2)) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_sin_div_one.comp h_half
  have h_sq : Tendsto (fun u : ℝ => (1 / 2) * (Real.sin (u / 2) / (u / 2)) ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) * 1 ^ 2)) := (h_s.pow 2).const_mul (1 / 2)
  rw [show ((1 : ℝ) / 2 * 1 ^ 2) = 1 / 2 from by norm_num] at h_sq
  refine h_sq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu_ne : u ≠ 0 := hu
  have hid : 1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
    have h2 : Real.cos u = 2 * Real.cos (u / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (u / 2)
      rwa [show 2 * (u / 2) = u from by ring] at this
    have h3 : Real.sin (u / 2) ^ 2 + Real.cos (u / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (u / 2)
    nlinarith [h2, h3]
  rw [hid]
  have h2ne : u / 2 ≠ 0 := div_ne_zero hu_ne (by norm_num)
  field_simp

/-! ### The per-step CRR characteristic function -/

/-- Real → complex exponential: `exp(↑x · I) = cos x + (sin x) i`. -/
private lemma cexp_ofReal_mul_I (x : ℝ) :
    Complex.exp (↑x * I) = ↑(Real.cos x) + ↑(Real.sin x) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The characteristic function of one CRR risk-neutral log-return increment,
evaluated at `t`: `φₙ(t) = pₙ e^{i (σ√Δt) t} + (1−pₙ) e^{i (−σ√Δt) t}`,
with `Δt = T/n` and `pₙ = crrProb`. -/
noncomputable def crrStepCharFun (r σ T : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (crrProb r σ T n : ℂ) * Complex.exp (I * ↑(σ * Real.sqrt (T / n) * t))
    + (1 - (crrProb r σ T n : ℂ)) * Complex.exp (I * ↑(-(σ * Real.sqrt (T / n)) * t))

/-- **Real/imaginary form of the per-step charFun**: since the increment takes
the real values `±σ√Δt`, `φₙ(t) = cos θₙ + i (2pₙ−1) sin θₙ` with
`θₙ = σ √(T/n) · t`. -/
lemma crrStepCharFun_eq (r σ T : ℝ) (n : ℕ) (t : ℝ) :
    crrStepCharFun r σ T n t
      = ↑(Real.cos (σ * Real.sqrt (T / n) * t))
        + ↑((2 * crrProb r σ T n - 1) * Real.sin (σ * Real.sqrt (T / n) * t)) * I := by
  unfold crrStepCharFun
  rw [mul_comm I (↑(σ * Real.sqrt (T / n) * t)),
      mul_comm I (↑(-(σ * Real.sqrt (T / n)) * t)),
      cexp_ofReal_mul_I, cexp_ofReal_mul_I,
      show (-(σ * Real.sqrt (T / n)) * t) = -(σ * Real.sqrt (T / n) * t) from by ring,
      Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-! ### The two scalar limits feeding the exponent `L` -/

variable {σ T r : ℝ}

/-- For `t ≠ 0`, the rescaled angle `θₙ = σ √(T/n) · t` tends to `0` through
nonzero values — so it can feed the punctured-neighbourhood trig limits. -/
private lemma tendsto_crrAngle_punctured (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => σ * Real.sqrt (T / n) * t) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : Tendsto (fun n : ℕ => Real.sqrt (T / n)) atTop (𝓝 0) := by
      simpa [crrStep] using tendsto_sqrt_crrStep_zero T
    have h1 : Tendsto (fun n : ℕ => σ * Real.sqrt (T / n) * t) atTop (𝓝 (σ * 0 * t)) :=
      (h0.const_mul σ).mul_const t
    simpa using h1
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_sqrt_pos : 0 < Real.sqrt (T / n) := Real.sqrt_pos.mpr (div_pos hT hn_pos)
    exact mul_ne_zero (mul_ne_zero hσ.ne' h_sqrt_pos.ne') ht

/-- **Real part of `n(φₙ−1)`**: `n (cos θₙ − 1) → −½ σ² t² T`, with
`θₙ = σ√(T/n) t`. Uses `n θₙ² = σ² t² T` (exact, `n ≥ 1`) and `(1−cos u)/u² → ½`. -/
private lemma tendsto_n_mul_cos_sub_one (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (σ * Real.sqrt (T / n) * t) - 1))
      atTop (𝓝 (-(σ ^ 2 * t ^ 2 * T) / 2)) := by
  have hθ := tendsto_crrAngle_punctured hσ hT ht
  have h_cos : Tendsto (fun n : ℕ =>
      (1 - Real.cos (σ * Real.sqrt (T / n) * t)) / (σ * Real.sqrt (T / n) * t) ^ 2)
      atTop (𝓝 (1 / 2)) := tendsto_one_sub_cos_div_sq.comp hθ
  have h_main : Tendsto (fun n : ℕ =>
      -((1 - Real.cos (σ * Real.sqrt (T / n) * t)) / (σ * Real.sqrt (T / n) * t) ^ 2
        * (σ ^ 2 * t ^ 2 * T)))
      atTop (𝓝 (-(1 / 2 * (σ ^ 2 * t ^ 2 * T)))) := (h_cos.mul_const (σ ^ 2 * t ^ 2 * T)).neg
  rw [show -(1 / 2 * (σ ^ 2 * t ^ 2 * T)) = -(σ ^ 2 * t ^ 2 * T) / 2 from by ring] at h_main
  refine h_main.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h_step_pos : 0 < T / n := div_pos hT hn_pos
  have h_sqrt_sq : Real.sqrt (T / n) ^ 2 = T / n := Real.sq_sqrt h_step_pos.le
  have hθsq : (σ * Real.sqrt (T / n) * t) ^ 2 = σ ^ 2 * (T / n) * t ^ 2 := by
    rw [mul_pow, mul_pow, h_sqrt_sq]
  rw [hθsq]
  field_simp
  ring

/-- **Imaginary part of `n(φₙ−1)`**: `n (2pₙ−1) sin θₙ → (r − σ²/2) T t`, with
`θₙ = σ√(T/n) t`. Feeds `crr_drift_limit_n` and `sin u/u → 1`. -/
private lemma tendsto_n_mul_two_p_sub_one_mul_sin
    (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) * (2 * crrProb r σ T n - 1) * Real.sin (σ * Real.sqrt (T / n) * t))
      atTop (𝓝 ((r - σ ^ 2 / 2) * T * t)) := by
  have hθ := tendsto_crrAngle_punctured hσ hT ht
  have h_sin : Tendsto (fun n : ℕ =>
      Real.sin (σ * Real.sqrt (T / n) * t) / (σ * Real.sqrt (T / n) * t))
      atTop (𝓝 1) := tendsto_sin_div_one.comp hθ
  have h_dt : Tendsto (fun n : ℕ =>
      (n : ℝ) * (2 * crrProb r σ T n - 1) * σ * Real.sqrt (T / n) * t)
      atTop (𝓝 ((r - σ ^ 2 / 2) * T * t)) := (crr_drift_limit_n (r := r) hσ hT).mul_const t
  have h_prod := h_dt.mul h_sin
  rw [mul_one] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_sqrt_pos : 0 < Real.sqrt (T / n) := Real.sqrt_pos.mpr (div_pos hT hn_pos)
  have hθ_ne : σ * Real.sqrt (T / n) * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ.ne' h_sqrt_pos.ne') ht
  field_simp

/-! ### The characteristic-function convergence -/

/-- **CRR → BS characteristic-function convergence.** For `σ, T > 0`, the
characteristic function of the `n`-step CRR risk-neutral log-return,
`crrStepCharFun r σ T n t ^ n`, converges to the Gaussian characteristic
function `exp(i t (r − σ²/2) T − ½ t² σ² T)` — the charFun of
`N((r − σ²/2) T, σ² T)`. This is the distributional heart of the
Cox–Ross–Rubinstein → Black–Scholes convergence theorem.

The increment is real-valued (`±σ√Δt`), so `φₙ = cos θₙ + i (2pₙ−1) sin θₙ`;
`n (φₙ − 1) → L := i t (r−σ²/2)T − ½ t²σ²T` (real and imaginary parts via the
two scalar limits above), and `φₙⁿ = (1 + (φₙ−1))ⁿ → exp L` by Mathlib's
`Complex.tendsto_one_add_pow_exp_of_tendsto`. -/
theorem crr_charFun_pow_tendsto (hσ : 0 < σ) (hT : 0 < T) (t : ℝ) :
    Tendsto (fun n : ℕ => crrStepCharFun r σ T n t ^ n) atTop
      (𝓝 (Complex.exp (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · -- `t = 0`: `φₙ = 1` and the exponent is `0`, so both sides are the constant `1`.
    have hφ1 : ∀ n : ℕ, crrStepCharFun r σ T n 0 = 1 := by
      intro n; rw [crrStepCharFun_eq]; simp
    have h0 : I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal (0 : ℝ)
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal (0 : ℝ) ^ 2 / 2 = 0 := by simp
    simp only [hφ1, one_pow, h0, Complex.exp_zero]
    exact tendsto_const_nhds
  · -- `t ≠ 0`: `n (φₙ − 1) → L := i t (r−σ²/2)T − ½ t²σ²T`, then `(1 + (φₙ−1))ⁿ → exp L`.
    have hA := tendsto_n_mul_cos_sub_one hσ hT ht
    have hB := tendsto_n_mul_two_p_sub_one_mul_sin (r := r) hσ hT ht
    have h_ng : Tendsto (fun n : ℕ => (n : ℂ) * (crrStepCharFun r σ T n t - 1)) atTop
        (𝓝 (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
          - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2)) := by
      have h_sum := ((Complex.continuous_ofReal.tendsto _).comp hA).add
        (((Complex.continuous_ofReal.tendsto _).comp hB).mul_const I)
      rw [show (Complex.ofReal (-(σ ^ 2 * t ^ 2 * T) / 2)
            + Complex.ofReal ((r - σ ^ 2 / 2) * T * t) * I)
          = I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
            - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2
        from by push_cast; ring] at h_sum
      refine h_sum.congr' (Eventually.of_forall fun n => ?_)
      simp only [Function.comp_apply, crrStepCharFun_eq]
      push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
      ring
    have h_pow := Complex.tendsto_one_add_pow_exp_of_tendsto
      (g := fun n => crrStepCharFun r σ T n t - 1) h_ng
    refine h_pow.congr (fun n => ?_)
    show (1 + (crrStepCharFun r σ T n t - 1)) ^ n = crrStepCharFun r σ T n t ^ n
    rw [show (1 : ℂ) + (crrStepCharFun r σ T n t - 1) = crrStepCharFun r σ T n t from by ring]

/-- **CRR → BS, Gaussian-characteristic-function form.** The same limit as
`crr_charFun_pow_tendsto`, with the target written explicitly as the characteristic
function of the Black–Scholes Gaussian `N((r − σ²/2)T, σ²T)`
(`MeasureTheory.charFun (gaussianReal ((r−σ²/2)T) (σ²T))`).

This is the precise hypothesis Lévy's continuity theorem consumes: once the `n`-step
CRR log-return law is identified as the `n`-fold convolution of the step law — whose
characteristic function is `crrStepCharFun`, so the convolution's is `crrStepCharFun ^ n`
(`MeasureTheory.charFun_conv`) — `ProbabilityMeasure.tendsto_iff_tendsto_charFun`
upgrades this pointwise charFun convergence to convergence in distribution, i.e. the
CRR risk-neutral log-return converges in law to the Black–Scholes normal. -/
theorem crr_charFun_pow_tendsto_gaussian (hσ : 0 < σ) (hT : 0 < T) (t : ℝ) :
    Tendsto (fun n : ℕ => crrStepCharFun r σ T n t ^ n) atTop
      (𝓝 (MeasureTheory.charFun
        (ProbabilityTheory.gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) t)) := by
  have hgauss : MeasureTheory.charFun
      (ProbabilityTheory.gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) t
      = Complex.exp (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2) := by
    rw [ProbabilityTheory.charFun_gaussianReal,
        Real.coe_toNNReal (σ ^ 2 * T) (mul_nonneg (sq_nonneg σ) hT.le)]
    congr 1
    push_cast
    ring
  rw [hgauss]
  exact crr_charFun_pow_tendsto hσ hT t

end QuantFin
