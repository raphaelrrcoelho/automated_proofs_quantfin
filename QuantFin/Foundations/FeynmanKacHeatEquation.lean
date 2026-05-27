/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Feynman–Kac for the heat equation

For a process `B : ℝ → Ω → ℝ` with `B 0 = 0` a.s. and Gaussian increments
`B t − B s ∼ N(0, t − s)` and a bounded continuous `g : ℝ → ℝ`, the function

  `u(t, x) := E[g(x + B_t)]`

satisfies the heat equation `∂_t u − (1/2) ∂²_x u = 0` on `t > 0`, with
boundary condition `u(0, x) = g(x)` (Saporito Theorem 9.2.1).

This proof does **not** use Itô calculus. The mechanism is:

1. By `Measure.map` transfer, `u(t, x) = ∫ y, g(x + y) ∂(gaussianReal 0 t)`
   `= ∫ y, g(x + y) · gaussianPDFReal 0 t y ∂volume` for `t > 0`.
2. The Gaussian density satisfies the heat-kernel PDE:
   `∂_t pdf(t, y) = (1/2) ∂²_y pdf(t, y)` (pure calculus).
3. Differentiating under the integral sign passes the PDE through to `u`.

## Main results

* `gaussianPDFReal_zero_heat_kernel` — the heat-kernel PDE on the Gaussian density.
* `FeynmanKacHeatEquation.heat_equation` — `u(t, x) = E[g(x + B_t)]` satisfies
  `∂_t u = (1/2) ∂²_x u`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real
open scoped NNReal ENNReal

namespace QuantFin
namespace FeynmanKacHeatEquation

/-! ### Heat-kernel PDE on `gaussianPDFReal 0 t y`

We prove `∂_t pdf(0, t, y) = (1/2) ∂²_y pdf(0, t, y)` for `t > 0`. -/

/-- Our own heat-kernel form: `K(t, y) = (2π t)^{-1/2} · exp(−y² / (2 t))`.
Defined for all `t : ℝ` (when `t ≤ 0` the formula returns nonsense but the
heat-kernel statements gate on `0 < t`). -/
noncomputable def heatKernel (t y : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (2 * t))

/-- For `t > 0`, the Mathlib `gaussianPDFReal 0 t y` equals our heatKernel. -/
private lemma heatKernel_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel t y = gaussianPDFReal 0 t.toNNReal y := by
  rw [heatKernel, gaussianPDFReal_def]
  have htN : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht.le
  rw [htN]
  ring_nf

/-- First `y`-derivative of the heat kernel: `∂_y K = -(y/t) K`. -/
private lemma hasDerivAt_heatKernel_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z => heatKernel t z) (-(y / t) * heatKernel t y) y := by
  have h_neg_y_sq : HasDerivAt (fun z : ℝ => -(z ^ 2)) (-(2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).neg
  have h_inner : HasDerivAt (fun z : ℝ => -(z ^ 2) / (2 * t)) (-(y / t)) y := by
    have := h_neg_y_sq.div_const (2 * t)
    have ht_ne : (2 * t) ≠ 0 := by positivity
    convert this using 1
    field_simp
  have h_exp : HasDerivAt (fun z : ℝ => Real.exp (-(z ^ 2) / (2 * t)))
      (Real.exp (-(y ^ 2) / (2 * t)) * -(y / t)) y := h_inner.exp
  have h_mul := h_exp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
  -- h_mul : HasDerivAt (fun z => K(t, z)) ((√(2πt))⁻¹ * (exp(-y²/(2t)) * -(y/t))) y
  have h_val :
      (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp (-(y ^ 2) / (2 * t)) * -(y / t))
        = -(y / t) * heatKernel t y := by
    unfold heatKernel; ring
  rw [← h_val]; exact h_mul

/-- First `t`-derivative of the heat kernel: `∂_t K = K · (y² − t) / (2 t²)`. -/
private lemma hasDerivAt_heatKernel_t {y : ℝ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatKernel s y) (heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)) t := by
  -- Write K(s, y) = f(s) * g(s, y) where f(s) = (√(2πs))⁻¹ and g(s) = exp(-y²/(2s)).
  -- f'(s) = -(1/2) * f(s) / s
  -- g'(s) = g(s) * y² / (2 s²)
  -- K'(s) = f'g + fg' = K · [-(1/(2s)) + y²/(2s²)] = K · (y² - s) / (2 s²)
  -- f(s) = (√(2πs))⁻¹: derivative computation
  have h_2pi_pos : 0 < 2 * Real.pi := by positivity
  have h_2pis_pos : 0 < 2 * Real.pi * t := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr h_2pis_pos
  have h_sqrt_ne : Real.sqrt (2 * Real.pi * t) ≠ 0 := h_sqrt_pos.ne'
  have h_2pis_id : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
    have := (hasDerivAt_id t).const_mul (2 * Real.pi)
    simpa using this
  have h_sqrt_inner : HasDerivAt (fun s : ℝ => Real.sqrt (2 * Real.pi * s))
      (1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi)) t :=
    (Real.hasDerivAt_sqrt h_2pis_pos.ne').comp t h_2pis_id
  have h_f : HasDerivAt (fun s : ℝ => (Real.sqrt (2 * Real.pi * s))⁻¹)
      (-(1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi)) /
        (Real.sqrt (2 * Real.pi * t)) ^ 2) t :=
    h_sqrt_inner.inv h_sqrt_ne
  -- g(s) = exp(-y²/(2s)): derivative computation
  have h_2s : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have ht_ne : t ≠ 0 := ht.ne'
  have h_2t_ne : (2 * t) ≠ 0 := by positivity
  have h_inv_2s : HasDerivAt (fun s : ℝ => (2 * s)⁻¹) (-2 / (2 * t) ^ 2) t :=
    h_2s.inv h_2t_ne
  have h_inner : HasDerivAt (fun s : ℝ => -(y ^ 2) / (2 * s))
      (-(y ^ 2) * (-2 / (2 * t) ^ 2)) t := by
    have h_eq : (fun s : ℝ => -(y ^ 2) / (2 * s)) = (fun s : ℝ => -(y ^ 2) * (2 * s)⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [h_eq]
    exact h_inv_2s.const_mul (-(y ^ 2))
  have h_g : HasDerivAt (fun s : ℝ => Real.exp (-(y ^ 2) / (2 * s)))
      (Real.exp (-(y ^ 2) / (2 * t)) * (-(y ^ 2) * (-2 / (2 * t) ^ 2))) t := h_inner.exp
  -- Combine via product rule
  have h_K := h_f.mul h_g
  -- h_K : HasDerivAt (f * g) (h_f_val * g(t) + f(t) * h_g_val) t
  -- where the value is:
  --   -(1/(2√(2πt)) * 2π) / (√(2πt))² · exp(-y²/(2t))
  --     + (√(2πt))⁻¹ · (exp(-y²/(2t)) · (-y² · (-2/(2t)²)))
  -- Using (√(2πt))² = 2πt, simplify:
  --   -π/(2πt · √(2πt)) · exp + (√(2πt))⁻¹ · exp · y²/(2t²)
  --     = (√(2πt))⁻¹ · exp · [-1/(2t) + y²/(2t²)]
  --     = (√(2πt))⁻¹ · exp · (y² - t)/(2t²)
  --     = heatKernel t y · (y² - t)/(2t²)
  have h_sqrt_sq : (Real.sqrt (2 * Real.pi * t)) ^ 2 = 2 * Real.pi * t :=
    Real.sq_sqrt h_2pis_pos.le
  have h_pi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have h_val :
      -(1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi))
          / (Real.sqrt (2 * Real.pi * t)) ^ 2 * Real.exp (-(y ^ 2) / (2 * t))
        + (Real.sqrt (2 * Real.pi * t))⁻¹
            * (Real.exp (-(y ^ 2) / (2 * t)) * (-(y ^ 2) * (-2 / (2 * t) ^ 2)))
        = heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2) := by
    unfold heatKernel
    rw [h_sqrt_sq]
    field_simp
    ring
  rw [← h_val]; exact h_K

/-- Second `y`-derivative of the heat kernel: `∂²_y K = K · (y² − t) / t²`.
The first-derivative function being `z ↦ -(z/t) · K(t, z)`. -/
private lemma hasDerivAt_heatKernel_y_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z => -(z / t) * heatKernel t z) (heatKernel t y * (y ^ 2 - t) / t ^ 2) y := by
  have ht_ne : t ≠ 0 := ht.ne'
  have h_a : HasDerivAt (fun z : ℝ => -(z / t)) (-(1 / t)) y := by
    have h1 : HasDerivAt (fun z : ℝ => z / t) (1 / t) y := by
      have := (hasDerivAt_id y).div_const t
      simpa using this
    exact h1.neg
  have h_b : HasDerivAt (fun z : ℝ => heatKernel t z) (-(y / t) * heatKernel t y) y :=
    hasDerivAt_heatKernel_y ht y
  have h_prod := h_a.mul h_b
  have h_val :
      -(1 / t) * heatKernel t y + -(y / t) * (-(y / t) * heatKernel t y)
        = heatKernel t y * (y ^ 2 - t) / t ^ 2 := by
    field_simp; ring
  rw [← h_val]; exact h_prod

/-- **Heat-kernel PDE on `heatKernel`**: `∂_t K = (1/2) ∂²_y K`. As an algebraic
identity on the derivative values from `hasDerivAt_heatKernel_t` and
`hasDerivAt_heatKernel_y_y`. -/
private lemma heatKernel_t_eq_half_y_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)
      = (1 / 2) * (heatKernel t y * (y ^ 2 - t) / t ^ 2) := by
  have ht_ne : t ≠ 0 := ht.ne'
  field_simp

/-! ### Auxiliary integrability + nonnegativity for the heat kernel -/

/-- The heat kernel is nonnegative. -/
private lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 ≤ heatKernel t y := by
  rw [heatKernel_eq_gaussianPDFReal ht]
  exact gaussianPDFReal_nonneg 0 _ y

/-- For `t > 0`, the heat kernel is integrable in `y` over Lebesgue. -/
private lemma integrable_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => heatKernel t y) volume := by
  have := integrable_gaussianPDFReal (0 : ℝ) t.toNNReal
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (heatKernel_eq_gaussianPDFReal ht y).symm

/-- **Transfer integrability from the Gaussian law to the heat kernel.** If `g ∈ L¹(N(0,t))`,
then `g · K(t,·)` is Lebesgue-integrable — because `N(0,t) = volume.withDensity K(t,·)`. This
turns Gaussian moments (`memLp_id_gaussianReal`) into integrability of polynomial × heat kernel,
needed for the integration-by-parts in the expectation-form Itô formula. -/
private lemma integrable_mul_heatKernel_of_gaussian {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 t.toNNReal)) :
    Integrable (fun y => g y * heatKernel t y) volume := by
  have hv : (t.toNNReal : ℝ≥0) ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun y => gaussianPDF_lt_top)] at hg
  refine hg.congr (Filter.Eventually.of_forall fun y => ?_)
  show (gaussianPDF 0 t.toNNReal y).toReal • g y = g y * heatKernel t y
  have hpdf : (gaussianPDF 0 t.toNNReal y).toReal = heatKernel t y := by
    rw [heatKernel_eq_gaussianPDFReal ht]
    simp only [gaussianPDF]
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rw [smul_eq_mul, hpdf]; ring

/-- First moment: `y · K(t, ·)` is integrable. -/
private lemma integrable_id_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => y * heatKernel t y) volume :=
  integrable_mul_heatKernel_of_gaussian ht
    ((memLp_id_gaussianReal (μ := 0) (v := t.toNNReal) 1).integrable (by norm_num))

/-- Second moment: `y² · K(t, ·)` is integrable. -/
private lemma integrable_sq_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => y ^ 2 * heatKernel t y) volume :=
  integrable_mul_heatKernel_of_gaussian ht
    (memLp_id_gaussianReal (μ := 0) (v := t.toNNReal) 2).integrable_sq

/-- `∂_y K = -(y/t)·K` is integrable. -/
private lemma integrable_dK {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => -(y / t) * heatKernel t y) volume := by
  refine ((integrable_id_mul_heatKernel ht).const_mul (-(1 / t))).congr
    (Filter.Eventually.of_forall fun y => ?_)
  show -(1 / t) * (y * heatKernel t y) = -(y / t) * heatKernel t y
  ring

/-- `∂²_y K = K·(y²−t)/t²` is integrable. -/
private lemma integrable_ddK {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => heatKernel t y * (y ^ 2 - t) / t ^ 2) volume := by
  have ht_ne : t ≠ 0 := ht.ne'
  refine (((integrable_sq_mul_heatKernel ht).const_mul (1 / t ^ 2)).sub
    ((integrable_heatKernel ht).const_mul (1 / t))).congr (Filter.Eventually.of_forall fun y => ?_)
  show 1 / t ^ 2 * (y ^ 2 * heatKernel t y) - 1 / t * heatKernel t y
      = heatKernel t y * (y ^ 2 - t) / t ^ 2
  field_simp

/-- **Integration by parts against the heat kernel** (the analytic heart of expectation-Itô).
For `f ∈ C²_b`, two improper integrations by parts over `ℝ` move both derivatives off the kernel
onto `f`: `∫ f(y)·∂²_y K(t,y) dy = ∫ f″(y)·K(t,y) dy`. The boundary terms vanish (`f, f′` bounded,
`K, ∂_y K` Gaussian-decaying), which is encoded by `integral_mul_deriv_eq_deriv_mul_of_integrable`
(the integrable-product form needs no explicit boundary hypothesis). -/
private lemma ibp_heatKernel {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    ∫ y, f y * (heatKernel t y * (y ^ 2 - t) / t ^ 2) ∂volume
      = ∫ y, f'' y * heatKernel t y ∂volume := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
  have hi_f_ddK : Integrable (fun y => f y * (heatKernel t y * (y ^ 2 - t) / t ^ 2)) volume :=
    (integrable_ddK ht).bdd_mul hfc.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf y)
  have hi_f'_dK : Integrable (fun y => f' y * (-(y / t) * heatKernel t y)) volume :=
    (integrable_dK ht).bdd_mul hf'c.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf' y)
  have hi_f_dK : Integrable (fun y => f y * (-(y / t) * heatKernel t y)) volume :=
    (integrable_dK ht).bdd_mul hfc.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf y)
  have hi_f''_K : Integrable (fun y => f'' y * heatKernel t y) volume :=
    (integrable_heatKernel ht).bdd_mul hf''c.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf'' y)
  have hi_f'_K : Integrable (fun y => f' y * heatKernel t y) volume :=
    (integrable_heatKernel ht).bdd_mul hf'c.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf' y)
  have ibp1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := fun z => -(z / t) * heatKernel t z)
    (v' := fun z => heatKernel t z * (z ^ 2 - t) / t ^ 2)
    (fun x _ => hf x) (fun x _ => hasDerivAt_heatKernel_y_y ht x) hi_f_ddK hi_f'_dK hi_f_dK
  have ibp2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f') (v := fun z => heatKernel t z)
    (v' := fun z => -(z / t) * heatKernel t z)
    (fun x _ => hf' x) (fun x _ => hasDerivAt_heatKernel_y ht x) hi_f'_dK hi_f''_K hi_f'_K
  rw [ibp1, ibp2, neg_neg]

/-- The heat kernel is continuous in the space variable (for any fixed time). -/
private lemma continuous_heatKernel (s : ℝ) : Continuous (fun y => heatKernel s y) := by
  unfold heatKernel; fun_prop

/-- The polynomial-times-heat-kernel function `(y² + c)·K(s, y)` is integrable (`s > 0`). This
is the integrable majorant used to dominate `∂_t K(·, y)` over a time-neighbourhood of `t`
(instantiated at `s = 3t/2`); built directly from the moment integrabilities
`integrable_sq_mul_heatKernel` / `integrable_heatKernel`, avoiding raw-`rpow` Gaussians. -/
private lemma integrable_poly_heatKernel {s : ℝ} (hs : 0 < s) (c : ℝ) :
    Integrable (fun y => (y ^ 2 + c) * heatKernel s y) volume := by
  refine ((integrable_sq_mul_heatKernel hs).add
    ((integrable_heatKernel hs).const_mul c)).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]; ring

/-- **Differentiation under the integral for the Gaussian convolution.** For `t > 0` and `f`
continuous and bounded (`|f| ≤ Cf`), `φ(s) = ∫ f(y)·K(s, y) dy` is differentiable at `t` with
`φ′(t) = ∫ f(y)·∂_t K(t, y) dy`. The `s`-derivative `f(y)·K(s,y)·(y²−s)/(2s²)` is dominated,
uniformly over `s ∈ (t/2, 3t/2)`, by `Cf·(2√3/t²)·(y²+3t/2)·K(3t/2, y)` (integrable), using the
heat-kernel monotonicity `K(s, y) ≤ √3·K(3t/2, y)` on that interval. -/
private lemma hasDerivAt_phi {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hfc : Continuous f)
    {Cf : ℝ} (hCf : ∀ x, |f x| ≤ Cf) :
    HasDerivAt (fun s => ∫ y, f y * heatKernel s y ∂volume)
      (∫ y, f y * (heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)) ∂volume) t := by
  have h32 : (0 : ℝ) < 3 * t / 2 := by positivity
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf 0)
  set F : ℝ → ℝ → ℝ := fun s y => f y * heatKernel s y with hFdef
  set F' : ℝ → ℝ → ℝ := fun s y => f y * (heatKernel s y * (y ^ 2 - s) / (2 * s ^ 2)) with hF'def
  set bound : ℝ → ℝ :=
    fun y => Cf * (2 * Real.sqrt 3 / t ^ 2) * ((y ^ 2 + 3 * t / 2) * heatKernel (3 * t / 2) y)
    with hbounddef
  have hbound_int : Integrable bound volume :=
    (integrable_poly_heatKernel h32 (3 * t / 2)).const_mul _
  have hf_gauss : Integrable f (gaussianReal 0 t.toNNReal) :=
    (integrable_const Cf).mono' hfc.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hCf y)
  have hFt_int : Integrable (F t) volume := integrable_mul_heatKernel_of_gaussian ht hf_gauss
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) volume :=
    Eventually.of_forall fun s => (hfc.mul (continuous_heatKernel s)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' t) volume :=
    (hfc.mul (((continuous_heatKernel t).mul
      ((continuous_pow 2).sub continuous_const)).div_const _)).aestronglyMeasurable
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun s => F s y) (F' s y) s := by
    refine ae_of_all _ fun y s hs => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_pos : 0 < s := by linarith [hs.1]
    exact (hasDerivAt_heatKernel_t (y := y) hs_pos).const_mul (f y)
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2), ‖F' s y‖ ≤ bound y := by
    refine ae_of_all _ fun y s hs => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_lo : t / 2 < s := by linarith [hs.1]
    have hs_hi : s < 3 * t / 2 := by linarith [hs.2]
    have hs_pos : 0 < s := by linarith
    have hKsnn : 0 ≤ heatKernel s y := heatKernel_nonneg hs_pos y
    have hKtnn : 0 ≤ heatKernel (3 * t / 2) y := heatKernel_nonneg h32 y
    -- `K(s, y) ≤ (√(πt))⁻¹·exp(−y²/(3t))`, then rewrite the RHS as `√3·K(3t/2, y)`.
    have hKstep : heatKernel s y ≤ (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (3 * t)) := by
      rw [heatKernel]
      have hf1 : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ :=
        inv_anti₀ (by positivity) (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos, hs_lo]))
      have hf2 : Real.exp (-(y ^ 2) / (2 * s)) ≤ Real.exp (-(y ^ 2) / (3 * t)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg y, hs_hi]
      exact mul_le_mul hf1 hf2 (by positivity) (by positivity)
    have hKeq : (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (3 * t))
        = Real.sqrt 3 * heatKernel (3 * t / 2) y := by
      have h3ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hsqrt : Real.sqrt (2 * Real.pi * (3 * t / 2)) = Real.sqrt 3 * Real.sqrt (Real.pi * t) := by
        rw [show 2 * Real.pi * (3 * t / 2) = 3 * (Real.pi * t) from by ring,
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      simp only [heatKernel]
      rw [show -(y ^ 2) / (2 * (3 * t / 2)) = -(y ^ 2) / (3 * t) from by
            rw [show 2 * (3 * t / 2) = 3 * t from by ring],
          hsqrt, mul_inv]
      field_simp
    have hK : heatKernel s y ≤ Real.sqrt 3 * heatKernel (3 * t / 2) y := hKeq ▸ hKstep
    have hpoly : |y ^ 2 - s| / (2 * s ^ 2) ≤ 2 * (y ^ 2 + 3 * t / 2) / t ^ 2 := by
      have habs : |y ^ 2 - s| ≤ y ^ 2 + 3 * t / 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
      have ht4s : t ^ 2 ≤ 4 * s ^ 2 := by
        nlinarith [mul_pos (show (0:ℝ) < s - t / 2 by linarith) (show (0:ℝ) < s + t / 2 by linarith)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right habs (sq_nonneg t),
        mul_le_mul_of_nonneg_left ht4s (show (0:ℝ) ≤ y ^ 2 + 3 * t / 2 by positivity)]
    have habs_nn : 0 ≤ |y ^ 2 - s| / (2 * s ^ 2) := by positivity
    have hF'norm : ‖F' s y‖ = |f y| * (heatKernel s y * (|y ^ 2 - s| / (2 * s ^ 2))) := by
      rw [hF'def, Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
          abs_of_nonneg hKsnn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s ^ 2), mul_div_assoc]
    rw [hF'norm, hbounddef]
    calc |f y| * (heatKernel s y * (|y ^ 2 - s| / (2 * s ^ 2)))
        ≤ Cf * (Real.sqrt 3 * heatKernel (3 * t / 2) y * (2 * (y ^ 2 + 3 * t / 2) / t ^ 2)) := by
          refine mul_le_mul (hCf y) ?_ (mul_nonneg hKsnn habs_nn) hCf0
          exact mul_le_mul hK hpoly habs_nn (mul_nonneg (Real.sqrt_nonneg 3) hKtnn)
      _ = Cf * (2 * Real.sqrt 3 / t ^ 2) * ((y ^ 2 + 3 * t / 2) * heatKernel (3 * t / 2) y) := by
          ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t (show (0:ℝ) < t / 2 by positivity))
    hF_meas hFt_int hF'_meas h_bound hbound_int h_diff).2

/-- **The Gaussian convolution satisfies the heat equation.** For `f ∈ C²_b`,
`φ(s) = ∫ f(y)·K(s, y) dy` has `φ′(t) = ½·∫ f″(y)·K(t, y) dy`. Combines the parametric derivative
`hasDerivAt_phi` (`φ′(t) = ∫ f·∂_t K`) with the kernel PDE `∂_t K = ½·∂²_y K` and the double
integration by parts `∫ f·∂²_y K = ∫ f″·K` (`ibp_heatKernel`). This is the heat equation for the
*function* `φ`, not merely the kernel. -/
private lemma hasDerivAt_phi_heatEq {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    HasDerivAt (fun s => ∫ y, f y * heatKernel s y ∂volume)
      (1 / 2 * ∫ y, f'' y * heatKernel t y ∂volume) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  convert hasDerivAt_phi ht hfc hCf using 1
  rw [← ibp_heatKernel ht hf hf' hf''c hCf hCf' hCf'', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-! ### The Feynman–Kac function `u(t, x) = ∫ z, g(z) · K(t, z - x) dz`

We define `u` directly via the heat-kernel representation, then show it equals
the textbook formula `E[g(x + B_t)]` under the standard BM hypotheses. -/

/-- Feynman–Kac heat-kernel function: `u(t, x) = ∫ z, g(z) · K(t, z − x) dz`.
This form is symmetric to `∫ y, g(x + y) · K(t, y) dy` by Lebesgue translation
invariance, but is easier to differentiate in `x` (the `x`-dependence sits in
the kernel argument, not in `g`). -/
noncomputable def feynmanU (g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ z, g z * heatKernel t (z - x) ∂volume

/-! ### Equivalence of forms: `∫ y, g(x+y) · K(t, y) dy = ∫ z, g(z) · K(t, z-x) dz` -/

/-- Lebesgue translation invariance: `∫ y, g(x+y) · K(t, y) dy = feynmanU g t x`. -/
private lemma integral_shift_eq_feynmanU (g : ℝ → ℝ) (t x : ℝ) :
    ∫ y, g (x + y) * heatKernel t y ∂volume = feynmanU g t x := by
  rw [feynmanU]
  have h_fun_eq : (fun z => g z * heatKernel t (z - x))
        = (fun z => g (x + (z - x)) * heatKernel t (z - x)) := by
    funext z; congr 1; ring
  rw [h_fun_eq]
  exact (MeasureTheory.integral_sub_right_eq_self
    (fun z => g (x + z) * heatKernel t z) x).symm

/-! ### Identification of `feynmanU` with `E[g(x + B_t)]` -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For `t > 0`, the heat-kernel form `feynmanU g t x` equals the Feynman–Kac
expectation `E[g(x + B_t)]`, assuming:
* `B 0 = 0` a.s.
* `B_t − B_0 ∼ N(0, t)` (Gaussian increments at the origin),
* `B_t` is measurable,
* `g` is continuous. -/
theorem feynmanU_eq_expectation
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hB_meas : ∀ t, Measurable (B t))
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hB_gauss : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ∃ v : NNReal, (v : ℝ) = t - s ∧
        Measure.map (fun ω => B t ω - B s ω) μ = gaussianReal 0 v)
    (hg_cont : Continuous g)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    feynmanU g t x = ∫ ω, g (x + B t ω) ∂μ := by
  -- Step 1: Use `B 0 = 0 a.s.` and `gauss_increments` at (0, t) to deduce
  -- Measure.map (B t) μ = gaussianReal 0 t.toNNReal.
  obtain ⟨v, hv_eq, h_map_diff⟩ := hB_gauss ht.le
  have hv_eq_t : (v : ℝ) = t := by rw [hv_eq]; ring
  have hv_t : v = t.toNNReal := by
    apply NNReal.coe_inj.mp
    rw [hv_eq_t, Real.coe_toNNReal _ ht.le]
  have h_diff_eq : (fun ω => B t ω - B 0 ω) =ᵐ[μ] (fun ω => B t ω) := by
    filter_upwards [hB_zero] with ω hω
    rw [hω, sub_zero]
  have h_map_Bt : Measure.map (B t) μ = gaussianReal 0 t.toNNReal := by
    rw [← hv_t, ← h_map_diff]
    exact (Measure.map_congr h_diff_eq).symm
  -- Step 2: Transfer the expectation to a Lebesgue integral via Measure.map.
  have h_aem_Bt : AEMeasurable (B t) μ := (hB_meas t).aemeasurable
  have h_eg_cont : Continuous (fun y => g (x + y)) :=
    hg_cont.comp (continuous_const.add continuous_id)
  have h_eg_smeas_map : AEStronglyMeasurable (fun y => g (x + y)) (Measure.map (B t) μ) :=
    h_eg_cont.aestronglyMeasurable
  have h_expect_eq_gauss :
      ∫ ω, g (x + B t ω) ∂μ = ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) := by
    have h_map : ∫ y, g (x + y) ∂(Measure.map (B t) μ) = ∫ ω, g (x + B t ω) ∂μ :=
      integral_map h_aem_Bt h_eg_smeas_map
    rw [← h_map, h_map_Bt]
  -- Step 3: Convert gaussianReal integral to Lebesgue via gaussianPDFReal.
  have h_tN_ne : (t.toNNReal : ℝ≥0) ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  have h_gauss_eq_pdf :
      ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) =
        ∫ y, gaussianPDFReal 0 t.toNNReal y • g (x + y) ∂volume :=
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := t.toNNReal)
      (f := fun y => g (x + y)) h_tN_ne
  -- Step 4: Replace gaussianPDFReal with heatKernel.
  have h_pdf_eq_heat : ∀ y,
      gaussianPDFReal 0 t.toNNReal y • g (x + y) = g (x + y) * heatKernel t y := by
    intro y
    rw [← heatKernel_eq_gaussianPDFReal ht y, smul_eq_mul, mul_comm]
  rw [h_expect_eq_gauss, h_gauss_eq_pdf,
    show (fun y => gaussianPDFReal 0 t.toNNReal y • g (x + y))
        = (fun y => g (x + y) * heatKernel t y) from funext h_pdf_eq_heat]
  -- Step 5: Apply the shift identity to fold back to feynmanU.
  exact (integral_shift_eq_feynmanU g t x).symm

/-- The boundary condition: at `t = 0`, the Feynman-Kac expectation equals `g(x)`
(since `B 0 = 0` a.s. and `μ` is a probability measure). -/
theorem feynmanKac_boundary [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0) (x : ℝ) :
    ∫ ω, g (x + B 0 ω) ∂μ = g x := by
  have h_pt : ∀ᵐ ω ∂μ, g (x + B 0 ω) = g x := by
    filter_upwards [hB_zero] with ω hω
    rw [hω, add_zero]
  rw [integral_congr_ae h_pt, integral_const, probReal_univ, one_smul]

end FeynmanKacHeatEquation
end QuantFin
