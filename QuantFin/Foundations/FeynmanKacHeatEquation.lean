/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion

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

* `heatConvolution_eq_add_integral_deriv` — the integrated heat-equation form
  `u(t, x) = u(0, x) + ½ ∫₀ᵗ ∂²_x u(s, x) ds` for the Gaussian convolution.
* `feynmanKac_boundary` / `feynmanU_eq_expectation` — `u(t, x) = E[g(x + B_t)]`.
* `expectation_ito` / `expectation_ito_isPreBrownian` — the expectation-form Itô
  identity `E[f(B_t)] = f(0) + ½ ∫₀ᵗ E[f''(B_s)] ds`.
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

/-- **One-sided exponential growth is dominated by the heat kernel.** `e^w · K(t, w)` is
integrable: dominated by `(e^t·√2)·K(2t, w)`, since completing the square gives
`w − w²/(4t) − t = −(w−2t)²/(4t) ≤ 0`, i.e. `e^w·e^{−w²/2t} ≤ e^t·e^{−w²/4t}`. This is the
integrability backbone for growth-controlled payoffs (the call satisfies `|g(z)| ≤ e^z`). -/
private lemma integrable_exp_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun w => Real.exp w * heatKernel t w) volume := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  refine Integrable.mono' ((integrable_heatKernel h2t).const_mul (Real.exp t * Real.sqrt 2))
    ((Real.continuous_exp.mul (continuous_heatKernel t)).aestronglyMeasurable)
    (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg w) (heatKernel_nonneg ht w))]
  have hsqrt : Real.sqrt (2 * Real.pi * (2 * t)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (2 * t) = 2 * (2 * Real.pi * t) from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hexp : Real.exp w * Real.exp (-(w ^ 2) / (2 * t))
      ≤ Real.exp t * Real.exp (-(w ^ 2) / (2 * (2 * t))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : (0:ℝ) ≤ (w - 2 * t) ^ 2 / (4 * t) := by positivity
    have hexpand : (w - 2 * t) ^ 2 / (4 * t)
        = (t + -(w ^ 2) / (2 * (2 * t))) - (w + -(w ^ 2) / (2 * t)) := by
      field_simp
      ring
    linarith [hexpand ▸ hkey]
  rw [heatKernel, heatKernel, hsqrt]
  rw [show Real.exp t * Real.sqrt 2 * ((Real.sqrt 2 * Real.sqrt (2 * Real.pi * t))⁻¹
        * Real.exp (-(w ^ 2) / (2 * (2 * t))))
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp t * Real.exp (-(w ^ 2) / (2 * (2 * t)))) from by
    rw [mul_inv]
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp]
  rw [show Real.exp w * ((Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(w ^ 2) / (2 * t)))
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp w * Real.exp (-(w ^ 2) / (2 * t))) from by ring]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `x`-derivative of the kernel `x ↦ K(t, z − x)`: `∂_x K(t, z−x) = ((z−x)/t)·K(t, z−x)`.
The chain rule on `hasDerivAt_heatKernel_y` (`∂_y K = −(y/t)K`) composed with `∂_x(z−x) = −1`.
This is what lets us differentiate `feynmanU g t x = ∫ g(z)·K(t,z−x) dz` in `x` by moving the
derivative onto the (smooth) kernel — so `g` need only be continuous, never differentiated. -/
private lemma hasDerivAt_heatKernel_sub {t : ℝ} (ht : 0 < t) (z x : ℝ) :
    HasDerivAt (fun x => heatKernel t (z - x))
      ((z - x) / t * heatKernel t (z - x)) x := by
  have h := (hasDerivAt_heatKernel_y ht (z - x)).comp x ((hasDerivAt_id x).const_sub z)
  simpa using h

/-- **`e^w · |w|ⁿ · K(t, w)` is integrable** for every `n`. Via the Gaussian MGF: the set of
exponential moments of `id` under `gaussianReal 0 t` is all of `ℝ`
(`integrableExpSet_id_gaussianReal`), so `|w|ⁿ · e^{1·w}` is `gaussianReal`-integrable
(`integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet`); transfer to the heat kernel
via `integrable_mul_heatKernel_of_gaussian`. Supplies the `∂ₓ`/`∂ₓₓ`-domination majorants for
growth-controlled payoffs. -/
private lemma integrable_exp_mul_abs_pow_heatKernel {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun w => Real.exp w * |w| ^ n * heatKernel t w) volume := by
  have hg : Integrable (fun w => |w| ^ n * Real.exp (1 * w)) (gaussianReal 0 t.toNNReal) :=
    integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
      (by rw [integrableExpSet_fun_id_gaussianReal, interior_univ]; exact Set.mem_univ 1) n
  refine (integrable_mul_heatKernel_of_gaussian ht hg).congr
    (Filter.Eventually.of_forall fun w => ?_)
  show (|w| ^ n * Real.exp (1 * w)) * heatKernel t w = Real.exp w * |w| ^ n * heatKernel t w
  rw [one_mul]; ring

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

/-- **The heat kernel is an approximate identity** (`ε → 0⁺`): for `f` continuous and bounded
(`|f| ≤ Cf`), `∫ f(y)·K(ε, y) dy → f(0)`. Proof by the rescaling `y = √ε·u`, which turns the
integral into `∫ f(√ε·u)·φ(u) du` against the *fixed* standard-normal density
`φ(u) = (2π)^{-1/2} e^{-u²/2}`, followed by dominated convergence (`f(√ε·u) → f(0)` pointwise,
dominated by the integrable `Cf·φ`). This supplies the `ε → 0` boundary value for the FTC. -/
private lemma tendsto_integral_heatKernel_zero {f : ℝ → ℝ} (hfc : Continuous f)
    {Cf : ℝ} (hCf : ∀ x, |f x| ≤ Cf) :
    Tendsto (fun ε => ∫ y, f y * heatKernel ε y ∂volume) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f 0)) := by
  set g : ℝ → ℝ := fun u => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * u ^ 2) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgnn : ∀ u, 0 ≤ g u := fun u => by rw [hg]; positivity
  have hg_int : Integrable g volume :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have hg_int1 : ∫ u, g u ∂volume = 1 := by
    simp only [hg]
    rw [integral_const_mul, integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi from by ring,
      inv_mul_cancel₀ (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)]
  -- rescaling identity `φ(ε) = ∫ u, f(√ε·u)·g(u)` for ε > 0
  have hrw : ∀ ε : ℝ, 0 < ε →
      (∫ y, f y * heatKernel ε y ∂volume) = ∫ u, f (Real.sqrt ε * u) * g u ∂volume := by
    intro ε hε
    have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hεne : ε ≠ 0 := hε.ne'
    have hscale : ∀ u, Real.sqrt ε * heatKernel ε (Real.sqrt ε * u) = g u := by
      intro u
      simp only [hg, heatKernel]
      have hse2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
      have hexp : -(Real.sqrt ε * u) ^ 2 / (2 * ε) = -(1 / 2) * u ^ 2 := by
        rw [mul_pow, hse2]; field_simp
      rw [hexp, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi) ε, mul_inv]
      field_simp
    have hcomp := Measure.integral_comp_mul_left (fun y => f y * heatKernel ε y) (Real.sqrt ε)
    rw [abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt ε)⁻¹), smul_eq_mul] at hcomp
    have hkey : ∀ u, f (Real.sqrt ε * u) * g u
        = Real.sqrt ε * (f (Real.sqrt ε * u) * heatKernel ε (Real.sqrt ε * u)) := by
      intro u; rw [← hscale u]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hkey), integral_const_mul, hcomp,
      ← mul_assoc, mul_inv_cancel₀ hsε.ne', one_mul]
  -- dominated convergence on the rescaled integrand
  have hlimeq : f 0 = ∫ u, f 0 * g u ∂volume := by rw [integral_const_mul, hg_int1, mul_one]
  rw [hlimeq]
  refine Tendsto.congr' (f₁ := fun ε => ∫ u, f (Real.sqrt ε * u) * g u ∂volume)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using (hrw ε hε).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u => Cf * g u) ?_ ?_
    (hg_int.const_mul Cf) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _hε
    exact ((hfc.comp (continuous_const.mul continuous_id)).mul hgc).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε _hε
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgnn u)]
    exact mul_le_mul_of_nonneg_right (hCf _) (hgnn u)
  · refine Filter.Eventually.of_forall fun u => ?_
    apply Tendsto.mul_const
    have hsqrt0 : Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      rwa [Real.sqrt_zero] at h
    have h_inner : Tendsto (fun ε : ℝ => Real.sqrt ε * u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := hsqrt0.mul_const u; rwa [zero_mul] at this
    exact (hfc.tendsto 0).comp h_inner

/-- The heat kernel integrates to `1` over `ℝ` (it is a probability density), for `s > 0`. -/
private lemma integral_heatKernel_eq_one {s : ℝ} (hs : 0 < s) :
    ∫ y, heatKernel s y ∂volume = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (heatKernel_eq_gaussianPDFReal hs))]
  exact integral_gaussianPDFReal_eq_one 0 (Real.toNNReal_pos.mpr hs).ne'

/-- Uniform bound on the time-derivative `φ′(s) = ½∫f″·K(s,·)`: `|φ′(s)| ≤ ½·Cf″` for `s > 0`
(since `∫ K(s,·) = 1` and `|f″| ≤ Cf″`). The majorant making `φ′` interval-integrable on `[0, t]`. -/
private lemma abs_half_integral_ddf_heatKernel_le {s : ℝ} (hs : 0 < s) {f'' : ℝ → ℝ}
    (_hf''c : Continuous f'') {Cf'' : ℝ} (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    |(1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume| ≤ (1 / 2) * Cf'' := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1 / 2)
  calc |∫ y, f'' y * heatKernel s y ∂volume|
      ≤ ∫ y, |f'' y * heatKernel s y| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ y, Cf'' * heatKernel s y ∂volume := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          ((integrable_heatKernel hs).const_mul Cf'') (Filter.Eventually.of_forall fun y => ?_)
        show |f'' y * heatKernel s y| ≤ Cf'' * heatKernel s y
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs y)]
        exact mul_le_mul_of_nonneg_right (hCf'' y) (heatKernel_nonneg hs y)
    _ = Cf'' := by rw [integral_const_mul, integral_heatKernel_eq_one hs, mul_one]

/-- **Itô's formula in expectation — analytic core (Feynman–Kac).** For `f ∈ C²_b` and `t > 0`,
`∫ f(y)·K(t,y) dy = f(0) + ∫₀ᵗ ½·(∫ f″(y)·K(s,y) dy) ds`. The Gaussian convolution at time `t`
equals its `t→0` boundary value `f(0)` plus the integral of its time-derivative
`φ′(s) = ½∫f″·K(s,·)`. Proof: the fundamental theorem of calculus for the continuous-corrected
`Φ` (value `φ(s)` for `s>0`, `f(0)` at `s=0`), whose right derivative on `(0,t)` is `φ′`
(`hasDerivAt_phi_heatEq`), whose boundary value is the approximate-identity limit
(`tendsto_integral_heatKernel_zero`), and whose derivative is interval-integrable (bounded by
`½Cf″`). Under the standard Brownian hypotheses this reads `E[f(Bₜ)] = f(0) + ½∫₀ᵗ E[f″(Bₛ)] ds`
via `feynmanU_eq_expectation`. -/
theorem heatConvolution_eq_add_integral_deriv {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ y, f y * heatKernel t y ∂volume)
      = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  set φ : ℝ → ℝ := fun s => ∫ y, f y * heatKernel s y ∂volume with hφdef
  set ψ : ℝ → ℝ := fun s => (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume with hψdef
  set Φ : ℝ → ℝ := fun s => if 0 < s then φ s else f 0 with hΦdef
  -- (a) `ψ = φ′` is interval-integrable on `[0, t]` (continuous on `(0,t]`, bounded by `½Cf″`)
  have hψ_cont : ∀ s : ℝ, 0 < s → ContinuousAt ψ s := fun s hs =>
    (hasDerivAt_phi hs hf''c hCf'').continuousAt.const_mul (1 / 2)
  have hψ_int : IntervalIntegrable ψ volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine Integrable.mono' (g := fun _ : ℝ => (1 / 2) * Cf'')
      (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (ContinuousOn.aestronglyMeasurable (fun s hs => (hψ_cont s hs.1).continuousWithinAt)
        measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    show ‖(1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume‖ ≤ (1 / 2) * Cf''
    rw [Real.norm_eq_abs]
    exact abs_half_integral_ddf_heatKernel_le hs.1 hf''c hCf''
  -- (b) `Φ` is continuous on `[0, t]`
  have hΦ_cont : ContinuousOn Φ (Set.Icc 0 t) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, ContinuousWithinAt, show Φ 0 = f 0 from if_neg (lt_irrefl 0),
        show Set.Icc (0:ℝ) t = {0} ∪ Set.Ioc 0 t from by
          rw [Set.union_comm, Set.Ioc_union_left ht.le],
        nhdsWithin_union, nhdsWithin_singleton, tendsto_sup]
      refine ⟨by rw [← show Φ 0 = f 0 from if_neg (lt_irrefl 0)]; exact tendsto_pure_nhds Φ 0, ?_⟩
      refine Filter.Tendsto.congr' ?_ ((tendsto_integral_heatKernel_zero hfc hCf).mono_left
        (nhdsWithin_mono 0 Set.Ioc_subset_Ioi_self))
      filter_upwards [self_mem_nhdsWithin] with x hx using (if_pos hx.1).symm
    · have hca : ContinuousAt Φ s := by
        refine (hasDerivAt_phi h0 hfc hCf).continuousAt.congr ?_
        filter_upwards [lt_mem_nhds h0] with x hx using (if_pos hx).symm
      exact hca.continuousWithinAt
  -- (c) right derivative of `Φ` on `(0, t)` is `ψ`
  have hΦ_deriv : ∀ s ∈ Set.Ioo (0:ℝ) t, HasDerivWithinAt Φ (ψ s) (Set.Ioi s) s := by
    intro s hs
    have heq : Φ =ᶠ[nhds s] φ := by
      filter_upwards [lt_mem_nhds hs.1] with x hx using if_pos hx
    exact ((hasDerivAt_phi_heatEq hs.1 hf hf' hf''c hCf hCf' hCf'').congr_of_eventuallyEq
      heq).hasDerivWithinAt
  -- (d) FTC, then read off the boundary values `Φ t = φ t`, `Φ 0 = f 0`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.le hΦ_cont hΦ_deriv hψ_int
  rw [show Φ t = φ t from if_pos ht, show Φ 0 = f 0 from if_neg (lt_irrefl 0)] at hFTC
  linarith [hFTC]

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

/-- **Core transfer.** If `B_t` has law `N(0, t)` (`Measure.map (B t) μ = gaussianReal 0 t.toNNReal`),
the heat-kernel form `feynmanU g t x` equals the expectation `E[g(x + B_t)]`. Factored out of
`feynmanU_eq_expectation` so the same transfer serves both the increment-hypothesis bundle and the
`IsPreBrownian` marginal law. -/
theorem feynmanU_eq_integral_of_map
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ} {t : ℝ}
    (h_aem : AEMeasurable (B t) μ)
    (h_map : Measure.map (B t) μ = gaussianReal 0 t.toNNReal)
    (hg_cont : Continuous g) (ht : 0 < t) (x : ℝ) :
    feynmanU g t x = ∫ ω, g (x + B t ω) ∂μ := by
  have h_eg_cont : Continuous (fun y => g (x + y)) :=
    hg_cont.comp (continuous_const.add continuous_id)
  have h_eg_smeas_map : AEStronglyMeasurable (fun y => g (x + y)) (Measure.map (B t) μ) :=
    h_eg_cont.aestronglyMeasurable
  have h_expect_eq_gauss :
      ∫ ω, g (x + B t ω) ∂μ = ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) := by
    have h_map' : ∫ y, g (x + y) ∂(Measure.map (B t) μ) = ∫ ω, g (x + B t ω) ∂μ :=
      integral_map h_aem h_eg_smeas_map
    rw [← h_map', h_map]
  have h_tN_ne : (t.toNNReal : ℝ≥0) ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  have h_gauss_eq_pdf :
      ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) =
        ∫ y, gaussianPDFReal 0 t.toNNReal y • g (x + y) ∂volume :=
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := t.toNNReal)
      (f := fun y => g (x + y)) h_tN_ne
  have h_pdf_eq_heat : ∀ y,
      gaussianPDFReal 0 t.toNNReal y • g (x + y) = g (x + y) * heatKernel t y := by
    intro y
    rw [← heatKernel_eq_gaussianPDFReal ht y, smul_eq_mul, mul_comm]
  rw [h_expect_eq_gauss, h_gauss_eq_pdf,
    show (fun y => gaussianPDFReal 0 t.toNNReal y • g (x + y))
        = (fun y => g (x + y) * heatKernel t y) from funext h_pdf_eq_heat]
  exact (integral_shift_eq_feynmanU g t x).symm

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
  -- Steps 2–5 are the core transfer, now factored out:
  exact feynmanU_eq_integral_of_map (hB_meas t).aemeasurable h_map_Bt hg_cont ht x

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

/-- **Itô's formula in expectation** (Dynkin / Kolmogorov form). For a Brownian motion `B`
(`B 0 = 0` a.s., Gaussian increments `B_t − B_s ∼ N(0, t−s)`, each `B_t` measurable) and
`f ∈ C²_b`, `E[f(Bₜ)] = f(0) + ½·∫₀ᵗ E[f″(Bₛ)] ds` for `t > 0`. This is the expectation form of
the analytic Feynman–Kac identity `heatConvolution_eq_add_integral_deriv`, transported across the
bridge `feynmanU_eq_expectation` (`∫ g·K(r,·) = E[g(B_r)]`). The `½ f″` term is the signature of
the quadratic variation of Brownian motion — the source of the Itô correction. -/
theorem expectation_ito
    {B : ℝ → Ω → ℝ}
    (hB_meas : ∀ t, Measurable (B t))
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hB_gauss : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ∃ v : NNReal, (v : ℝ) = t - s ∧
        Measure.map (fun ω => B t ω - B s ω) μ = gaussianReal 0 v)
    {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ ω, f (B t ω) ∂μ) = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ ω, f'' (B s ω) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  -- the heat-kernel ↔ expectation bridge, for any continuous `g` and time `r > 0`
  have hbridge : ∀ (g : ℝ → ℝ), Continuous g → ∀ {r : ℝ}, 0 < r →
      (∫ y, g y * heatKernel r y ∂volume) = ∫ ω, g (B r ω) ∂μ := by
    intro g hgc r hr
    have h1 := integral_shift_eq_feynmanU g r 0
    simp only [zero_add] at h1
    rw [h1, feynmanU_eq_expectation hB_meas hB_zero hB_gauss hgc hr 0]
    simp only [zero_add]
  rw [← hbridge f hfc ht, heatConvolution_eq_add_integral_deriv ht hf hf' hf''c hCf hCf' hCf'']
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [Set.uIoc_of_le ht.le] at hs
  show (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume = (1 / 2) * ∫ ω, f'' (B s ω) ∂μ
  rw [hbridge f'' hf''c hs.1]

/-- **Itô's formula in expectation for a pre-Brownian motion** — the repo-standard `IsPreBrownian`
(Degenne) reading of `expectation_ito`. For `f ∈ C²_b` and `t > 0`,
`E[f(X_t)] = f(0) + ½·∫₀ᵗ E[f″(X_s)] ds`. The increment-law hypotheses are discharged from the
marginal law `IsPreBrownian.hasLaw_eval` through the shared transfer `feynmanU_eq_integral_of_map`.
(`X` is `ℝ≥0`-indexed; the `∫₀ᵗ` runs over real `s`, so `X` is read at `·.toNNReal`.) -/
theorem expectation_ito_isPreBrownian {X : ℝ≥0 → Ω → ℝ} [IsPreBrownian X μ]
    {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ ω, f (X t.toNNReal ω) ∂μ)
      = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ ω, f'' (X s.toNNReal ω) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hbridge : ∀ (g : ℝ → ℝ), Continuous g → ∀ {r : ℝ}, 0 < r →
      (∫ y, g y * heatKernel r y ∂volume) = ∫ ω, g (X r.toNNReal ω) ∂μ := by
    intro g hgc r hr
    have h1 := integral_shift_eq_feynmanU g r 0
    simp only [zero_add] at h1
    rw [h1, feynmanU_eq_integral_of_map (B := fun s => X s.toNNReal) (t := r)
      (IsPreBrownian.aemeasurable (P := μ) r.toNNReal)
      (IsPreBrownian.hasLaw_eval (P := μ) r.toNNReal).map_eq hgc hr 0]
    simp only [zero_add]
  rw [← hbridge f hfc ht, heatConvolution_eq_add_integral_deriv ht hf hf' hf''c hCf hCf' hCf'']
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [Set.uIoc_of_le ht.le] at hs
  show (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume = (1 / 2) * ∫ ω, f'' (X s.toNNReal ω) ∂μ
  rw [hbridge f'' hf''c hs.1]

end FeynmanKacHeatEquation
end QuantFin
