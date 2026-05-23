/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion

/-!
# The adapted Itô isometry (the increment-independence cornerstone)

The Wiener integral (`Foundations/WienerIntegralL2.lean`) handles
*deterministic* integrands: there the cross-terms vanish by the BM
covariance `E[(B_t-B_s)(B_v-B_u)] = vol((s,t]∩(u,v])`. That is *not* the
Itô integral. The Itô integral allows a **random, adapted** integrand
`φ`, and the cross-terms vanish for a different, deeper reason: the next
increment `B_{t₁} - B_{t₀}` is *independent of the past* `𝓕_{t₀}` (the weak
Markov property `IsPreBrownian.indepFun_shift`), and has mean zero.

This file builds that genuinely-stochastic core, grounded directly on
Degenne's `IsPreBrownian.indepFun_shift` and `hasLaw_sub`. Adaptedness is
encoded faithfully as factoring through the *past process*
`fun (t : Set.Iic t₀) ↦ B t ω` — the natural Brownian filtration, which is
exactly what `indepFun_shift` is stated against.

## Crux results

* `adapted_indepFun_increment` — an integrand adapted to `𝓕_{t₀}` is
  independent of the forward increment `B_{t₁} - B_{t₀}`.
* `integral_adapted_mul_increment` — **martingale-difference property**:
  `E[φ · (B_{t₁} - B_{t₀})] = 0` for `φ` adapted and integrable. This is
  the discrete statement that the Itô integral is a martingale.
* `integral_adapted_sq_mul_increment_sq` — **isometry kernel**:
  `E[φ² · (B_{t₁} - B_{t₀})²] = E[φ²] · (t₁ - t₀)`.
-/

namespace QuantFin
namespace ItoIsometryAdapted

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

/-- The past process up to time `t₀`: `ω ↦ (fun t : Iic t₀ ↦ B t ω)`.
This is the random variable generating the natural filtration `𝓕_{t₀}`. -/
def pastProcess (B : ℝ≥0 → Ω → ℝ) (t₀ : ℝ≥0) : Ω → (Set.Iic t₀ → ℝ) :=
  fun ω t => B t ω

/-- A function `φ : Ω → ℝ` is **adapted at `t₀`** if it factors through the
past process via a measurable map — i.e. it is `𝓕_{t₀}`-measurable in the
natural Brownian filtration. -/
def AdaptedAt (B : ℝ≥0 → Ω → ℝ) (t₀ : ℝ≥0) (φ : Ω → ℝ) : Prop :=
  ∃ g : (Set.Iic t₀ → ℝ) → ℝ, Measurable g ∧ φ = g ∘ pastProcess B t₀

/-- Measurability of an adapted integrand (factors through the measurable
past process). -/
theorem AdaptedAt.measurable (hBmeas : ∀ t, Measurable (B t)) {t₀ : ℝ≥0}
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) : Measurable φ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact hg.comp (measurable_pi_lambda _ fun _ => hBmeas _)

/-! ### Adaptedness algebra (the natural Brownian filtration `𝓕_{t₀}`)

`AdaptedAt B t₀` behaves as a `𝓕_{t₀}`-measurability predicate: it contains
each `B u` for `u ≤ t₀`, is monotone in `t₀`, and is closed under products
and differences. This is exactly the closure needed to certify that the
cross-term factor `φⱼ · ΔBⱼ · φₖ` is `𝓕_{tₖ}`-measurable. -/

/-- `B u` is adapted at any later time `t₀ ≥ u`. -/
theorem adaptedAt_eval {t₀ u : ℝ≥0} (hu : u ≤ t₀) : AdaptedAt B t₀ (B u) :=
  ⟨fun p => p ⟨u, hu⟩, measurable_pi_apply _, rfl⟩

/-- Adaptedness is monotone in the time index. -/
theorem AdaptedAt.mono {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) {φ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) : AdaptedAt B t₁ φ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact ⟨g ∘ fun p : Set.Iic t₁ → ℝ => fun s : Set.Iic t₀ => p ⟨(s : ℝ≥0), le_trans s.2 ht⟩,
    hg.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _), rfl⟩

/-- Products of adapted integrands are adapted. -/
theorem AdaptedAt.mul {t₀ : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) (hψ : AdaptedAt B t₀ ψ) :
    AdaptedAt B t₀ (fun ω => φ ω * ψ ω) := by
  obtain ⟨g, hg, rfl⟩ := hφ
  obtain ⟨h, hh, rfl⟩ := hψ
  exact ⟨fun p => g p * h p, hg.mul hh, rfl⟩

/-- Differences of adapted integrands are adapted. -/
theorem AdaptedAt.sub {t₀ : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) (hψ : AdaptedAt B t₀ ψ) :
    AdaptedAt B t₀ (fun ω => φ ω - ψ ω) := by
  obtain ⟨g, hg, rfl⟩ := hφ
  obtain ⟨h, hh, rfl⟩ := hψ
  exact ⟨fun p => g p - h p, hg.sub hh, rfl⟩

/-- An adapted integrand is independent of the forward increment. The deep
content: `B_{t₁} - B_{t₀}` is independent of `𝓕_{t₀}` (weak Markov,
`IsPreBrownian.indepFun_shift`), and `φ` is `𝓕_{t₀}`-measurable. -/
theorem adapted_indepFun_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    IndepFun φ (fun ω => B t₁ ω - B t₀ ω) μ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  -- Forward increment process is independent of the past process.
  have hshift := hB.indepFun_shift hBmeas t₀
  -- `B t₁ - B t₀ = eval_(t₁-t₀) ∘ fwd`, with `t₀ + (t₁-t₀) = t₁`.
  have hΔ : t₀ + (t₁ - t₀) = t₁ := add_tsub_cancel_of_le ht
  have hfun : (fun ω => B t₁ ω - B t₀ ω) =
      (fun p : ℝ≥0 → ℝ => p (t₁ - t₀)) ∘ (fun ω t => B (t₀ + t) ω - B t₀ ω) := by
    funext ω
    simp only [Function.comp_apply, hΔ]
  rw [hfun]
  exact hshift.symm.comp hg (measurable_pi_apply _)

/-- **Martingale-difference property of the Itô integral** (discrete form):
for `φ` adapted to `𝓕_{t₀}`, the integrand times the next Brownian increment
has mean zero, `E[φ · (B_{t₁} - B_{t₀})] = 0`. This is the reason the Itô
integral is a martingale — and it holds for *random* `φ`, where the Wiener
(deterministic) covariance argument does not apply. -/
theorem integral_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    ∫ ω, φ ω * (B t₁ ω - B t₀ ω) ∂μ = 0 := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  rw [hindep.integral_fun_mul_eq_mul_integral hφm.aestronglyMeasurable
        hΔm.aestronglyMeasurable]
  have hmean : ∫ ω, (B t₁ ω - B t₀ ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t₁ t₀).integral_eq
    rwa [integral_id_gaussianReal] at h
  rw [hmean, mul_zero]

/-- The forward increment has second moment `E[(B_{t₁} - B_{t₀})²] = t₁ - t₀`
(mean zero, variance `t₁ - t₀`). -/
theorem integral_increment_sq
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) (hBmeas : ∀ t, Measurable (B t)) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (t₁ : ℝ) - t₀ := by
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hmean : ∫ ω, (B t₁ ω - B t₀ ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t₁ t₀).integral_eq
    rwa [integral_id_gaussianReal] at h
  have hmax : (max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) = t₁ - t₀ :=
    max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le _)
  rw [← variance_of_integral_eq_zero hΔm.aemeasurable hmean]
  show Var[B t₁ - B t₀; μ] = (t₁ : ℝ) - t₀
  rw [(hB.hasLaw_sub t₁ t₀).variance_eq, variance_id_gaussianReal, hmax, NNReal.coe_sub ht]

/-- **Isometry kernel** (the diagonal term of the Itô isometry): for `φ`
adapted to `𝓕_{t₀}`, `E[φ² · (B_{t₁} - B_{t₀})²] = E[φ²] · (t₁ - t₀)`. The
independence of `φ` from the increment (weak Markov) factorises the
expectation; the increment contributes its variance `t₁ - t₀`. -/
theorem integral_adapted_sq_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    ∫ ω, (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2 ∂μ =
      (∫ ω, (φ ω) ^ 2 ∂μ) * ((t₁ : ℝ) - t₀) := by
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have key := hindep2.integral_fun_mul_eq_mul_integral
    (hφm.pow_const 2).aestronglyMeasurable (hΔm.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  rw [key, integral_increment_sq (μ := μ) ht hBmeas]

/-! ### The discrete Itô isometry over a partition -/

/-- **Cross terms vanish.** For `j < k`, `E[(φⱼ·ΔBⱼ)·(φₖ·ΔBₖ)] = 0`: the
factor `φⱼ·ΔBⱼ·φₖ` is `𝓕_{tₖ}`-measurable (adaptedness algebra), and the
forward increment `ΔBₖ` is independent of it with mean zero. -/
theorem integral_cross_increment_eq_zero
    (hBmeas : ∀ s, Measurable (B s)) {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ : ℕ → Ω → ℝ} (hadapt : ∀ n, AdaptedAt B (t n) (φ n)) {j k : ℕ} (hjk : j < k) :
    ∫ ω, (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
          (φ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ = 0 := by
  have hΦ : AdaptedAt B (t k)
      (fun ω => φ j ω * (B (t (j + 1)) ω - B (t j) ω) * φ k ω) :=
    (((hadapt j).mono (hmono hjk.le)).mul
      ((adaptedAt_eval (hmono hjk)).sub (adaptedAt_eval (hmono hjk.le)))).mul (hadapt k)
  have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
  have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hstep hΦ
  rw [show (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
        (φ k ω * (B (t (k + 1)) ω - B (t k) ω)))
      = (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω) * φ k ω) *
        (B (t (k + 1)) ω - B (t k) ω)) from by funext ω; ring]
  exact h0

/-- **The discrete Itô isometry** (adapted simple integrands). For a partition
`t : ℕ → ℝ≥0` and integrands `φ k` adapted to `𝓕_{t k}` and in `L²`,

  `E[(Σₖ φₖ·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ E[φₖ²]·(t_{k+1} − t_k)`.

This is the genuine Itô isometry: the integrand is *random*. The diagonal
terms give the variance kernel (`integral_adapted_sq_mul_increment_sq`); the
off-diagonal terms vanish by the martingale-difference property
(`integral_cross_increment_eq_zero`). -/
theorem ito_isometry_discrete
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ : ℕ → Ω → ℝ} (hadapt : ∀ n, AdaptedAt B (t n) (φ n))
    (hL2 : ∀ n, MemLp (φ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  classical
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set a : ℕ → Ω → ℝ := fun k ω => φ k ω * (B (t (k + 1)) ω - B (t k) ω) with ha_def
  -- Each `aₖ = φₖ·ΔBₖ` is in `L²`: `φₖ²` and `ΔBₖ²` are integrable and
  -- independent, so their product is integrable, i.e. `E[aₖ²] < ∞`.
  have ha_L2 : ∀ k, MemLp (a k) 2 μ := by
    intro k
    have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
    have hindep := adapted_indepFun_increment (μ := μ) hBmeas hstep (hadapt k)
    have hφm : Measurable (φ k) := (hadapt k).measurable hBmeas
    have hΔm : Measurable (fun ω => B (t (k + 1)) ω - B (t k) ω) := (hBmeas _).sub (hBmeas _)
    have hφsq : Integrable (fun ω => (φ k ω) ^ 2) μ := (hL2 k).integrable_sq
    have hΔsq : Integrable (fun ω => (B (t (k + 1)) ω - B (t k) ω) ^ 2) μ :=
      (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_sq
    have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
    have hprod : Integrable
        (fun ω => (φ k ω) ^ 2 * (B (t (k + 1)) ω - B (t k) ω) ^ 2) μ := by
      have h := hindep2.integrable_mul hφsq hΔsq
      simpa [Function.comp, Pi.mul_apply] using h
    refine (memLp_two_iff_integrable_sq (hφm.mul hΔm).aestronglyMeasurable).mpr ?_
    simpa [ha_def, mul_pow] using hprod
  have hint : ∀ j k, Integrable (fun ω => a j ω * a k ω) μ := fun j k =>
    (ha_L2 j).integrable_mul (ha_L2 k)
  -- Diagonal term = variance kernel.
  have hdiag : ∀ k, ∫ ω, a k ω * a k ω ∂μ =
      (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) := by
    intro k
    have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
    rw [show (fun ω => a k ω * a k ω)
          = (fun ω => (φ k ω) ^ 2 * (B (t (k + 1)) ω - B (t k) ω) ^ 2) from by
            funext ω; simp only [ha_def]; ring]
    exact integral_adapted_sq_mul_increment_sq (μ := μ) hBmeas hstep (hadapt k)
  -- Off-diagonal terms vanish.
  have hcross : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N, j ≠ k →
      ∫ ω, a j ω * a k ω ∂μ = 0 := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact integral_cross_increment_eq_zero hBmeas hmono hadapt h
    · rw [show (fun ω => a j ω * a k ω) = (fun ω => a k ω * a j ω) from by funext ω; ring]
      exact integral_cross_increment_eq_zero hBmeas hmono hadapt h
  calc ∫ ω, (∑ k ∈ Finset.range N, a k ω) ^ 2 ∂μ
      = ∫ ω, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * a k ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range N, a k ω) ^ 2
          = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * a k ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∫ ω, a j ω * a k ω ∂μ := by
        rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k))]
        exact Finset.sum_congr rfl
          (fun j _ => integral_finset_sum _ (fun k _ => hint j k))
    _ = ∑ j ∈ Finset.range N, ∫ ω, a j ω * a j ω ∂μ := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        exact Finset.sum_eq_single j (fun k hk hkj => hcross j hj k hk (Ne.symm hkj))
          (fun hj' => absurd hj hj')
    _ = ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) :=
        Finset.sum_congr rfl (fun k _ => hdiag k)

/-- `E[B_s²] = s` (mean zero, variance `s`). -/
theorem integral_eval_sq (hBmeas : ∀ s, Measurable (B s)) (s : ℝ≥0) :
    ∫ ω, (B s ω) ^ 2 ∂μ = (s : ℝ) := by
  rw [← variance_of_integral_eq_zero (hBmeas s).aemeasurable (hB.integral_eval s)]
  show Var[B s; μ] = (s : ℝ)
  rw [(hB.hasLaw_eval s).variance_eq, variance_id_gaussianReal]

/-- **The discrete `∫₀ᵀ B dB` isometry** — the canonical instance, with *no*
remaining hypotheses beyond measurability. Taking the adapted `L²` integrand
`φₖ = B(tₖ)`,

  `E[(Σₖ B(tₖ)·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ t_k·(t_{k+1} − t_k)`,

the Riemann-sum form of the Itô isometry `E[(∫₀ᵀ B dB)²] = ∫₀ᵀ t dt`. -/
theorem ito_isometry_brownian_self
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t) :
    ∫ ω, (∑ k ∈ Finset.range N, B (t k) ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (t k : ℝ) * ((t (k + 1) : ℝ) - t k) := by
  rw [ito_isometry_discrete (μ := μ) hBmeas hmono (φ := fun k => B (t k))
    (fun n => adaptedAt_eval le_rfl)
    (fun n => (hB.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two)]
  exact Finset.sum_congr rfl (fun k _ => by rw [integral_eval_sq hBmeas])

end ItoIsometryAdapted
end QuantFin
