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

open MeasureTheory ProbabilityTheory ItoIsometryAdapted Filter
open scoped NNReal ENNReal Topology

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

/-- A Brownian increment has finite fourth moment (`MemLp 4`) — a centered Gaussian has all
moments. Needed for the `L²`-integrability of products of squared increments in the
quadratic-variation assembly. -/
theorem memLp_increment_four (t₀ t₁ : ℝ≥0) :
    MemLp (fun ω => B t₁ ω - B t₀ ω) 4 μ := by
  have hmap : MemLp (id : ℝ → ℝ) 4 (Measure.map (fun ω => B t₁ ω - B t₀ ω) μ) := by
    rw [show Measure.map (fun ω => B t₁ ω - B t₀ ω) μ
          = gaussianReal 0 (max (t₁ - t₀) (t₀ - t₁)) from (hB.hasLaw_sub t₁ t₀).map_eq]
    exact memLp_id_gaussianReal (μ := 0) 4
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (hB.hasLaw_sub t₁ t₀).aemeasurable).mp hmap

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

/-- A centered squared Brownian increment is in `L²` (`Yₖ = (ΔB)² − Δt`): the squared
increment is `L²` since the increment is `L⁴`, and a constant is `L²` on a probability space. -/
theorem memLp_increment_sq_centered_two (t₀ t₁ : ℝ≥0) (r : ℝ) :
    MemLp (fun ω => (B t₁ ω - B t₀ ω) ^ 2 - r) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by
    have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have ht : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
      ENNReal.mul_inv (Or.inl h2) (Or.inl ht), ← two_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel h2 ht, one_mul]⟩
  have hmul : MemLp (fun ω => (B t₁ ω - B t₀ ω) * (B t₁ ω - B t₀ ω)) 2 μ :=
    (memLp_increment_four t₀ t₁).mul (memLp_increment_four t₀ t₁)
  have hsq : MemLp (fun ω => (B t₁ ω - B t₀ ω) ^ 2) 2 μ := by
    simpa only [← pow_two] using hmul
  exact hsq.sub (memLp_const r)

/-- **Quadratic variation of Brownian motion, L² form** (Saporito Theorem 6.1.1, the strong
form). Along any monotone partition `0 = s₀ ≤ s₁ ≤ ⋯` of `[0, sₙ]`, the squared-increment sum
converges to `sₙ` in mean square, with the *exact* rate

  `E[(∑ₖ (B_{sₖ₊₁} − B_{sₖ})² − sₙ)²] = ∑ₖ 2(sₖ₊₁ − sₖ)²`.

This is the Pythagorean identity for the centered squared increments `Yₖ = (ΔBₖ)² − Δsₖ`:
they are pairwise orthogonal (`integral_increment_sq_centered_cross`, weak Markov), so the
mean-square error is the sum of their individual variances `E[Yₖ²] = 2(Δsₖ)²`
(`integral_increment_sq_centered`, the Gaussian kurtosis). For the uniform partition
`sₖ = kt/n` the right side is `2t²/n → 0` — the precise reason `(dB)² = dt` and Itô's lemma
carries a second-order term. -/
theorem sum_increment_sq_sub_sq_integral (hBmeas : ∀ t, Measurable (B t))
    {s : ℕ → ℝ≥0} (hmono : Monotone s) (hs0 : s 0 = 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, (B (s (k + 1)) ω - B (s k) ω) ^ 2 - (s n : ℝ)) ^ 2 ∂μ
      = ∑ k ∈ Finset.range n, 2 * ((s (k + 1) : ℝ) - s k) ^ 2 := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  set Y : ℕ → Ω → ℝ :=
    fun k ω => (B (s (k + 1)) ω - B (s k) ω) ^ 2 - ((s (k + 1) : ℝ) - s k) with hY
  have hYL2 : ∀ k, MemLp (Y k) 2 μ := fun k => memLp_increment_sq_centered_two _ _ _
  have hint : ∀ k l, Integrable (fun ω => Y k ω * Y l ω) μ :=
    fun k l => (hYL2 k).integrable_mul (hYL2 l)
  -- Telescoping: `∑ Δsₖ = sₙ − s₀ = sₙ`, so `∑ (ΔBₖ)² − sₙ = ∑ Yₖ`.
  have htel : ∑ k ∈ Finset.range n, ((s (k + 1) : ℝ) - s k) = (s n : ℝ) := by
    rw [Finset.sum_range_sub (fun k => (s k : ℝ))]; simp [hs0]
  have hrw : ∀ ω, ∑ k ∈ Finset.range n, Y k ω
      = (∑ k ∈ Finset.range n, (B (s (k + 1)) ω - B (s k) ω) ^ 2) - (s n : ℝ) := by
    intro ω; simp only [hY, Finset.sum_sub_distrib, htel]
  -- Off-diagonal terms vanish (orthogonality); diagonal terms give `2(Δsₖ)²`.
  have hcross : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, l ≠ k →
      ∫ ω, Y k ω * Y l ω ∂μ = 0 := by
    intro k _ l _ hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · -- l < k
      rw [show (fun ω => Y k ω * Y l ω) = fun ω => Y l ω * Y k ω from funext fun ω => mul_comm _ _]
      exact integral_increment_sq_centered_cross hBmeas (hmono (Nat.le_succ l))
        (hmono (Nat.succ_le_of_lt hlt)) (hmono (Nat.le_succ k))
    · -- k < l
      exact integral_increment_sq_centered_cross hBmeas (hmono (Nat.le_succ k))
        (hmono (Nat.succ_le_of_lt hgt)) (hmono (Nat.le_succ l))
  calc ∫ ω, (∑ k ∈ Finset.range n, (B (s (k + 1)) ω - B (s k) ω) ^ 2 - (s n : ℝ)) ^ 2 ∂μ
      = ∫ ω, (∑ k ∈ Finset.range n, Y k ω) ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range n, (B (s (k + 1)) ω - B (s k) ω) ^ 2 - (s n : ℝ)) ^ 2
          = (∑ k ∈ Finset.range n, Y k ω) ^ 2
        rw [hrw ω]
    _ = ∫ ω, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, Y k ω * Y l ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range n, Y k ω) ^ 2
          = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, Y k ω * Y l ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∫ ω, Y k ω * Y l ω ∂μ := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hint k l
    _ = ∑ k ∈ Finset.range n, 2 * ((s (k + 1) : ℝ) - s k) ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.sum_eq_single k (fun l hl hlk => hcross k hk l hl hlk)
          (fun hk' => absurd hk hk')]
        show ∫ ω, Y k ω * Y k ω ∂μ = 2 * ((s (k + 1) : ℝ) - s k) ^ 2
        rw [show (fun ω => Y k ω * Y k ω)
              = fun ω => ((B (s (k + 1)) ω - B (s k) ω) ^ 2 - ((s (k + 1) : ℝ) - s k)) ^ 2
            from funext fun ω => by rw [hY]; ring]
        exact integral_increment_sq_centered (hmono (Nat.le_succ k))

/-- **Quadratic variation converges as the mesh shrinks.** If every gap `sₖ₊₁ − sₖ ≤ δ`, the
mean-square error of the squared-increment sum is at most `2δ·sₙ`. Hence along any sequence of
partitions of `[0, T]` with mesh `→ 0`, `∑ₖ (B_{sₖ₊₁} − B_{sₖ})² → T` in `L²` — Brownian
motion has quadratic variation `T`. (From the exact identity `∑ 2(Δsₖ)² ≤ 2δ·∑ Δsₖ = 2δ·sₙ`.) -/
theorem sum_increment_sq_sub_sq_le (hBmeas : ∀ t, Measurable (B t))
    {s : ℕ → ℝ≥0} (hmono : Monotone s) (hs0 : s 0 = 0) (n : ℕ) {δ : ℝ}
    (hδ : ∀ k ∈ Finset.range n, (s (k + 1) : ℝ) - s k ≤ δ) :
    ∫ ω, (∑ k ∈ Finset.range n, (B (s (k + 1)) ω - B (s k) ω) ^ 2 - (s n : ℝ)) ^ 2 ∂μ
      ≤ 2 * δ * (s n : ℝ) := by
  rw [sum_increment_sq_sub_sq_integral hBmeas hmono hs0 n]
  have htel : ∑ k ∈ Finset.range n, ((s (k + 1) : ℝ) - s k) = (s n : ℝ) := by
    rw [Finset.sum_range_sub (fun k => (s k : ℝ))]; simp [hs0]
  calc ∑ k ∈ Finset.range n, 2 * ((s (k + 1) : ℝ) - s k) ^ 2
      ≤ ∑ k ∈ Finset.range n, 2 * δ * ((s (k + 1) : ℝ) - s k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hΔ0 : 0 ≤ (s (k + 1) : ℝ) - s k :=
          sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hmono (Nat.le_succ k)))
        nlinarith [hδ k hk, hΔ0]
    _ = 2 * δ * (s n : ℝ) := by rw [← Finset.mul_sum, htel]

/-- The uniform partition of `[0, T]`: the `n`-th refinement places its `k`-th node at `kT/n`. -/
noncomputable def unifPart (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n : ℝ≥0) * T

/-- **Brownian motion has quadratic variation `T` (textbook L² form).** Along the uniform
partition of `[0, T]` into `n` pieces, the sum of squared increments converges to `T` in mean
square: `E[(∑_{k<n} (B_{(k+1)T/n} − B_{kT/n})² − T)²] → 0`. Immediate from the mesh bound
(`sum_increment_sq_sub_sq_le`, here mesh `= T/n`) with explicit rate `2T²/n`, squeezed to `0`. -/
theorem tendsto_qv (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, (∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 - (T : ℝ)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine squeeze_zero' (g := fun n : ℕ => 2 * (T : ℝ) ^ 2 / (n : ℝ))
    (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (T : ℝ) ^ 2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmono : Monotone (unifPart T n) := fun a b hab => by
    simp only [unifPart]; gcongr
  have hs0 : unifPart T n 0 = 0 := by simp [unifPart]
  have hsn : unifPart T n n = T := by simp only [unifPart, div_self hn0, one_mul]
  have hgap : ∀ k ∈ Finset.range n, (unifPart T n (k + 1) : ℝ) - unifPart T n k ≤ (T : ℝ) / n := by
    intro k _
    have : (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n := by
      simp only [unifPart]; push_cast; field_simp; ring
    exact le_of_eq this
  have hbound := sum_increment_sq_sub_sq_le (μ := μ) hBmeas hmono hs0 n hgap
  rw [hsn] at hbound
  rw [show (2 : ℝ) * (T : ℝ) ^ 2 / (n : ℝ) = 2 * ((T : ℝ) / n) * T from by ring]
  exact hbound

/-- **Quadratic variation converges in probability**: along the uniform partition of `[0, T]`,
`∑ₖ (ΔBₖ)² → T` in measure. This is the textbook form of `[B, B]_T = T`, and a *genuine*
consequence of the L² convergence `tendsto_qv` (through `tendstoInMeasure_of_tendsto_eLpNorm`) —
not of the marginal mean alone (which gives only `E[∑(ΔBₖ)²] = T`). It is the L² headline
result's first real consumer. -/
theorem tendstoInMeasure_qv (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    TendstoInMeasure μ
      (fun n ω => ∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2)
      atTop (fun _ => (T : ℝ)) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  -- each centered sum `Sₙ − T` lies in `L²` (each squared increment is `L²`, via `r = 0`)
  have hmem : ∀ n : ℕ, MemLp (fun ω => (∑ k ∈ Finset.range n,
      (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) 2 μ := by
    intro n
    have hsum : MemLp (fun ω => ∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
      apply memLp_finset_sum
      intro k _
      simpa using memLp_increment_sq_centered_two (unifPart T n k) (unifPart T n (k + 1)) 0
    exact hsum.sub (memLp_const (T : ℝ))
  refine tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (Finset.measurable_sum _ fun k _ =>
      ((hBmeas _).sub (hBmeas _)).pow_const 2).aestronglyMeasurable)
    aestronglyMeasurable_const ?_
  -- `eLpNorm (Sₙ − T) 2 = ofReal √(∫ (Sₙ − T)²) → 0`, the L² convergence `tendsto_qv`
  have hconv : ∀ n : ℕ, eLpNorm (fun ω => (∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) 2 μ
      = ENNReal.ofReal (Real.sqrt (∫ ω, ((∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) ^ 2 ∂μ)) := by
    intro n
    rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat, ← one_div, ← Real.sqrt_eq_rpow]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖(∑ k ∈ Finset.range n,
          (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)‖ ^ (2 : ℝ)
        = ((∑ k ∈ Finset.range n,
          (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) ^ 2
    rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (∫ ω, ((∑ k ∈ Finset.range n,
      (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) ^ 2 ∂μ)))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt 0) from by simp]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_sqrt.tendsto _).comp (tendsto_qv hBmeas T))
  exact Tendsto.congr (fun n => (hconv n).symm) hlim

end QuadraticVariationL2
end QuantFin
