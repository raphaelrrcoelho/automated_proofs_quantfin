/-
  QuantFin.Foundations.MartingaleTransform
  Theorem 2.2.9: the martingale transform of a martingale by a bounded
  predictable process is itself a martingale (discrete stochastic integral).
-/
import Mathlib

namespace QuantFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0}
  {M A : ℕ → Ω → ℝ}

/-- The discrete stochastic integral / martingale-transform process
`(A · M)_n ω := ∑_{k=0}^{n−1} A_{k+1}(ω) · (M_{k+1}(ω) − M_k(ω))`. -/
noncomputable def martingaleTransform (A M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, A (k + 1) ω * (M (k + 1) ω - M k ω)

omit [IsFiniteMeasure μ] in
/-- Successor expansion for the martingale transform. -/
private lemma martingaleTransform_succ (A M : ℕ → Ω → ℝ) (n : ℕ) :
    martingaleTransform A M (n + 1) =
      martingaleTransform A M n + fun ω ↦ A (n + 1) ω * (M (n + 1) ω - M n ω) := by
  funext ω
  show ∑ k ∈ Finset.range (n + 1), _ = _
  rw [Finset.sum_range_succ]
  rfl

omit [IsFiniteMeasure μ] in
/-- Each summand `A_{k+1}(ω) · (M_{k+1}(ω) − M_k(ω))` is `𝓕 n`-measurable when `k < n`. -/
private lemma summand_stronglyMeasurable
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (n k : ℕ) (hk : k < n) :
    StronglyMeasurable[𝓕 n] (fun ω ↦ A (k + 1) ω * (M (k + 1) ω - M k ω)) :=
  (hA.stronglyMeasurable_le hk.le).mul
    ((hM.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hk)).sub
      (hM.stronglyAdapted.stronglyMeasurable_le hk.le))

omit [IsFiniteMeasure μ] in
/-- The martingale transform is adapted. -/
private lemma martingaleTransform_adapted
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1))) :
    StronglyAdapted 𝓕 (martingaleTransform A M) := fun n ↦
  Finset.stronglyMeasurable_fun_sum (m := 𝓕 n) (M := ℝ) (Finset.range n) fun k hk ↦
    summand_stronglyMeasurable hM hA n k (Finset.mem_range.mp hk)

omit [IsFiniteMeasure μ] in
/-- Each summand is integrable (bounded `A` × integrable martingale increment). -/
private lemma integrable_summand
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ n ω, |A n ω| ≤ K) (k : ℕ) :
    Integrable (fun ω ↦ A (k + 1) ω * (M (k + 1) ω - M k ω)) μ := by
  obtain ⟨K, hK⟩ := hA_bdd
  exact Integrable.bdd_mul (c := K)
    ((hM.integrable (k + 1)).sub (hM.integrable k))
    (hA.stronglyMeasurable (i := k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hK (k + 1) ω)

omit [IsFiniteMeasure μ] in
/-- `(A · M)_n` is integrable. -/
private lemma integrable_martingaleTransform
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ n ω, |A n ω| ≤ K) (n : ℕ) :
    Integrable (martingaleTransform A M n) μ :=
  integrable_finset_sum _ fun k _ ↦ integrable_summand hM hA hA_bdd k

/-- The conditional expectation of a martingale increment is zero. -/
private lemma condExp_increment_eq_zero (hM : Martingale M 𝓕 μ) (n : ℕ) :
    μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] (0 : Ω → ℝ) := by
  have h_sub : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] μ[M (n + 1) | 𝓕 n] - μ[M n | 𝓕 n] :=
    condExp_sub (hM.integrable (n + 1)) (hM.integrable n) _
  have h_next : μ[M (n + 1) | 𝓕 n] =ᵐ[μ] M n :=
    hM.condExp_ae_eq (Nat.le_succ n)
  have h_now : μ[M n | 𝓕 n] = M n :=
    condExp_of_stronglyMeasurable (𝓕.le n) (hM.stronglyAdapted n) (hM.integrable n)
  filter_upwards [h_sub, h_next] with ω hω_sub hω_next
  simp [Pi.sub_apply, hω_sub, hω_next, h_now]

/-- The martingale step: `(A · M)_n =ᵐ μ[(A · M)_{n+1} | 𝓕 n]`. -/
private lemma martingaleTransform_step
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ n ω, |A n ω| ≤ K) (n : ℕ) :
    martingaleTransform A M n =ᵐ[μ] μ[martingaleTransform A M (n + 1) | 𝓕 n] := by
  set δ : Ω → ℝ := fun ω ↦ A (n + 1) ω * (M (n + 1) ω - M n ω)
  have hAM_succ_eq : martingaleTransform A M (n + 1) = martingaleTransform A M n + δ :=
    martingaleTransform_succ A M n
  have hδ_int : Integrable δ μ := integrable_summand hM hA hA_bdd n
  have hMdiff : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] (0 : Ω → ℝ) :=
    condExp_increment_eq_zero hM n
  have hδ_condExp : μ[δ | 𝓕 n] =ᵐ[μ] (0 : Ω → ℝ) := by
    refine (condExp_mul_of_stronglyMeasurable_left
      (hA n) hδ_int ((hM.integrable (n + 1)).sub (hM.integrable n))).trans ?_
    filter_upwards [hMdiff] with ω hω
    change A (n + 1) ω * (μ[M (n + 1) - M n | 𝓕 n]) ω = (0 : ℝ)
    rw [hω]
    simp
  have hAM_n_int : Integrable (martingaleTransform A M n) μ :=
    integrable_martingaleTransform hM hA hA_bdd n
  have hcondAM_n : μ[martingaleTransform A M n | 𝓕 n] = martingaleTransform A M n :=
    condExp_of_stronglyMeasurable (𝓕.le n)
      (martingaleTransform_adapted hM hA n) hAM_n_int
  have hsplit : μ[martingaleTransform A M (n + 1) | 𝓕 n] =ᵐ[μ]
                μ[martingaleTransform A M n | 𝓕 n] + μ[δ | 𝓕 n] := by
    rw [hAM_succ_eq]
    exact condExp_add hAM_n_int hδ_int (𝓕 n)
  filter_upwards [hsplit, hδ_condExp] with ω hω1 hω2
  show martingaleTransform A M n ω = (μ[martingaleTransform A M (n + 1) | 𝓕 n]) ω
  rw [hω1]
  simp [Pi.add_apply, hcondAM_n, hω2]

/-- Theorem 2.2.9: the martingale transform of a martingale `M` by a bounded
predictable process `A` is itself a martingale. -/
theorem martingaleTransform_isMartingale
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ n ω, |A n ω| ≤ K) :
    Martingale (martingaleTransform A M) 𝓕 μ :=
  martingale_nat (martingaleTransform_adapted hM hA)
    (integrable_martingaleTransform hM hA hA_bdd)
    (martingaleTransform_step hM hA hA_bdd)

end QuantFin
