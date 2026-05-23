/-
  QuantFin.Foundations.CondExpJensen
  Proposition 2.1.11(9): conditional Jensen's inequality, parametrized by an
  explicit subgradient (Mathlib v4.30 has no general subgradient API for
  convex functions on ℝ; any convex `φ` has such a `g`, e.g. its right
  derivative).
-/
import Mathlib

namespace QuantFin

open MeasureTheory

variable {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {m : MeasurableSpace α} {φ : ℝ → ℝ} {X : α → ℝ}

/-- Conditional Jensen's inequality with an explicit subgradient.

For a convex `φ : ℝ → ℝ` with an explicit subgradient `g` satisfying the
supporting-line property `φ(y) + g(y)(x − y) ≤ φ(x)` and uniformly bounded,
together with the usual integrability hypotheses, one has
`φ(E[X|m]) ≤ᵐ E[φ(X)|m]`.

The subgradient is supplied explicitly because Mathlib v4.30 has no general
subgradient API for convex functions on `ℝ`; any convex `φ` has such a `g`
(e.g. its right derivative). -/
theorem conditional_jensen_inequality
    (hm : m ≤ m₀)
    (hφ_meas : Measurable φ)
    (hX_int : Integrable X μ)
    (hφX_int : Integrable (fun a ↦ φ (X a)) μ)
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_subgrad : ∀ x y, φ y + g y * (x - y) ≤ φ x)
    (hg_bdd : ∃ K : ℝ, ∀ x, |g x| ≤ K)
    (hφcE_int : Integrable (fun a ↦ φ ((μ[X | m]) a)) μ) :
    (fun a ↦ φ ((μ[X | m]) a)) ≤ᵐ[μ] (μ[fun a ↦ φ (X a) | m]) := by
  obtain ⟨K, hK⟩ := hg_bdd
  set Y : α → ℝ := μ[X | m] with hY_def
  have hY_meas : StronglyMeasurable[m] Y := stronglyMeasurable_condExp
  have hY_int : Integrable Y μ := integrable_condExp
  have hgY_meas : StronglyMeasurable[m] (fun a ↦ g (Y a)) :=
    (hg_meas.comp hY_meas.measurable).stronglyMeasurable
  have hgY_bound : ∀ᵐ a ∂μ, ‖g (Y a)‖ ≤ K :=
    ae_of_all _ fun a ↦ by simpa [Real.norm_eq_abs] using hK (Y a)
  have hXmY_int : Integrable (X - Y) μ := hX_int.sub hY_int
  have hgYmul_int : Integrable ((fun a ↦ g (Y a)) * (X - Y)) μ :=
    Integrable.bdd_mul hXmY_int (hgY_meas.mono hm).aestronglyMeasurable hgY_bound
  have hY_self : μ[Y | m] = Y := condExp_of_stronglyMeasurable hm hY_meas hY_int
  have hXmY_condExp : μ[X - Y | m] =ᵐ[μ] (0 : α → ℝ) := by
    filter_upwards [condExp_sub hX_int hY_int (m := m)] with a ha
    show (μ[X - Y | m]) a = 0
    rw [ha, Pi.sub_apply, hY_self]
    simp [hY_def]
  have hgYmul_condExp : μ[(fun a ↦ g (Y a)) * (X - Y) | m] =ᵐ[μ] (0 : α → ℝ) := by
    refine (condExp_mul_of_stronglyMeasurable_left hgY_meas hgYmul_int hXmY_int).trans ?_
    filter_upwards [hXmY_condExp] with a ha
    show g (Y a) * (μ[X - Y | m]) a = 0
    rw [ha]
    simp
  have h_supporting_line :
      (fun a ↦ g (Y a) * (X a - Y a)) ≤ᵐ[μ] (fun a ↦ φ (X a) - φ (Y a)) :=
    ae_of_all _ fun a ↦ by
      have h := hg_subgrad (X a) (Y a)
      linarith
  have hgYmul_eq : (fun a ↦ g (Y a) * (X a - Y a)) = (fun a ↦ g (Y a)) * (X - Y) := rfl
  have hφ_diff_int : Integrable (fun a ↦ φ (X a) - φ (Y a)) μ :=
    hφX_int.sub hφcE_int
  have hgYmul_int' : Integrable (fun a ↦ g (Y a) * (X a - Y a)) μ := hgYmul_eq ▸ hgYmul_int
  have h_condExp_mono :
      μ[fun a ↦ g (Y a) * (X a - Y a) | m] ≤ᵐ[μ]
        μ[fun a ↦ φ (X a) - φ (Y a) | m] :=
    condExp_mono hgYmul_int' hφ_diff_int h_supporting_line
  have h_subgradient_condExp :
      μ[fun a ↦ g (Y a) * (X a - Y a) | m] =ᵐ[μ] (0 : α → ℝ) :=
    hgYmul_eq ▸ hgYmul_condExp
  have hφY_meas : StronglyMeasurable[m] (fun a ↦ φ (Y a)) :=
    (hφ_meas.comp hY_meas.measurable).stronglyMeasurable
  have hφY_self : μ[fun a ↦ φ (Y a) | m] = fun a ↦ φ (Y a) :=
    condExp_of_stronglyMeasurable hm hφY_meas hφcE_int
  have h_condExp_phi_diff :
      μ[fun a ↦ φ (X a) - φ (Y a) | m] =ᵐ[μ]
        fun a ↦ (μ[fun a ↦ φ (X a) | m]) a - φ (Y a) := by
    have h1 : μ[fun a ↦ φ (X a) - φ (Y a) | m] =ᵐ[μ]
              μ[fun a ↦ φ (X a) | m] - μ[fun a ↦ φ (Y a) | m] := by
      change μ[(fun a ↦ φ (X a)) - (fun a ↦ φ (Y a)) | m] =ᵐ[μ] _
      exact condExp_sub hφX_int hφcE_int _
    filter_upwards [h1] with a ha
    rw [ha, Pi.sub_apply, hφY_self]
  filter_upwards [h_condExp_mono, h_subgradient_condExp, h_condExp_phi_diff]
    with a h_mono h_subgrad h_phi_diff
  rw [h_subgrad, h_phi_diff] at h_mono
  simp only [Pi.zero_apply] at h_mono
  linarith

end QuantFin
