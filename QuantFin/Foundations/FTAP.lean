/-
  QuantFin.Foundations.FTAP
  Theorem 2.6.7: First Fundamental Theorem of Asset Pricing (⇒ direction).
  EMM existence ⇒ no arbitrage. Uses QuantFin.MartingaleTransform.
-/
import Mathlib
import QuantFin.Foundations.MartingaleTransform

namespace QuantFin

open MeasureTheory ProbabilityTheory

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale
measure precludes arbitrage.

Given a discounted-price process `S` adapted to a filtration `𝓕`, an equivalent
probability measure `Q ≪≫ P` under which `S` is a martingale, and a bounded
predictable strategy `φ`, the discounted P&L
`V_T = ∑_{t<T} φ_{t+1}(ω) · (S_{t+1} − S_t)`
cannot be `P`-a.s. nonnegative and strictly positive on a `P`-non-null set. -/
theorem emm_implies_no_arbitrage
    {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℕ} {𝓕 : Filtration ℕ m0} {S : ℕ → Ω → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hSQ : Martingale S 𝓕 Q)
    (φ : ℕ → Ω → ℝ)
    (hφ_pred : StronglyAdapted 𝓕 (fun n ↦ φ (n + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ω, |φ n ω| ≤ K)
    (hV_nonneg : ∀ᵐ ω ∂P,
      0 ≤ ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)) :
    P {ω | 0 < ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)} = 0 := by
  set V : ℕ → Ω → ℝ := martingaleTransform φ S with hV_def
  have hV_mart : Martingale V 𝓕 Q :=
    martingaleTransform_isMartingale hSQ hφ_pred hφ_bdd
  have hV0_zero : V 0 = 0 := by funext ω; simp [V, martingaleTransform]
  have hV_T_integral : ∫ ω, V T ω ∂Q = 0 := by
    have : ∫ ω, V T ω ∂Q = ∫ ω, V 0 ω ∂Q := by
      rw [(integral_condExp (𝓕.le 0)).symm]
      exact integral_congr_ae (hV_mart.condExp_ae_eq (Nat.zero_le T))
    rw [this, hV0_zero]; simp
  have hV_T_nonneg_Q : 0 ≤ᵐ[Q] V T := hQP.ae_le hV_nonneg
  have hV_T_zero_Q : V T =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hV_T_nonneg_Q (hV_mart.integrable T)).mp hV_T_integral
  have h_pos_Q_zero : Q {ω | 0 < V T ω} = 0 :=
    measure_mono_null (fun ω hω ↦ ne_of_gt hω : {ω | 0 < V T ω} ⊆ {ω | V T ω ≠ 0})
      (ae_iff.mp hV_T_zero_Q)
  exact hPQ h_pos_Q_zero

end QuantFin
