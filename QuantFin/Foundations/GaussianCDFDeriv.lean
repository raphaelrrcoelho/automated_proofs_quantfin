/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.Call

/-!
# Derivative of the standard normal CDF: `Φ'(x) = ϕ(x)`

The standard normal CDF `Phi x = (gaussianReal 0 1 (Iic x)).toReal` has
derivative equal to the standard normal PDF at every point, by FTC.

This is a foundational identity not present in Mathlib (no `Real.erf`, no
`gaussianReal_Iic_hasDerivAt`). Proved here via Lebesgue-`Iic` decomposition
into an interval integral plus a constant, then `intervalIntegral.integral_hasDerivAt_right`.

## Main result

* `hasDerivAt_Phi` — `HasDerivAt Phi (gaussianPDFReal 0 1 x) x` for every `x : ℝ`.
-/

namespace QuantFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Standard normal CDF derivative**: `Phi'(x) = gaussianPDFReal 0 1 x`. -/
theorem hasDerivAt_Phi (x : ℝ) :
    HasDerivAt Phi (gaussianPDFReal 0 1 x) x := by
  set a : ℝ := x - 1
  have hax : a < x := by show x - 1 < x; linarith
  have h_pdf_int : Integrable (gaussianPDFReal 0 1) volume :=
    integrable_gaussianPDFReal _ _
  have h_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    exact (continuous_const).mul (by fun_prop)
  have h_int_ax : IntervalIntegrable (gaussianPDFReal 0 1) volume a x :=
    h_pdf_int.intervalIntegrable
  -- FTC right endpoint
  have h_ftc : HasDerivAt (fun u => ∫ z in a..u, gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 x) x :=
    intervalIntegral.integral_hasDerivAt_right h_int_ax
      h_pdf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      h_pdf_cont.continuousAt
  -- Add the constant Phi a.
  have h_shifted : HasDerivAt
      (fun u => Phi a + ∫ z in a..u, gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 x) x := by
    have := h_ftc.const_add (Phi a)
    simpa using this
  -- Phi equals this function in a neighborhood of x (for y > a).
  have h_eq_nhds : Phi =ᶠ[nhds x]
      (fun u => Phi a + ∫ z in a..u, gaussianPDFReal 0 1 z) := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hax) ?_
    intro y hy
    rw [Set.mem_Ioi] at hy
    show Phi y = Phi a + ∫ z in a..y, gaussianPDFReal 0 1 z
    rw [Phi_eq_integral, Phi_eq_integral, intervalIntegral.integral_of_le hy.le]
    have h_decomp : Set.Iic y = Set.Iic a ∪ Set.Ioc a y := by
      ext z
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · by_cases h : z ≤ a
        · exact Or.inl h
        · exact Or.inr ⟨not_le.mp h, hz⟩
      · rcases hz with h | ⟨_, h⟩
        · linarith
        · exact h
    have h_disj : Disjoint (Set.Iic a) (Set.Ioc a y) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      simp only [Set.mem_Iic] at hz1
      simp only [Set.mem_Ioc] at hz2
      linarith [hz2.1]
    rw [h_decomp, setIntegral_union h_disj measurableSet_Ioc
      h_pdf_int.integrableOn h_pdf_int.integrableOn]
  exact h_shifted.congr_of_eventuallyEq h_eq_nhds

end QuantFin
