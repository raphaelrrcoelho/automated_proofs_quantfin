/-
  QuantFin.Foundations.Basic
  Starter formalizations for stochastic processes verification.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory

/-- Every probability measure assigns measure 1 to the full space. -/
theorem prob_measure_univ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 :=
  measure_univ

/-- The measure of the empty set is zero. -/
theorem prob_measure_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : μ ∅ = 0 :=
  measure_empty
