/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion
import BrownianMotion.StochasticIntegral.SimpleProcess
import QuantFin.Foundations.ItoIsometryAdapted

/-!
# The continuous L²-adapted Itô integral (construction, anchored on Degenne's `SimpleProcess`)

This file builds the continuous Itô integral as a continuous linear isometry
extending the elementary (simple-process) integral, **anchored on Degenne's
`BrownianMotion.StochasticIntegral` objects** (the maximally-coherent /
upstream-track choice). The algebraic core is the adapted Itô isometry from
`ItoIsometryAdapted.lean` — in particular the predictable-rectangle pairing
`rect_increment_pairing`, which is exactly the right tool because Degenne's
`SimpleProcess` allows *overlapping* intervals.

## Setup

* `natFiltration` — the natural Brownian filtration `𝓕ᴮ_t = σ(B_u : u ≤ t)`
  (Mathlib `Filtration.natural`). By `IsPreBrownian.isFilteredPreBrownian` a
  pre-Brownian motion is automatically `IsFilteredPreBrownian` for it.
* `adaptedAt_of_measurable_natural` — **the bridge** connecting Degenne's
  filtration-measurability (which `SimpleProcess.value` carries) to this
  library's `ItoIsometryAdapted.AdaptedAt` (factoring through the past process),
  via Doob–Dynkin (`Measurable.exists_eq_measurable_comp`). This is what lets the
  `AdaptedAt`-stated isometry core consume Degenne's `SimpleProcess`.
* `itoSimple` — the elementary Itô integral `(V ● B)_⊤ = ∑ₚ V(p)·(B_{p.2}−B_{p.1})`
  of a simple process `V` against Brownian motion, as a function `Ω → ℝ`
  (Degenne's `SimpleProcess.integral` against the multiplication bilinear map,
  evaluated at the terminal time `⊤`).

## Construction roadmap (mirrors `WienerIntegralL2.lean`, integrand space adapted)

1. [done here] `itoSimple V` and its `⊤`-unfolding `itoSimple_apply`.
2. [next] `itoSimple V ∈ L²(μ)`: a finite sum of `V(p)·ΔB_p`, each in `L²` by
   `memLp_adapted_mul_increment` (via the bridge + `V`'s boundedness).
3. [next] the **isometry on simple processes**:
   `‖itoSimple V‖²_{L²(μ)} = ‖V‖²_{L2Predictable}` — the diagonal/off-diagonal
   double sum collapses by `rect_increment_pairing`.
4. [next] **density** of `SimpleProcess` images in `L2Predictable` via Degenne's
   `ElementaryPredictableSet.generateFrom_eq_predictable` + the Wiener
   orthogonal-complement route over the trimmed (predictable) measure.
5. [next] `LinearMap.extendOfNorm` ⇒ `itoIntegralL2 : L2Predictable ν μ →L[ℝ] Lp ℝ 2 μ`,
   with the Itô isometry `‖itoIntegralL2 φ‖² = ∫₀ᵀ E[φ_t²] dt`.
-/

namespace QuantFin
namespace ItoIntegralL2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The **natural Brownian filtration** `𝓕ᴮ_t = σ(B_u : u ≤ t)`. -/
noncomputable def natFiltration (hBmeas : ∀ t, Measurable (B t)) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t => (hBmeas t).stronglyMeasurable)

/-- **Bridge to the past-process encoding.** A function measurable with respect to
the natural Brownian filtration at `s` is `ItoIsometryAdapted.AdaptedAt B s` —
it factors through the past process `ω ↦ (B u ω)_{u ≤ s}`. This is the
Doob–Dynkin factorisation (`Measurable.exists_eq_measurable_comp`, valid since
ℝ is a standard Borel space), and it is what makes the `AdaptedAt`-stated
isometry core (`rect_increment_pairing` et al.) applicable to Degenne's
`SimpleProcess`, whose `value` is `𝓕 p.1`-measurable. -/
theorem adaptedAt_of_measurable_natural (hBmeas : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {f : Ω → ℝ} (hf : Measurable[natFiltration hBmeas s] f) :
    ItoIsometryAdapted.AdaptedAt B s f := by
  -- `natural B s = ⨆ u ≤ s, comap (B u) ≤ comap (pastProcess B s)`, since each
  -- `B u` (u ≤ s) factors as `eval_u ∘ pastProcess`.
  have hle : (natFiltration hBmeas s) ≤
      MeasurableSpace.comap (ItoIsometryAdapted.pastProcess B s) inferInstance := by
    refine iSup₂_le fun u hu => ?_
    have hBu : B u
        = (fun p : Set.Iic s → ℝ => p ⟨u, hu⟩) ∘ ItoIsometryAdapted.pastProcess B s := rfl
    rw [hBu, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_pi_apply _))
  obtain ⟨g, hg, hgeq⟩ := (hf.mono hle le_rfl).exists_eq_measurable_comp
  exact ⟨g, hg, hgeq⟩

/-- The **elementary Itô integral** of a simple process `V` against Brownian motion
`B`, evaluated at the terminal time: `(V ● B)_⊤`. Built from Degenne's
`SimpleProcess.integral` against the multiplication bilinear map. -/
noncomputable def itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B ⊤

/-- The terminal Itô integral as the explicit increment sum
`(V ● B)_⊤ ω = ∑ₚ V(p) ω · (B_{p.2} ω − B_{p.1} ω)`. -/
lemma itoSimple_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ω : Ω) :
    itoSimple hBmeas V ω
      = V.value.sum fun p v => v ω * (B p.2 ω - B p.1 ω) := by
  simp only [itoSimple, SimpleProcess.integral_top, ContinuousLinearMap.mul_apply']

end ItoIntegralL2
end QuantFin
