/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Foundations.ItoIntegralL2

/-!
# Continuous Itô integral on `[0,T]` as a continuous linear isometry

This file extends the discrete Itô isometry on adapted simple step processes
(`ItoIntegralL2.assembly_isometry`) to a continuous-time Itô integral as a CLM

`itoIntegralCLM_T : Lp ℝ 2 trimMeasure_T →L[ℝ] Lp ℝ 2 μ`

where `trimMeasure_T = ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod` and
`timeMeasure_T T = timeMeasure.restrict (Ioc 0 T)`. The construction mirrors
`WienerIntegralL2.lean` line-for-line at the orthogonal-complement layer.

## Mathematical thesis

The Itô integral on adapted simple step processes is a finite Riemann-style sum
`∑ φₖ (B_{tₖ₊₁} − B_{tₖ})`. Density of these among all `L²`-predictable
integrands reduces, via Dynkin's π-λ theorem over the **basic predictable
rectangles** `Ioc a b ×ˢ F` with `F ∈ ℱₐ` (a π-system that generates the
predictable σ-algebra), to "a function orthogonal to every rectangle indicator
is zero a.e." We have the discrete isometry (`assembly_isometry`, imported);
we provide the density here. The CLM falls out of `LinearMap.extendOfNorm`.

## Coherence with Degenne / `BrownianMotion`

Consumes upstream (all from
`.lake/packages/BrownianMotion/BrownianMotion/StochasticIntegral/SimpleProcess.lean`):

* `ProbabilityTheory.SimpleProcess` — the integrand type, used by the
  existing `ItoIntegralL2.simpleAssembly` (= `Finsupp.linearCombination` over
  predictable indicators).
* `ProbabilityTheory.ElementaryPredictableSet` + `.indicator` — the
  predictable-set indicator realisation as a `SimpleProcess`.
* `ProbabilityTheory.ElementaryPredictableSet.generateFrom_eq_predictable` —
  the **upstream Stage-3 generation lemma** for any filtration on a
  countably-generated-`atTop` index (`ℝ≥0` qualifies).

Adds (the genuinely new content of this file):

* `predictableRect` — the basic-rectangle family generating the predictable
  σ-algebra. T enters at the measure layer (`trimMeasure_T`), not here.
* `isPiSystem_predictableRect` — closure under non-empty intersection.
* `setIntegral_eq_zero_of_orthogonal_pred` — π-λ-induction set-integral
  vanishing.
* `simpleAssembly_T_denseRange` — density of the existing simple-process
  assembly's range, in the restricted trim `L²`.
* `itoIntegralCLM_T` — the CLM.
* `itoIntegralCLM_T_norm` — the `L²`-Itô isometry.

## Conventions

* Time axis: `ℝ≥0`. Bounded horizon `T : ℝ≥0` enters via
  `timeMeasure.restrict (Ioc 0 T)` (the trim measure becomes finite of mass `T`).
* Predictable rectangles use `Ioc` (left-open, right-closed), matching
  `stochasticIoc` in `BrownianMotion` and the Wiener case.

The `ℝ≥0` (unbounded-horizon) Itô CLM requires σ-finite exhaustion of the
predictable σ-algebra and is left gated (see `docs/blueprint.md`); it is not
required by any downstream pricing module in this library.
-/

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace QuantFin
namespace ItoIntegralCLM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-! ### Bounded horizon: the restricted trim measure -/

/-- The restriction of `timeMeasure` (the σ-finite Lebesgue pushforward to
`ℝ≥0`, defined in `ItoIntegralL2.lean`) to `Ioc 0 T`. Finite of total mass `T`. -/
noncomputable def timeMeasure_T (T : ℝ≥0) : Measure ℝ≥0 :=
  ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)

/-- `timeMeasure_T T` has finite total mass `T`. The acceptance of bounded
horizon is precisely that this instance exists; the unbounded `timeMeasure`
is only σ-finite. -/
instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure_T T) := by
  refine ⟨?_⟩
  rw [timeMeasure_T, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
  exact ENNReal.ofReal_lt_top

/-- The product measure `timeMeasure_T T ⊗ μ`, trimmed to the predictable
σ-algebra of the natural Brownian filtration. The `L²`-domain of the CLM.

Reuses Degenne's `Filtration.predictable_le_prod` (upstream `L2M.lean` L27),
which is exactly the σ-algebra hypothesis `extendOfNorm` consumes.

The return type is left implicit so the σ-algebra is the predictable one (the
`trim` result), not the default `Prod.instMeasurableSpace` — annotating the
return type would force the default and cause an `Application type mismatch`. -/
noncomputable def trimMeasure_T (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :=
  ((timeMeasure_T T).prod μ).trim
    (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod

/-! ### Basic predictable rectangles: the π-system

We work with **basic** rectangles `Ioc a b ×ˢ F` (single rectangles,
`F ∈ ℱₐ`) — plus the `{0} ×ˢ F₀` "bottom" piece for `F₀ ∈ ℱ₀` — rather than
upstream's `ElementaryPredictableSet` (finite disjoint unions). Reason:
intersection of two basic rectangles is trivially another basic rectangle
(`Set.Ioc_inter_Ioc`, filtration monotonicity); intersection of two
`ElementaryPredictableSet`s would require reorganising disjoint unions, which
is mathematically equivalent but adds friction at the π-system layer.

Both families generate the same σ-algebra, `𝓕.predictable`: the basic
rectangles are exactly the components from which any `ElementaryPredictableSet`
is built (finite disjoint union of `{⊥} × B` and `(s,t] × B'`), so they
generate everything `ElementaryPredictableSet` does (upstream:
`ElementaryPredictableSet.generateFrom_eq_predictable`). -/

/-- A basic predictable rectangle in `ℝ≥0 × Ω`: either `{0} ×ˢ F₀`
(`F₀ ∈ ℱ₀`) or `Ioc a b ×ˢ F` (`F ∈ ℱₐ`, `0 < a < b`). The two cases together
mirror the upstream `ElementaryPredictableSet` constituents (the `{⊥} × B` and
`(s,t] × B'` pieces). No `T` constraint at the σ-algebra level: T enters only
via the support of `timeMeasure_T`. -/
def predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    Set (Set (ℝ≥0 × Ω)) :=
  -- The `{0} × F₀` piece (the "⊥" case)
  {S | (∃ F₀ : Set Ω,
          MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) 0] F₀ ∧
          S = ({(0 : ℝ≥0)} ×ˢ F₀))} ∪
  -- The `(a,b] × F` piece
  {S | ∃ a b : ℝ≥0, ∃ F : Set Ω,
         a < b ∧
         MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) a] F ∧
         S = (Set.Ioc a b ×ˢ F)}

/-- The basic predictable rectangles form a **π-system**: their non-empty
intersections are again basic predictable rectangles. Case analysis on which
piece (`{0}×ˢ ...` or `Ioc a b ×ˢ ...`) each rectangle belongs to:

1. `{0}×ˢ F₀₁ ∩ {0}×ˢ F₀₂ = {0}×ˢ (F₀₁∩F₀₂)`, `F₀₁∩F₀₂ ∈ ℱ₀`.
2. `{0}×ˢ F₀ ∩ Ioc a b ×ˢ F = ∅` (since `0 ∉ Ioc a b` for `a : ℝ≥0`).
   Excluded by the non-emptiness hypothesis.
3. Symmetric to (2).
4. `Ioc a₁ b₁ ×ˢ F₁ ∩ Ioc a₂ b₂ ×ˢ F₂ = Ioc (a₁⊔a₂) (b₁⊓b₂) ×ˢ (F₁∩F₂)`
   with the time interval non-degenerate (from intersection non-emptiness) and
   `F₁∩F₂ ∈ ℱ_{a₁⊔a₂}` (filtration monotonicity). -/
lemma isPiSystem_predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    IsPiSystem (predictableRect (mΩ := mΩ) hBmeas) := by
  rintro S₁ hS₁ S₂ hS₂ hne
  rcases hS₁ with ⟨F₀₁, hF₀₁, rfl⟩ | ⟨a₁, b₁, F₁, hab₁, hF₁, rfl⟩
  all_goals rcases hS₂ with ⟨F₀₂, hF₀₂, rfl⟩ | ⟨a₂, b₂, F₂, hab₂, hF₂, rfl⟩
  -- Case (bot, bot)
  · left
    refine ⟨F₀₁ ∩ F₀₂, hF₀₁.inter hF₀₂, ?_⟩
    rw [Set.prod_inter_prod, Set.inter_self]
  -- Case (bot, Ioc): intersection is empty (0 ∉ Ioc a b for a : ℝ≥0)
  · exfalso
    obtain ⟨⟨t, ω⟩, ht_mem⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff,
               Set.mem_Ioc] at ht_mem
    obtain ⟨⟨rfl, _⟩, ⟨ha₂, _⟩, _⟩ := ht_mem
    -- `ha₂ : a₂ < 0` is impossible in `ℝ≥0` (`⊥ = 0`)
    exact not_lt_bot ha₂
  -- Case (Ioc, bot): symmetric to the previous
  · exfalso
    obtain ⟨⟨t, ω⟩, ht_mem⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc,
               Set.mem_singleton_iff] at ht_mem
    obtain ⟨⟨⟨ha₁, _⟩, _⟩, rfl, _⟩ := ht_mem
    exact not_lt_bot ha₁
  -- Case (Ioc, Ioc)
  · right
    obtain ⟨⟨t, ω⟩, ht_mem⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc] at ht_mem
    obtain ⟨⟨⟨ha₁, hb₁⟩, _⟩, ⟨ha₂, hb₂⟩, _⟩ := ht_mem
    have h_lt : a₁ ⊔ a₂ < b₁ ⊓ b₂ :=
      lt_of_lt_of_le (max_lt ha₁ ha₂) (le_min hb₁ hb₂)
    refine ⟨a₁ ⊔ a₂, b₁ ⊓ b₂, F₁ ∩ F₂, h_lt, ?_, ?_⟩
    · -- F₁ ∩ F₂ ∈ ℱ_{a₁⊔a₂} (filtration monotonicity)
      have h1 := (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).mono
        (le_max_left a₁ a₂) _ hF₁
      have h2 := (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).mono
        (le_max_right a₁ a₂) _ hF₂
      exact h1.inter h2
    · -- The set equation
      rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc]

/-! ### σ-algebra generation

The basic predictable rectangles generate the predictable σ-algebra. Mirrors
upstream `ElementaryPredictableSet.generateFrom_eq_predictable`, but with the
*basic* rectangles (single, not finite-disjoint-union) — the proof is short
because we avoid the EPS-coercion-decomposition step and instead push directly
through the predictable σ-algebra's own generators (`{⊥} ×ˢ A`, `Ioi i ×ˢ A`).
The `Ioi i` decomposition is the same upstream trick: countable-generation of
`atTop` on `ℝ≥0` (via separability) gives a monotone sequence exhausting `Ioi i`
through `Ioc`-pieces. -/

/-- Generators of the predictable σ-algebra: the basic predictable rectangles
form a generating family. -/
theorem generateFrom_predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    MeasurableSpace.generateFrom (predictableRect (mΩ := mΩ) hBmeas) =
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  apply le_antisymm
  · -- ≤: every basic rectangle is predictable-measurable
    apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, _hab, hF, rfl⟩)
    · -- `{0} ×ˢ F₀ = {⊥} ×ˢ F₀` (`(⊥ : ℝ≥0) = 0` by `rfl`)
      exact MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
    · exact MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
  · -- ≥: the predictable σ-algebra is contained in `generateFrom predictableRect`
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    -- Bot generator `{⊥} ×ˢ A`: directly a basic rectangle (`⊥ = 0`)
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    -- Ioi generator `Ioi i ×ˢ A`: write as countable union of `Ioc i (seq n) ×ˢ A`
    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have h_Ioi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [h_Ioi, Set.iUnion_prod_const]
      refine MeasurableSet.iUnion fun n ↦ ?_
      by_cases hin : i < seq n
      · exact MeasurableSpace.measurableSet_generateFrom
          (Or.inr ⟨i, seq n, A, hin, hA, rfl⟩)
      · -- `Ioc i (seq n) = ∅` so the rectangle is empty; ∅ is in any σ-algebra
        have hempty : Set.Ioc i (seq n) ×ˢ A = (∅ : Set (ℝ≥0 × Ω)) := by
          rw [Set.Ioc_eq_empty_of_le (not_lt.mp hin), Set.empty_prod]
        rw [hempty]
        exact @MeasurableSet.empty _
          (MeasurableSpace.generateFrom (predictableRect (mΩ := mΩ) hBmeas))

/-! ### Phase 4: T-restricted simple-process embedding

The bridge `trimMeasure_T = trim_full.restrict (Ioc 0 T × univ)` lets us reuse
`ItoIntegralL2.memLp_uncurry_trim` (the full-trim `L²` claim) by simply
restricting to `[0,T] × Ω`. T-bounded simple processes (intervals ≤ T) form a
submodule of `SimpleProcess`; on this submodule, the existing Itô isometry
(`assembly_isometry`) directly gives the T-Itô isometry — no separate
T-truncation machinery needed. -/

/-- **Bridge.** The T-restricted predictable trim equals the restriction of the
full predictable trim to `Ioc 0 T × univ`. Proof: `prod_restrict_eq_prod_univ`
moves the time-restrict out of the product, then `restrict_trim` swaps `restrict`
and `trim` (legal because `Ioc 0 T × univ` is a basic predictable rectangle, hence
predictable-measurable). -/
lemma trimMeasure_T_eq_restrict (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    trimMeasure_T (μ := μ) T hBmeas =
      ((ItoIntegralL2.timeMeasure.prod μ).trim
        (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict
        (Set.Ioc 0 T ×ˢ Set.univ) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  show ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod = _
  unfold timeMeasure_T
  rw [Measure.restrict_prod_eq_prod_univ,
      ← MeasureTheory.restrict_trim 𝓕.predictable_le_prod _
        (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ)]

variable [hB : IsPreBrownian B μ]

/-- `uncurry V ∈ L²` in the T-restricted trim. Mirrors
`ItoIntegralL2.memLp_uncurry_trim` via the bridge + `MemLp.restrict`. -/
lemma memLp_uncurry_trim_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2 (trimMeasure_T (μ := μ) T hBmeas) := by
  rw [trimMeasure_T_eq_restrict]
  exact (ItoIntegralL2.memLp_uncurry_trim hBmeas V).restrict _

/-- The simple process's `L²` class in the T-restricted trim. -/
noncomputable def simpleProcessL2_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  (memLp_uncurry_trim_T T hBmeas V).toLp (Function.uncurry ⇑V)

/-! ### T-bounded simple processes -/

/-- The submodule of simple processes whose intervals all have right endpoint
`≤ T`. The discrete Itô integral `∑ V(p)(B_{p.2}−B_{p.1})` on such a `V`
automatically lives in `[0,T]`, so the existing `assembly_isometry` directly
gives the T-Itô isometry. -/
def TBoundedSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Submodule ℝ (SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) where
  carrier := { V | ∀ p ∈ V.value.support, p.2 ≤ T }
  add_mem' {V W} hV hW p hp := by
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    · exact hV p h
    · exact hW p h
  zero_mem' p hp := absurd hp (by simp)
  smul_mem' c V hV p hp := hV p (Finsupp.support_smul hp)

/-- For T-bounded `V`, `uncurry V` vanishes for `t > T`. The bot piece vanishes
because `t > T ≥ ⊥` rules out `t = ⊥`; each interval piece
`1_{Ioc p.1 p.2}(t) · V(p)(ω)` vanishes because `t > T ≥ p.2`. -/
lemma uncurry_eq_zero_of_lt {T : ℝ≥0} {hBmeas : ∀ t, Measurable (B t)}
    (V : TBoundedSP T hBmeas) {t : ℝ≥0} (ht : T < t) (ω : Ω) :
    Function.uncurry ⇑V.val (t, ω) = 0 := by
  show ⇑V.val t ω = 0
  rw [SimpleProcess.apply_eq]
  have ht0 : t ≠ ⊥ := by
    intro h
    rw [h, NNReal.bot_eq_zero] at ht
    exact absurd ht (by simp)
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ V.val.valueBot ω) t = 0 :=
    Set.indicator_of_notMem (by simpa using ht0) _
  rw [hbot, zero_add, Finsupp.sum]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  refine Set.indicator_of_notMem ?_ _
  simp only [Set.mem_Ioc, not_and, not_le]
  intro _
  exact lt_of_le_of_lt (V.property p hp) ht

/-- For T-bounded `V`, the `L²` norm of `uncurry V` in `trim_T` equals the norm
in the full trim. Both integrate `|uncurry V|²` over the same effective support:
trim_T integrates over `[0,T] × Ω`, and `uncurry V` vanishes off it (the bot
fibre `{0} × Ω` has measure zero in `timeMeasure.prod μ`).
(The `IsPreBrownian B μ` instance is in section scope but unused here — this is a
pure measure-theoretic equality. The linter notes this but doesn't error.) -/
private lemma eLpNorm_uncurry_trim_T_eq_trim (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) :
    eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasure_T (μ := μ) T hBmeas)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim
            (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  -- `Ioc 0 T × univ` is predictable-measurable (the natural σ-algebra of the
  -- trimmed measure). The `eLpNorm_indicator_eq_eLpNorm_restrict` lemma uses
  -- the trim's σ-algebra (via the file-level variable binding), so we need the
  -- predictable witness, not the larger product one.
  have hS_pred : MeasurableSet[𝓕.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ
  -- The bot fibre `{0} × Ω` has zero predictable-trim-measure (timeMeasure {0} = 0).
  have hnull : ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod)
      ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) = 0 := by
    have hbot_meas : MeasurableSet[𝓕.predictable] ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) :=
      MeasureTheory.measurableSet_predictable_singleton_bot_prod
        (𝓕 := 𝓕) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    rw [MeasureTheory.trim_measurableSet_eq 𝓕.predictable_le_prod hbot_meas,
        Measure.prod_prod, ItoIntegralL2.timeMeasure_singleton, zero_mul]
  -- For T-bounded V: indicator over `Ioc 0 T × univ` of `uncurry V` is a.e. equal
  -- to `uncurry V` itself (the difference is supported on the null bot fibre).
  have hae : {z : ℝ≥0 × Ω | z.1 ≠ 0} ∈ MeasureTheory.ae
      ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) := by
    rw [show {z : ℝ≥0 × Ω | z.1 ≠ 0} = ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω))ᶜ by
          ext ⟨t, ω⟩; simp]
    exact compl_mem_ae_iff.mpr hnull
  have h_ae_eq : (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)
      =ᵐ[((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod)]
        Function.uncurry ⇑V.val := by
    filter_upwards [hae] with z hz
    -- hz : z.1 ≠ 0
    by_cases htT : z.1 ≤ T
    · rw [Set.indicator_of_mem]
      refine ⟨⟨?_, htT⟩, Set.mem_univ _⟩
      exact pos_iff_ne_zero.mpr hz
    · push Not at htT
      rw [Set.indicator_of_notMem]
      · exact (uncurry_eq_zero_of_lt V htT z.2).symm
      · intro ⟨⟨_, hle⟩, _⟩
        exact absurd hle (not_le.mpr htT)
  -- Chain: trim_T → restrict (bridge) → indicator (lemma, .symm) → uncurry V (a.e.).
  calc eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasure_T (μ := μ) T hBmeas)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          (((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod).restrict
            (Set.Ioc 0 T ×ˢ Set.univ)) := by rw [trimMeasure_T_eq_restrict]
    _ = eLpNorm ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) :=
        (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hS_pred).symm
    _ = eLpNorm (Function.uncurry ⇑V.val) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) :=
        MeasureTheory.eLpNorm_congr_ae h_ae_eq

/-- The T-restricted simple-process `L²` norm equals the full-trim norm for
T-bounded `V`. -/
private lemma simpleProcessL2_T_norm_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) :
    ‖simpleProcessL2_T (μ := μ) T hBmeas V.val‖
      = ‖ItoIntegralL2.simpleProcessL2 (μ := μ) hBmeas V.val‖ := by
  have h := eLpNorm_uncurry_trim_T_eq_trim (μ := μ) T hBmeas V
  unfold simpleProcessL2_T ItoIntegralL2.simpleProcessL2
  rw [Lp.norm_toLp, Lp.norm_toLp, h]

/-- **The T-restricted simple-process `L²` embedding** as a linear map. -/
noncomputable def simpleAssembly_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) where
  toFun V := simpleProcessL2_T T hBmeas V.val
  map_add' V W := by
    show simpleProcessL2_T T hBmeas ((V + W).val) = _
    rw [Submodule.coe_add, simpleProcessL2_T, simpleProcessL2_T, simpleProcessL2_T,
        ← MemLp.toLp_add (memLp_uncurry_trim_T T hBmeas V.val)
          (memLp_uncurry_trim_T T hBmeas W.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_add hBmeas V.val W.val
  map_smul' c V := by
    show simpleProcessL2_T T hBmeas ((c • V).val) = _
    rw [Submodule.coe_smul, simpleProcessL2_T, simpleProcessL2_T, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim_T T hBmeas V.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_smul hBmeas c V.val

/-- The Itô assembly composed with the inclusion `TBoundedSP T ↪ SimpleProcess`.
For T-bounded `V`, the discrete Itô integral `∑ V(p)(B_{p.2}−B_{p.1})`
automatically lives in `[0,T]`. -/
noncomputable def itoAssembly_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 μ :=
  (ItoIntegralL2.itoAssembly (μ := μ) hBmeas).comp (TBoundedSP T hBmeas).subtype

/-- **The T-restricted Itô isometry on simple processes.** Inherits the full
isometry (`ItoIntegralL2.assembly_isometry`) via the trim-norm equality. -/
theorem assembly_isometry_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) :
    ‖itoAssembly_T (μ := μ) T hBmeas V‖ = ‖simpleAssembly_T (μ := μ) T hBmeas V‖ := by
  show ‖ItoIntegralL2.itoAssembly hBmeas V.val‖
      = ‖simpleProcessL2_T (μ := μ) T hBmeas V.val‖
  rw [simpleProcessL2_T_norm_eq T hBmeas V]
  exact ItoIntegralL2.assembly_isometry hBmeas V.val

/-! ### Phase 5: Set-integral vanishing on the orthogonal complement

The heart of the density argument. A function `g ∈ L²(trim_T)` whose set-integral
over every basic predictable rectangle vanishes has vanishing set-integral on
every measurable set in the predictable σ-algebra. The proof is Dynkin's π-λ
theorem applied to `predictableRect` (π-system from Phase 2; generator from
Phase 3). The total-integral step uses that `Ioc 0 T × univ` is a basic
rectangle (when `T > 0`) and supports `trim_T` fully; for `T = 0`, `trim_T` is
the zero measure and the total integral is trivially zero. -/

/-- `trimMeasure_T` is a finite measure (product of `timeMeasure_T` — bounded
by `T` — and the probability measure `μ`, then trimmed). -/
instance (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    IsFiniteMeasure (trimMeasure_T (μ := μ) T hBmeas) := by
  unfold trimMeasure_T
  infer_instance

private lemma setIntegral_eq_zero_of_orthogonal_pred (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) hBmeas,
      ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0)
    (s : Set (ℝ≥0 × Ω))
    (hs : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] s) :
    ∫ z in s, g z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0 := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  have hg_int : Integrable g (trimMeasure_T (μ := μ) T hBmeas) :=
    (Lp.memLp g).integrable one_le_two
  -- Total integral vanishes: trim_T is supported on `Ioc 0 T × univ`. For
  -- `T > 0` the rect is in `predictableRect` (orthogonality); for `T = 0`
  -- trim_T is zero.
  have h_total : ∫ z, g z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0 := by
    by_cases hT : 0 < T
    · -- `T > 0`: split ∫ univ into ∫_S + ∫_Sᶜ; both vanish.
      have hR : Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) ∈ predictableRect (mΩ := mΩ) hBmeas :=
        Or.inr ⟨0, T, Set.univ, hT, MeasurableSet.univ, rfl⟩
      have hS_pred : MeasurableSet[𝓕.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ
      -- Sᶜ has zero trim_T-measure: trim_T = trim_full.restrict S, so trim_T Sᶜ = trim_full(Sᶜ∩S) = 0.
      have hSc_null :
          (trimMeasure_T (μ := μ) T hBmeas) (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = 0 := by
        rw [trimMeasure_T_eq_restrict,
            Measure.restrict_apply (MeasurableSet.compl hS_pred),
            Set.compl_inter_self]
        exact measure_empty
      have h_int_Sc : ∫ z in (Set.Ioc 0 T ×ˢ Set.univ)ᶜ, g z
          ∂(trimMeasure_T (μ := μ) T hBmeas) = 0 :=
        setIntegral_measure_zero g hSc_null
      have h_int_S := h_orth _ hR
      have h_split := integral_add_compl
        (μ := trimMeasure_T (μ := μ) T hBmeas) (f := g) hS_pred hg_int
      linarith
    · -- `T = 0`: trim_T is the zero measure.
      push Not at hT
      have hT0 : T = 0 := le_antisymm hT bot_le
      have h_zero : trimMeasure_T (μ := μ) T hBmeas = 0 := by
        subst hT0
        unfold trimMeasure_T timeMeasure_T
        rw [Set.Ioc_self, Measure.restrict_empty, Measure.zero_prod,
            MeasureTheory.zero_trim]
      -- Extract `g` as a standalone function to avoid the motive issue.
      let gf : ℝ≥0 × Ω → ℝ := (g : ℝ≥0 × Ω → ℝ)
      show ∫ z, gf z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0
      rw [h_zero]
      exact integral_zero_measure gf
  -- π-system induction over `predictableRect` (Phase 2 + Phase 3).
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => ∫ z in s, g z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0)
    (h_eq := (generateFrom_predictableRect hBmeas).symm)
    (h_inter := isPiSystem_predictableRect hBmeas)
    (empty := setIntegral_empty)
    (basic := fun R hR => h_orth R hR)
    (compl := ?_) (iUnion := ?_) s hs
  · -- Complement: `∫ g = ∫_S g + ∫_Sᶜ g`; total is zero, S piece is zero, so Sᶜ piece is zero.
    intro S hS hPS
    have h_split := integral_add_compl
      (μ := trimMeasure_T (μ := μ) T hBmeas) (f := g) hS hg_int
    linarith
  · -- Disjoint countable union.
    intro f hf hfm hf_zero
    rw [integral_iUnion hfm hf hg_int.integrableOn]
    simp [hf_zero]

/-! ### Phase 6: Density of `simpleAssembly_T` and the CLM

The image of `simpleAssembly_T : TBoundedSP T →ₗ[ℝ] Lp ℝ 2 trim_T` is dense.
Proof: orthogonal-complement argument. Take `g ⊥ range(simpleAssembly_T)`.
For each basic predictable rect `R` we construct a T-bounded SP `V_R` such that
`⟪simpleAssembly_T V_R, g⟫ = ∫_R g d trim_T`. Orthogonality gives the integral
zero; Phase 5 extends to all measurable sets; `ae_eq_zero_of_forall_setIntegral`
concludes `g = 0`. The CLM `itoIntegralCLM_T` is then the `extendOfNorm` of
`itoAssembly_T` along the (now dense) `simpleAssembly_T`. -/

/-- The T-bounded SimpleProcess representing the indicator of `Ioc a b × F`,
built from upstream `ElementaryPredictableSet.IocProd.indicator`. We require
`a ≤ b` (so the IocProd's index set `I` is `{(a, b)}`) and `b ≤ T` (so the only
interval is in `[0, T]`). -/
noncomputable def iocSP_T {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) a] F) :
    TBoundedSP T hBmeas :=
  ⟨(ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ), fun p hp ↦ by
    classical
    -- The value is `Finsupp.onFinset I (...)` so its support is contained in I.
    have h_I_eq : (ElementaryPredictableSet.IocProd a b hF).I = {(a, b)} := by
      show (if a ≤ b then ({(a, b)} : Finset _) else ∅) = _
      rw [if_pos hab]
    have h_in_I : p ∈ (ElementaryPredictableSet.IocProd a b hF).I := by
      by_contra hp_not
      apply Finsupp.mem_support_iff.mp hp
      show ((ElementaryPredictableSet.IocProd a b hF).indicator 1).value p = 0
      simp [ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hp_not]
    rw [h_I_eq, Finset.mem_singleton] at h_in_I
    rcases h_in_I with rfl
    exact hbT⟩

/-- The uncurry of `iocSP_T hab hbT hF` agrees pointwise with `(Ioc a b × F).indicator 1`. -/
private lemma uncurry_iocSP_T_eq {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) a] F) :
    Function.uncurry ⇑(iocSP_T hBmeas hab hbT hF : TBoundedSP T hBmeas).val
      = (Set.Ioc a b ×ˢ F).indicator (fun _ => (1 : ℝ)) := by
  funext ⟨t, ω⟩
  change ⇑((ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ)) t ω
      = (Set.Ioc a b ×ˢ F).indicator (fun _ => (1 : ℝ)) (t, ω)
  rw [ElementaryPredictableSet.coe_indicator,
      ElementaryPredictableSet.coe_IocProd a b hF]
  rfl

/-- Inner product of `simpleAssembly_T (iocSP_T ...)` with `g` equals the
set-integral of `g` over the rectangle. -/
private lemma inner_simpleAssembly_T_iocSP_T {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) a] F)
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⟪simpleAssembly_T (μ := μ) T hBmeas (iocSP_T hBmeas hab hbT hF), g⟫_ℝ
      = ∫ z in Set.Ioc a b ×ˢ F, g z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  -- The Lp inner product takes its typeclass MeasurableSpace from trim_T's σ-alg
  -- (which is predictable, not the default product σ-alg). Make it explicit so
  -- `L2.inner_def` synthesises correctly.
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  rw [L2.inner_def]
  -- The L² inner product unfolds to ∫ ⟪f z, g z⟫_ℝ = ∫ g z * f z (Mathlib's
  -- real inner product convention `⟪x, y⟫_ℝ = y * x`).
  have h_coe := MemLp.coeFn_toLp
    (memLp_uncurry_trim_T (μ := μ) T hBmeas
      (iocSP_T hBmeas hab hbT hF : TBoundedSP T hBmeas).val)
  have h_uncurry_eq := uncurry_iocSP_T_eq hBmeas hab hbT hF
  have h_ae_eq : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      (⟪(simpleAssembly_T (μ := μ) T hBmeas (iocSP_T hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z,
        (g : ℝ≥0 × Ω → ℝ) z⟫_ℝ : ℝ)
        = (Set.Ioc a b ×ˢ F).indicator (fun z => (g : ℝ≥0 × Ω → ℝ) z) z := by
    filter_upwards [h_coe] with z hz
    -- Rewrite simpleAssembly_T V into uncurry V via h_coe; then uncurry V via h_uncurry_eq.
    have hSA_eq :
        (simpleAssembly_T (μ := μ) T hBmeas (iocSP_T hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = (Set.Ioc a b ×ˢ F).indicator (fun _ => (1 : ℝ)) z := by
      calc (simpleAssembly_T (μ := μ) T hBmeas (iocSP_T hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = Function.uncurry ⇑(iocSP_T hBmeas hab hbT hF : TBoundedSP T hBmeas).val z := hz
        _ = (Set.Ioc a b ×ˢ F).indicator (fun _ => (1 : ℝ)) z := by rw [h_uncurry_eq]
    rw [hSA_eq]
    -- Real inner product: ⟪x, y⟫_ℝ = y * x for x, y : ℝ.
    show (g : ℝ≥0 × Ω → ℝ) z * (Set.Ioc a b ×ˢ F).indicator (fun _ => (1 : ℝ)) z
        = (Set.Ioc a b ×ˢ F).indicator (fun z => (g : ℝ≥0 × Ω → ℝ) z) z
    by_cases hz_in : z ∈ Set.Ioc a b ×ˢ F
    · rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hz_in, mul_one]
    · rw [Set.indicator_of_notMem hz_in, Set.indicator_of_notMem hz_in, mul_zero]
  rw [integral_congr_ae h_ae_eq]
  -- ∫ z, R.indicator g z d trim_T = ∫_R g z d trim_T (since R is predictable-measurable)
  exact integral_indicator
    (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF)

/-! ### Density of `simpleAssembly_T` -/

/-- Bridge lemma: integrating any `g : Lp 2 trim_T` over a predictable-measurable
`R` equals the integral over `R ∩ (Ioc 0 T × univ)`. The complement of
`Ioc 0 T × univ` is `trim_T`-null because `trim_T = trim_full.restrict
(Ioc 0 T × univ)`. -/
private lemma setIntegral_eq_setIntegral_inter_supp {T : ℝ≥0}
    (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (R : Set (ℝ≥0 × Ω))
    (hR : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] R) :
    ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T hBmeas) =
      ∫ z in R ∩ (Set.Ioc 0 T ×ˢ Set.univ), g z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  -- Reset the typeclass to predictable σ-alg locally (trim_T's natural σ-alg).
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hS_pred : MeasurableSet (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ
  -- (trim_T).restrict R = (trim_full.restrict S).restrict R = trim_full.restrict (R ∩ S)
  -- and (trim_T).restrict (R ∩ S) = trim_full.restrict ((R ∩ S) ∩ S) = trim_full.restrict (R ∩ S).
  have h1 : (trimMeasure_T (μ := μ) T hBmeas).restrict R
      = (trimMeasure_T (μ := μ) T hBmeas).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ) := by
    rw [trimMeasure_T_eq_restrict,
        Measure.restrict_restrict hR,
        Measure.restrict_restrict (hR.inter hS_pred),
        Set.inter_assoc, Set.inter_self]
  show ∫ z, g z ∂((trimMeasure_T (μ := μ) T hBmeas).restrict R)
      = ∫ z, g z ∂((trimMeasure_T (μ := μ) T hBmeas).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ))
  rw [h1]

/-- **Density**: the image of `simpleAssembly_T` is dense in `Lp 2 trim_T`.
Proof outline: take `g ⊥ range(simpleAssembly_T)`. For every basic predictable
rect `R`, derive `∫_R g d trim_T = 0`:
* For the bot piece `{0} × F₀`: subset of `{0} × univ`, which is `trim_T`-null.
* For `Ioc a b × F`: reduce to `Ioc a (min b T) × F` via the bridge, then apply
  orthogonality (when non-empty) or get `∫_∅ = 0` (when degenerate).
Phase 5 extends to all predictable-measurable sets; `Lp.ae_eq_zero` concludes. -/
theorem simpleAssembly_T_denseRange (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    DenseRange (simpleAssembly_T (μ := μ) T hBmeas) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  suffices h_orth_bot :
      (LinearMap.range (simpleAssembly_T (μ := μ) T hBmeas))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range,
        ← LinearMap.coe_range (simpleAssembly_T (μ := μ) T hBmeas),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem
  -- For every basic predictable rect R, ∫_R g d trim_T = 0.
  have h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) hBmeas,
      ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T hBmeas) = 0 := by
    intro R hR
    rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, _hab, hF, rfl⟩
    · -- Bot: ∫_{{0} × F₀} g = 0 because {0} × F₀ ⊆ {0} × univ ⊆ (Ioc 0 T × univ)ᶜ
      -- (trim_T is supported on Ioc 0 T × univ).
      have h_R_pred : MeasurableSet[𝓕.predictable] ({(0 : ℝ≥0)} ×ˢ F₀) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas g _ h_R_pred]
      have h_empty : ({(0 : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) = ∅ := by
        rw [Set.prod_inter_prod,
            show ({(0 : ℝ≥0)} ∩ Set.Ioc 0 T : Set ℝ≥0) = ∅ by
              ext x; simp,
            Set.empty_prod]
      rw [h_empty, setIntegral_empty]
    · -- Ioc a b × F: bridge to Ioc a (min b T) × F, then orthogonality or empty.
      have h_R_pred : MeasurableSet[𝓕.predictable] (Set.Ioc a b ×ˢ F) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas g _ h_R_pred]
      have h_inter : (Set.Ioc a b ×ˢ F) ∩ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          = Set.Ioc (max a 0) (min b T) ×ˢ F := by
        ext ⟨t, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hω⟩, ⟨h3, h4⟩⟩
          exact ⟨⟨max_lt h1 h3, le_min h2 h4⟩, hω⟩
        · rintro ⟨⟨h1, h2⟩, hω⟩
          refine ⟨⟨⟨(le_max_left _ _).trans_lt h1, h2.trans (min_le_left _ _)⟩, hω⟩, ?_⟩
          exact ⟨(le_max_right _ _).trans_lt h1, h2.trans (min_le_right _ _)⟩
      rw [h_inter]
      have hmax : max a 0 = a := max_eq_left bot_le
      rw [hmax]
      -- Now: ∫_{Ioc a (min b T) × F} g d trim_T = 0
      by_cases hab' : a ≤ min b T
      · -- Build iocSP_T at (a, min b T, F): T-bounded with b' = min b T ≤ T.
        have hbT' : min b T ≤ T := min_le_right _ _
        have h_set := inner_simpleAssembly_T_iocSP_T (μ := μ) hBmeas hab' hbT' hF g
        have h_inner := h_mem _ ⟨iocSP_T hBmeas hab' hbT' hF, rfl⟩
        rw [← h_set]
        exact h_inner
      · -- a > min b T: Ioc a (min b T) = ∅, so R_T = ∅.
        push Not at hab'
        rw [Set.Ioc_eq_empty (not_lt.mpr hab'.le), Set.empty_prod, setIntegral_empty]
  -- Apply Phase 5 + Lp.ae_eq_zero_of_forall_setIntegral_eq_zero. Use letI to make
  -- trim_T's σ-alg (predictable) the ambient typeclass.
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun _ _ _ => ((Lp.memLp g).integrable one_le_two).integrableOn)
    (fun s hs _ => setIntegral_eq_zero_of_orthogonal_pred T hBmeas g h_orth s hs)

/-! ### The CLM `itoIntegralCLM_T` and its isometry -/

/-- **The continuous Itô integral as a CLM on `[0,T]`.** Built from
`itoAssembly_T` along `simpleAssembly_T` via `LinearMap.extendOfNorm`. -/
noncomputable def itoIntegralCLM_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoAssembly_T (μ := μ) T hBmeas).extendOfNorm (simpleAssembly_T (μ := μ) T hBmeas)

/-- **The continuous-time Itô isometry on `[0,T]`.** For every
`f ∈ Lp 2 trim_T`, `‖itoIntegralCLM_T f‖ = ‖f‖`. -/
theorem itoIntegralCLM_T_norm (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖itoIntegralCLM_T (μ := μ) T hBmeas f‖ = ‖f‖ := by
  set I := itoIntegralCLM_T (μ := μ) T hBmeas with hI
  have h_dense := simpleAssembly_T_denseRange (μ := μ) T hBmeas
  -- Norm bound `‖itoAssembly_T V‖ ≤ 1 * ‖simpleAssembly_T V‖` (i.e., the isometry).
  have h_norm : ∀ V : TBoundedSP T hBmeas,
      ‖itoAssembly_T (μ := μ) T hBmeas V‖ ≤ 1 * ‖simpleAssembly_T (μ := μ) T hBmeas V‖ :=
    fun V => by rw [one_mul]; exact (assembly_isometry_T T hBmeas V).le
  -- Equality on `range simpleAssembly_T` by `extendOfNorm_eq` + assembly isometry.
  have h_on_range : ∀ V : TBoundedSP T hBmeas,
      ‖I (simpleAssembly_T (μ := μ) T hBmeas V)‖ = ‖simpleAssembly_T (μ := μ) T hBmeas V‖ := by
    intro V
    rw [hI, itoIntegralCLM_T, LinearMap.extendOfNorm_eq h_dense ⟨1, h_norm⟩,
        assembly_isometry_T]
  -- Both sides continuous in `f`; agree on a dense set ⇒ agree everywhere.
  exact h_dense.induction_on (p := fun y => ‖I y‖ = ‖y‖) f
    (isClosed_eq (continuous_norm.comp I.continuous) continuous_norm) h_on_range

end ItoIntegralCLM
end QuantFin
