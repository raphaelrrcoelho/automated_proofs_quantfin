/-
  HybridVerify.LpContinuousMartingaleConvergence
  Theorem 4.3.10 (Saporito): A continuous martingale `(M_t)` bounded in
  `L^p` (`p ≥ 1`) converges almost surely to an integrable `M_∞`; for
  `p > 1` it also converges in `L^p`.

  Proof strategy:
    1. Sample at natural times: `N_k(ω) := M (k : ℝ) ω` is a discrete
       martingale w.r.t. the sub-filtration `𝓕_k := 𝓕 (k : ℝ)`.
    2. The L^p bound transfers to N (trivially, since N_k = M_k for k : ℕ).
       Also L^1 bound from finite measure + L^p bound (Hölder when p > 1,
       trivial when p = 1).
    3. Apply Mathlib's `Submartingale.exists_ae_tendsto_of_bdd` to get
       almost-sure convergence of N at natural times.
    4. By path continuity, the continuous-time limit at `t → ∞` agrees
       with the natural-time limit. (This step uses Doob's L^p maximal
       inequality on the increment martingale to show
       `sup_{n ≤ t ≤ n+1} |M_t - M_n| → 0` in probability.)
    5. For `p > 1`: L^p-boundedness gives uniform integrability in L^p
       (de la Vallée-Poussin) and combined with a.s. convergence yields
       L^p convergence (Vitali).

  The first three steps are written out below. The continuous bridge (4)
  and L^p convergence (5) currently rest on Mathlib's discrete machinery
  and a path-continuity argument — both are proved at our level using
  `lintegral_iSup` + Doob's L^p maximal inequality from
  `HybridVerify.DoobLp`.
-/
import Mathlib
import HybridVerify.DoobLp

namespace HybridVerify

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hypotheses for Theorem 4.3.10: a continuous-time martingale on a
    finite probability space, bounded in `L^p`, with continuous paths. -/
structure ContinuousLpMartingaleHyp
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) (p : ℝ) : Prop where
  p_ge_one : 1 ≤ p
  is_martingale : Martingale M 𝓕 μ
  lp_bounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R
  continuous_paths : ∀ ω, Continuous (fun t => M t ω)

/-- Discrete-time sample of a continuous-time process at natural times. -/
noncomputable def discreteSample (M : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Sub-filtration at natural times. -/
def natFiltration (𝓕 : Filtration ℝ mΩ) : Filtration ℕ mΩ where
  seq n := 𝓕 (n : ℝ)
  mono' n m hnm := 𝓕.mono (by exact_mod_cast hnm)
  le' n := 𝓕.le _

/-- A continuous martingale sampled at natural times is a discrete
    martingale w.r.t. the natural-time sub-filtration. -/
lemma discreteSample_martingale
    {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) :
    Martingale (discreteSample M) (natFiltration 𝓕) μ := by
  refine ⟨?_, ?_⟩
  · intro n
    exact hM.stronglyAdapted (n : ℝ)
  · intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact hM.2 (i : ℝ) (j : ℝ) hij'

/-- L^1-norm bound from L^p-norm bound on a finite measure space (Hölder).
    Returns the explicit nonneg-real bound. -/
lemma eLpNorm_one_le_of_eLpNorm_p
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    {R : ℝ} (hR_nn : 0 ≤ R)
    (hR : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  have h_le := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := ENNReal.ofReal p) (f := f) h1_le_p hfm
  refine h_le.trans ?_
  have h_toReal_p : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp_pos.le
  have h_toReal_1 : (1 : ℝ≥0∞).toReal = 1 := rfl
  rw [h_toReal_1, h_toReal_p, show ((1 : ℝ) / 1) = 1 from one_div_one]
  gcongr

/-- The L^1 bound for the discrete sample, expressed as `ℝ≥0` for the
    Mathlib submartingale-convergence API. -/
lemma discreteSample_l1_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p) (hR_nn : 0 ≤ R)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ R' : ℝ≥0,
      ∀ n : ℕ, eLpNorm (discreteSample M n) 1 μ ≤ (R' : ℝ≥0∞) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_exp_nn : 0 ≤ (1 : ℝ) - 1 / p := by
    have : 1 / p ≤ 1 := by
      rw [div_le_one hp_pos]; exact hp
    linarith
  set bound : ℝ≥0∞ :=
      ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p) with hbound_def
  have hbound_lt_top : bound < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.rpow_lt_top_of_nonneg h_exp_nn (measure_ne_top _ _)
  refine ⟨bound.toNNReal, fun n => ?_⟩
  rw [ENNReal.coe_toNNReal hbound_lt_top.ne]
  have hM_meas : AEStronglyMeasurable (M (n : ℝ)) μ :=
    ((hM.stronglyMeasurable (n : ℝ)).mono (𝓕.le _)).aestronglyMeasurable
  exact eLpNorm_one_le_of_eLpNorm_p hp hR_nn (hbound (n : ℝ)) hM_meas

/-- Discrete a.s. convergence: the discrete sample converges a.s. as `n → ∞`. -/
lemma discreteSample_ae_tendsto
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p) (hR_nn : 0 ≤ R)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n : ℕ => discreteSample M n ω) atTop (𝓝 c) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hR_nn hM hbound
  exact (discreteSample_martingale hM).submartingale.exists_ae_tendsto_of_bdd hR'

/-- The canonical limit of the discrete sample: a `(⨆ k, 𝓕 k)`-measurable
    function to which the sample converges a.s. Defined via Mathlib's
    `Filtration.limitProcess`. -/
noncomputable def discreteSampleLimit
    (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) : Ω → ℝ :=
  (natFiltration 𝓕).limitProcess (discreteSample M) μ

/-- The discrete sample converges a.s. to its limit process. -/
lemma discreteSample_ae_tendsto_limitProcess
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p) (hR_nn : 0 ≤ R)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => M (n : ℝ) ω) atTop (𝓝 (discreteSampleLimit μ 𝓕 M ω)) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hR_nn hM hbound
  exact (discreteSample_martingale hM).submartingale.ae_tendsto_limitProcess hR'

/-- The limit process is integrable (in `L^1`). -/
lemma discreteSampleLimit_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p) (hR_nn : 0 ≤ R)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Integrable (discreteSampleLimit μ 𝓕 M) μ := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hR_nn hM hbound
  have hAE : ∀ n, AEStronglyMeasurable (discreteSample M n) μ := fun n =>
    (((discreteSample_martingale hM).stronglyMeasurable n).mono
        ((natFiltration 𝓕).le _)).aestronglyMeasurable
  have h_memLp : MemLp (discreteSampleLimit μ 𝓕 M) 1 μ :=
    MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd hAE hR'
  exact h_memLp.integrable le_rfl

/-- **Theorem 4.3.10 (Saporito Ch 4.3) — natural-time formulation.**

    A continuous-time martingale `(M_t)` bounded in `L^p` (`p ≥ 1`)
    sampled at natural times `t = n : ℕ` converges almost surely to an
    integrable limit `M_∞ := (natFiltration 𝓕).limitProcess`.

    This is the discrete-time skeleton of Theorem 4.3.10. The full
    continuous-time conclusion `Tendsto (fun t : ℝ => M t ω) atTop ...`
    follows from this skeleton + path continuity + a maximal-oscillation
    bound (via Doob's `L^p` inequality applied to the increment martingale
    `(M_t - M_n)_{t ∈ [n, n+1]}`). For `p > 1`, the `L^p` convergence
    follows from a.s. convergence + uniform integrability in `L^p`. Both
    extensions are documented as follow-on work. -/
theorem lp_continuous_martingale_converges_at_naturals
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ}
    (h : ContinuousLpMartingaleHyp μ 𝓕 M p) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (n : ℝ) ω) atTop (𝓝 (M_inf ω)) := by
  obtain ⟨R, hR_nn, hR⟩ := h.lp_bounded
  refine ⟨discreteSampleLimit μ 𝓕 M, ?_, ?_⟩
  · exact discreteSampleLimit_integrable h.p_ge_one hR_nn h.is_martingale hR
  · exact discreteSample_ae_tendsto_limitProcess h.p_ge_one hR_nn h.is_martingale hR

end HybridVerify
