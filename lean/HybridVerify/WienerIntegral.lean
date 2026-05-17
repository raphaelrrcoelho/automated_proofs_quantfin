/-
  HybridVerify.WienerIntegral

  Construction of the **Wiener integral** `∫₀ᵀ f(s) dB_s` for a deterministic
  `L²`-integrand `f : ℝ → ℝ` against a Brownian motion `B`, together with
  the **Itô isometry** for the deterministic case:

       E[(∫₀ᵀ f dB)²] = ∫₀ᵀ f(s)² ds.

  This is a special case of the full Itô integral construction (which
  requires general `L²`-predictable integrands and is multi-week
  research-grade Lean work). For deterministic integrands the construction
  collapses to a standard Cauchy-completion argument:

  1. For a single step `f = c · 𝟙_{(s, t]}`, the Wiener integral is
     `c · (B_t − B_s)`. Isometry follows from
     `E[(B_t − B_s)²] = Var[B_t − B_s] = t − s` (BM increment variance).
  2. For a finite linear combination of disjoint steps, the integral is
     a sum of independent Gaussian increments. Isometry follows from
     independence + centering: `E[(∑ X_k)²] = ∑ E[X_k²]`.
  3. (Future work) For general `f ∈ L²([0, T])`, simple functions are
     dense in `L²` (Mathlib: `MeasureTheory.SimpleFunc.dense_lp`), so the
     step-function integral extends by L²-Cauchy completion. Isometry is
     preserved under the extension.

  This file completes step 1 (single-step isometry) end-to-end with no
  sorries. Step 2 follows by induction on a `Finset` (sketched as a
  follow-on lemma). Step 3 — the full Cauchy-completion construction — is
  documented as remaining work; it is the standard piece of the Wiener
  integral that requires several hundred more lines of Lean.
-/
import Mathlib

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hypotheses captured from the textbook setup for the Wiener integral
    against a (real-time-indexed) Brownian motion. -/
structure BrownianIncrementSpec (μ : Measure Ω) (B : ℝ → Ω → ℝ) : Prop where
  /-- `B_0 = 0` almost surely. -/
  zero_start : ∀ᵐ ω ∂μ, B 0 ω = 0
  /-- Each increment `B_t − B_s` (for `s ≤ t`) is centered Gaussian with
      variance `t − s`. -/
  gaussian_increments : ∀ ⦃s t : ℝ⦄, s ≤ t →
    ∃ v : NNReal, (v : ℝ) = t - s ∧
      Measure.map (fun ω => B t ω - B s ω) μ = gaussianReal 0 v
  /-- BM has independent increments: for `r ≤ s ≤ t`, `B s − B r` and
      `B t − B s` are independent. -/
  indep_increments : HasIndepIncrements B μ

/-- A BM increment is `AEMeasurable` — its law is a (nonzero) Gaussian, and
`AEMeasurable.of_map_ne_zero` recovers measurability from a nonzero pushforward. -/
private lemma BrownianIncrementSpec.aemeasurable_increment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {s t : ℝ} (hst : s ≤ t) :
    AEMeasurable (fun ω => B t ω - B s ω) μ := by
  obtain ⟨v, _, hv_map⟩ := hB.gaussian_increments hst
  exact AEMeasurable.of_map_ne_zero (by rw [hv_map]; exact IsProbabilityMeasure.ne_zero _)

/-- BM increments have mean zero (under the Gaussian-increments hypothesis). -/
lemma BrownianIncrementSpec.integral_increment_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {s t : ℝ} (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
  obtain ⟨_, _, hv_map⟩ := hB.gaussian_increments hst
  rw [show ∫ ω, (B t ω - B s ω) ∂μ
        = ∫ x, x ∂(Measure.map (fun ω => B t ω - B s ω) μ) from
        (integral_map (hB.aemeasurable_increment hst)
          measurable_id'.aestronglyMeasurable).symm,
      hv_map, integral_id_gaussianReal]

/-- **Wiener step-integral isometry.**

    For a Brownian motion `B` with centered Gaussian increments of
    variance `t − s` and any scalar `c`, the single-step Wiener integral
    `c · (B_t − B_s)` satisfies

         `∫ ω, (c · (B_t ω − B_s ω))² ∂μ = c² · (t − s)`.

    This is the kernel of the Itô isometry: for a step function
    `f = c · 𝟙_{(s, t]}`, both `E[(∫ f dB)²] = c² (t − s)` and
    `∫₀ᵀ f² ds = c² (t − s)` (when `T ≥ t ≥ s ≥ 0`). -/
theorem wiener_step_isometry
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    (c : ℝ) {s t : ℝ} (hst : s ≤ t) :
    ∫ ω, (c * (B t ω - B s ω)) ^ 2 ∂μ = c ^ 2 * (t - s) := by
  -- Extract the increment distribution.
  obtain ⟨v, hv_eq, hv_map⟩ := hB.gaussian_increments hst
  have h_aemeas := hB.aemeasurable_increment hst
  -- Rewrite `∫ ω, (c · (B_t − B_s))² ∂μ = c² · ∫ ω, (B_t − B_s)² ∂μ`.
  simp_rw [mul_pow]
  rw [integral_const_mul]
  congr 1
  -- `∫ ω, (B_t − B_s)² ∂μ = ∫ x, x² ∂(law of B_t − B_s)`.
  have h_map : ∫ ω, (B t ω - B s ω) ^ 2 ∂μ
              = ∫ x, x ^ 2 ∂(Measure.map (fun ω => B t ω - B s ω) μ) := by
    rw [integral_map h_aemeas
      (continuous_pow 2).measurable.aestronglyMeasurable]
  rw [h_map, hv_map]
  -- `∫ x, x² ∂(gaussianReal 0 v) = v` (variance of centered Gaussian).
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  have h_var : Var[id; gaussianReal (0:ℝ) v] = (v : ℝ) :=
    variance_id_gaussianReal
  have h_var_eq : Var[id; gaussianReal (0:ℝ) v] = ∫ x, x ^ 2 ∂(gaussianReal (0:ℝ) v) := by
    have := variance_of_integral_eq_zero
      (X := (id : ℝ → ℝ)) (μ := gaussianReal (0:ℝ) v)
      measurable_id'.aemeasurable h_mean
    simpa using this
  rw [← h_var_eq, h_var]
  exact hv_eq

/-- BM increment has integrable square (variance is finite, i.e., MemLp 2). -/
lemma BrownianIncrementSpec.integrable_increment_sq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {s t : ℝ} (hst : s ≤ t) :
    Integrable (fun ω => (B t ω - B s ω) ^ 2) μ := by
  obtain ⟨_, _, hv_map⟩ := hB.gaussian_increments hst
  have h_aemeas := hB.aemeasurable_increment hst
  -- Pushforward integrability: ∫ x², ∂(law) < ∞.
  rw [show (fun ω => (B t ω - B s ω) ^ 2) = (fun x : ℝ => x ^ 2) ∘ (fun ω => B t ω - B s ω)
        from rfl]
  apply Integrable.comp_aemeasurable _ h_aemeas
  rw [hv_map]
  -- Integrable (x ↦ x²) under gaussianReal 0 v.
  exact ((memLp_id_gaussianReal 2).integrable_norm_rpow
    (by norm_num) ENNReal.ofNat_ne_top).mono'
    (by fun_prop) (by filter_upwards with x; simp [sq_abs])

/-- Variance of a single BM increment equals the time gap. -/
lemma BrownianIncrementSpec.variance_increment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {s t : ℝ} (hst : s ≤ t) :
    Var[fun ω => B t ω - B s ω; μ] = t - s := by
  obtain ⟨_, hv_eq, _⟩ := hB.gaussian_increments hst
  have h_aemeas := hB.aemeasurable_increment hst
  have h_mean_zero : ∫ ω, (B t ω - B s ω) ∂μ = 0 :=
    hB.integral_increment_eq_zero hst
  -- Var = E[X²] when E[X] = 0.
  rw [variance_of_integral_eq_zero h_aemeas h_mean_zero]
  -- E[X²] = (LHS of wiener_step_isometry with c = 1).
  have := wiener_step_isometry (μ := μ) hB 1 hst
  simp at this
  exact this

/-- A single scaled BM increment is in `L²`. -/
private lemma BrownianIncrementSpec.memLp_increment_two
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {s t : ℝ} (hst : s ≤ t) :
    MemLp (fun ω => B t ω - B s ω) 2 μ :=
  (memLp_two_iff_integrable_sq (hB.aemeasurable_increment hst).aestronglyMeasurable).mpr
    (hB.integrable_increment_sq hst)

/-- **Finset Wiener isometry.** For a monotone partition `p : Fin (n+1) → ℝ`
    and coefficients `c : Fin n → ℝ`, the Wiener step-sum

       `I ω = ∑ k, c k · (B (p k.succ) ω − B (p k.castSucc) ω)`

    satisfies the discrete Itô isometry

       `E[I²] = ∑ k, c k² · (p k.succ − p k.castSucc)`.

    Each summand is centered, the summands are jointly independent (the
    increment processes `B(p_{k+1}) − B(p_k)` are independent via
    `HasIndepIncrements`, and scaling by `c k` preserves independence
    pointwise). Therefore `E[I²] = Var(I) = ∑ Var(c k · increment_k)
    = ∑ c k² · (p_{k+1} − p_k)`. -/
theorem wiener_finset_isometry
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianIncrementSpec μ B)
    {n : ℕ} (p : Fin (n + 1) → ℝ) (hp : Monotone p) (c : Fin n → ℝ) :
    ∫ ω, (∑ k : Fin n, c k * (B (p k.succ) ω - B (p k.castSucc) ω)) ^ 2 ∂μ
      = ∑ k : Fin n, c k ^ 2 * (p k.succ - p k.castSucc) := by
  set X : Fin n → Ω → ℝ :=
    fun k ω => c k * (B (p k.succ) ω - B (p k.castSucc) ω) with hX
  have hpk : ∀ k : Fin n, p k.castSucc ≤ p k.succ :=
    fun k => hp (Fin.castSucc_le_succ k)
  have h_aemeas : ∀ k, AEMeasurable (X k) μ := fun k =>
    (hB.aemeasurable_increment (hpk k)).const_mul (c k)
  have h_memLp : ∀ k, MemLp (X k) 2 μ := fun k =>
    (hB.memLp_increment_two (hpk k)).const_mul (c k)
  have h_mean_zero : ∀ k, ∫ ω, X k ω ∂μ = 0 := fun k => by
    simp only [hX, integral_const_mul, hB.integral_increment_eq_zero (hpk k), mul_zero]
  have h_var_X : ∀ k, Var[X k; μ] = c k ^ 2 * (p k.succ - p k.castSucc) := fun k => by
    simp only [hX, variance_const_mul, hB.variance_increment (hpk k)]
  have h_iIndep :
      iIndepFun (fun (k : Fin n) ω => B (p k.succ) ω - B (p k.castSucc) ω) μ :=
    hB.indep_increments n p hp
  have h_iIndep_X : iIndepFun X μ :=
    h_iIndep.comp (fun k x => c k * x) (fun _ => measurable_const.mul measurable_id)
  have h_pair :
      Set.Pairwise (↑(Finset.univ : Finset (Fin n))) (fun i j => X i ⟂ᵢ[μ] X j) :=
    fun _ _ _ _ hij => h_iIndep_X.indepFun hij
  have h_aemeas_sum : AEMeasurable (∑ k : Fin n, X k) μ :=
    Finset.aemeasurable_sum _ (fun k _ => h_aemeas k)
  have h_mean_sum : ∫ ω, (∑ k : Fin n, X k) ω ∂μ = 0 := by
    simp_rw [Finset.sum_apply]
    rw [integral_finset_sum _ (fun k _ => (h_memLp k).integrable one_le_two)]
    exact Finset.sum_eq_zero (fun k _ => h_mean_zero k)
  calc ∫ ω, (∑ k : Fin n, X k ω) ^ 2 ∂μ
      = ∫ ω, ((∑ k : Fin n, X k) ω) ^ 2 ∂μ := by simp_rw [Finset.sum_apply]
    _ = Var[∑ k : Fin n, X k; μ] :=
        (variance_of_integral_eq_zero h_aemeas_sum h_mean_sum).symm
    _ = ∑ k : Fin n, Var[X k; μ] :=
        IndepFun.variance_sum (fun k _ => h_memLp k) h_pair
    _ = ∑ k : Fin n, c k ^ 2 * (p k.succ - p k.castSucc) :=
        Finset.sum_congr rfl (fun k _ => h_var_X k)

end HybridVerify
