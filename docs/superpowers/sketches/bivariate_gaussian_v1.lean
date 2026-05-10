/-
  HybridVerify.BivariateGaussian
  Theorem B.1.3(2): conditional expectation of bivariate Gaussian.

  For (X, Y) jointly Gaussian with positive marginal variances and correlation
  ρ ∈ (−1, 1):
      E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y) (Y − μ_Y)   a.s.

  Strategy:
    Let β := ρ σ_X / σ_Y. Define Xhat := μ_X + β (Y − μ_Y), the "linear regression
    estimator" of X given Y.
    1. Xhat is σ(Y)-measurable (it is a continuous function of Y), so
       E[Xhat | σ(Y)] = Xhat.
    2. The pair (X − Xhat, Y) is also jointly Gaussian (linear map of (X, Y)).
    3. Cov(X − Xhat, Y) = Cov(X, Y) − β · Cov(Y, Y) = ρ σ_X σ_Y − β σ_Y² = 0
       (by the choice of β).
    4. Joint Gaussian + zero covariance ⇒ X − Xhat ⊥ Y (Mathlib's
       `HasGaussianLaw.indepFun_of_covariance_eq_zero`).
    5. Hence E[X − Xhat | σ(Y)] =ᵐ E[X − Xhat] (a constant).
    6. E[X − Xhat] = E[X] − E[Xhat] = μ_X − μ_X = 0.
    7. Combine: E[X | σ(Y)] = E[Xhat | σ(Y)] + E[X − Xhat | σ(Y)] = Xhat + 0 = Xhat.
-/
import Mathlib

namespace HybridVerify

open MeasureTheory ProbabilityTheory

/-- Hypothesis bundle for the bivariate Gaussian conditional formula. The
    conclusion `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y − μ_Y)` is **derived**
    below (`conditional_expectation_formula`); it is not axiomatized as a
    field of this structure. -/
structure BivariateGaussianHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (μ_X μ_Y σ_X σ_Y ρ : ℝ) : Prop where
  σ_X_pos : 0 < σ_X
  σ_Y_pos : 0 < σ_Y
  X_meas : Measurable X
  Y_meas : Measurable Y
  /-- (X, Y) is jointly Gaussian. -/
  joint_gaussian : HasGaussianLaw (fun ω => (X ω, Y ω)) P
  /-- Marginal mean of X. -/
  mean_X : ∫ ω, X ω ∂P = μ_X
  /-- Marginal mean of Y. -/
  mean_Y : ∫ ω, Y ω ∂P = μ_Y
  /-- Variance of Y is σ_Y². -/
  var_Y : Var[Y; P] = σ_Y ^ 2
  /-- Cov(X, Y) = ρ σ_X σ_Y. -/
  cov_XY : cov[X, Y; P] = ρ * σ_X * σ_Y

namespace BivariateGaussianHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ} {μ_X μ_Y σ_X σ_Y ρ : ℝ}

/-- The regression coefficient `β = ρ σ_X / σ_Y`. -/
private noncomputable def beta (σ_X σ_Y ρ : ℝ) : ℝ := ρ * σ_X / σ_Y

/-- The linear regression estimator `Xhat = μ_X + β (Y − μ_Y)`. -/
private noncomputable def Xhat (μ_X μ_Y β : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => μ_X + β * (Y ω - μ_Y)

/-- The continuous linear map `T : ℝ × ℝ → ℝ × ℝ` sending `(x, y) ↦ (x − β y, y)`,
    used to transfer joint Gaussianity from `(X, Y)` to `(X − β·Y, Y)`.
    Built from primitive `ContinuousLinearMap.fst`/`.snd`/`.prod` to sidestep
    Prod.mk equality elaboration. -/
private noncomputable def linearShift (β : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Pointwise-evaluation lemma for `linearShift` to keep proofs readable. -/
@[simp] private lemma linearShift_apply (β : ℝ) (p : ℝ × ℝ) :
    linearShift β p = (p.1 - β * p.2, p.2) := by
  simp [linearShift]

/-- **Theorem B.1.3 (2)**: the conditional expectation formula for bivariate
    Gaussians, *derived* from the joint-Gaussian hypothesis. -/
theorem conditional_expectation_formula
    (h : BivariateGaussianHyp P X Y μ_X μ_Y σ_X σ_Y ρ) :
    (P[X | MeasurableSpace.comap Y inferInstance])
      =ᵐ[P] fun ω => μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y) := by
  -- Set up β and Xhat.
  set β : ℝ := ρ * σ_X / σ_Y with hβ_def
  set Xhat : Ω → ℝ := fun ω => μ_X + β * (Y ω - μ_Y) with hXhat_def
  -- σ(Y) sub-σ-algebra inclusion.
  have hY_le : MeasurableSpace.comap Y inferInstance ≤ mΩ := by
    rintro s ⟨t, ht, rfl⟩; exact h.Y_meas ht
  -- Xhat is σ(Y)-measurable (continuous function of Y).
  have hY_smeas_comap : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Y := by
    exact (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hXhat_smeas : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Xhat := by
    refine StronglyMeasurable.add stronglyMeasurable_const ?_
    refine StronglyMeasurable.const_mul ?_ β
    exact hY_smeas_comap.sub stronglyMeasurable_const
  -- Integrability: HasGaussianLaw of (X, Y) implies marginals are integrable.
  have hX_int : Integrable X P := h.joint_gaussian.fst.integrable
  have hY_int : Integrable Y P := h.joint_gaussian.snd.integrable
  -- Xhat is integrable: linear in Y plus a constant, both integrable on a probability space.
  have hXhat_int : Integrable Xhat P := by
    refine Integrable.add (integrable_const _) ?_
    exact (hY_int.sub (integrable_const _)).const_mul β
  -- E[Xhat] = μ_X (since E[Y - μ_Y] = 0).
  have hE_Xhat : ∫ ω, Xhat ω ∂P = μ_X := by
    have : ∫ ω, μ_X + β * (Y ω - μ_Y) ∂P = μ_X + β * (∫ ω, Y ω ∂P - μ_Y) := by
      rw [integral_add (integrable_const _) ((hY_int.sub (integrable_const _)).const_mul β)]
      rw [integral_const_mul, integral_sub hY_int (integrable_const _)]
      simp
    rw [show (fun ω => μ_X + β * (Y ω - μ_Y)) = Xhat from rfl] at this
    rw [this, h.mean_Y]
    ring
  -- Conditional of Xhat given σ(Y): Xhat is σ(Y)-measurable, so E[Xhat | σ(Y)] = Xhat.
  have h_condXhat : P[Xhat | MeasurableSpace.comap Y inferInstance] = Xhat :=
    condExp_of_stronglyMeasurable hY_le hXhat_smeas hXhat_int
  -- The pair (X − Xhat, Y) is jointly Gaussian.
  -- It is (linearShift β) ∘ (X, Y).
  have hXmXhat_eq : (fun ω => X ω - Xhat ω) = (fun ω => X ω - μ_X - β * (Y ω - μ_Y)) := by
    funext ω; show _ = _; ring
  have hPair_eq :
      (fun ω => (X ω - μ_X - β * (Y ω - μ_Y), Y ω - μ_Y))
        = (linearShift β) ∘ (fun ω => (X ω - μ_X, Y ω - μ_Y)) := by
    funext ω
    simp [linearShift, Function.comp]
  -- Need: HasGaussianLaw of the centered pair (X − μ_X, Y − μ_Y).
  -- Translation by a constant preserves HasGaussianLaw via map_of_measurable
  -- with the linear map (a, b) ↦ (a − μ_X, b − μ_Y). But translation by a
  -- constant isn't linear; instead use HasGaussianLaw.add_const-style results.
  -- For our purposes here we can sidestep and apply linearShift directly to
  -- (X, Y), which is jointly Gaussian.
  have hPair_eq2 :
      (fun ω => (X ω - β * Y ω, Y ω))
        = (linearShift β) ∘ (fun ω => (X ω, Y ω)) := by
    funext ω
    simp [linearShift, Function.comp]
  have h_linShift_meas : Measurable (linearShift β) := (linearShift β).continuous.measurable
  have h_jointGaussian_diff : HasGaussianLaw (fun ω => (X ω - β * Y ω, Y ω)) P := by
    rw [hPair_eq2]
    exact h.joint_gaussian.map_of_measurable (linearShift β) h_linShift_meas
  -- Cov(X − β Y, Y) = Cov(X, Y) − β · Cov(Y, Y) = ρ σ_X σ_Y − β σ_Y² = 0.
  have hcov_zero : cov[fun ω => X ω - β * Y ω, Y; P] = 0 := by
    have h_memLp_X : MemLp X 2 P := h.joint_gaussian.fst.memLp_two
    have h_memLp_Y : MemLp Y 2 P := h.joint_gaussian.snd.memLp_two
    have h_memLp_betaY : MemLp (fun ω => β * Y ω) 2 P := h_memLp_Y.const_mul β
    rw [show (fun ω => X ω - β * Y ω) = (fun ω => X ω) - (fun ω => β * Y ω) from rfl]
    rw [covariance_sub_left h_memLp_X h_memLp_betaY h_memLp_Y]
    rw [show (fun ω => β * Y ω) = β • Y from by funext; simp [Pi.smul_apply, smul_eq_mul]]
    rw [covariance_smul_left, h.cov_XY,
        show cov[Y, Y; P] = Var[Y; P] from (covariance_self h_memLp_Y.aemeasurable).symm,
        h.var_Y]
    have hY_ne : σ_Y ≠ 0 := ne_of_gt h.σ_Y_pos
    field_simp
    ring
  -- IndepFun (X − β Y) Y P (Gaussian + cov 0).
  have hIndep : IndepFun (fun ω => X ω - β * Y ω) Y P :=
    h_jointGaussian_diff.indepFun_of_covariance_eq_zero hcov_zero
  -- Bridge: indep of σ-algebras (comap of (X − βY) and comap of Y).
  have h_diff_meas : Measurable (fun ω => X ω - β * Y ω) :=
    h.X_meas.sub (h.Y_meas.const_mul β)
  have h_diff_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω => X ω - β * Y ω) (borel ℝ)]
        (fun ω => X ω - β * Y ω) :=
    fun s' hs' => ⟨s', hs', rfl⟩
  have h_diff_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω => X ω - β * Y ω) (borel ℝ)]
        (fun ω => X ω - β * Y ω) :=
    h_diff_meas_comap.stronglyMeasurable
  have h_diff_le_comap :
      MeasurableSpace.comap (fun ω => X ω - β * Y ω) (borel ℝ) ≤ mΩ := by
    rintro s' ⟨t', ht', rfl⟩; exact h_diff_meas ht'
  have h_indep_sigma :
      Indep (MeasurableSpace.comap (fun ω => X ω - β * Y ω) (borel ℝ))
            (MeasurableSpace.comap Y inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).mp hIndep
  -- E[X − β Y | σ(Y)] =ᵐ E[X − β Y] = μ_X − β μ_Y (constant).
  have hE_diff : ∫ ω, X ω - β * Y ω ∂P = μ_X - β * μ_Y := by
    rw [integral_sub hX_int (hY_int.const_mul β), integral_const_mul, h.mean_X, h.mean_Y]
  have h_int_diff : Integrable (fun ω => X ω - β * Y ω) P :=
    hX_int.sub (hY_int.const_mul β)
  have h_condDiff :
      P[fun ω => X ω - β * Y ω | (MeasurableSpace.comap Y inferInstance)]
        =ᵐ[P] fun _ => μ_X - β * μ_Y := by
    have := condExp_indep_eq h_diff_le_comap hY_le h_diff_smeas_comap h_indep_sigma
    rw [hE_diff] at this
    exact this
  -- Decomposition: X = Xhat + (X − Xhat), where X − Xhat = X − μ_X − β(Y − μ_Y) = (X − β Y) − (μ_X − β μ_Y).
  -- E[X | σ(Y)] = E[Xhat | σ(Y)] + E[X − Xhat | σ(Y)] = Xhat + 0 = Xhat.
  have h_X_decomp : (X : Ω → ℝ) = Xhat + (fun ω => X ω - β * Y ω - (μ_X - β * μ_Y)) := by
    funext ω
    show X ω = (μ_X + β * (Y ω - μ_Y)) + (X ω - β * Y ω - (μ_X - β * μ_Y))
    ring
  have h_int_XhatplusD : Integrable
      (Xhat + (fun ω => X ω - β * Y ω - (μ_X - β * μ_Y))) P := by
    rw [← h_X_decomp]; exact hX_int
  have h_cond_split :
      P[X | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] (P[Xhat | MeasurableSpace.comap Y inferInstance])
          + (P[fun ω => X ω - β * Y ω - (μ_X - β * μ_Y)
              | MeasurableSpace.comap Y inferInstance]) := by
    rw [h_X_decomp]
    exact condExp_add hXhat_int (h_int_diff.sub (integrable_const _)) _
  -- Compute the second term: E[(X − β Y) − const | σ(Y)] =ᵐ (μ_X − β μ_Y) − (μ_X − β μ_Y) = 0.
  have h_cond_centered :
      P[fun ω => X ω - β * Y ω - (μ_X - β * μ_Y)
        | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] fun _ => (0 : ℝ) := by
    have h1 : P[fun ω => X ω - β * Y ω - (μ_X - β * μ_Y)
        | MeasurableSpace.comap Y inferInstance]
              =ᵐ[P]
              (P[fun ω => X ω - β * Y ω | MeasurableSpace.comap Y inferInstance])
                - P[fun _ : Ω => μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance] :=
      condExp_sub h_int_diff (integrable_const _) _
    have h2 : P[fun _ : Ω => μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance]
            = fun _ => μ_X - β * μ_Y :=
      condExp_const hY_le (μ_X - β * μ_Y)
    filter_upwards [h1, h_condDiff] with ω hω1 hω2
    show _ = (0 : ℝ)
    rw [hω1]
    show _ - _ = 0
    rw [show (P[fun ω => X ω - β * Y ω | MeasurableSpace.comap Y inferInstance])
            - P[fun _ : Ω => μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance]
          = (fun ω => (P[fun ω => X ω - β * Y ω | MeasurableSpace.comap Y inferInstance]) ω
                      - (P[fun _ : Ω => μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance]) ω)
        from rfl]
    rw [hω2, h2]
    show _ - (μ_X - β * μ_Y) = 0
    ring
  -- Combine.
  refine h_cond_split.trans ?_
  filter_upwards [h_cond_centered] with ω hω
  show ((P[Xhat | MeasurableSpace.comap Y inferInstance]) +
        (P[fun ω => X ω - β * Y ω - (μ_X - β * μ_Y)
          | MeasurableSpace.comap Y inferInstance])) ω
      = μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y)
  simp only [Pi.add_apply]
  rw [hω, h_condXhat]
  show (μ_X + β * (Y ω - μ_Y)) + (0 : ℝ) = μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y)
  rw [hβ_def]
  ring

end BivariateGaussianHyp

end HybridVerify
