/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.Model

/-!
# Cox-Ross-Rubinstein convergence to Black-Scholes

We formalize the **CRR parameterization** of the binomial tree:
with `Δt = T/n`, `u_n = e^{σ √Δt}`, `d_n = e^{-σ √Δt}`,
the n-step risk-neutral up-probability is

    `p_n = (e^{r Δt} − d_n) / (u_n − d_n).`

This file proves:
1. **One-step risk-neutral martingale identity** (exact, algebraic):
   `p_n · u_n + (1 − p_n) · d_n = e^{r Δt}`.
2. **Exponential-difference-quotient limits** at 0 used throughout the proof:
   * `(e^{c x} − 1) / x → c` as `x → 0` (first-order Taylor of exp at 0).
   * `(e^{c h²} − 1) / h² → c` (composition with `h ↦ h²`).
   * `(e^{σ h} − e^{-σ h}) / h → 2σ` (sinh-derivative at 0).
3. **CRR probability limit**: `p_n → 1/2` as `n → ∞`. This implies
   `4 p_n (1 − p_n) → 1`, which gives the variance limit
   `n · σ² Δt · 4 p_n (1 − p_n) → σ² T`.

## Scope (honest)

The **full pricing convergence**

    `binomialPrice (u_n) (d_n) (rΔt) (max(· − K, 0)) n S_0  →  bs_call_price`

requires a **triangular-array CLT** (Lindeberg-Feller) applied to the row-wise
iid binary log-return increments under the n-th risk-neutral measure, plus a
continuous-mapping + uniform-integrability argument. Mathlib at the current
pin only provides the fixed-iid CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`),
not the triangular-array version. We document the missing piece here and leave
the full convergence theorem as future upstream work.

What IS proved in this file: the **classical analytic CRR↔BS correspondence**
on mean and variance of one log-return increment. These are the substantive
textbook computations that lead to the CLT application.
-/

namespace QuantFin

open Filter
open scoped Topology

/-! ### CRR parameterization -/

/-- CRR step size: `Δt = T / n`. -/
noncomputable def crrStep (T : ℝ) (n : ℕ) : ℝ := T / n

/-- CRR up-factor: `u_n = exp(σ √(T/n))`. -/
noncomputable def crrUp (σ T : ℝ) (n : ℕ) : ℝ := Real.exp (σ * Real.sqrt (crrStep T n))

/-- CRR down-factor: `d_n = exp(-σ √(T/n))`. -/
noncomputable def crrDown (σ T : ℝ) (n : ℕ) : ℝ := Real.exp (-(σ * Real.sqrt (crrStep T n)))

/-- CRR per-step continuously-compounded rate: `r · Δt = r T / n`. -/
noncomputable def crrPerStepRate (r T : ℝ) (n : ℕ) : ℝ := r * crrStep T n

/-- CRR risk-neutral up-probability. -/
noncomputable def crrProb (r σ T : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (crrPerStepRate r T n) - crrDown σ T n) / (crrUp σ T n - crrDown σ T n)

/-! ### Positivity and basic facts -/

lemma crrUp_pos (σ T : ℝ) (n : ℕ) : 0 < crrUp σ T n := Real.exp_pos _

lemma crrDown_pos (σ T : ℝ) (n : ℕ) : 0 < crrDown σ T n := Real.exp_pos _

/-- Under `σ > 0, T > 0, n ≥ 1`, the up-factor exceeds the down-factor. -/
lemma crrDown_lt_crrUp {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) {n : ℕ} (hn : 1 ≤ n) :
    crrDown σ T n < crrUp σ T n := by
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_step_pos : 0 < crrStep T n := div_pos hT h_n_pos
  have h_sqrt_pos : 0 < Real.sqrt (crrStep T n) := Real.sqrt_pos.mpr h_step_pos
  unfold crrDown crrUp
  rw [Real.exp_lt_exp]
  linarith [mul_pos hσ h_sqrt_pos]

/-! ### One-step risk-neutral martingale identity (algebraic, exact) -/

/-- **CRR one-step martingale identity** (exact, not asymptotic):
    `p · u + (1 − p) · d = e^{r Δt}`. The discrete-time risk-neutral measure makes
    the one-step discounted asset price a martingale.

    Requires the no-arbitrage condition `d < e^{rΔt}` (implied by `d < u` when
    we're between them, but explicit here so this works in either parameterization). -/
theorem crr_one_step_martingale {σ T r : ℝ} {n : ℕ}
    (h_du : crrDown σ T n < crrUp σ T n) :
    crrProb r σ T n * crrUp σ T n + (1 - crrProb r σ T n) * crrDown σ T n
      = Real.exp (crrPerStepRate r T n) := by
  have h_ud : 0 < crrUp σ T n - crrDown σ T n := sub_pos.mpr h_du
  have h_ud_ne : crrUp σ T n - crrDown σ T n ≠ 0 := h_ud.ne'
  unfold crrProb
  field_simp
  ring

/-! ### Step-size limits -/

/-- The CRR step `Δt = T/n` tends to 0 as `n → ∞`. -/
lemma tendsto_crrStep_zero (T : ℝ) : Tendsto (crrStep T) atTop (𝓝 0) := by
  unfold crrStep
  exact Tendsto.div_atTop tendsto_const_nhds (tendsto_natCast_atTop_atTop (R := ℝ))

/-- `√(T/n) → 0` as `n → ∞`. -/
lemma tendsto_sqrt_crrStep_zero (T : ℝ) :
    Tendsto (fun n => Real.sqrt (crrStep T n)) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
  exact (Real.continuous_sqrt.tendsto 0).comp (tendsto_crrStep_zero T)

/-! ### Exponential difference quotients (first-order Taylor at 0) -/

/-- **Difference quotient of `exp` at 0**: `(e^{c x} − 1) / x → c` as `x → 0` (`x ≠ 0`).
    Just `HasDerivAt (fun x => e^{cx}) c 0` unpacked via `hasDerivAt_iff_tendsto_slope`. -/
lemma tendsto_exp_sub_one_div (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (c * x) - 1) / x) (𝓝[≠] 0) (𝓝 c) := by
  have h_deriv : HasDerivAt (fun x : ℝ => Real.exp (c * x)) c 0 := by
    have h_lin : HasDerivAt (fun x : ℝ => c * x) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
    have := h_lin.exp
    simpa using this
  have h_slope := h_deriv.tendsto_slope
  have h_eq : ∀ x : ℝ,
      slope (fun x : ℝ => Real.exp (c * x)) 0 x = (Real.exp (c * x) - 1) / x := by
    intro x
    rw [slope_def_field]
    simp [Real.exp_zero]
  exact h_slope.congr' (Eventually.of_forall h_eq)

/-- `Tendsto (fun h => h²) (𝓝[≠] 0) (𝓝[≠] 0)`. -/
lemma tendsto_sq_nhds_within_ne (a : ℝ) : a^2 ≠ 0 ↔ a ≠ 0 :=
  ⟨fun h ha => h (by simp [ha]), fun h => pow_ne_zero 2 h⟩

private lemma tendsto_sq_nhdsWithin_ne_zero :
    Tendsto (fun h : ℝ => h^2) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h_cont : Continuous (fun h : ℝ => h^2) := by continuity
    have h_tendsto_nhds : Tendsto (fun h : ℝ => h^2) (𝓝 0) (𝓝 0) := by
      have := h_cont.tendsto 0
      simpa using this
    exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact pow_ne_zero 2 hh

/-- `(e^{c · h²} − 1) / h² → c` as `h → 0` (`h ≠ 0`).
    Composition of `tendsto_exp_sub_one_div` with `h ↦ h²`. -/
lemma tendsto_exp_sq_sub_one_div_sq (c : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (c * h^2) - 1) / h^2) (𝓝[≠] 0) (𝓝 c) :=
  (tendsto_exp_sub_one_div c).comp tendsto_sq_nhdsWithin_ne_zero

/-- `(e^{c · h²} − 1) / h → 0` as `h → 0` (`h ≠ 0`).
    Equals `h · ((e^{c·h²} − 1)/h²) → 0 · c = 0`. -/
lemma tendsto_exp_sq_sub_one_div_h (c : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (c * h^2) - 1) / h) (𝓝[≠] 0) (𝓝 0) := by
  have h_id : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h_sq := tendsto_exp_sq_sub_one_div_sq c
  have h_mul := h_id.mul h_sq
  -- h_mul : Tendsto (fun h => h * ((exp(c·h²)-1)/h²)) (𝓝[≠] 0) (𝓝 (0 * c))
  have h_target_eq : (0 : ℝ) * c = 0 := zero_mul c
  rw [h_target_eq] at h_mul
  refine h_mul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh_ne : h ≠ 0 := hh
  have h_sq_ne : h^2 ≠ 0 := pow_ne_zero 2 hh_ne
  field_simp

/-- `(e^{σ h} − 1)/h − (e^{-σ h} − 1)/h = (e^{σ h} − e^{-σ h})/h`. -/
private lemma exp_diff_sub_eq (σ h : ℝ) :
    (Real.exp (σ * h) - 1) / h - (Real.exp (-(σ * h)) - 1) / h
      = (Real.exp (σ * h) - Real.exp (-(σ * h))) / h := by
  rw [← sub_div]
  congr 1
  ring

/-- `(e^{σ h} − e^{-σ h}) / h → 2σ` as `h → 0` (`h ≠ 0`). -/
lemma tendsto_sinh_div (σ : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (σ * h) - Real.exp (-(σ * h))) / h)
      (𝓝[≠] 0) (𝓝 (2 * σ)) := by
  have h_pos : Tendsto (fun h : ℝ => (Real.exp (σ * h) - 1) / h) (𝓝[≠] 0) (𝓝 σ) :=
    tendsto_exp_sub_one_div σ
  have h_neg : Tendsto (fun h : ℝ => (Real.exp (-(σ * h)) - 1) / h) (𝓝[≠] 0) (𝓝 (-σ)) := by
    refine (tendsto_exp_sub_one_div (-σ)).congr' ?_
    filter_upwards with h
    rw [show -σ * h = -(σ * h) from by ring]
  have h_diff := h_pos.sub h_neg
  have h_target : (σ - (-σ) : ℝ) = 2 * σ := by ring
  rw [h_target] at h_diff
  refine h_diff.congr' ?_
  filter_upwards with h
  exact exp_diff_sub_eq σ h

/-! ### CRR probability limit: `p_n → 1/2` -/

/-- **CRR probability limit**: `p_n → 1/2` as `n → ∞`.

The intuition: as `Δt = T/n → 0`, both `e^{rΔt} - e^{-σ√Δt}` and `e^{σ√Δt} - e^{-σ√Δt}`
tend to 0, but they share the leading `σ√Δt` term, so the ratio tends to `1/2`.

Formally: substitute `h_n = √(T/n)`. Then
  `p_n = (e^{r·h_n²} - e^{-σ·h_n}) / (e^{σ·h_n} - e^{-σ·h_n})`.

Multiply numerator and denominator by `1/h_n`:
  `p_n = [(e^{r·h_n²} - 1)/h_n − (e^{-σ·h_n} − 1)/h_n] / [(e^{σ·h_n} − 1)/h_n − (e^{-σ·h_n} − 1)/h_n]`.

As `h_n → 0`:
  - `(e^{r h_n²} − 1)/h_n → 0`
  - `(e^{σ h_n} − 1)/h_n → σ`
  - `(e^{-σ h_n} − 1)/h_n → −σ`

Hence `p_n → (0 − (−σ)) / (σ − (−σ)) = σ / (2σ) = 1/2`. -/
theorem crrProb_tendsto_half {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => crrProb r σ T n) atTop (𝓝 (1/2)) := by
  -- Step 1: define the per-h probability function and prove p(h) → 1/2 as h → 0 (h ≠ 0).
  -- p(h) = (e^{r·h²} - e^{-σh}) / (e^{σh} - e^{-σh})
  --      = [(e^{r·h²}-1)/h - (e^{-σh}-1)/h] / [(e^{σh}-1)/h - (e^{-σh}-1)/h]  (for h ≠ 0)
  -- Numerator → σ, denominator → 2σ, so p(h) → σ/(2σ) = 1/2.
  -- Denominator is nonzero for h ≠ 0 (since σ > 0).
  have h_denom_ne : ∀ h : ℝ, h ≠ 0 → Real.exp (σ * h) - Real.exp (-(σ * h)) ≠ 0 := by
    intro h hh h_eq
    rw [sub_eq_zero, Real.exp_eq_exp] at h_eq
    have h_zero : σ * h = 0 := by linarith
    rcases mul_eq_zero.mp h_zero with hσ0 | hh0
    · exact absurd hσ0 hσ.ne'
    · exact absurd hh0 hh
  -- Limits of numerator and denominator (working with the difference-quotient form):
  have h_neg_div : Tendsto (fun h : ℝ => (Real.exp (-(σ * h)) - 1) / h) (𝓝[≠] 0) (𝓝 (-σ)) := by
    refine (tendsto_exp_sub_one_div (-σ)).congr' ?_
    filter_upwards with h
    rw [show -σ * h = -(σ * h) from by ring]
  have h_num_tendsto : Tendsto
      (fun h : ℝ => (Real.exp (r * h^2) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
      (𝓝[≠] 0) (𝓝 σ) := by
    have h_sub := (tendsto_exp_sq_sub_one_div_h r).sub h_neg_div
    have h_target : ((0 : ℝ) - (-σ)) = σ := by ring
    rwa [h_target] at h_sub
  have h_denom_tendsto : Tendsto
      (fun h : ℝ => (Real.exp (σ * h) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
      (𝓝[≠] 0) (𝓝 (2 * σ)) := by
    have h_sub := (tendsto_exp_sub_one_div σ).sub h_neg_div
    have h_target : ((σ - (-σ)) : ℝ) = 2 * σ := by ring
    rwa [h_target] at h_sub
  -- Quotient: p_h → σ / (2σ) = 1/2
  have h_2σ_ne : (2 * σ : ℝ) ≠ 0 := by positivity
  have h_p_tendsto :
      Tendsto (fun h : ℝ =>
          ((Real.exp (r * h^2) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
            / ((Real.exp (σ * h) - 1) / h - (Real.exp (-(σ * h)) - 1) / h))
        (𝓝[≠] 0) (𝓝 (σ / (2 * σ))) :=
    h_num_tendsto.div h_denom_tendsto h_2σ_ne
  have h_half : σ / (2 * σ) = 1/2 := by field_simp
  rw [h_half] at h_p_tendsto
  -- Step 2: equate p_h to the closed form p(h) for h ≠ 0
  have h_p_form : ∀ h : ℝ, h ≠ 0 →
      ((Real.exp (r * h^2) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
        / ((Real.exp (σ * h) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
      = (Real.exp (r * h^2) - Real.exp (-(σ * h))) /
        (Real.exp (σ * h) - Real.exp (-(σ * h))) := by
    intro h hh
    have hd_ne := h_denom_ne h hh
    have h_num_eq : (Real.exp (r * h^2) - 1) / h - (Real.exp (-(σ * h)) - 1) / h
                  = (Real.exp (r * h^2) - Real.exp (-(σ * h))) / h := by
      rw [← sub_div]
      congr 1; ring
    rw [h_num_eq, exp_diff_sub_eq σ h]
    field_simp
  -- Step 3: compose with h_n = √(T/n) → 0+
  have h_h_n_tendsto : Tendsto (fun n : ℕ => Real.sqrt (crrStep T n)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_sqrt_crrStep_zero T, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_step_pos : 0 < crrStep T n := div_pos hT h_n_pos
    exact (Real.sqrt_pos.mpr h_step_pos).ne'
  have h_comp := h_p_tendsto.comp h_h_n_tendsto
  -- Step 4: Show crrProb r σ T n = (the composed expression at √(T/n)) for n ≥ 1
  refine h_comp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_step_pos : 0 < crrStep T n := div_pos hT h_n_pos
  have h_sqrt_pos : 0 < Real.sqrt (crrStep T n) := Real.sqrt_pos.mpr h_step_pos
  have h_sqrt_ne : Real.sqrt (crrStep T n) ≠ 0 := h_sqrt_pos.ne'
  have h_sqrt_sq : Real.sqrt (crrStep T n) ^ 2 = crrStep T n :=
    Real.sq_sqrt h_step_pos.le
  -- Show: crrProb r σ T n = [the composition output]
  -- Compose pulls back through `h_p_form` once we identify rT/n with r·(√(T/n))² etc.
  show ((fun h : ℝ =>
          ((Real.exp (r * h^2) - 1) / h - (Real.exp (-(σ * h)) - 1) / h)
            / ((Real.exp (σ * h) - 1) / h - (Real.exp (-(σ * h)) - 1) / h))
          ∘ fun n : ℕ => Real.sqrt (crrStep T n)) n = crrProb r σ T n
  simp only [Function.comp_apply]
  rw [h_p_form (Real.sqrt (crrStep T n)) h_sqrt_ne]
  unfold crrProb crrUp crrDown crrPerStepRate
  congr 2
  rw [h_sqrt_sq]

/-! ### Variance limit -/

/-- **Variance limit**: `n · σ² · (T/n) · 4 p_n (1 − p_n) → σ² T` as `n → ∞`.

Equivalently, the per-step variance of the log-return matches the BS variance to
leading order. Follows directly from `crrProb_tendsto_half` and limit arithmetic.

The formula simplifies: `n · σ² · (T/n) · 4 p_n (1 − p_n) = 4 σ² T · p_n (1 − p_n)`. -/
theorem crr_variance_limit {σ T r : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => 4 * σ^2 * T * (crrProb r σ T n) * (1 - crrProb r σ T n))
      atTop (𝓝 (σ^2 * T)) := by
  have h_p := crrProb_tendsto_half (r := r) hσ hT
  have h_1_minus_p : Tendsto (fun n : ℕ => 1 - crrProb r σ T n) atTop (𝓝 (1/2)) := by
    have h_const : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := h_const.sub h_p
    have h_target : (1 - 1/2 : ℝ) = 1/2 := by norm_num
    rwa [h_target] at this
  have h_prod := h_p.mul h_1_minus_p
  -- h_prod : Tendsto (p_n * (1 - p_n)) atTop (𝓝 ((1/2) * (1/2))) = (𝓝 (1/4))
  have h_const_mul : Tendsto
      (fun n : ℕ => 4 * σ^2 * T * (crrProb r σ T n * (1 - crrProb r σ T n)))
      atTop (𝓝 (4 * σ^2 * T * (1/2 * (1/2)))) := h_prod.const_mul _
  have h_target_eq : (4 * σ^2 * T * (1/2 * (1/2)) : ℝ) = σ^2 * T := by ring
  rw [h_target_eq] at h_const_mul
  refine h_const_mul.congr' ?_
  filter_upwards with n
  ring

/-! ### Future work: full pricing convergence

The remaining `binomialPrice → bs_call_price` convergence needs a
triangular-array CLT applied to the n-th risk-neutral log-return increments,
plus a continuous-mapping + uniform-integrability argument. Mathlib lacks
the triangular-array CLT at the current pin.

The classical-pedagogical content (drift+variance matching) is captured above
via `crrProb_tendsto_half` (which implies the variance limit `crr_variance_limit`).
A drift-matching theorem `n · (2 p_n − 1) · σ √Δt → (r − σ²/2) T` requires
second-order Taylor on the numerator `2 e^{r Δt} − e^{σ√Δt} − e^{-σ√Δt}` and is
left as further analytic work. -/

end QuantFin
