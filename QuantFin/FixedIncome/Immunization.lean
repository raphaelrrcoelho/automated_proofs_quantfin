/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Bond portfolio immunization under a deterministic short rate

A portfolio of zero-coupon bonds with face values `w i` and maturities `T i`,
indexed by a finite set `s`:

  `P(r) = ∑_{i ∈ s} w_i · exp(−r · (T_i − t))`,   `t` fixed (today).

The Macaulay-duration-times-value of the portfolio is

  `D_P · P(r) = ∑_{i ∈ s} w_i · (T_i − t) · exp(−r · (T_i − t))`.

First-order rate sensitivity: `∂P/∂r = −D_P · P`.

A portfolio is **first-order immunized** against a liability `L(r)` with duration
`D_L` if the duration-weighted asset value matches that of the liability, in
which case `∂(P − L)/∂r = 0` at the current rate.

Results:

* `bondPortfolioValue`: definition.
* `bondPortfolioDur`: duration-times-value (`D_P · P`).
* `hasDerivAt_bondPortfolioValue_r`: `∂P/∂r = −D_P · P`.
* `bondPortfolio_single_bond_dur`: a single-bond portfolio's duration-value
  equals `w · (T − t) · exp(−r·(T − t))`, recovering the ZCB result in
  `FixedIncome.lean`.
* `bondPortfolio_immunization_first_order`: when the duration-weighted asset
  and liability values match, the net portfolio's first-order rate sensitivity
  is zero.
-/

namespace QuantFin

open Real

/-- Bond portfolio value at rate `r`. -/
noncomputable def bondPortfolioValue
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * Real.exp (-(r * (T i - t)))

/-- Duration-times-value `D_P · P` of the bond portfolio. -/
noncomputable def bondPortfolioDur
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (T i - t) * Real.exp (-(r * (T i - t)))

/-- **First-order rate sensitivity**: `∂P/∂r = −D_P · P` (here equivalently
`−bondPortfolioDur`). -/
lemma hasDerivAt_bondPortfolioValue_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' => bondPortfolioValue s w T t r')
      (-bondPortfolioDur s w T t r) r := by
  unfold bondPortfolioValue bondPortfolioDur
  have h_each : ∀ i ∈ s, HasDerivAt
      (fun r' => w i * Real.exp (-(r' * (T i - t))))
      (-(w i * (T i - t) * Real.exp (-(r * (T i - t))))) r := by
    intro i _
    have h_lin : HasDerivAt (fun r' : ℝ => -(r' * (T i - t))) (-(T i - t)) r := by
      have h := (hasDerivAt_id r).mul_const (T i - t)
      simpa using h.neg
    have h_exp := h_lin.exp
    have h_prod := h_exp.const_mul (w i)
    convert h_prod using 1
    ring
  have h_raw := HasDerivAt.sum h_each
  -- `HasDerivAt.sum` yields a Pi-typed sum; convert back to a function of a sum.
  have h_fn_eq :
      (∑ i ∈ s, fun r' : ℝ => w i * Real.exp (-(r' * (T i - t)))) =
        (fun r' : ℝ => ∑ i ∈ s, w i * Real.exp (-(r' * (T i - t)))) := by
    funext r'
    rw [Finset.sum_apply]
  rw [h_fn_eq] at h_raw
  rw [Finset.sum_neg_distrib] at h_raw
  exact h_raw

/-- **Single-bond portfolio duration**: matches the ZCB duration `(T − t)`. -/
lemma bondPortfolio_single_bond_dur
    {ι : Type*} [DecidableEq ι] (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioDur {i} w T t r =
      w i * (T i - t) * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioDur
  simp

/-- Single-bond portfolio value matches the ZCB price `w · exp(−r(T − t))`. -/
lemma bondPortfolio_single_bond_value
    {ι : Type*} [DecidableEq ι] (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioValue {i} w T t r = w i * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioValue
  simp

/-- **First-order immunization**: if the duration-weighted asset value equals
the duration-weighted liability value, then the net portfolio's first-order
rate sensitivity is zero. -/
lemma bondPortfolio_immunization_first_order
    {ι κ : Type*}
    (sA : Finset ι) (wA TA : ι → ℝ)
    (sL : Finset κ) (wL TL : κ → ℝ)
    (t r : ℝ)
    (h_match : bondPortfolioDur sA wA TA t r =
               bondPortfolioDur sL wL TL t r) :
    HasDerivAt (fun r' =>
        bondPortfolioValue sA wA TA t r' -
        bondPortfolioValue sL wL TL t r')
      0 r := by
  have hA := hasDerivAt_bondPortfolioValue_r sA wA TA t r
  have hL := hasDerivAt_bondPortfolioValue_r sL wL TL t r
  have h := hA.sub hL
  convert h using 1
  rw [h_match]
  ring

end QuantFin
