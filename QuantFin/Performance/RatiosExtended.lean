/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Performance.Ratios

/-!
# Extended performance ratios: Sortino, Treynor, Information ratio

Standard quant performance metrics beyond the basic Sharpe ratio:

* **Sortino ratio** `S = (μ - target) / σ_down`, with `σ_down` the downside
  semi-deviation. Like Sharpe but penalises only downside variation.
* **Treynor ratio** `T = (μ - r_f) / β`, with `β = Cov(R, R_m) / Var(R_m)` the
  systematic risk. The market-model analogue of Sharpe.
* **Information ratio** `IR = (μ_p - μ_b) / σ_active`, with `σ_active` the
  tracking error (std-dev of `R_p − R_b`). Measures active management skill.
* **Tracking-error decomposition**: `σ_active² = σ_p² − 2·Cov + σ_b²`.

Sortino, Treynor, and IR are all instances of `(a − b)/d`. Their
*scale-invariance* lemmas are one-line consequences of the algebraic master
`diff_div_scale_invariant` in `Performance.Ratios`. (The same master also
handles the Sharpe scale invariance — proving that the master is load-bearing
across all four ratios in the library.)

Results:

* `sortinoRatio`, `sortinoRatio_scale_invariant`, `sortinoRatio_translation`.
* `treynorRatio`, `treynorRatio_scale_invariant`.
* `informationRatio`, `informationRatio_scale_invariant`.
* `trackingErrorSq`, `trackingErrorSq_self`, `trackingErrorSq_ge_diff_sq`.
-/

namespace QuantFin

open Real

/-- **Sortino ratio** `(μ - target) / σ_down`. Inputs are the mean, the target
return, and the downside semi-deviation. -/
noncomputable def sortinoRatio (μ target σ_down : ℝ) : ℝ :=
  (μ - target) / σ_down

/-- Sortino is invariant under uniform rescaling. One-line consequence of
`diff_div_scale_invariant`. -/
lemma sortinoRatio_scale_invariant {c : ℝ} (hc : c ≠ 0)
    (μ target σ_down : ℝ) :
    sortinoRatio (c * μ) (c * target) (c * σ_down) =
      sortinoRatio μ target σ_down := by
  unfold sortinoRatio
  exact diff_div_scale_invariant hc μ target σ_down

/-- Sortino is translation-invariant in the additive shift of both mean and
target. -/
lemma sortinoRatio_translation (μ target σ_down shift : ℝ) :
    sortinoRatio (μ + shift) (target + shift) σ_down =
      sortinoRatio μ target σ_down := by
  unfold sortinoRatio
  ring_nf

/-- **Treynor ratio** `(μ - r_f) / β`, with `β` the systematic-risk coefficient. -/
noncomputable def treynorRatio (μ r_f β : ℝ) : ℝ := (μ - r_f) / β

/-- Treynor is invariant under uniform rescaling. One-line consequence of
`diff_div_scale_invariant`. -/
lemma treynorRatio_scale_invariant {c : ℝ} (hc : c ≠ 0) (μ r_f β : ℝ) :
    treynorRatio (c * μ) (c * r_f) (c * β) = treynorRatio μ r_f β := by
  unfold treynorRatio
  exact diff_div_scale_invariant hc μ r_f β

/-- **Information ratio** `(μ_p - μ_b) / σ_active`, with `σ_active` the
tracking error. -/
noncomputable def informationRatio (μ_p μ_b σ_active : ℝ) : ℝ :=
  (μ_p - μ_b) / σ_active

/-- Information ratio is invariant under uniform rescaling. One-line
consequence of `diff_div_scale_invariant`. -/
lemma informationRatio_scale_invariant {c : ℝ} (hc : c ≠ 0)
    (μ_p μ_b σ_active : ℝ) :
    informationRatio (c * μ_p) (c * μ_b) (c * σ_active) =
      informationRatio μ_p μ_b σ_active := by
  unfold informationRatio
  exact diff_div_scale_invariant hc μ_p μ_b σ_active

/-- **Tracking error squared**: `σ_active² = σ_p² − 2·Cov(R_p, R_b) + σ_b²`.
We define `trackingError² := σ_p² - 2 · cov + σ_b²` and prove this matches the
expansion of `Var(R_p − R_b)`. -/
noncomputable def trackingErrorSq (σ_p σ_b cov : ℝ) : ℝ :=
  σ_p ^ 2 - 2 * cov + σ_b ^ 2

/-- **Tracking-error decomposition**: when the benchmark equals the portfolio
(`σ_p = σ_b` and `cov = σ_p²`), the tracking error vanishes. -/
lemma trackingErrorSq_self (σ_p : ℝ) :
    trackingErrorSq σ_p σ_p (σ_p ^ 2) = 0 := by
  unfold trackingErrorSq
  ring

/-- **Tracking error non-negativity** when `cov ≤ σ_p · σ_b` (Cauchy-Schwarz
bound): `σ_active² ≥ (σ_p - σ_b)²`. -/
lemma trackingErrorSq_ge_diff_sq (σ_p σ_b cov : ℝ) (h_cs : cov ≤ σ_p * σ_b) :
    (σ_p - σ_b) ^ 2 ≤ trackingErrorSq σ_p σ_b cov := by
  unfold trackingErrorSq
  nlinarith [h_cs]

end QuantFin
