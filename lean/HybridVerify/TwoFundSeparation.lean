/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.PerformanceRatios

/-!
# Capital Market Line and two-fund separation (algebraic)

In the presence of a risk-free asset with rate `r_f` and a Sharpe-optimal
"tangent" portfolio with mean `μ_t` and standard deviation `σ_t > 0`, every
combined portfolio formed as `α · tangent + (1 − α) · risk-free` satisfies:

* **CML equation**: `μ_combined = r_f + α · σ_t · Sharpe_t`, i.e. the (mean, std)
  pairs trace the line `μ = r_f + Sharpe_t · σ` through `(0, r_f)`.
* **Sharpe invariance**: the Sharpe ratio of any CML portfolio equals the
  tangent Sharpe ratio (for `α > 0`, `σ_t > 0`).
* **Decomposition**: any `(μ_p, σ_p)` lying on the CML decomposes uniquely as
  `α = σ_p / σ_t` units of the tangent fund plus `1 − α` units of risk-free.

These are the algebraic content of Tobin's two-fund separation theorem.

Results:

* `cmlMean`, `cmlStdev`: the (mean, std) of a CML portfolio at weight `α`.
* `cml_equation`: `μ_combined = r_f + Sharpe_t · σ_combined` on the CML.
* `cml_sharpeRatio_invariant`: Sharpe is preserved along the CML.
* `cml_decomposition_unique`: the inverse map `(μ_p, σ_p) ↦ α` is `σ_p / σ_t`.
-/

namespace HybridVerify

open Real

/-- CML portfolio expected return at tangent weight `α`. -/
noncomputable def cmlMean (μ_t r_f α : ℝ) : ℝ := α * μ_t + (1 - α) * r_f

/-- CML portfolio standard deviation at tangent weight `α`. -/
noncomputable def cmlStdev (σ_t α : ℝ) : ℝ := α * σ_t

/-- **CML equation**: `μ_combined = r_f + σ_combined · Sharpe_t`. -/
lemma cml_equation (μ_t σ_t r_f α : ℝ) (hσ_t : σ_t ≠ 0) :
    cmlMean μ_t r_f α =
      r_f + cmlStdev σ_t α * sharpeRatio μ_t r_f σ_t := by
  unfold cmlMean cmlStdev sharpeRatio
  field_simp
  ring

/-- **Sharpe invariance along the CML**: for `α ≠ 0` and `σ_t ≠ 0`, any
CML portfolio has the same Sharpe ratio as the tangent portfolio. -/
lemma cml_sharpeRatio_invariant (μ_t σ_t r_f α : ℝ)
    (hα : α ≠ 0) (hσ_t : σ_t ≠ 0) :
    sharpeRatio (cmlMean μ_t r_f α) r_f (cmlStdev σ_t α) =
      sharpeRatio μ_t r_f σ_t := by
  unfold cmlMean cmlStdev sharpeRatio
  have hασt_ne : α * σ_t ≠ 0 := mul_ne_zero hα hσ_t
  field_simp
  ring

/-- **CML decomposition (uniqueness of weight)**: given a portfolio standard
deviation `σ_p` on the CML, the tangent-fund weight is uniquely determined by
`α = σ_p / σ_t`. -/
lemma cml_decomposition_unique (σ_t σ_p : ℝ) (hσ_t : σ_t ≠ 0) :
    cmlStdev σ_t (σ_p / σ_t) = σ_p := by
  unfold cmlStdev
  field_simp

/-- **Mean recovery on the CML**: a portfolio with std deviation `σ_p` on the
CML through `r_f` with tangent slope `Sharpe_t` has expected return
`μ_p = r_f + σ_p · Sharpe_t`. -/
lemma cml_mean_at_stdev (μ_t σ_t r_f σ_p : ℝ) (hσ_t : σ_t ≠ 0) :
    cmlMean μ_t r_f (σ_p / σ_t) = r_f + σ_p * sharpeRatio μ_t r_f σ_t := by
  unfold cmlMean sharpeRatio
  field_simp
  ring

end HybridVerify
