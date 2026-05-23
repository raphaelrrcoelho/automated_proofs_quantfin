/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Risk parity portfolio (two-asset closed form)

A risk-parity portfolio sets each asset's *marginal contribution to variance*
equal across assets. For two assets with volatilities `σ₁, σ₂` and
correlation `ρ`, the closed-form risk-parity weights (under the budget
constraint `w₁ + w₂ = 1`) are independent of `ρ`:

  `w₁^RP = σ₂ / (σ₁ + σ₂)`,
  `w₂^RP = σ₁ / (σ₁ + σ₂)`.

The independence from correlation is the surprising feature: only the
relative volatilities matter for equal-risk allocation.

Result:

* `riskParityWeightTwo`: definition `σ₂ / (σ₁ + σ₂)`.
* `risk_parity_equal_contribution`: at the RP weights, the two assets'
  contributions to portfolio variance are equal.
-/

namespace QuantFin

/-- Risk-parity weight on asset 1 in the two-asset case. The other asset gets
the complementary weight `σ₁ / (σ₁ + σ₂)`. -/
noncomputable def riskParityWeightTwo (σ₁ σ₂ : ℝ) : ℝ :=
  σ₂ / (σ₁ + σ₂)

/-- **Risk-parity equal-contribution identity** for two assets: at
`w₁ = σ₂/(σ₁+σ₂)`, `w₂ = σ₁/(σ₁+σ₂)`, asset 1 and asset 2 contribute
identically to portfolio variance regardless of correlation `ρ`. The
contribution of asset `i` is `w_i · (Σ·w)_i = w_i · (w_i σ_i² + w_j ρ σ_i σ_j)`. -/
theorem risk_parity_equal_contribution (σ₁ σ₂ ρ : ℝ)
    (hσ : σ₁ + σ₂ ≠ 0) :
    let w₁ := riskParityWeightTwo σ₁ σ₂
    let w₂ := riskParityWeightTwo σ₂ σ₁
    w₁ * (w₁ * σ₁^2 + w₂ * ρ * σ₁ * σ₂) =
      w₂ * (w₁ * ρ * σ₁ * σ₂ + w₂ * σ₂^2) := by
  unfold riskParityWeightTwo
  rw [show σ₂ + σ₁ = σ₁ + σ₂ from by ring]
  field_simp
  ring

/-- **Risk-parity weights sum to one**: `w₁ + w₂ = 1`. -/
lemma riskParity_weights_sum_one (σ₁ σ₂ : ℝ) (hσ : σ₁ + σ₂ ≠ 0) :
    riskParityWeightTwo σ₁ σ₂ + riskParityWeightTwo σ₂ σ₁ = 1 := by
  unfold riskParityWeightTwo
  rw [show σ₂ + σ₁ = σ₁ + σ₂ from by ring]
  field_simp
  ring

end QuantFin
