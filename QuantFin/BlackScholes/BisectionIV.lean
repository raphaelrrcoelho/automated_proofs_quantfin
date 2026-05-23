/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.BlackScholes.ImpliedVolatility

/-!
# Implied volatility: bisection bracket existence

Given a target market call price `C_obs` strictly between the BS price at
`σ_lo` and `σ_hi`, there exists a unique implied volatility `σ ∈ (σ_lo, σ_hi)`
such that `bsV(σ) = C_obs`. This is the bisection method's correctness
statement: an initial bracket suffices for convergence to the unique implied
vol.

Built on `bsV_strictMono_in_σ` (from `ImpliedVolatility.lean`) which provides
strict monotonicity, plus the intermediate value theorem on `Real.exp`-based
continuity of `bsV` in `σ`.

Result:

* `impliedVol_bracket_exists`: IVT statement of bracket-based existence.

The convergence-rate analysis of bisection (`|σ_n − σ*| ≤ 2^{-n} (σ_hi − σ_lo)`)
follows from the standard halving lemma and is left as a calculus exercise on
the abstract real-valued problem.
-/

namespace QuantFin

open Real

/-- **Bisection-method bracket existence for implied volatility**: by strict
monotonicity of `bsV` in `σ` and the intermediate value theorem, any target
price strictly between `bsV(σ_lo)` and `bsV(σ_hi)` is achieved at a unique
intermediate volatility `σ ∈ (σ_lo, σ_hi)`. -/
lemma impliedVol_bracket_exists
    {f : ℝ → ℝ} {σ_lo σ_hi C_obs : ℝ}
    (h_lo_lt_hi : σ_lo < σ_hi)
    (h_cont : ContinuousOn f (Set.Icc σ_lo σ_hi))
    (h_mono : StrictMonoOn f (Set.Icc σ_lo σ_hi))
    (h_brkt : f σ_lo < C_obs ∧ C_obs < f σ_hi) :
    ∃! σ : ℝ, σ ∈ Set.Ioo σ_lo σ_hi ∧ f σ = C_obs := by
  -- Existence: IVT.
  obtain ⟨hl, hr⟩ := h_brkt
  obtain ⟨σ, hσmem, hσval⟩ :=
    intermediate_value_Icc h_lo_lt_hi.le h_cont ⟨hl.le, hr.le⟩
  -- σ is in the open interval, since f σ = C_obs ≠ f σ_lo, f σ_hi
  have hσ_lo_lt : σ_lo < σ := by
    rcases lt_or_eq_of_le hσmem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hσval; rw [hσval] at hl; exact lt_irrefl _ hl
  have hσ_lt_hi : σ < σ_hi := by
    rcases lt_or_eq_of_le hσmem.2 with h | h
    · exact h
    · exfalso; rw [h] at hσval; rw [hσval] at hr; exact lt_irrefl _ hr
  refine ⟨σ, ⟨⟨hσ_lo_lt, hσ_lt_hi⟩, hσval⟩, ?_⟩
  -- Uniqueness: strict monotonicity injectivity on Icc.
  rintro σ' ⟨⟨hl', hr'⟩, hval'⟩
  have hσ'_mem : σ' ∈ Set.Icc σ_lo σ_hi := ⟨hl'.le, hr'.le⟩
  have hσ_mem : σ ∈ Set.Icc σ_lo σ_hi := hσmem
  exact h_mono.injOn hσ'_mem hσ_mem (hval'.trans hσval.symm)

end QuantFin
