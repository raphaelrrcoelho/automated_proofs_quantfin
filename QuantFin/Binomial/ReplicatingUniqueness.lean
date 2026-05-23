/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.Model

/-!
# Uniqueness of the binomial replicating portfolio

The single-period binomial replicating portfolio is given by the closed-form

  `Δ = (V_u − V_d) / (S₀ · (u − d))`,
  `B = e^{−r} · (u · V_d − d · V_u) / (u − d)`,

which pays exactly `V_u` in the up-state and `V_d` in the down-state
(see `replicating_payoff_up` and `replicating_payoff_down` in `Binomial.Model`).
This file proves the *uniqueness* of this pair:

  **Given target payoffs `V_u, V_d` and the spot `S₀ > 0`, the linear system

      Δ · (S₀ · u) + B · e^r = V_u,
      Δ · (S₀ · d) + B · e^r = V_d,

  has a *unique* solution `(Δ, B)` whenever `u ≠ d` (which holds under no-arb).**

This is the discrete-time *market completeness* statement: every two-state
contingent claim is replicated by a unique portfolio. Combined with the
First FTAP (existence of a risk-neutral measure) and the Second FTAP
(uniqueness of EMM, proved single-period in `SecondFTAP.lean`), this gives
the full FTAP equivalence

  no-arb ⟺ ∃ EMM ⟺ (∃ EMM ∧ completeness) ⟺ unique EMM ⟺ completeness.

The proof is pure linear algebra: the coefficient matrix has determinant
`S₀ · (u − d) · e^r ≠ 0` under no-arb (`u > d > 0`, `e^r > 0`).

## Result

* `binomial_replicatingPortfolio_unique`: the replicating portfolio `(Δ, B)`
  is uniquely determined by the target payoffs `(V_u, V_d)`.
-/

namespace QuantFin

open Real

/-- **Uniqueness of the single-period binomial replicating portfolio**.

Under no-arbitrage (`d < e^r < u`, hence `u > d`) with positive spot `S₀ > 0`,
the linear system

  `Δ · (S₀ · u) + B · e^r = V_u`,
  `Δ · (S₀ · d) + B · e^r = V_d`

has a unique solution `(Δ, B)`, given explicitly by

  `Δ = (V_u − V_d) / (S₀ · (u − d))`,    `B = e^{−r} · (u · V_d − d · V_u) / (u − d)`.

The proof: the system is a 2×2 linear system in `(Δ, B)` with coefficient
matrix `[[S₀·u, e^r], [S₀·d, e^r]]`. Its determinant is
`S₀ · u · e^r − S₀ · d · e^r = S₀ · (u − d) · e^r`, which is strictly positive
(and so non-zero) since `S₀ > 0`, `u > d` (no-arb), and `e^r > 0`. -/
theorem binomial_replicatingPortfolio_unique
    {S₀ u d r V_u V_d : ℝ} (hS₀ : 0 < S₀) (h : BinomialNoArb u d r) :
    ∃! p : ℝ × ℝ,
      p.1 * (S₀ * u) + p.2 * Real.exp r = V_u ∧
      p.1 * (S₀ * d) + p.2 * Real.exp r = V_d := by
  have h_ud : 0 < u - d := sub_pos.mpr h.d_lt_u
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have h_S₀_ne : S₀ ≠ 0 := hS₀.ne'
  have h_exp_pos : 0 < Real.exp r := Real.exp_pos _
  have h_exp_ne : Real.exp r ≠ 0 := h_exp_pos.ne'
  set Δ : ℝ := (V_u - V_d) / (S₀ * (u - d)) with Δ_def
  set B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d) with B_def
  refine ⟨(Δ, B), ?_, ?_⟩
  · -- Existence: `(Δ, B)` satisfies both equations.
    have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
      rw [← Real.exp_add]; simp
    refine ⟨?_, ?_⟩
    · -- Δ · S₀·u + B · e^r = V_u
      rw [Δ_def, B_def]
      have h_S₀_ud_ne : S₀ * (u - d) ≠ 0 := mul_ne_zero h_S₀_ne h_ud_ne
      field_simp
      linear_combination (u * V_d - d * V_u) * h_exp_inv
    · -- Δ · S₀·d + B · e^r = V_d
      rw [Δ_def, B_def]
      have h_S₀_ud_ne : S₀ * (u - d) ≠ 0 := mul_ne_zero h_S₀_ne h_ud_ne
      field_simp
      linear_combination (u * V_d - d * V_u) * h_exp_inv
  · -- Uniqueness: any `(Δ', B')` satisfying both equations must equal `(Δ, B)`.
    rintro ⟨Δ', B'⟩ ⟨h_up, h_down⟩
    -- Subtract the two equations: Δ' · S₀ · (u - d) = V_u - V_d
    have h_sub : Δ' * (S₀ * (u - d)) = V_u - V_d := by
      have : Δ' * (S₀ * u) - Δ' * (S₀ * d) = V_u - V_d := by linarith
      linarith [show Δ' * (S₀ * u) - Δ' * (S₀ * d) = Δ' * (S₀ * (u - d)) from by ring]
    -- So Δ' = (V_u - V_d) / (S₀ · (u - d)) = Δ
    have h_S₀_ud_ne : S₀ * (u - d) ≠ 0 := mul_ne_zero h_S₀_ne h_ud_ne
    have h_Δ_eq : Δ' = Δ := by
      rw [Δ_def]
      rw [eq_div_iff h_S₀_ud_ne]
      exact h_sub
    -- From h_up and Δ' = Δ: B' · e^r = V_u − Δ' · S₀ · u; substitute Δ' = Δ:
    have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
      rw [← Real.exp_add]; simp
    have h_B'_eq : B' * Real.exp r = (u * V_d - d * V_u) / (u - d) := by
      have h_step : B' * Real.exp r = V_u - Δ' * (S₀ * u) := by linarith [h_up]
      rw [h_step, h_Δ_eq, Δ_def]
      field_simp
      ring
    have h_B_eq : B' = B := by
      rw [B_def]
      have h_recover : B' = B' * Real.exp r * Real.exp (-r) := by
        rw [mul_assoc, mul_comm (Real.exp r) (Real.exp (-r)), h_exp_inv, mul_one]
      rw [h_recover, h_B'_eq]
      ring
    exact Prod.ext h_Δ_eq h_B_eq

end QuantFin
