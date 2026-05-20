/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholesCall
import HybridVerify.BlackScholesPDE
import HybridVerify.BlackScholesPutGreeks

/-!
# Static Black-Scholes option-price bounds and arbitrage identities

Three families of model-light identities that follow directly from the formula
definitions:

* **Phi bounds** `0 ≤ Φ(x) ≤ 1`: standard normal CDF range.
* **Call and put upper bounds**:
  - `bsV ≤ S`, `bsP ≤ K·e^{-rτ}` from `Φ ≤ 1`.
* **Box-spread identity**: `(bsV(K₁) - bsP(K₁)) - (bsV(K₂) - bsP(K₂)) =
  (K₂ - K₁) · e^{-rτ}` — pure-arbitrage identity from put-call parity at two
  strikes.

The intrinsic-value lower bound `bsV ≥ S - K·e^{-rτ}` reduces to the put
non-negativity `bsP ≥ 0`. From the closed-form alone this is not pure algebra
— a monotonicity-in-`K` argument (`∂_K bsV ≤ 0`) plus `bsV(0) = S` is needed;
deferred to a follow-up that adds the `∂_K bsV` lemma.

Results:

* `Phi_le_one`: `Φ(x) ≤ 1`.
* `bsV_le_S`: `bsV(K, r, σ, S, τ) ≤ S` for `S ≥ 0, K ≥ 0`.
* `bsP_le_K_disc`: `bsP(K, r, σ, S, τ) ≤ K · e^{-rτ}` for `S ≥ 0, K ≥ 0`.
* `box_spread_identity`: the box spread payoff equals `(K₂ - K₁) · e^{-rτ}`.
-/

namespace HybridVerify

open Real

/-- The standard normal CDF is at most `1`. -/
lemma Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  have h_sum : Phi x + Phi (-x) = 1 := Phi_add_Phi_neg x
  have h_neg : 0 ≤ Phi (-x) := Phi_nonneg _
  linarith

/-- **Call upper bound**: `bsV ≤ S` for `S, K ≥ 0`. -/
lemma bsV_le_S (K r σ : ℝ) (S τ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) :
    bsV K r σ S τ ≤ S := by
  unfold bsV
  have h_Φd1 : Phi (bsd1 S K r σ τ) ≤ 1 := Phi_le_one _
  have h_Φd2 : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  have h_exp : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_S_term : S * Phi (bsd1 S K r σ τ) ≤ S := by
    have := mul_le_mul_of_nonneg_left h_Φd1 hS
    simpa using this
  have h_K_term : 0 ≤ K * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) := by
    positivity
  linarith

/-- **Put upper bound**: `bsP ≤ K · e^{-rτ}` for `S, K ≥ 0`. -/
lemma bsP_le_K_disc (K r σ : ℝ) (S τ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) :
    bsP K r σ S τ ≤ K * Real.exp (-(r * τ)) := by
  unfold bsP
  have h_Φnegd2 : Phi (-bsd2 S K r σ τ) ≤ 1 := Phi_le_one _
  have h_Φnegd1 : 0 ≤ Phi (-bsd1 S K r σ τ) := Phi_nonneg _
  have h_exp : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_first :
      K * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ) ≤
        K * Real.exp (-(r * τ)) := by
    have h_factor_nn : 0 ≤ K * Real.exp (-(r * τ)) := mul_nonneg hK h_exp
    have := mul_le_mul_of_nonneg_left h_Φnegd2 h_factor_nn
    simpa using this
  have h_second : 0 ≤ S * Phi (-bsd1 S K r σ τ) := mul_nonneg hS h_Φnegd1
  linarith

/-- **Box-spread identity**: `(bsV(K₁) − bsP(K₁)) − (bsV(K₂) − bsP(K₂)) =
(K₂ − K₁) · e^{-rτ}` — a pure-arbitrage identity from put-call parity at two
strikes. -/
lemma box_spread_identity (K₁ K₂ r σ S τ : ℝ) :
    (bsV K₁ r σ S τ - bsP K₁ r σ S τ) -
      (bsV K₂ r σ S τ - bsP K₂ r σ S τ) =
      (K₂ - K₁) * Real.exp (-(r * τ)) := by
  have h₁ : bsP K₁ r σ S τ = bsV K₁ r σ S τ - S + K₁ * Real.exp (-(r * τ)) :=
    bsP_eq_bsV K₁ r σ S τ
  have h₂ : bsP K₂ r σ S τ = bsV K₂ r σ S τ - S + K₂ * Real.exp (-(r * τ)) :=
    bsP_eq_bsV K₂ r σ S τ
  linarith

end HybridVerify
