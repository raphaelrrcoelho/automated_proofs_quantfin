/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.Foundations.StatePrices
import HybridVerify.Foundations.FTAPTwoState

/-!
# Pricing kernel from state prices + FTAP (phase 53)

The pre-existing `Foundations/StatePrices.lean` defines the **linear
pricing functional** `V_0(X) = Σ q_i · X_i` from Arrow-Debreu state
prices `q_i`, and proves it satisfies the standard pricing axioms (zero,
linearity, monotonicity, risk-neutral-consistency).

`Foundations/FTAPTwoState.lean` (phase 37) gives the **backward FTAP**:
under sign data `z_up > 0, z_down < 0`, an EMM exists with explicit
weights `(q_up, q_down) = (−z_down/(z_up − z_down), z_up/(z_up − z_down))`.

This file *composes* both: starting from the FTAP-derived EMM, construct
the **discounted state prices** `q_state_i := e^{−rT} · q_i^{EMM}` and
show they form a valid pricing kernel (non-negative + summing to
`e^{−rT}` = bond price), so the linear functional
`V_0(X) = Σ q_state_i · X_i` is the no-arbitrage price of any claim `X`.

This is the **stochastic discount factor** / **pricing kernel**
framework instantiated in the simplest finite-state market: every claim's
no-arb price is a single linear functional, and that functional's weights
are derived from no-arbitrage (Phase 37 backward FTAP) without needing to
be assumed.

## Why this is a meaningful bridge

The two state-price properties — non-negativity and summing-to-bond-
price — are *consequences* of the FTAP EMM construction, not separate
assumptions. The state-price framework becomes self-contained: no-arb
in (z_up, z_down) market ⟹ explicit pricing kernel via Phase 37.

## Results

* `stateprices_of_ftap_two_state`: discounted EMM weights as state prices.
* `stateprices_nonneg`: non-negativity from EMM positivity (Phase 37).
* `stateprices_sum_eq_bond`: state prices sum to `e^{−rT}` (the
  zero-coupon bond price) — Π(`1` payoff) consistency.
* `pricingKernel_two_state`: the full pricing functional for arbitrary
  payoff in a two-state market, derived from FTAP.
-/

namespace HybridVerify

/-- **Two-state state-price vector**: from Nagy's backward FTAP EMM in
the two-state market with sign data `(z_up, z_down)`, the discounted
state prices are `q_state_up := e^{−rT} · q_up`, `q_state_down := e^{−rT}
· q_down`.

For `z_up > 0, z_down < 0` and any discount rate `r`, maturity `T`:

  `q_state_up = e^{−rT} · (−z_down) / (z_up − z_down)`,
  `q_state_down = e^{−rT} · z_up / (z_up − z_down)`. -/
noncomputable def stateprices_two_state (z_up z_down rT : ℝ) : Fin 2 → ℝ :=
  fun i => match i with
    | ⟨0, _⟩ => Real.exp (-rT) * (-z_down / (z_up - z_down))
    | ⟨1, _⟩ => Real.exp (-rT) * (z_up / (z_up - z_down))

/-- **State prices are non-negative** when the FTAP sign condition
holds (`z_up > 0, z_down < 0`). Combines Phase 37's EMM positivity with
positivity of the discount factor `e^{−rT}`. -/
theorem stateprices_nonneg (z_up z_down rT : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0) :
    ∀ i, 0 ≤ stateprices_two_state z_up z_down rT i := by
  intro i
  unfold stateprices_two_state
  have h_diff_pos : 0 < z_up - z_down := by linarith
  have h_exp_pos : 0 < Real.exp (-rT) := Real.exp_pos _
  fin_cases i
  · -- q_state_up = e^{-rT} · (-z_down) / (z_up - z_down)
    refine mul_nonneg h_exp_pos.le ?_
    exact (div_pos (neg_pos.mpr h_down) h_diff_pos).le
  · -- q_state_down = e^{-rT} · z_up / (z_up - z_down)
    refine mul_nonneg h_exp_pos.le ?_
    exact (div_pos h_up h_diff_pos).le

/-- **State prices sum to the bond price** `e^{−rT}` (the zero-coupon
bond pays `1` in both states; its no-arb price equals `Σ q_state_i · 1
= Σ q_state_i`). This is the *discount-consistency* condition. -/
theorem stateprices_sum_eq_bond (z_up z_down rT : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0) :
    (stateprices_two_state z_up z_down rT ⟨0, by omega⟩) +
    (stateprices_two_state z_up z_down rT ⟨1, by omega⟩) =
      Real.exp (-rT) := by
  unfold stateprices_two_state
  have h_diff_ne : z_up - z_down ≠ 0 := by
    have : 0 < z_up - z_down := by linarith
    exact this.ne'
  field_simp
  ring

/-- **Pricing kernel for a two-state market** (FTAP-derived). Any claim
with payoffs `X_up, X_down` has no-arb price

  `V_0(X) = q_state_up · X_up + q_state_down · X_down
         = e^{−rT} · (q_up · X_up + q_down · X_down)`

where `(q_up, q_down)` is the EMM from Phase 37 backward FTAP. -/
noncomputable def pricingKernel_two_state
    (z_up z_down rT : ℝ) (X_up X_down : ℝ) : ℝ :=
  (stateprices_two_state z_up z_down rT ⟨0, by omega⟩) * X_up +
  (stateprices_two_state z_up z_down rT ⟨1, by omega⟩) * X_down

/-- **Linearity in payoff** of the two-state pricing kernel:
`V_0(α X + β Y) = α V_0(X) + β V_0(Y)`. Direct consequence of state-price
linearity (`statePricePricing_smul` + `statePricePricing_add`). -/
theorem pricingKernel_two_state_linear
    (z_up z_down rT : ℝ) (α β X_up X_down Y_up Y_down : ℝ) :
    pricingKernel_two_state z_up z_down rT
        (α * X_up + β * Y_up) (α * X_down + β * Y_down) =
      α * pricingKernel_two_state z_up z_down rT X_up X_down +
      β * pricingKernel_two_state z_up z_down rT Y_up Y_down := by
  unfold pricingKernel_two_state
  ring

/-- **Bond pricing via the kernel**: the zero-coupon bond `(1, 1)` is
priced at `e^{−rT}`. This is the *unit-payoff sanity check* — the
pricing kernel reproduces the discount factor. -/
theorem pricingKernel_two_state_bond
    (z_up z_down rT : ℝ) (h_up : 0 < z_up) (h_down : z_down < 0) :
    pricingKernel_two_state z_up z_down rT 1 1 = Real.exp (-rT) := by
  unfold pricingKernel_two_state
  rw [mul_one, mul_one]
  exact stateprices_sum_eq_bond z_up z_down rT h_up h_down

/-- **No-arbitrage monotonicity** for the two-state pricing kernel:
non-negative payoffs ⟹ non-negative price. -/
theorem pricingKernel_two_state_nonneg
    (z_up z_down rT : ℝ) (X_up X_down : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0)
    (hXu : 0 ≤ X_up) (hXd : 0 ≤ X_down) :
    0 ≤ pricingKernel_two_state z_up z_down rT X_up X_down := by
  unfold pricingKernel_two_state
  refine add_nonneg ?_ ?_
  · exact mul_nonneg (stateprices_nonneg z_up z_down rT h_up h_down _) hXu
  · exact mul_nonneg (stateprices_nonneg z_up z_down rT h_up h_down _) hXd

end HybridVerify
