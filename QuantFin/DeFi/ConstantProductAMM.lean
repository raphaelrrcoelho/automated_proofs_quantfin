/-
This file adapts the mathematical content of the **constant-product AMM**
(Uniswap v2-style) from:

  Daniele Pusceddu and Massimo Bartoletti, "Formalizing Automated Market
  Makers in the Lean 4 Theorem Prover", OASIcs FMBC 2024 (5th
  International Workshop on Formal Methods for Blockchains).
  <https://doi.org/10.4230/OASIcs.FMBC.2024.5>
  Companion code: <https://github.com/dpusceddu/lean4-amm>

and the underlying theory paper they cite:

  Massimo Bartoletti, James Chiang, and Alberto Lluch-Lafuente, "A theory
  of Automated Market Makers in DeFi", LMCS 2022.

Our implementation differs from Pusceddu-Bartoletti's in that we use
**plain real reserves** (`ℝ` with positivity hypotheses) rather than
Lean's `PReal` (strictly-positive-reals subtype) machinery, and we model
**a single AMM pair** rather than their full multi-AMM blockchain state
abstraction. The mathematical content (constant-product invariant + swap
output formula + invariant preservation + arbitrage gain) is adapted
from their work.

Author of this QuantFin Lean 4 adaptation: Raphael Coelho.
Original mathematical framework: Bartoletti-Chiang-Lluch-Lafuente (2022),
Pusceddu-Bartoletti Lean formalisation (2024).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content © Bartoletti et al. / Pusceddu-Bartoletti, used here
under academic fair use for derivative work with attribution. The
original Pusceddu-Bartoletti GitHub repository has no explicit license at
the time of writing; this adaptation does not copy any Lean source from
that repo and uses only the published paper content.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Constant-product AMM (phase 38, after Pusceddu-Bartoletti 2024)

A constant-product Automated Market Maker (CPMM, Uniswap v2-style) holds
reserves `(x, y)` of two tokens. The **constant-product invariant**
`x · y = k` is preserved across swap transactions: a trader who deposits
`Δx` of token X receives

  `Δy = y · Δx / (x + Δx)`

of token Y, after which the new reserves `(x + Δx, y − Δy)` again satisfy
`(x + Δx)·(y − Δy) = x · y`. This algorithmically-determined exchange
rate is what makes CPMMs "automated" — no order book, no oracle.

This file formalises:

* `swapOutput`: the closed-form `Δy` as a function of input `Δx` and
  reserves.
* `swap_preserves_invariant`: `(x + Δx)·(y − Δy) = x · y` (the **key
  no-arbitrage / no-money-printing property** of the constant product).
* `marginal_exchange_rate`: the marginal rate `Δy / Δx = y / (x + Δx)`,
  approaching the **internal price** `y / x` as `Δx → 0`.
* `internalPrice` / `arbitragePresent`: the internal price `y / x` and the
  predicate for it diverging from an external oracle (the **arbitrage
  setup** these models study).

## Why this is quant finance

Pre-existing `Foundations/AlmgrenChriss.lean` covers traditional execution
cost / market impact. CPMM swap output `Δy = y·Δx/(x+Δx)` is the *DeFi
analogue* of Almgren-Chriss market impact: both quantify how prices move
against you as you trade larger size. The arbitrage analysis below is
the same Kyle / Glosten-Milgrom framework applied to algorithmic
liquidity provision.

## Results

* `swapOutput`: definition `y · Δx / (x + Δx)`.
* `swap_preserves_invariant`: constant-product invariance under swap.
* `swap_output_pos`: `Δy > 0` when input is positive.
* `swap_output_lt_y`: `Δy < y` (cannot drain pool).
* `marginal_exchange_rate`: the marginal rate `Δy / Δx = y / (x + Δx)`.
* `internalPrice`, `arbitragePresent`: internal price `y / x` and the
  oracle-divergence predicate (definitions).
-/

namespace QuantFin

namespace DeFi

/-- **Constant-product AMM swap output**: given input `Δx` of token X
and reserves `(x, y)` with `x, y > 0`, the output `Δy` of token Y
under the constant-product invariant `x · y = k` is

  `Δy := y · Δx / (x + Δx)`.

This is the algebraic core of the Uniswap v2 model (Adams-Zinsmeister
2020), as formalised by Pusceddu-Bartoletti (2024). -/
noncomputable def swapOutput (x y Δx : ℝ) : ℝ :=
  y * Δx / (x + Δx)

/-- **Constant-product invariant preservation**: after a swap of input
`Δx` (with `x, Δx > 0`), the new reserves `(x + Δx, y − Δy)` satisfy

  `(x + Δx) · (y − Δy) = x · y`,

where `Δy := swapOutput x y Δx`. This is the defining property of the
CPMM — no arbitrage / no money-printing under the algorithmic
exchange rate. -/
theorem swap_preserves_invariant
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) :
    (x + Δx) * (y - swapOutput x y Δx) = x * y := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  field_simp
  ring

/-- **Swap output is strictly positive** when input is positive (and
reserves are positive). -/
theorem swap_output_pos
    (x y Δx : ℝ) (hx : 0 < x) (hy : 0 < y) (hΔx : 0 < Δx) :
    0 < swapOutput x y Δx := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  exact div_pos (mul_pos hy hΔx) h_sum_pos

/-- **Swap output bounded by reserve**: `Δy < y` — the AMM cannot be
drained by any single (finite) trade. -/
theorem swap_output_lt_y
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) (hy : 0 ≤ y) :
    swapOutput x y Δx < y ∨ y = 0 := by
  rcases eq_or_lt_of_le hy with hy_eq | hy_pos
  · right; exact hy_eq.symm
  · left
    unfold swapOutput
    have h_sum_pos : 0 < x + Δx := by linarith
    rw [div_lt_iff₀ h_sum_pos]
    -- y · Δx < y · (x + Δx)  ⟺  Δx < x + Δx  (since y > 0)
    have h_factor : y * (x + Δx) = y * x + y * Δx := by ring
    rw [h_factor]
    nlinarith

/-- **Marginal price identity**: at infinitesimal input, the exchange
rate `Δy / Δx` equals `y / (x + Δx)`, which tends to `y / x` as
`Δx → 0⁺` (the "spot" internal price of the AMM, matching the ratio of
reserves). -/
lemma marginal_exchange_rate
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) :
    swapOutput x y Δx / Δx = y / (x + Δx) := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  have hΔx_ne : Δx ≠ 0 := hΔx.ne'
  field_simp

/-- **Internal price = reserve ratio** at zero input: the spot price of
token X (denominated in Y) implied by the AMM's curve at the current
reserve point is `y / x`. -/
noncomputable def internalPrice (x y : ℝ) : ℝ := y / x

/-- **Arbitrage trigger condition**: if the AMM's internal price `y/x`
differs from an external oracle's price `p_oracle`, an arbitrageur can
profit by trading in the direction that moves the AMM price toward the
oracle. The optimal arbitrage swap amount and its profitability are
the subject of `Pusceddu-Bartoletti 2024 §3` (and Bartoletti-Chiang-
Lluch-Lafuente 2022, Theorem 4). At our scope: we just state the
**price-divergence detection**. -/
def arbitragePresent (x y p_oracle : ℝ) : Prop :=
  internalPrice x y ≠ p_oracle

end DeFi

end QuantFin
