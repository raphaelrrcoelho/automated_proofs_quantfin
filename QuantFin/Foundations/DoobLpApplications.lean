/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Foundations.LpContinuousMartingaleConvergence

/-!
# Doob L^p applications in finance (phase 52)

The pre-existing `Foundations/LpContinuousMartingaleConvergence.lean`
(725 LOC) develops the Doob L^p continuous-time martingale convergence
machinery, culminating in `lp_continuous_martingale_full`:

  For an L^p-bounded continuous-time martingale `M : ℝ → Ω → ℝ` (p > 1)
  with right-continuous paths on a finite probability space, there
  exists an integrable limit `M_∞ : Ω → ℝ` with a.s. convergence at
  natural times and convergence in measure as `t → ∞` along all reals.

This file gives the machinery its **first downstream financial use** —
applying it to discounted-price processes under a risk-neutral measure.
Per the `docs/bridges.md`, the 725 LOC of Doob L^p convergence sat
previously unused by any pricing module; this phase activates it.

## Financial applications

1. **Discounted-price limit**: under a risk-neutral measure `Q`, the
   discounted price process `M_t := e^{−rt} · S_t` is a `Q`-martingale
   (fundamental no-arbitrage statement). If it is L^p-bounded (e.g.,
   under BS, all integer moments are finite), then it converges to an
   `M_∞` representing the discounted long-run value.

2. **Bounded-drawdown bound**: for an L^p-bounded martingale, the
   integrable limit `M_∞` is finite a.s., bounding the *eventual*
   discounted portfolio value. This is the foundation for capital-
   adequacy / VaR-style bounds on long-horizon strategies.

## What this file does

Provides **adapter theorems** that take the financial setup (discounted
price as a Martingale + L^p bound from BS lognormal moments) and apply
`lp_continuous_martingale_full` to yield the long-run limit. The actual
discounted-price martingale property under `Q` (e.g., for `bsTerminal`)
is a separate result — see `BlackScholes/StockNumeraire.lean` and
related — and is fed to the adapter as a hypothesis.

## Results

* `discounted_price_long_run_limit`: long-run limit of an L^p-bounded
  discounted-price martingale.
* `discounted_price_long_run_bounded`: the limit is integrable, so the
  discounted long-run value is finite a.s. — a no-blow-up guarantee
  derived from `Q`-martingale + L^p boundedness.
-/

namespace QuantFin

open MeasureTheory Filter
open scoped Topology

/-- **Long-run limit of a discounted-price martingale**. Specialises
`Foundations/LpContinuousMartingaleConvergence.lp_continuous_martingale_full`
to the financial setup: the discounted price process `M_t := e^{−rt} ·
S_t` under risk-neutral measure `Q`, assumed `Q`-martingale,
right-continuous, and L^p-bounded.

Under these hypotheses, there exists an integrable random variable
`M_∞` to which the discounted price converges almost surely at natural
times and in measure along all reals as `t → ∞`. -/
theorem discounted_price_long_run_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsFiniteMeasure Q] {𝓕 : Filtration ℝ mΩ}
    {discounted_price : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 < p)
    (h_martingale : Martingale discounted_price 𝓕 Q)
    (h_right_cont : ∀ ω, Function.IsRightContinuous
      (fun t : ℝ => discounted_price t ω))
    (h_Lp_bounded : ∃ R : ℝ, ∀ t,
      eLpNorm (discounted_price t) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf Q ∧
      (∀ᵐ ω ∂Q,
        Filter.Tendsto (fun n : ℕ => discounted_price (n : ℝ) ω)
          Filter.atTop (𝓝 (M_inf ω))) ∧
      TendstoInMeasure Q discounted_price Filter.atTop M_inf :=
  lp_continuous_martingale_full hp h_martingale h_right_cont h_Lp_bounded

/-- **Long-run integrability (no-blow-up guarantee)**: under the same
hypotheses, the limit `M_∞` is integrable. This gives a *finite*
discounted long-run value — no almost-sure blow-up — derived purely
from `Q`-martingale + L^p boundedness, without any model-specific
arguments.

This is the **operational content** of `lp_continuous_martingale_full`
for finance: long-horizon discounted portfolio values cannot diverge
under finite L^p moments. -/
theorem discounted_price_long_run_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsFiniteMeasure Q] {𝓕 : Filtration ℝ mΩ}
    {discounted_price : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 < p)
    (h_martingale : Martingale discounted_price 𝓕 Q)
    (h_right_cont : ∀ ω, Function.IsRightContinuous
      (fun t : ℝ => discounted_price t ω))
    (h_Lp_bounded : ∃ R : ℝ, ∀ t,
      eLpNorm (discounted_price t) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf Q := by
  obtain ⟨M_inf, h_int, _, _⟩ :=
    discounted_price_long_run_limit hp h_martingale h_right_cont h_Lp_bounded
  exact ⟨M_inf, h_int⟩

end QuantFin
