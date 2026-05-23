/-
This file is a **Lean 4 derivative work** based on Definition 4.1, Theorem
4.2, and Theorem 4.3 of:

  Tamás Nagy, "From Itô to Black–Scholes: A Machine-Verified Derivation in
  Lean 4", SSRN Working Paper 6336503, March 2026.
  <https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503>

The simple-process Itô integral definition and its linearity / constant-
isometry properties are adapted from Nagy's Section 4. The L² extension
via Cauchy completeness (Nagy Section 4.3) is deferred — see
`Foundations/WienerIntegralL2.lean` for our existing parallel work via a
different construction path.

Author of this QuantFin Lean 4 adaptation: Raphael Coelho.
Original Lean derivation: Tamás Nagy (SSRN 6336503, 2026).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content and original Lean code © Tamás Nagy 2026, used here
under academic fair use for derivative work with attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Itô integral for simple processes (phase 36, after Nagy 2026)

For a **simple integrand** `c : Fin N → ℝ` (values constant on each
sub-interval of the partition) and Brownian increments `ΔB : Fin N → ℝ`,
the Itô integral is *defined* as the finite sum

  `∫_0^T f(t) dB(t) := Σ_{k=0}^{N−1} c_k · ΔB_k`.

This is a *definition*, not an axiom — the integral exists by
construction. Key algebraic properties:

* **Linearity**: `Σ (a·c_k + b·d_k) · ΔB_k = a · Σ c_k·ΔB_k + b · Σ d_k·ΔB_k`.
* **Isometry (constant integrand)**: `Σ c² · Δt_k = c² · Σ Δt_k = c² · T`.
  The full Itô isometry `E[(∫f dB)²] = E[∫f² dt]` for *adapted random*
  integrands is proved in `Foundations/ItoIsometryAdapted.lean`
  (`ito_isometry_discrete`), grounded on `IsPreBrownian.hasIndepIncrements`
  and the weak Markov property `IsPreBrownian.indepFun_shift` — not on any
  unavailable upstream machinery.

The `L²` extension via Cauchy completeness (Mathlib's `MemLp` API) reuses
our `Foundations/WienerIntegralL2.lean` infrastructure.

## Why this matters

The discrete Itô formula (`Foundations/DiscreteIto.lean`, phase 35) needs
the discrete stochastic integral as its building block. Together they
form the *bottom-up* construction of Itô calculus that Nagy's paper
champions: every step is a finite sum until the final continuous limit.

## Results

* `itoIntegralSimple`: definition (finite sum).
* `itoIntegralSimple_linear`: linearity in the integrand.
* `itoIntegralSimple_isometry_constant_integrand`: the algebraic isometry
  identity for constant integrand (no probability assumed).
-/

namespace QuantFin

/-- **Itô integral for simple processes** (Nagy 2026, Definition 4.1): the
finite sum `Σ_{k=0}^{N−1} c_k · ΔB_k`. *Definition*, not an axiom — the
integral is constructed, not assumed. -/
noncomputable def itoIntegralSimple
    (N : ℕ) (c ΔB : Fin N → ℝ) : ℝ :=
  ∑ k, c k * ΔB k

/-- **Linearity of the simple Itô integral** (Nagy 2026, Theorem 4.2). -/
theorem itoIntegralSimple_linear
    (N : ℕ) (a b : ℝ) (c d ΔB : Fin N → ℝ) :
    itoIntegralSimple N (fun k => a * c k + b * d k) ΔB =
      a * itoIntegralSimple N c ΔB + b * itoIntegralSimple N d ΔB := by
  unfold itoIntegralSimple
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **Isometry-like identity for constant integrand** (Nagy 2026, Theorem
4.3, algebraic core): for constant `c` and time increments `Δt : Fin N →
ℝ` summing to `T`, the squared-integrand sum `Σ c² · Δt_k` equals `c² · T`.

This is the *deterministic* algebraic ingredient of the Itô isometry
`E[(∫ f dB)²] = E[∫ f² dt]`. The full probabilistic isometry requires the
independent-increment hypothesis (see `BrownianQuadraticVariation`). -/
theorem itoIntegralSimple_isometry_constant_integrand
    (N : ℕ) (c : ℝ) (Δt : Fin N → ℝ) :
    ∑ k, c ^ 2 * Δt k = c ^ 2 * ∑ k, Δt k := by
  rw [← Finset.mul_sum]

/-- **Scaling**: `Σ (α·c_k) · ΔB_k = α · Σ c_k·ΔB_k`. -/
theorem itoIntegralSimple_scale
    (N : ℕ) (α : ℝ) (c ΔB : Fin N → ℝ) :
    itoIntegralSimple N (fun k => α * c k) ΔB =
      α * itoIntegralSimple N c ΔB := by
  unfold itoIntegralSimple
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

end QuantFin
