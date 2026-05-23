/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Spectral risk measures: monotonicity and convex combinations

A **spectral risk measure** assigns to a loss its risk via a weighted
average of quantiles, with non-negative non-decreasing weight function
`φ : [0,1] → ℝ₊` integrating to one:

  `ρ_φ(L) := ∫₀¹ φ(u) · VaR_u(L) du`.

Special cases:
- `φ ≡ 1` (uniform): `ρ_φ = E[L]`.
- `φ(u) = 𝟙_{u ≥ α} / (1−α)`: `ρ_φ = CVaR_α(L)`.

Key abstract properties:
- **Linearity** in the loss: `ρ_φ(L + c) = ρ_φ(L) + c` (using `∫φ = 1`).
- **Convex combinations**: any convex combination of spectral measures with
  individually normalized spectra is again spectral (the combined weight
  function is the convex combination of the individual ones).

Since Mathlib's quantile calculus has limited support at the current pin,
we formalize spectral risk *axiomatically* via the integral operator on
finite weighted sums of quantile evaluations. This is sufficient for the
finite-state discrete-distribution case (which is itself the standard
banking-regulation formulation).

Results:

* `spectralRiskFinite`: weighted sum `Σ φ_i · Q_i` over a finite quantile grid.
* `spectralRisk_translation`: `ρ(L + c) = ρ(L) + c` when weights sum to `1`.
* `spectralRisk_convex_combination`: a convex combination of two normalized
  weight vectors is itself a normalized weight vector.
-/

namespace QuantFin

open Finset

variable {ι : Type*}

/-- Finite-grid spectral risk: weighted sum `Σ φ_i · Q_i`. -/
noncomputable def spectralRiskFinite (s : Finset ι) (φ : ι → ℝ) (Q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, φ i * Q i

/-- **Translation invariance**: if `Σ φ = 1`, then `ρ(Q + c·𝟙) = ρ(Q) + c`. -/
theorem spectralRisk_translation (s : Finset ι) (φ : ι → ℝ) (Q : ι → ℝ)
    (c : ℝ) (h_norm : ∑ i ∈ s, φ i = 1) :
    spectralRiskFinite s φ (fun i => Q i + c) =
      spectralRiskFinite s φ Q + c := by
  unfold spectralRiskFinite
  rw [show (fun i => φ i * (Q i + c)) = (fun i => φ i * Q i + φ i * c) from by
        funext i; ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, h_norm, one_mul]

/-- **Convex combination of normalized spectra remains normalized**:
`t Σ φ + (1−t) Σ ψ = t · 1 + (1−t) · 1 = 1`. The convex-combination weight
`t·φ + (1−t)·ψ` is therefore a valid spectral weight. -/
theorem spectralRisk_convex_combination_normalized
    (s : Finset ι) (φ ψ : ι → ℝ) (t : ℝ)
    (hφ : ∑ i ∈ s, φ i = 1) (hψ : ∑ i ∈ s, ψ i = 1) :
    ∑ i ∈ s, (t * φ i + (1 - t) * ψ i) = 1 := by
  rw [Finset.sum_add_distrib]
  rw [show (∑ i ∈ s, t * φ i) = t * ∑ i ∈ s, φ i from (Finset.mul_sum s _ _).symm]
  rw [show (∑ i ∈ s, (1 - t) * ψ i) = (1 - t) * ∑ i ∈ s, ψ i from
        (Finset.mul_sum s _ _).symm]
  rw [hφ, hψ]
  ring

/-- **Convex combination of spectral risks**: a convex combination of
spectral risk measures (with normalized weight functions) acts on the loss
by the convex combination of the underlying weight functions. -/
theorem spectralRisk_convex_combination
    (s : Finset ι) (φ ψ : ι → ℝ) (Q : ι → ℝ) (t : ℝ) :
    t * spectralRiskFinite s φ Q + (1 - t) * spectralRiskFinite s ψ Q =
      spectralRiskFinite s (fun i => t * φ i + (1 - t) * ψ i) Q := by
  unfold spectralRiskFinite
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end QuantFin
