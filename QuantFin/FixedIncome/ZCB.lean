/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Fixed-income basics under a deterministic short rate

Closed-form identities for a zero-coupon bond with continuous compounding under
a constant short rate `r`:

  `B(t, T) = exp(-(r · (T - t)))`.

Results:

* `zcb_at_maturity`: `B(T, T) = 1`.
* `zcb_yield_eq_rate`: under a constant `r`, the yield-to-maturity equals `r`.
* `hasDerivAt_zcb_r`: `∂_r B(t, T) = -(T - t) · B(t, T)` — the bond duration is
  the time-to-maturity.
* `zcb_duration_eq_time_to_maturity`: `-∂_r B / B = T - t`.
* `hasDerivAt_zcb_r_r`: second-derivative identity giving convexity
  `∂²_r B / B = (T - t)²`.

The model is purely deterministic; the Vasicek / CIR / HJM stochastic versions
would need Itô calculus.
-/

namespace QuantFin

open Real

/-- Continuous-compounding zero-coupon bond price under a constant short rate. -/
noncomputable def zcb (r : ℝ) (t T : ℝ) : ℝ := Real.exp (-(r * (T - t)))

/-- The bond pays `1` at maturity. -/
lemma zcb_at_maturity (r T : ℝ) : zcb r T T = 1 := by
  unfold zcb
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- The bond is positive. -/
lemma zcb_pos (r t T : ℝ) : 0 < zcb r t T := Real.exp_pos _

/-- Yield-to-maturity for a ZCB under a constant rate equals the rate. -/
lemma zcb_yield_eq_rate {r t T : ℝ} (htT : t < T) :
    -Real.log (zcb r t T) / (T - t) = r := by
  unfold zcb
  rw [Real.log_exp, neg_neg]
  have h_ne : T - t ≠ 0 := sub_ne_zero.mpr htT.ne'
  field_simp

/-- `∂_r B(t, T) = -(T - t) · B(t, T)`. Duration of a ZCB equals time-to-maturity. -/
lemma hasDerivAt_zcb_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' => zcb r' t T) (-(T - t) * zcb r t T) r := by
  unfold zcb
  have h_lin : HasDerivAt (fun r' : ℝ => -(r' * (T - t))) (-(T - t)) r := by
    have h := (hasDerivAt_id r).mul_const (T - t)
    simpa using h.neg
  have h := h_lin.exp
  convert h using 1
  ring

/-- ZCB Macaulay duration equals time-to-maturity: `-∂_r B / B = T - t`. -/
lemma zcb_duration_eq_time_to_maturity (t T r : ℝ) :
    -(-(T - t) * zcb r t T) / zcb r t T = T - t := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  field_simp

/-- `∂²_r B(t, T) = (T - t)² · B(t, T)`. Convexity = (time-to-maturity)². -/
lemma hasDerivAt_zcb_r_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' => -(T - t) * zcb r' t T) ((T - t)^2 * zcb r t T) r := by
  have h := (hasDerivAt_zcb_r t T r).const_mul (-(T - t))
  convert h using 1
  ring

/-- ZCB convexity = squared time-to-maturity: `∂²_r B / B = (T - t)²`. -/
lemma zcb_convexity_eq_time_to_maturity_sq (t T r : ℝ) :
    ((T - t)^2 * zcb r t T) / zcb r t T = (T - t)^2 := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  field_simp

end QuantFin
