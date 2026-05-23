/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.FixedIncome.Credit

/-!
# CDS fair spread — re-export

CDS pricing under constant hazard with recovery (`c = h · (1 − R)`) is a
recovery-extension of the bare constant-hazard credit spread
(`creditSpread_eq_hazard`). The two lemmas have been folded into
`FixedIncome/Credit.lean` next to the base credit model.

The namespace `QuantFin` exposes `cdsFairSpread`, `cds_leg_equality`,
and `cdsFairSpread_zero_recovery` through the transitive import.
-/
