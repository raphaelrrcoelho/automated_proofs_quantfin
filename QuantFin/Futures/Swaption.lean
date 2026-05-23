/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Futures.Black76

/-!
# Black model for swaptions — re-export

The Black-model swaption pricing (payer + receiver + parity) has been folded
into `Futures/Black76.lean`, where it sits next to the base Black-76 futures
formula — both are specialisations of the same `F · Φ(d_1) − K · Φ(d_2)`
structure, with the swap-rate version scaled by the annuity numéraire `A`.

The namespace `QuantFin` exposes `blackPayerSwaption`,
`blackReceiverSwaption`, and `swaption_payer_receiver_parity` through the
transitive import.
-/
