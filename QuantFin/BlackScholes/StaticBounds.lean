/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.BlackScholes.PriceBounds

/-!
# Static Black-Scholes option-price bounds — re-export

The unified narrative — `Phi_le_one`, `bsV_le_S`, `bsP_le_K_disc`,
`box_spread_identity`, and the broader no-arbitrage rectangle — has been
absorbed into `PriceBounds.lean`, where it sits alongside the parity-driven
forward lower bound and the Merton 1973 strict-dominance result.

This file is retained as an import path; importing it pulls in the same
namespace `QuantFin` containing all the bound theorems.
-/
