/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.BlackScholes.PriceBounds

/-!
# American = European for non-dividend call (Merton 1973) — re-export

The unified narrative — `bsV_ge_forward_lower_bound` and
`bsV_strict_gt_immediate_exercise` — has been absorbed into
`PriceBounds.lean`, where it sits alongside the other six static price-bound
theorems. All seven are corollaries of the same three foundational facts:
non-negativity of the call price, non-negativity of the put price, and
put-call parity (plus the `e^{−rT} < 1` arithmetic for the strict version).

This file is retained as an import path; importing it pulls in the same
namespace `QuantFin` containing the Merton 1973 strict dominance theorem.
-/
