/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.BlackScholes.BreedenLitzenberger

/-!
# Lognormal-to-gaussian change of variables — re-export

The differential change-of-variables identity `f(K) · K · σ · √T = ϕ(d_2(K))`
has been folded into `BlackScholes/BreedenLitzenberger.lean`, where it sits
next to the implied-PDF definition and positivity.

The namespace `QuantFin` exposes `lognormalTerminalPDF_change_of_variables`
through the transitive import.
-/
