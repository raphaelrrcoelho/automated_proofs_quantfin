/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Bermudan sandwich: European ≤ Bermudan ≤ American

A Bermudan option's exercise set sits between the European (only at maturity)
and American (any time) exercise sets. As a stopping problem its value is the
maximum over admissible exercise times of the discounted exercise value, and
the maximum is monotone in the exercise set.

The clean abstract statement: for a value function `v : ι → ℝ` and exercise
sets `Eur ⊆ Berm ⊆ Amer`, `sup_Eur v ≤ sup_Berm v ≤ sup_Amer v`. We give the
discrete-time finite version using `Finset.sup'`, which is what the binomial
tree directly produces.

Results:

* `bermudan_le_american`: `Berm ⊆ Amer ⇒ sup_Berm ≤ sup_Amer`.
* `european_le_bermudan`: `Eur ⊆ Berm ⇒ sup_Eur ≤ sup_Berm`.
* `bermudan_sandwich`: the two-sided combination.
-/

namespace QuantFin

open Finset

variable {ι : Type*} {v : ι → ℝ}

/-- **Bermudan ≤ American**: extending the exercise set never lowers the
optimal-stopping value. -/
lemma bermudan_le_american
    {Berm Amer : Finset ι} (hBA : Berm ⊆ Amer) (hBermNE : Berm.Nonempty)
    (v : ι → ℝ) :
    Berm.sup' hBermNE v ≤ Amer.sup' (hBermNE.mono hBA) v :=
  sup'_mono v hBA hBermNE

/-- **European ≤ Bermudan**: the European exercise set (which in practice is
the singleton maturity date) is contained in the Bermudan set. -/
lemma european_le_bermudan
    {Eur Berm : Finset ι} (hEB : Eur ⊆ Berm) (hEurNE : Eur.Nonempty)
    (v : ι → ℝ) :
    Eur.sup' hEurNE v ≤ Berm.sup' (hEurNE.mono hEB) v :=
  sup'_mono v hEB hEurNE

/-- **Bermudan sandwich**: `Eur ⊆ Berm ⊆ Amer` ⇒ values are sandwiched
in the same order. -/
lemma bermudan_sandwich
    {Eur Berm Amer : Finset ι}
    (hEB : Eur ⊆ Berm) (hBA : Berm ⊆ Amer) (hEurNE : Eur.Nonempty)
    (v : ι → ℝ) :
    Eur.sup' hEurNE v ≤ Berm.sup' (hEurNE.mono hEB) v ∧
      Berm.sup' (hEurNE.mono hEB) v ≤ Amer.sup' (hEurNE.mono (hEB.trans hBA)) v :=
  ⟨european_le_bermudan hEB hEurNE v,
   bermudan_le_american hBA (hEurNE.mono hEB) v⟩

end QuantFin
