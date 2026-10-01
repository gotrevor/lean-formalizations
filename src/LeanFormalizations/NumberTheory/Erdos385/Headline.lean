/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.Discharge
import LeanFormalizations.NumberTheory.Erdos385.ShortSumParseval

/-!
# Erdős #385: the almost-all theorem with its discharged inputs

`almost_all_F385` takes four literature Props.  Three are now proved
(`Discharge.lean`, `ShortSumParseval.lean`), so Theorem A rests on Vinogradov–Korobov alone:
for every `δ ∈ (0, 1/4)`, `#{n ≤ X : F(n) < n + (1 − δ)√n} = o(X)`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **Theorem A, modulo Vinogradov–Korobov only.** -/
theorem almost_all_F385_of_VK (h : VKZeroFreeLogDeriv) : AlmostAllF385 :=
  almost_all_F385 _root_.Erdos385.mr16Lemma14_holds _root_.Erdos385.montgomeryVaughanMVT_holds h
    _root_.Erdos385.mediumPNTStatement_holds

end LeanFormalizations.Erdos385
