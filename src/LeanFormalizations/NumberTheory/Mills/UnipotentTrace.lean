/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence

/-!
# Phase 48: traces in the unipotent class mod 3 (sub-node R4 of `ShiftedTraceRigidity`)

`PROOF-THEOREM-E.md` Step 5: in the class `χ ≡ (X − z)³ (mod 3)` every trace of a nonzero power is
divisible by 3.  That is what kills `tr(ξ^s) = ±1`.  Matrix form, so negative shifts are covered through
the adjugate.

## Route
1. `three_dvd_trace_pow`: if `(M − w·1)^3 ≡ 0 (mod 3)` entrywise, then `N := M − w·1` is nilpotent over
   `ZMod 3`, so `tr (N^i) = 0` there for `i ≥ 1` (a nilpotent matrix over a field has nilpotent powers, and
   the trace of a nilpotent matrix is 0; look for `Matrix.isNilpotent_trace_of_isNilpotent` /
   `IsNilpotent.trace` or prove it via `charpoly`).  Expand `(w + N)^s` binomially (`w·1` commutes):
   `tr M^s ≡ 3 w^s ≡ 0 (mod 3)` (`d = 3`: `tr 1 = 3`).
2. `adjugate_unipotent`: if `(M − w·1)^3 ≡ 0 (mod 3)` and `3 ∤ w`, then
   `(adjugate M − w²·1)^3 ≡ 0 (mod 3)`.  Over `ZMod 3`: `M = w(1 + N′)` with `N′` nilpotent,
   `adjugate M = det M · M⁻¹`, `det M = w³ = w` in `ZMod 3` (unipotent determinant 1), and
   `M⁻¹ = w⁻¹ (1 − N′ + N′²)`.  So `adjugate M = w² (1 + nilpotent)`, and `w² = 1`.
3. `three_dvd_trace_adjugate_pow`: combine 1 and 2.

Frozen: the statements below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.UnipotentTrace

open Matrix

theorem three_dvd_trace_pow (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) (s : ℕ) (hs : 1 ≤ s) :
    (3 : ℤ) ∣ (M ^ s).trace := by
  sorry

theorem adjugate_unipotent (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ) (hw : ¬ (3 : ℤ) ∣ w)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) :
    ∀ i j, (3 : ℤ) ∣ ((M.adjugate - (w ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j := by
  sorry

theorem three_dvd_trace_adjugate_pow (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ) (hw : ¬ (3 : ℤ) ∣ w)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) (s : ℕ) (hs : 1 ≤ s) :
    (3 : ℤ) ∣ (M.adjugate ^ s).trace := by
  sorry

end LeanFormalizations.Mills.UnipotentTrace
