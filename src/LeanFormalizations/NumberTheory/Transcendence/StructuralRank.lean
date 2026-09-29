/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Rank of matrices of logarithms (Waldschmidt 2023 §5, phase 20)

Survey claims, each proved here from the stated input:

* `rk(M) ≤ r_str(M)`, "plain" (specialise `Xₖ ↦ eₖ`).
* Conjecture 1 ⇒ `rk(M) = r_str(M)` for matrices of logarithms (Roy 1995; survey p. 7).  Route:
  pick the basis `e` among `ℚ`-combinations of the entries, which are again logarithms of algebraic
  numbers.  Conjecture 1 makes `e` algebraically independent, so the specialisation
  `ℚ[X] → ℂ, Xₖ ↦ eₖ` is injective, and it preserves every minor's (non)vanishing.
* Six exponentials ⇒ (`r_str(M) ≥ 3` ⇒ `rk(M) ≥ 2`) for matrices of logarithms (survey p. 7,
  "From the six exponentials Theorem, one deduces").  Expected route: a rank-one log matrix is
  `xᵢyⱼ` with algebraic exponentials, and `r_str ≥ 3` supplies two `ℚ`-independent rows and three
  `ℚ`-independent columns.
* Sanity anchor: the 2×2 matrix `[[log 2, log 3], [2 log 2, 2 log 3]]` has structural rank 1.

If a frozen statement is false as written (e.g. the six-exponentials claim needs an extra
hypothesis), record the counterexample; that is an advance.  Frozen: the statements below, every
earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.StructuralRank
import LeanFormalizations.Literature.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.Waldschmidt2023

namespace LeanFormalizations.StructuralRank

open LeanFormalizations.Literature Matrix

theorem rank_le_structRank {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    {M : Matrix m n ℂ} {r : ℕ} (h : IsStructRank M r) : M.rank ≤ r := by
  sorry

theorem rank_eq_structRank_of_algIndepLogs (h1 : AlgIndepLogsConjecture) {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] {M : Matrix m n ℂ} {r : ℕ} (hM : IsLogMatrix M)
    (h : IsStructRank M r) : M.rank = r := by
  sorry

theorem two_le_rank_of_sixExponentials (h6 : SixExponentials) {m n : Type} [Fintype m]
    [Fintype n] [DecidableEq n] {M : Matrix m n ℂ} {r : ℕ} (hM : IsLogMatrix M)
    (h : IsStructRank M r) (hr : 3 ≤ r) : 2 ≤ M.rank := by
  sorry

theorem structRank_log_example :
    IsStructRank !![(Real.log 2 : ℂ), (Real.log 3 : ℂ); 2 * (Real.log 2 : ℂ), 2 * (Real.log 3 : ℂ)] 1 := by
  sorry

end LeanFormalizations.StructuralRank
