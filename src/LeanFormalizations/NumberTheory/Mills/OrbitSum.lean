/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ExteriorDold
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence

/-!
# Phase 51: the Frobenius orbit sum is scalar (Theorem A route, steps 3–5)

Let `A ∈ M_d(ℤ)` with `χ_A` irreducible mod the prime `c`, and `B = A^(c^n)`.  Then

  `Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n)) · I   (mod c^(n+1))`.

This is the order-`d` generalization of the sign flip (`d = 2`: `A^(c^(n+1)) ≡ tr(B)·I − B`).  In
particular every off-diagonal entry of the orbit sum vanishes mod `c^(n+1)`, which is what Theorem A
(`u(c^n) + h` composite i.o. for order-`d` recurrences at inert `c`) consumes next phase.

Checked numerically on 604 cases (`d ∈ {2,…,5}`, `c ∈ {2,3,5,7}`, `n ≤ 3`, plus Tribonacci at 3):
0 failures.  Controls: at precision `c^(n+2)` it fails in 581 of 604 cases; with a reducible `χ_A`
(mod 3) it fails in 46 of 47 cases.  So precision `n + 1` and the irreducibility hypothesis are sharp.

## Route (see `ROADMAP-PRIME-TOWERS.md` §4a, steps 3–5)
0. **Period** (`pow_prime_pow_add_card_congr`).  Mod `c`, `𝔽_c[A] ≅ 𝔽_c[X]/(χ̄_A)` is the field
   `𝔽_(c^d)`, so `A^(c^d) ≡ A (mod c)` (Frobenius, `FiniteField.pow_card`, via `AdjoinRoot` /
   `Polynomial.aeval`, or Cayley–Hamilton mod `c` plus `X^(c^d) ≡ X mod χ̄`).  Lift with phase 47's
   `TeichmullerCongruence.pow_congr_lift` (`X ≡ Y mod c^m`, commuting ⇒ `X^c ≡ Y^c mod c^(m+1)`),
   `n` times.
1. Work in `R = ZMod (c^(n+1))` and let `B̄` be the image of `A^(c^n)`.  `1, B̄, …, B̄^(d−1)` are
   `R`-linearly independent because they are independent mod `c` (the minimal polynomial of `Ā` is
   `χ̄_A`, since it is irreducible), so `R[B̄]` is free of rank `d`.
2. `σ : q(B̄) ↦ q(B̄^c)` is well defined: phase 50's `aeval_charpoly_prime_pow_congr` gives
   `χ_B(B^c) ≡ 0 (mod c^(n+1))`.  It is a ring endomorphism.
3. **Fixed ring = scalars.**  Induct on precision: if `σ(y) = y` and `y ≡ s (mod c)`, then
   `y − s = c·y′` with `σ(y′) ≡ y′ (mod c^n)`.  At precision 1, `σ` is Frobenius on `𝔽_(c^d)`,
   whose fixed field is `𝔽_c`.
4. `S = Σ_(k<d) B̄^(c^k)` is `σ`-fixed: `σ(S) = S − B̄ + B̄^(c^d)`, and `B̄^(c^d) = B̄` by step 0.  So
   `S = s·I`.  Taking traces with Dold (`tr B̄^(c^k) = tr B̄`, phase 49) gives `d·s = d·tr B̄`.  To
   get `s = tr B̄` even when `c ∣ d`, identify `S` with the trace of the free `R`-algebra `R[B̄]`
   (the trace of multiplication by `B̄` in the basis `B̄^i` is `tr B̄`, as it is the companion
   matrix of `χ_B`), or run step 3's induction on `S − tr(B̄)·I` directly.
   **Any other route is welcome**, e.g. an induction on `n` that uses only `ExteriorDold` and
   step 0.  Add as many public helpers as needed.

Frozen: the three statements below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.OrbitSum

open Matrix Polynomial

/-- **Period:** with `χ_A` irreducible mod `c`, `A^(c^(n+d)) ≡ A^(c^n) (mod c^(n+1))`. -/
theorem pow_prime_pow_add_card_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ)
    (i j : Fin d) :
    (c : ℤ) ^ (n + 1) ∣ (A ^ (c ^ (n + d))) i j - (A ^ (c ^ n)) i j := by
  sorry

/-- **Orbit sum is scalar:** `Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n))·I (mod c^(n+1))`. -/
theorem orbit_sum_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) (i j : Fin d) :
    (c : ℤ) ^ (n + 1) ∣
      (∑ k ∈ Finset.range d, A ^ (c ^ (n + k))) i j - (A ^ (c ^ n)).trace * (1 : Matrix (Fin d) (Fin d) ℤ) i j := by
  sorry

/-- **Off-diagonal entries of the orbit sum vanish** (the input to Theorem A). -/
theorem orbit_sum_entry_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) {i j : Fin d}
    (hij : i ≠ j) :
    (c : ℤ) ^ (n + 1) ∣ ∑ k ∈ Finset.range d, (A ^ (c ^ (n + k))) i j := by
  sorry

end LeanFormalizations.Mills.OrbitSum
