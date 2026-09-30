/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciCovering
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 41: the Theorem C engine — covering and prime-free intervals along `c^n`, any matrix

Phase 40 proved (D1) and prime-free intervals for `F(2^n)`.  Its mechanism is general.  If every
value `ℓ(A^(c^n)) + h` (for `|h| ≤ H`, `n` large) has a prime factor `p` with a small `c`-part of
`|GL_d(𝔽_p)|`, then one `m` and one period `L` work for all `h` at once.  See
`ROADMAP-PRIME-TOWERS.md` §1 Theorem C.

## Route
1. `covering_of_good`: refactor phase 40's steps 3–4 (`exists_entry_pow_congr_mul`, one `m` via
   `Filter.eventually_all_finset`, `L = ∏` periods) to a general `A : Matrix (Fin d) (Fin d) ℤ`
   and a `ℤ`-linear functional `ℓ` (entries and the trace are both `ℓ`).  Linearity makes the entrywise
   congruence `A^(c^(m+kj)) ≡ A^(c^m) (mod p)` pass to `ℓ`.
2. `prime_free_of_good`: phase 40's step 5 (compare `k = K` and `K + 1`), assuming only
   `|ℓ(A^(c^n))| → ∞`.
3. Lucas instance: `lucasV_good` gives the hypothesis of step 1 for `A = lucasM P`, `ℓ = trace`,
   odd prime `c ∤ P`.
   - **Window at a single `n` is impossible for large `n`.**  If every prime factor `q` of
     `V(c^n) + h` has `v_c(glCard 2 q) > n`, then each `q ≡ ±1 (mod c^(n/2))`
     (`FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat`), hence so is the product, and
     `V(c^n) ≡ x (mod c^(n/2))` with `x ∈ {±1 − h}`.
   - Descend with the Gauss-type congruence `V(c^(k+1)) ≡ V(c^k) (mod c^(k+1))` (prove it from
     `lucasV_mul_odd`: `V_c(y) − V_c(x) ≡ 0 (mod c^(k+1))` when `y ≡ x (mod c^k)`, because
     `V_c(x, −1) = x^c + c·g(x)`).  This gives `V(c^r) ≡ x (mod c^r)` for `r ≈ n/2`, then
     `lucasV x (−1) c ≡ x (mod c^(r−1))`.
   - `lucasV_neg_one_growth` makes `lucasV x (−1) c − x` a nonzero integer bounded in terms of
     `|h|`, unless `x = 0`, which contradicts `lucasV_prime_pow_mod` (`V ≡ P ≢ 0`).  So `r`, hence
     `n`, is bounded.
   - Also handle prime factors dividing `det = −1` (none) and the prime `c` itself
     (`v_c(glCard 2 c) = 0`, so `c` is always good).
4. Fibonacci instance at odd `c ≠ 5`: same, with phase 37's `fibOddPoly` at `2j + 1 = c²`
   (`F(c^(k+2)) = Φ_j(F(c^k))`; `Φ_j` is odd, so both `Φ_j(x) ∓ x ≠ 0` for `x ≠ 0` by
   `fibOddPoly_far`) and `not_dvd_fib_prime_pow`.  The descent uses
   `F(c^(k+1)) ≡ ±F(c^k) (mod c^(k+1))`; prove whichever sign-agnostic form is convenient, e.g.
   `F(c^(k+2)) ≡ F(c^k) (mod c^(k+1))` from `fib_odd_mul`.
5. `fib_prime_pow_prime_free`: every prime `c ≠ 5` (`c = 2` is phase 40).

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.CoveringEngine

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasPrimePow Filter

/-- **The engine: (D1) along `c^n`** for any integer matrix and linear functional. -/
theorem covering_of_good {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (ℓ : Matrix (Fin d) (Fin d) ℤ →ₗ[ℤ] ℤ) {c : ℕ} (hc : c.Prime) (H : ℕ)
    (hgood : ∀ h : ℤ, |h| ≤ H → ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A.det ∧
      (p : ℤ) ∣ ℓ (A ^ (c ^ n)) + h ∧ padicValNat c (glCard d p) ≤ n) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ ℓ (A ^ (c ^ (L * k + m))) + h := by
  sorry

/-- **The engine: prime-free intervals** of half-width `H` around `ℓ(A^(c^n))`, infinitely often. -/
theorem prime_free_of_good {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (ℓ : Matrix (Fin d) (Fin d) ℤ →ₗ[ℤ] ℤ) {c : ℕ} (hc : c.Prime) (H : ℕ)
    (hgrow : Tendsto (fun n : ℕ => |ℓ (A ^ (c ^ n))|) atTop atTop)
    (hgood : ∀ h : ℤ, |h| ≤ H → ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A.det ∧
      (p : ℤ) ∣ ℓ (A ^ (c ^ n)) + h ∧ padicValNat c (glCard d p) ≤ n) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (ℓ (A ^ (c ^ n)) + h) := by
  sorry

/-- **Prime-free intervals around `V_(c^n)(P, −1)`** (e.g. Lucas numbers `P = 1`), odd prime `c ∤ P`. -/
theorem lucasV_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP : ¬ (c : ℤ) ∣ P) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  sorry

/-- **Prime-free intervals around `F(c^n)`**, every prime `c ≠ 5`. -/
theorem fib_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (h5 : c ≠ 5) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.CoveringEngine
