/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremA

/-!
# Phase 53: prime-free intervals around Tribonacci `T(3^n)` (Theorem C for an order-3 recurrence)

For `n ≡ 95 (mod 1980)`, all seven numbers `T(3^n) + h` with `|h| ≤ 3` are composite.  Each is
divisible by a fixed small prime:

| `h` | prime | `ord_p(A)` | `T(3^95) mod p` |
|---|---|---|---|
| −3 | 53 | 52 = 2²·13 | 3 |
| −2 | 5 | 31 | 2 |
| −1 | 7 | 48 = 2⁴·3 | 1 |
| 0 | 13 | 168 = 2³·3·7 | 0 |
| 1 | 593 | 3256 = 2³·11·37 | 592 |
| 2 | 47 | 46 = 2·23 | 45 |
| 3 | 5 | 31 | 2 |

`A = TheoremA.tribMat` (`T N = (A^N) 2 0` is `TheoremA.tribMat_pow_apply`).  Found by
`scripts/tribonacci-covering-search.py 3 14 800` and checked for `k < 6` by `scripts/tribonacci-covering-verify.py`.
Control: at `n = 96` six of the seven divisibilities fail.

## Route
1. For each `p`: `A^o = 1` over `ZMod p` with `o = ord_p(A)` from the table (`decide +kernel`
   on `Matrix (Fin 3) (Fin 3) (ZMod p)`; `o = 3256` is split with `pow_mul` because `npowRec`
   at that exponent is slow — see `tribMatMod_593_pow_order`).
2. `o ∣ 3^95 · (3^1980 − 1)` (`norm_num`/`decide` on `ℕ`), so `3^(1980k + 95) ≡ 3^95 (mod o)`, hence
   `A^(3^(1980k+95)) = A^(3^95)` over `ZMod p`.  (`3^95 ≥ v₃(o)` trivially; `3^1980 ≡ 1` modulo the
   3-free part of `o`.)  Use `pow_eq_pow_mod`-style reduction: `A^N = A^(N % o)` when `A^o = 1`.
3. `(A^(3^95)) 2 0` over `ZMod p` from the table (`decide +kernel` with the reduced exponent
   `3^95 % o`).  Transfer to `ℤ` via `Matrix.map` / `Int.cast` and phase 52's `trib = entry` lemma.
4. Composite: `trib (3^(1980k+95)) + h` is divisible by `p` and exceeds `p` in absolute value
   (`T(3^95)` is astronomically larger than 593; monotonicity of `trib`), so it is not prime.

No `native_decide` in the end: every computation is kernel-checked, so the three theorems below
depend only on `propext`, `Classical.choice`, `Quot.sound`.

Frozen: `tribCoverPrime` and the three statements below; all earlier statements; `Literature/`.
No `private`.
-/

set_option maxRecDepth 1000000

namespace LeanFormalizations.Mills.TribonacciCovering

open LeanFormalizations.Mills.TheoremA Filter

/-- The covering prime for the shift `h`, `|h| ≤ 3`. -/
def tribCoverPrime (h : ℤ) : ℤ :=
  if h = -3 then 53 else if h = -2 then 5 else if h = -1 then 7 else if h = 0 then 13
  else if h = 1 then 593 else if h = 2 then 47 else 5

/-! ### Step 0: generic tools -/

/-- If `a ^ o = 1` and `o ∣ N - r` with `r ≤ N`, then `a ^ N = a ^ r`. -/
theorem pow_eq_pow_of_dvd_sub {M : Type*} [Monoid M] (a : M) {o N r : ℕ}
    (ho : a ^ o = 1) (hr : r ≤ N) (hd : o ∣ N - r) : a ^ N = a ^ r := by
  obtain ⟨m, hm⟩ := hd
  have hN : N = r + o * m := by omega
  rw [hN, pow_add, pow_mul, ho, one_pow, mul_one]

/-- The reduction of `tribMat` modulo `p`. -/
def tribMatMod (p : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  (Int.castRingHom (ZMod p)).mapMatrix tribMat

theorem trib_cast_eq (p N : ℕ) :
    ((trib N : ℤ) : ZMod p) = ((tribMatMod p) ^ N) 2 0 := by
  have h : ((Int.castRingHom (ZMod p)).mapMatrix (tribMat ^ N)) 2 0
      = ((tribMatMod p) ^ N) 2 0 := by
    rw [tribMatMod, map_pow]
  rw [← tribMat_pow_apply]
  exact h

/-- The exponent bookkeeping: with `r = 3 ^ 95 % o` and `o ∣ 3 ^ 95 * (3 ^ 1980 - 1)`,
the order `o` divides `3 ^ (1980 * k + 95) - r`. -/
theorem order_dvd_exp_sub {o : ℕ} (ho : o ∣ 3 ^ 95 * (3 ^ 1980 - 1)) (k : ℕ) :
    o ∣ 3 ^ (1980 * k + 95) - 3 ^ 95 % o := by
  have h1 : o ∣ 3 ^ 95 - 3 ^ 95 % o := Nat.dvd_sub_mod _
  have hgeom : (3 : ℕ) ^ 1980 - 1 ∣ 3 ^ (1980 * k) - 1 := by
    simpa only [one_pow, pow_mul] using Nat.sub_dvd_pow_sub_pow ((3:ℕ) ^ 1980) 1 k
  have h2 : o ∣ 3 ^ (1980 * k + 95) - 3 ^ 95 := by
    refine ho.trans ?_
    have hrw : (3:ℕ) ^ (1980 * k + 95) - 3 ^ 95 = 3 ^ 95 * (3 ^ (1980 * k) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add]
      ring_nf
    rw [hrw]
    exact mul_dvd_mul_left _ hgeom
  have hle1 : 3 ^ 95 % o ≤ 3 ^ 95 := Nat.mod_le _ _
  have hle2 : (3:ℕ) ^ 95 ≤ 3 ^ (1980 * k + 95) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : (3:ℕ) ^ (1980 * k + 95) - 3 ^ 95 % o
      = (3 ^ (1980 * k + 95) - 3 ^ 95) + (3 ^ 95 - 3 ^ 95 % o) := by omega
  rw [hsplit]
  exact Nat.dvd_add h2 h1

/-- The certificate-driven covering step. -/
theorem dvd_trib_add_of_cert {p o : ℕ} (h : ℤ)
    (ho : (tribMatMod p) ^ o = 1)
    (hv : ((tribMatMod p) ^ (3 ^ 95 % o)) 2 0 = - (h : ZMod p))
    (hdvd : o ∣ 3 ^ 95 * (3 ^ 1980 - 1)) (k : ℕ) :
    (p : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + h := by
  have hle : 3 ^ 95 % o ≤ 3 ^ (1980 * k + 95) :=
    le_trans (Nat.mod_le _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
  push_cast
  rw [trib_cast_eq, pow_eq_pow_of_dvd_sub _ ho hle (order_dvd_exp_sub hdvd k), hv]
  ring

/-- A number with a proper prime divisor is not prime. -/
theorem not_prime_of_dvd_of_lt {x : ℤ} {q : ℕ} (hq : q.Prime) (hd : (q : ℤ) ∣ x)
    (hlt : (q : ℤ) < x) : ¬ Prime x := by
  intro hx
  have hxn : x.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hx
  have hdn : q ∣ x.natAbs := Int.natCast_dvd.1 hd
  have heq : q = x.natAbs := (Nat.prime_dvd_prime_iff_eq hq hxn).1 hdn
  have hx0 : (0:ℤ) ≤ x := le_trans (Int.natCast_nonneg q) hlt.le
  have : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
  rw [heq, this] at hlt
  exact absurd hlt (lt_irrefl x)

/-! ### Step 1: the seven certificates

All the matrix computations are packed into two kernel-checked `decide +kernel` blocks.  The order `3256` of
`tribMat` mod `593` is too large for a single `npowRec` evaluation, so it is staged through the
literal matrices `tribMat^8` and `tribMat^88` (`3256 = 8 * 11 * 37`). -/

theorem tribMatMod_593_pow_order : (tribMatMod 593) ^ 3256 = 1 := by
  have h8 : (tribMatMod 593) ^ 8 = !![81, 68, 44; 44, 37, 24; 24, 20, 13] := by decide +kernel
  have h88 : (!![81, 68, 44; 44, 37, 24; 24, 20, 13] : Matrix (Fin 3) (Fin 3) (ZMod 593)) ^ 11
      = !![438, 142, 106; 106, 332, 36; 36, 70, 296] := by decide +kernel
  have h37 : (!![438, 142, 106; 106, 332, 36; 36, 70, 296] :
      Matrix (Fin 3) (Fin 3) (ZMod 593)) ^ 37 = 1 := by decide +kernel
  rw [show (3256 : ℕ) = 8 * 11 * 37 by norm_num, pow_mul, pow_mul, h8, h88, h37]

/-- The seven residue certificates of the table in the module docstring, together with the six
orders `ord_p(A)` (the `p = 593` order is `tribMatMod_593_pow_order`). -/
theorem tribCerts :
    (tribMatMod 53) ^ 52 = 1 ∧
    ((tribMatMod 53) ^ (3 ^ 95 % 52)) 2 0 = -((-3 : ℤ) : ZMod 53) ∧
    (tribMatMod 5) ^ 31 = 1 ∧
    ((tribMatMod 5) ^ (3 ^ 95 % 31)) 2 0 = -((-2 : ℤ) : ZMod 5) ∧
    ((tribMatMod 5) ^ (3 ^ 95 % 31)) 2 0 = -((3 : ℤ) : ZMod 5) ∧
    (tribMatMod 7) ^ 48 = 1 ∧
    ((tribMatMod 7) ^ (3 ^ 95 % 48)) 2 0 = -((-1 : ℤ) : ZMod 7) ∧
    (tribMatMod 13) ^ 168 = 1 ∧
    ((tribMatMod 13) ^ (3 ^ 95 % 168)) 2 0 = -((0 : ℤ) : ZMod 13) ∧
    ((tribMatMod 593) ^ (3 ^ 95 % 3256)) 2 0 = -((1 : ℤ) : ZMod 593) ∧
    (tribMatMod 47) ^ 46 = 1 ∧
    ((tribMatMod 47) ^ (3 ^ 95 % 46)) 2 0 = -((2 : ℤ) : ZMod 47) := by
  decide +kernel

theorem cert_53 (k : ℕ) : (53 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + (-3) :=
  dvd_trib_add_of_cert (p := 53) (o := 52) (-3) tribCerts.1 tribCerts.2.1 (by decide +kernel) k

theorem cert_5_neg2 (k : ℕ) : (5 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + (-2) :=
  dvd_trib_add_of_cert (p := 5) (o := 31) (-2) tribCerts.2.2.1 tribCerts.2.2.2.1
    (by decide +kernel) k

theorem cert_7 (k : ℕ) : (7 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + (-1) :=
  dvd_trib_add_of_cert (p := 7) (o := 48) (-1) tribCerts.2.2.2.2.2.1
    tribCerts.2.2.2.2.2.2.1 (by decide +kernel) k

theorem cert_13 (k : ℕ) : (13 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + 0 :=
  dvd_trib_add_of_cert (p := 13) (o := 168) 0 tribCerts.2.2.2.2.2.2.2.1
    tribCerts.2.2.2.2.2.2.2.2.1 (by decide +kernel) k

theorem cert_593 (k : ℕ) : (593 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + 1 :=
  dvd_trib_add_of_cert (p := 593) (o := 3256) 1 tribMatMod_593_pow_order
    tribCerts.2.2.2.2.2.2.2.2.2.1 (by decide +kernel) k

theorem cert_47 (k : ℕ) : (47 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + 2 :=
  dvd_trib_add_of_cert (p := 47) (o := 46) 2 tribCerts.2.2.2.2.2.2.2.2.2.2.1
    tribCerts.2.2.2.2.2.2.2.2.2.2.2 (by decide +kernel) k

theorem cert_5_three (k : ℕ) : (5 : ℤ) ∣ trib (3 ^ (1980 * k + 95)) + 3 :=
  dvd_trib_add_of_cert (p := 5) (o := 31) 3 tribCerts.2.2.1 tribCerts.2.2.2.2.1
    (by decide +kernel) k

/-- **Covering:** `p_h ∣ T(3^(1980k + 95)) + h` for every `k` and `|h| ≤ 3`. -/
theorem trib_three_pow_covering (k : ℕ) (h : ℤ) (hh : |h| ≤ 3) :
    tribCoverPrime h ∣ trib (3 ^ (1980 * k + 95)) + h := by
  rw [abs_le] at hh
  have hcases : h = -3 ∨ h = -2 ∨ h = -1 ∨ h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [tribCoverPrime] using cert_53 k
  · simpa [tribCoverPrime] using cert_5_neg2 k
  · simpa [tribCoverPrime] using cert_7 k
  · simpa [tribCoverPrime] using cert_13 k
  · simpa [tribCoverPrime] using cert_593 k
  · simpa [tribCoverPrime] using cert_47 k
  · simpa [tribCoverPrime] using cert_5_three k

/-! ### Step 2: the covering primes are small compared with `T(3^(1980k+95))` -/

theorem trib_ge_self {N : ℕ} (hN : 4 ≤ N) : (N : ℤ) - 2 ≤ trib N := by
  obtain ⟨m, hm⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
  subst hm
  have := trib_ge m
  push_cast
  omega

theorem big_trib (k : ℕ) : (600 : ℤ) ≤ trib (3 ^ (1980 * k + 95)) := by
  have h1 : (3:ℕ) ^ 95 ≤ 3 ^ (1980 * k + 95) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (1000 : ℕ) ≤ 3 ^ 95 := by norm_num
  have h4 : 4 ≤ 3 ^ (1980 * k + 95) := by omega
  have h3 := trib_ge_self h4
  have : (1000 : ℤ) ≤ ((3 ^ (1980 * k + 95) : ℕ) : ℤ) := by exact_mod_cast le_trans h2 h1
  omega

/-- **Seven consecutive composites** around `T(3^(1980k + 95))`. -/
theorem trib_three_pow_prime_free (k : ℕ) (h : ℤ) (hh : |h| ≤ 3) :
    ¬ Prime (trib (3 ^ (1980 * k + 95)) + h) := by
  have hbig := big_trib k
  rw [abs_le] at hh
  have hcases : h = -3 ∨ h = -2 ∨ h = -1 ∨ h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_prime_of_dvd_of_lt (q := 53) (by norm_num) (by exact_mod_cast cert_53 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 5) (by norm_num) (by exact_mod_cast cert_5_neg2 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 7) (by norm_num) (by exact_mod_cast cert_7 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 13) (by norm_num) (by exact_mod_cast cert_13 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 593) (by norm_num) (by exact_mod_cast cert_593 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 47) (by norm_num) (by exact_mod_cast cert_47 k) (by
      push_cast; omega)
  · exact not_prime_of_dvd_of_lt (q := 5) (by norm_num) (by exact_mod_cast cert_5_three k) (by
      push_cast; omega)

/-- **Prime-free intervals `[T(3^n) − 3, T(3^n) + 3]` for infinitely many `n`.** -/
theorem trib_three_pow_prime_free_often :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ 3 → ¬ Prime (trib (3 ^ n) + h) := by
  refine frequently_atTop.2 fun a => ⟨1980 * a + 95, by omega, fun h hh => ?_⟩
  exact trib_three_pow_prime_free a h hh

end LeanFormalizations.Mills.TribonacciCovering
