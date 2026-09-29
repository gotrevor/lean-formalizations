/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.GaussCongruence
import LeanFormalizations.NumberTheory.Mills.TranscendentalRH

/-!
# A 3-adic obstruction to an algebraic Mills constant (phase 29, new math)

Saito (2024, Remark 4.4 and Prop. 5.1; 2025, arXiv:2504.14968 Problem 1.1) leaves the case where
`β = ξ^(3^m)` is a totally real cubic Pisot number, and notes that the geometric exponent `3^k`
defeats the periodicity method: `3^k mod L` never returns to `1` when `3 ∣ L`.  The observation
here is that when the modulus is the prime `p_m = tr C^(3^m)` **itself**, the `3`-part of `L` is
controlled by `v₃ |GL_n(𝔽_{p_m})|`.  The Gauss congruence pins `p_m` `3`-adically, so that
valuation stays bounded unless `p_m → ±1` in `ℤ₃`.  Write-up and numerics: `PROBE-MILLS-3ADIC.md`,
`scripts/mills-3adic-probe.py`.

## Route

1. `dvd_trace_pow_three_of_glCard` (pure group theory).  Reduce `C` mod `p`.  `det ≠ 0` makes it a
   unit `u` of `GL_n(𝔽_p)`, so `u ^ glCard n p = 1` (`Matrix.card_GL_field`, `pow_card_eq_one`).
   Write `glCard = 3^v · M` with `3 ∤ M`.  Since `v ≤ m`, `g := u^(3^m)` has `g^M = 1`.  Take
   `j := φ(M) ≥ 1`, so `3^j ≡ 1 (mod M)` (`Nat.ModEq.pow_totient`) and `g^(3^j) = g`.  Hence
   `tr C^(3^(m+j)) ≡ tr C^(3^m) ≡ 0 (mod p)`.
2. `lt_padicValNat_glCard`.  For large `k`, `t_k` is a positive prime above `|det C|`.  If
   `v₃ (glCard n t_k) ≤ k`, step 1 gives `t_k ∣ t_(k+j)`, and `t_(k+j) > t_k` is prime: contradiction.
3. `threeAdic_pm_one`.  By the Gauss congruence, `t_k mod 3^e` is constant for `k ≥ e`.  If that
   residue is not `±1`, then `v₃(t_k ∓ 1) < e`.  Lifting the exponent (`padicValNat.pow_sub_pow`
   and the `p ≡ 2 mod 3` even/odd split) then bounds `v₃(t_k^s − 1) ≤ 2e + log₃ s` for `s ≤ n`,
   hence `v₃ (glCard n t_k)` by a constant.  This contradicts step 2.
4. `mills_threeAdic`.  In Saito's Pisot branch (`transcendental_or_pisot`), the floor
   `⌊A^(3^(m+i))⌋` equals `tr C^(3^i)` for an integer matrix `C` (companion matrix of the integer
   minimal polynomial of `β = A^(3^m)`).  From `pair_pow_sum_re_neg`, the other conjugates' power sum
   is real, negative and `> −1/2`, and `pisot_branch_otherConj_real` shows the conjugates are real.
   Primality is `IsMills`, and monotonicity is `mdigit_cube_lt`.  Apply step 3.
5. `transcendental_of_not_pm_one` is the contrapositive of 4.

Frozen: every statement below, all of `Literature/`.  Infrastructure leaves are progress; a false
frozen statement is an advance (record the counterexample, do not repair it).
-/

namespace LeanFormalizations.Mills.ThreeAdic

open LeanFormalizations.Literature Matrix Filter

/-- `|GL_n(𝔽_p)| = ∏_{i<n} (p^n − p^i)`, as a natural number. -/
def glCard (n p : ℕ) : ℕ := ∏ i : Fin n, (p ^ n - p ^ (i : ℕ))

/-- **Step 1.**  If the prime `p` divides `tr C^(3^m)`, does not divide `det C`, and
`v₃ |GL_n(𝔽_p)| ≤ m`, then `p` divides `tr C^(3^(m+j))` for some `j ≥ 1`. -/
theorem dvd_trace_pow_three_of_glCard {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m : ℕ}
    (hp : p.Prime) (hdiv : (p : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (p : ℤ) ∣ C.det)
    (h3 : padicValNat 3 (glCard n p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace := by
  sorry

/-- **Step 2 (unconditional).**  If `t_k = tr C^(3^k)` is prime and strictly increasing from some
point on, then `v₃ |GL_n(𝔽_{t_k})| > k` for all large `k`. -/
theorem lt_padicValNat_glCard {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0)
    {k₀ : ℕ} (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∃ K, ∀ k ≥ K, k < padicValNat 3 (glCard n (C ^ (3 ^ k)).trace.toNat) := by
  sorry

/-- **Step 3.**  Under the Gauss congruence, a trace sequence `tr C^(3^k)` that is eventually prime
and increasing converges to `±1` in `ℤ₃`. -/
theorem threeAdic_pm_one (hG : GaussCongruenceTrace) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0) {k₀ : ℕ}
    (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (C ^ (3 ^ k)).trace ≡ 1 [ZMOD 3 ^ e] ∨ (C ^ (3 ^ k)).trace ≡ -1 [ZMOD 3 ^ e] := by
  sorry

/-- **Step 4: if the least Mills constant is algebraic, its primes tend to `±1` in `ℤ₃`.** -/
theorem mills_threeAdic (hGc : GaussCongruenceTrace)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) (halg : IsAlgebraic ℚ A) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨ (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e] := by
  sorry

/-- **Step 5.**  If for some `e` infinitely many Mills primes avoid `±1 mod 3^e`, the least Mills
constant is transcendental. -/
theorem transcendental_of_not_pm_one (hGc : GaussCongruenceTrace)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) {e : ℕ}
    (h : ∃ᶠ k in atTop, ¬ ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e])) :
    Transcendental ℚ A := by
  sorry

end LeanFormalizations.Mills.ThreeAdic
