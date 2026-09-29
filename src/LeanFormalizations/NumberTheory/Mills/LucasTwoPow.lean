/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoFibonacci

/-!
# Phase 33: Saito's Problem 1.8 for every Lucas sequence `U(P,Q)` with `P, Q` odd

Phase 32 answered Saito's Problem 1.8 (arXiv:2504.14968): `F(2^n) + h` is composite i.o. for
every `h`.  The argument uses only three facts, each of which holds for the Lucas sequence
`U_N(P,Q)` (`U₀ = 0`, `U₁ = 1`, `U_(N+2) = P U_(N+1) − Q U_N`) whenever `P` and `Q` are odd:
1. `U(2^n)` is odd (`U_N` is even iff `3 ∣ N` when `P, Q` are odd).
2. **Sign flip**: `2^(n+1) ∣ U(2^(n+1)) + U(2^n)` for `n ≥ 1`.  `U(2m) = U(m) V(m)` with
   `V(m) = 2U(m+1) − P U(m)`, and `V(2m) = V(m)^2 − 2Q^m`; since `Q^(2^n) ≡ 1 (mod 2^(n+2))`,
   the induction `2^(n+1) ∣ V(2^n) + 1` of phase 32 goes through with one extra term.
   Base: `V(2) + 1 = P^2 − 2Q + 1 ≡ 2 − 2Q ≡ 0 (mod 4)`.  Checked numerically for
   `(P,Q) ∈ {(1,-1),(3,1),(1,3),(3,-1),(5,3),(-1,-5),(7,-3)}`, `n ≤ 10`.
3. **Mechanism**: `U_N = (A^N) 1 0` for `A = !![P, -Q; 1, 0]`, `det A = Q`; for a prime
   `p ∤ Q` the phase-32 lemma `exists_entry_pow_congr` applies (it is `private` in
   `SaitoFibonacci.lean`: make it public, changing nothing else there).

Differences from phase 32 the proof must handle:
- `U(2^n)` need not be positive or monotone; the hypothesis is `|U(2^n)| → ∞`.  Work with
  `natAbs`.  Prime in `ℤ` is up to sign.
- The mechanism gives some `j ≥ 1` with `p ∣ U(2^(n+j)) − U(2^n)`; the proof shows
  `D^(c^(m+j)) = D^(c^m)`, hence also for every multiple of `j`.  Use a large multiple so that
  `|p_(n+kj)| > |p_n|` (growth), contradicting primality.
- `p ∤ Q` holds once `|p_n| > |Q|`.
- The `(1, 1)` sequence is periodic (degenerate), which is why growth is assumed.

Frozen: every statement below; `SaitoFibonacci.lean` statements (only the visibility of
`exists_entry_pow_congr` may change); `ThreeAdic`, `SharedConjecture`, `Projective`, `Literature/`.
-/

namespace LeanFormalizations.Mills.LucasTwoPow

open LeanFormalizations.Mills.ThreeAdic Filter

/-- The Lucas sequence `U_N(P,Q)`, as the `(1,0)` entry of `!![P, -Q; 1, 0] ^ N`. -/
def lucasU (P Q : ℤ) (N : ℕ) : ℤ := ((!![P, -Q; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ N) 1 0


/-! ### The sequences `U` and `V`, and the companion matrix -/

/-- The companion matrix `A = !![P, -Q; 1, 0]`. -/
private def lucasMat (P Q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![P, -Q; 1, 0]

/-- `U` by the recurrence (`u 0 = 0`, `u 1 = 1`). -/
private def uSeq (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P * uSeq P Q (n + 1) - Q * uSeq P Q n

/-- The companion solution (`v 0 = 1`, `v 1 = 0`); it is `u (n+1) - P * u n`. -/
private def vSeq (P Q : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | (n + 2) => P * vSeq P Q (n + 1) - Q * vSeq P Q n

@[simp] private lemma uSeq_zero (P Q : ℤ) : uSeq P Q 0 = 0 := rfl
@[simp] private lemma uSeq_one (P Q : ℤ) : uSeq P Q 1 = 1 := rfl
private lemma uSeq_add_two (P Q : ℤ) (n : ℕ) :
    uSeq P Q (n + 2) = P * uSeq P Q (n + 1) - Q * uSeq P Q n := rfl
@[simp] private lemma vSeq_zero (P Q : ℤ) : vSeq P Q 0 = 1 := rfl
@[simp] private lemma vSeq_one (P Q : ℤ) : vSeq P Q 1 = 0 := rfl
private lemma vSeq_add_two (P Q : ℤ) (n : ℕ) :
    vSeq P Q (n + 2) = P * vSeq P Q (n + 1) - Q * vSeq P Q n := rfl

private lemma lucasMat_pow (P Q : ℤ) (N : ℕ) :
    lucasMat P Q ^ N =
      !![uSeq P Q (N + 1), vSeq P Q (N + 1); uSeq P Q N, vSeq P Q N] := by
  induction N with
  | zero =>
      simp only [pow_zero, uSeq_zero, uSeq_one, vSeq_zero, vSeq_one]
      exact Matrix.one_fin_two
  | succ N ih =>
      rw [pow_succ', ih, lucasMat, Matrix.mul_fin_two]
      rw [uSeq_add_two, vSeq_add_two]
      norm_num [sub_eq_add_neg]

private lemma lucasU_eq (P Q : ℤ) (N : ℕ) : lucasU P Q N = uSeq P Q N := by
  rw [lucasU, show (!![P, -Q; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = lucasMat P Q from rfl,
    lucasMat_pow]
  simp

private lemma lucasMat_det (P Q : ℤ) : (lucasMat P Q).det = Q := by
  simp [lucasMat, Matrix.det_fin_two_of]

private lemma vSeq_eq_aux (P Q : ℤ) : ∀ N : ℕ,
    vSeq P Q N = uSeq P Q (N + 1) - P * uSeq P Q N ∧
      vSeq P Q (N + 1) = uSeq P Q (N + 2) - P * uSeq P Q (N + 1) := by
  intro N
  induction N with
  | zero => constructor <;> simp [uSeq_add_two]
  | succ N ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : uSeq P Q (N + 3) = P * uSeq P Q (N + 2) - Q * uSeq P Q (N + 1) :=
        uSeq_add_two P Q (N + 1)
      have h2 : uSeq P Q (N + 2) = P * uSeq P Q (N + 1) - Q * uSeq P Q N := uSeq_add_two P Q N
      have h3 : vSeq P Q (N + 2) = P * vSeq P Q (N + 1) - Q * vSeq P Q N := vSeq_add_two P Q N
      show vSeq P Q (N + 2) = uSeq P Q (N + 3) - P * uSeq P Q (N + 2)
      rw [h3, h1, ih.1, ih.2, h2]; ring

private lemma vSeq_eq (P Q : ℤ) (N : ℕ) :
    vSeq P Q N = uSeq P Q (N + 1) - P * uSeq P Q N := (vSeq_eq_aux P Q N).1

/-- The companion Lucas sequence `V m = trace (A ^ m) = 2 U(m+1) − P U(m)`. -/
private def vLuc (P Q : ℤ) (m : ℕ) : ℤ := uSeq P Q (m + 1) + vSeq P Q m

private lemma vLuc_eq (P Q : ℤ) (m : ℕ) :
    vLuc P Q m = 2 * uSeq P Q (m + 1) - P * uSeq P Q m := by
  rw [vLuc, vSeq_eq]; ring

@[simp] private lemma vLuc_one (P Q : ℤ) : vLuc P Q 1 = P := by
  have h : uSeq P Q 2 = P := by rw [uSeq_add_two]; simp
  rw [vLuc_eq, h, uSeq_one]; ring

private lemma pow_two_mul (P Q : ℤ) (m : ℕ) :
    lucasMat P Q ^ (2 * m) = (lucasMat P Q ^ m) ^ 2 := by
  rw [← pow_mul, mul_comm]

/-- `U(2m) = U(m) V(m)`. -/
private lemma uSeq_two_mul (P Q : ℤ) (m : ℕ) :
    uSeq P Q (2 * m) = uSeq P Q m * vLuc P Q m := by
  have h := pow_two_mul P Q m
  rw [lucasMat_pow, lucasMat_pow, sq, Matrix.mul_fin_two] at h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
  simp at h10
  rw [h10, vLuc]; ring

/-- `V(2m) = V(m)^2 − 2 Q^m`. -/
private lemma vLuc_two_mul (P Q : ℤ) (m : ℕ) :
    vLuc P Q (2 * m) = vLuc P Q m ^ 2 - 2 * Q ^ m := by
  have hdet : (lucasMat P Q ^ m).det = Q ^ m := by
    rw [Matrix.det_pow, lucasMat_det]
  rw [lucasMat_pow] at hdet
  rw [Matrix.det_fin_two_of] at hdet
  have h := pow_two_mul P Q m
  rw [lucasMat_pow, lucasMat_pow, sq, Matrix.mul_fin_two] at h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) h
  simp at h00 h11
  rw [vLuc, vLuc, show 2 * m + 1 = 2 * m + 1 from rfl]
  have : uSeq P Q (2 * m + 1) = _ := h00
  rw [this, h11]
  nlinarith [hdet]

/-- Sanity: `U(1, -1)` is Fibonacci. -/
theorem lucasU_one_neg_one (N : ℕ) : lucasU 1 (-1) N = Nat.fib N := by
  rw [lucasU_eq]
  have key : ∀ N : ℕ, uSeq 1 (-1) N = Nat.fib N ∧ uSeq 1 (-1) (N + 1) = Nat.fib (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        refine ⟨ih.2, ?_⟩
        have h1 : uSeq 1 (-1) (N + 2) = 1 * uSeq 1 (-1) (N + 1) - (-1) * uSeq 1 (-1) N :=
          uSeq_add_two 1 (-1) N
        have h2 : (Nat.fib (N + 2) : ℤ) = Nat.fib N + Nat.fib (N + 1) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := N))
        show uSeq 1 (-1) (N + 2) = (Nat.fib (N + 2) : ℤ)
        rw [h1, h2, ih.1, ih.2]; ring
  exact (key N).1

/-- The recurrence, as a sanity check on the definition. -/
theorem lucasU_add_two (P Q : ℤ) (N : ℕ) :
    lucasU P Q (N + 2) = P * lucasU P Q (N + 1) - Q * lucasU P Q N := by
  rw [lucasU_eq, lucasU_eq, lucasU_eq, uSeq_add_two]

/-- `U(2^n)` is odd when `P, Q` are odd. -/
private lemma odd_two_pow_aux {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ) :
    Odd (uSeq P Q (2 ^ n)) ∧ Odd (vLuc P Q (2 ^ n)) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa using odd_one
      · simpa using hP
  | succ n ih =>
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      constructor
      · rw [hpow, uSeq_two_mul]
        exact ih.1.mul ih.2
      · rw [hpow, vLuc_two_mul]
        obtain ⟨a, ha⟩ := ih.2
        refine ⟨2 * a ^ 2 + 2 * a - Q ^ 2 ^ n, ?_⟩
        rw [ha]; ring

theorem lucasU_two_pow_odd {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ) :
    Odd (lucasU P Q (2 ^ n)) := by
  rw [lucasU_eq]
  exact (odd_two_pow_aux hP hQ n).1


/-- For odd `Q`, `2^(n+1) ∣ Q^(2^n) − 1`. -/
private lemma two_pow_dvd_odd_pow_two_pow_sub_one {Q : ℤ} (hQ : Odd Q) (n : ℕ) :
    (2 : ℤ) ^ (n + 1) ∣ Q ^ 2 ^ n - 1 := by
  induction n with
  | zero =>
      obtain ⟨a, ha⟩ := hQ
      exact ⟨a, by rw [ha]; ring⟩
  | succ n ih =>
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have hid : Q ^ 2 ^ (n + 1) - 1 = (Q ^ 2 ^ n - 1) * (Q ^ 2 ^ n + 1) := by
        rw [hpow, pow_mul]; ring
      obtain ⟨c, hc⟩ := ih
      have h2 : (2 : ℤ) ∣ Q ^ 2 ^ n + 1 := by
        obtain ⟨a, ha⟩ := hQ.pow (n := 2 ^ n)
        exact ⟨a + 1, by rw [ha]; ring⟩
      obtain ⟨e, he⟩ := h2
      exact ⟨c * e, by rw [hid, hc, he]; ring⟩

/-- `v₂(V(2^n) + 1) ≥ n + 1` for `n ≥ 1`: the engine of the sign flip. -/
private lemma two_pow_dvd_vLuc_two_pow_add_one {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ)
    (hn : 1 ≤ n) : (2 : ℤ) ^ (n + 1) ∣ vLuc P Q (2 ^ n) + 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
      have h2 : vLuc P Q (2 ^ 1) = P ^ 2 - 2 * Q := by
        have : (2 : ℕ) ^ 1 = 2 * 1 := by norm_num
        rw [this, vLuc_two_mul, vLuc_one]; ring
      obtain ⟨a, ha⟩ := hP
      obtain ⟨b, hb⟩ := hQ
      refine ⟨a ^ 2 + a - b, ?_⟩
      rw [h2, ha, hb]; ring
  | succ n hn ih =>
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have hsq : vLuc P Q (2 ^ (n + 1)) = vLuc P Q (2 ^ n) ^ 2 - 2 * Q ^ 2 ^ n := by
        rw [hpow, vLuc_two_mul]
      obtain ⟨c, hc⟩ := ih
      have h4 : (4 : ℤ) ∣ vLuc P Q (2 ^ n) + 1 := by
        refine Dvd.dvd.trans ?_ ⟨c, hc⟩
        have h : (4 : ℤ) = 2 ^ 2 := by norm_num
        rw [h]
        exact pow_dvd_pow 2 (by omega)
      obtain ⟨d, hd⟩ := h4
      obtain ⟨g, hg⟩ := two_pow_dvd_odd_pow_two_pow_sub_one hQ n
      refine ⟨(2 * d - 1) * c - g, ?_⟩
      have hvm : vLuc P Q (2 ^ n) = 4 * d - 1 := by linarith
      have hqm : Q ^ 2 ^ n = 2 ^ (n + 1) * g + 1 := by linarith
      have hd' : (4 : ℤ) * d = 2 ^ (n + 1) * c := by linarith
      rw [hsq, hvm, hqm]
      linear_combination (2 * (2 * d - 1)) * hd'

/-- **The sign flip** for `P, Q` odd. -/
theorem two_pow_dvd_lucasU_two_pow_succ_add {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ)
    (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ lucasU P Q (2 ^ (n + 1)) + lucasU P Q (2 ^ n) := by
  rw [lucasU_eq, lucasU_eq]
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hid : uSeq P Q (2 ^ (n + 1)) + uSeq P Q (2 ^ n)
      = uSeq P Q (2 ^ n) * (vLuc P Q (2 ^ n) + 1) := by
    rw [hpow, uSeq_two_mul]; ring
  rw [hid]
  exact Dvd.dvd.mul_left (two_pow_dvd_vLuc_two_pow_add_one hP hQ n hn) _

/-- **Saito's Problem 1.8, for every Lucas sequence with `P, Q` odd.**  If `|U(2^n)| → ∞`
then `U(2^n) + h` is not prime for infinitely many `n`, for every integer `h`. -/
theorem lucasU_two_pow_add_not_prime {P Q : ℤ} (hP : Odd P) (hQ : Odd Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (2 ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (2 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasTwoPow
