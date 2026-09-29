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


/-! ### Divisibility along the tower, and elementary primality obstructions -/

private lemma lucasU_two_pow_dvd (P Q : ℤ) {m n : ℕ} (hmn : m ≤ n) :
    lucasU P Q (2 ^ m) ∣ lucasU P Q (2 ^ n) := by
  rw [lucasU_eq, lucasU_eq]
  induction n, hmn using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n hn ih =>
      refine ih.trans ?_
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [hpow, uSeq_two_mul]
      exact dvd_mul_right _ _

private lemma not_prime_of_two_dvd {x : ℤ} (hd : (2 : ℤ) ∣ x) (hx : 2 < |x|) : ¬ Prime x := by
  intro hpx
  have hn : x.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hpx
  have hd' : (2 : ℕ) ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd
    simpa using this
  have habs : |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs x
  rcases hn.eq_one_or_self_of_dvd 2 hd' with hh | hh <;> omega

private lemma abs_add_ge {a b : ℤ} : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  rw [abs_neg, sub_neg_eq_add] at h
  linarith

/-- **Saito's Problem 1.8, for every Lucas sequence with `P, Q` odd.**  If `|U(2^n)| → ∞`
then `U(2^n) + h` is not prime for infinitely many `n`, for every integer `h`. -/
theorem lucasU_two_pow_add_not_prime {P Q : ℤ} (hP : Odd P) (hQ : Odd Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (2 ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (2 ^ n) + h) := by
  set U : ℕ → ℤ := fun n => lucasU P Q (2 ^ n) with hUdef
  set t : ℕ → ℤ := fun n => U n + h with htdef
  have hgr : ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B ≤ |U n| := by
    intro B
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow B)
    exact ⟨N, hN⟩
  have hlow : ∀ n : ℕ, |U n| - |h| ≤ |t n| := fun n => abs_add_ge
  rcases Int.even_or_odd h with hev | hodd
  swap
  · -- `h` odd: `U(2^n) + h` is even, and `|U(2^n) + h| > 2` eventually
    refine Filter.Eventually.frequently ?_
    obtain ⟨N, hN⟩ := hgr (|h| + 3)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hlow n
    show ¬ Prime (t n)
    refine not_prime_of_two_dvd ?_ (by linarith)
    obtain ⟨a, ha⟩ := lucasU_two_pow_odd hP hQ n
    obtain ⟨b, hb⟩ := hodd
    refine ⟨a + b + 1, ?_⟩
    show U n + h = _
    rw [show U n = lucasU P Q (2 ^ n) from rfl, ha, hb]; ring
  rcases eq_or_ne h 0 with h0 | h0
  · -- `h = 0`: `U(2^m) ∣ U(2^n)` with `1 < |U(2^m)| < |U(2^n)|`
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨M, hM⟩ := hgr 2
    obtain ⟨N₂, hN₂⟩ := hgr (|U M| + 1)
    refine ⟨max (max N₂ (M + 1)) a, le_max_right _ _, ?_⟩
    set n : ℕ := max (max N₂ (M + 1)) a with hn
    have hMn : M ≤ n := by omega
    have h1 : 2 ≤ |U M| := hM M le_rfl
    have h2 : |U M| + 1 ≤ |U n| := hN₂ n (by omega)
    have hdvd : U M ∣ U n := lucasU_two_pow_dvd P Q hMn
    show ¬ Prime (t n)
    intro hpr
    rw [show t n = U n + h from rfl, h0, add_zero] at hpr
    have hnp : (U n).natAbs.Prime := Int.prime_iff_natAbs_prime.1 hpr
    have hdn : (U M).natAbs ∣ (U n).natAbs := Int.natAbs_dvd_natAbs.2 hdvd
    have e1 : |U M| = ((U M).natAbs : ℤ) := Int.abs_eq_natAbs _
    have e2 : |U n| = ((U n).natAbs : ℤ) := Int.abs_eq_natAbs _
    rcases hnp.eq_one_or_self_of_dvd _ hdn with hh | hh <;> omega
  -- `h` even and nonzero: the main argument
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set H : ℕ := h.natAbs with hH
  have hHabs : |h| = (H : ℤ) := Int.abs_eq_natAbs h
  obtain ⟨N₁, hN₁⟩ := hgr (|h| + |Q| + 3)
  set N : ℕ := max n₀ N₁ with hNdef
  have hprime : ∀ n ≥ N, Prime (t n) := by
    intro n hn
    exact hn₀ n (by omega)
  have hbig : ∀ n ≥ N, |Q| + 3 ≤ |t n| := by
    intro n hn
    have := hN₁ n (by omega)
    have := hlow n
    linarith
  have hoddt : ∀ n : ℕ, Odd (t n) := by
    intro n
    obtain ⟨a, ha⟩ := lucasU_two_pow_odd hP hQ n
    obtain ⟨b, hb⟩ := hev
    refine ⟨a + b, ?_⟩
    show U n + h = _
    rw [show U n = lucasU P Q (2 ^ n) from rfl, ha, hb]; ring
  have hpn : ∀ n ≥ N, (t n).natAbs.Prime := fun n hn =>
    Int.prime_iff_natAbs_prime.1 (hprime n hn)
  have hpne2 : ∀ n : ℕ, (t n).natAbs ≠ 2 := by
    intro n hn
    obtain ⟨a, ha⟩ := hoddt n
    omega
  have hpabs : ∀ n : ℕ, ((t n).natAbs : ℤ) = |t n| := fun n => (Int.abs_eq_natAbs _).symm
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  have hpdvdQ : ∀ n ≥ N, ¬ ((t n).natAbs : ℤ) ∣ (lucasMat P Q).det := by
    intro n hn hd
    rw [lucasMat_det] at hd
    have h1 : ((t n).natAbs : ℤ) ≤ |Q| := Int.le_of_dvd (abs_pos.2 hQ0) ((dvd_abs _ _).2 hd)
    have := hbig n hn
    rw [hpabs n] at h1
    linarith
  -- the return step
  have hstep : ∀ n ≥ N, padicValNat 2 (glCard 2 (t n).natAbs) ≤ n →
      ∃ j, 1 ≤ j ∧ (t (n + j)).natAbs = (t n).natAbs := by
    intro n hn hv
    obtain ⟨j, hj1, hj⟩ := LeanFormalizations.Mills.SaitoFibonacci.exists_entry_pow_congr
      (lucasMat P Q) (hpn n hn) Nat.prime_two (hpdvdQ n hn) hv
    have hent := hj 1 0
    have hUj : ((lucasMat P Q) ^ (2 ^ (n + j))) 1 0 = U (n + j) := rfl
    have hUn : ((lucasMat P Q) ^ (2 ^ n)) 1 0 = U n := rfl
    rw [hUj, hUn] at hent
    have hdvd : ((t n).natAbs : ℤ) ∣ t (n + j) := by
      have h1 : ((t n).natAbs : ℤ) ∣ t n := Int.natAbs_dvd.2 dvd_rfl
      have h2 : t (n + j) = (U (n + j) - U n) + t n := by
        show U (n + j) + h = _
        show U (n + j) + h = (U (n + j) - U n) + (U n + h)
        ring
      rw [h2]
      exact dvd_add hent h1
    have hq := hpn (n + j) (by omega)
    have hdq : (t n).natAbs ∣ (t (n + j)).natAbs :=
      Int.natAbs_dvd_natAbs.2 (Int.natAbs_dvd.1 hdvd)
    rcases hq.eq_one_or_self_of_dvd _ hdq with hh | hh
    · exact absurd hh (hpn n hn).ne_one
    · exact ⟨j, hj1, hh.symm⟩
  -- step 2: the 2-part of `|GL₂(𝔽_p)|` exceeds `n`
  have hstep2 : ∀ n ≥ N, n < padicValNat 2 (glCard 2 (t n).natAbs) := by
    intro n hn
    by_contra hle
    push_neg at hle
    have chain : ∀ k : ℕ, ∃ n' : ℕ, n + k ≤ n' ∧ (t n').natAbs = (t n).natAbs ∧
        padicValNat 2 (glCard 2 (t n').natAbs) ≤ n' := by
      intro k
      induction k with
      | zero => exact ⟨n, by omega, rfl, hle⟩
      | succ k ih =>
          obtain ⟨n', hn'1, hn'2, hn'3⟩ := ih
          obtain ⟨j, hj1, hj⟩ := hstep n' (by omega) hn'3
          refine ⟨n' + j, by omega, ?_, ?_⟩
          · rw [hj]; exact hn'2
          · rw [hj]; omega
    obtain ⟨Nb, hNb⟩ := hgr (|t n| + |h| + 1)
    obtain ⟨n', hc1, hc2, _⟩ := chain (Nb + n)
    have h1 : |t n'| = |t n| := by
      rw [← hpabs n', ← hpabs n, hc2]
    have h2 := hNb n' (by omega)
    have h3 := hlow n'
    linarith
  -- step 3: `t n ≡ ±1` modulo `2 ^ (n / 2)`
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (2 : ℤ) ^ (n / 2) ∣ t n - s := by
    intro n hn
    have hlt := hstep2 n hn
    obtain ⟨s0, hs0, hd⟩ : ∃ s0 : ℤ, (s0 = 1 ∨ s0 = -1) ∧
        (2 : ℤ) ^ (n / 2) ∣ ((t n).natAbs : ℤ) - s0 := by
      rcases LeanFormalizations.Mills.SaitoFibonacci.two_pow_dvd_sub_or_add_of_lt_padicValNat
        (hpn n hn) (hpne2 n) hlt with hd | hd
      · exact ⟨1, Or.inl rfl, hd⟩
      · exact ⟨-1, Or.inr rfl, by simpa using hd⟩
    rcases Int.natAbs_eq (t n) with he | he
    · exact ⟨s0, hs0, by rw [he]; exact hd⟩
    · refine ⟨-s0, ?_, ?_⟩
      · rcases hs0 with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · have hrw : t n - -s0 = -(((t n).natAbs : ℤ) - s0) := by omega
        rw [hrw]
        exact dvd_neg.2 hd
  -- step 4: contradict `h ≠ 0`
  set n : ℕ := 4 * H + N + 4 with hn
  set e : ℕ := n / 2 with he
  have hnN : N ≤ n := by omega
  have he2 : 2 ≤ e := by omega
  have hbnd : (2 * H : ℤ) < (2 : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 * H : ℕ) < 2 ^ e := by omega
    exact_mod_cast h2
  obtain ⟨s, hs, hsd⟩ := hstep3 n hnN
  obtain ⟨s', hs', hsd'⟩ := hstep3 (n + 1) (by omega)
  have hdvd' : (2 : ℤ) ^ e ∣ t (n + 1) - s' := by
    refine dvd_trans (pow_dvd_pow 2 ?_) hsd'
    omega
  have hflip : (2 : ℤ) ^ e ∣ U (n + 1) + U n := by
    refine dvd_trans (pow_dvd_pow 2 ?_) (two_pow_dvd_lucasU_two_pow_succ_add hP hQ n (by omega))
    omega
  have hsum : (2 : ℤ) ^ e ∣ s + s' - 2 * h := by
    have h1 : (s + s' - 2 * h) = (U (n + 1) + U n) - ((t n - s) + (t (n + 1) - s')) := by
      show _ = (U (n + 1) + U n) - ((U n + h - s) + (U (n + 1) + h - s'))
      ring
    rw [h1]
    exact dvd_sub hflip (dvd_add hsd hdvd')
  obtain ⟨b, hb⟩ := hev
  have h4 : (4 : ℤ) ∣ s + s' - 2 * h := by
    refine dvd_trans ?_ hsum
    have hf : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [hf]
    exact pow_dvd_pow 2 he2
  have hss : s + s' = 0 := by
    obtain ⟨c, hc⟩ := h4
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> omega
  have hfin : (2 : ℤ) ^ e ∣ 2 * h := by
    have hz : (2 * h : ℤ) = -(s + s' - 2 * h) := by omega
    rw [hz]
    exact dvd_neg.2 hsum
  have hh0 : (2 : ℤ) * h ≠ 0 := by omega
  have hle : (2 : ℤ) ^ e ≤ |2 * h| := Int.le_of_dvd (abs_pos.2 hh0) ((dvd_abs _ _).2 hfin)
  have habs : |2 * h| = 2 * (H : ℤ) := by
    rw [abs_mul, abs_two, hHabs]
  omega

end LeanFormalizations.Mills.LucasTwoPow
