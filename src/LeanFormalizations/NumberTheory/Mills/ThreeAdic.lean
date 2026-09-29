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
  haveI : Fact p.Prime := ⟨hp⟩
  -- reduce mod `p`
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hf
  set D : Matrix (Fin n) (Fin n) (ZMod p) := f.mapMatrix C with hD
  have htr : ∀ N : ℕ, ((C ^ N).trace : ZMod p) = (D ^ N).trace := by
    intro N
    rw [hD, ← map_pow]
    simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply, hf]
  -- `D` is a unit
  have hdetD : IsUnit D.det := by
    have hmd : D.det = f C.det := by
      rw [hD]; exact (RingHom.map_det f C).symm
    rw [hmd]
    refine Ne.isUnit ?_
    simpa [hf, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdet
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det D).2 hdetD
  -- the order of the general linear group
  have hcard : Nat.card (GL (Fin n) (ZMod p)) = glCard n p := by
    rw [Matrix.card_GL_field]
    simp [glCard, ZMod.card]
  obtain ⟨N, hN⟩ : ∃ N, N = glCard n p := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hN, ← hcard]; exact Nat.card_pos
  have hNne : N ≠ 0 := hNpos.ne'
  have huN : u ^ N = 1 := by
    rw [hN, ← hcard]; exact pow_card_eq_one'
  -- split off the 3-part
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat 3 N := ⟨_, rfl⟩
  have hvm : v ≤ m := by rw [hv, hN]; exact h3
  obtain ⟨M, hM⟩ : ∃ M, M = N / 3 ^ v := ⟨_, rfl⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hfac : N.factorization 3 = v := by
    rw [hv, Nat.factorization_def _ hp3]
  have hsplit : 3 ^ v * M = N := by
    have := Nat.ordProj_mul_ordCompl_eq_self N 3
    rw [hfac] at this
    rw [hM, hfac] at *
    exact this
  have hMdvd : ¬ (3 ∣ M) := by
    have := Nat.not_dvd_ordCompl hp3 hNne
    rw [hfac] at this
    rwa [hM]
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hsplit; exact absurd hsplit.symm hNne
    · exact h
  -- `g := u ^ 3 ^ m` satisfies `g ^ M = 1`
  set g := u ^ (3 ^ m) with hg
  have hgM : g ^ M = 1 := by
    rw [hg, ← pow_mul]
    have : N ∣ 3 ^ m * M := by
      rw [← hsplit]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow 3 hvm) M
    obtain ⟨c, hc⟩ := this
    rw [hc, pow_mul, huN, one_pow]
  -- `3 ^ j ≡ 1 [MOD M]` for `j = φ M`
  set j := Nat.totient M with hj
  have hjpos : 1 ≤ j := Nat.totient_pos.2 hMpos
  have hcop : Nat.Coprime 3 M := (Nat.Prime.coprime_iff_not_dvd hp3).2 hMdvd
  have hmod : 3 ^ j ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcop
  obtain ⟨s, hs⟩ : ∃ s, 3 ^ j = 1 + M * s := by
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨c, by omega⟩
  have hgfix : g ^ (3 ^ j) = g := by
    rw [hs, pow_add, pow_one, pow_mul, hgM, one_pow, mul_one]
  refine ⟨j, hjpos, ?_⟩
  have key : D ^ (3 ^ (m + j)) = D ^ (3 ^ m) := by
    have : (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (3 ^ (m + j)) =
        (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (3 ^ m) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
      congr 1
      rw [pow_add, pow_mul, ← hg, hgfix]
    rwa [hu] at this
  have : ((C ^ (3 ^ (m + j))).trace : ZMod p) = 0 := by
    rw [htr, key, ← htr]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/-- The trace sequence, being strictly increasing from `k₀` on, exceeds any bound eventually. -/
private lemma trace_eventually_gt {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {k₀ : ℕ}
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) (B : ℤ) :
    ∃ K, k₀ ≤ K ∧ ∀ k ≥ K, B < (C ^ (3 ^ k)).trace := by
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  have growth : ∀ k, k₀ ≤ k → t k₀ + ((k : ℤ) - (k₀ : ℤ)) ≤ t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have := hmono' k hk
        push_cast
        push_cast at ih
        omega
  refine ⟨k₀ + (B - t k₀ + 1).toNat, by omega, ?_⟩
  intro k hk
  show B < t k
  have := growth k (by omega)
  have h2 : ((k₀ + (B - t k₀ + 1).toNat : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  push_cast at h2
  omega

/-- **Step 2 (unconditional).**  If `t_k = tr C^(3^k)` is prime and strictly increasing from some
point on, then `v₃ |GL_n(𝔽_{t_k})| > k` for all large `k`. -/
theorem lt_padicValNat_glCard {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0)
    {k₀ : ℕ} (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∃ K, ∀ k ≥ K, k < padicValNat 3 (glCard n (C ^ (3 ^ k)).trace.toNat) := by
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  -- weak monotonicity from `k₀` on
  have hle : ∀ a, k₀ ≤ a → ∀ d, t a ≤ t (a + d) := by
    intro a ha d
    induction d with
    | zero => simp
    | succ d ih =>
        have := hmono' (a + d) (by omega)
        have he : a + (d + 1) = (a + d) + 1 := by omega
        rw [he]; omega
  -- growth: the sequence increases by at least one per step
  obtain ⟨K, hK0, hKB'⟩ := trace_eventually_gt C hmono |C.det|
  have hKB : ∀ k ≥ K, |C.det| < t k := hKB'
  refine ⟨K, ?_⟩
  intro k hk
  have hk0 : k₀ ≤ k := le_trans hK0 hk
  by_contra hcon
  push_neg at hcon
  -- `p := t k` is a prime exceeding `|det C|`
  have htpos : 0 < t k := lt_of_le_of_lt (abs_nonneg _) (hKB k hk)
  have htprime : Prime (t k) := hprime k hk0
  obtain ⟨p, hpv⟩ : ∃ p : ℕ, (p : ℤ) = t k := ⟨(t k).toNat, Int.toNat_of_nonneg htpos.le⟩
  have hpnat : p.Prime := by
    rw [Int.prime_iff_natAbs_prime] at htprime
    simpa [← hpv] using htprime
  have hptoNat : (t k).toNat = p := by omega
  have hdvd : (p : ℤ) ∣ (C ^ (3 ^ k)).trace := by rw [hpv]
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro h
    have h1 : (p : ℤ) ≤ |C.det| := Int.le_of_dvd (abs_pos.2 hdet) ((dvd_abs _ _).2 h)
    have := hKB k hk
    omega
  have h3 : padicValNat 3 (glCard n p) ≤ k := by
    rw [← hptoNat]; exact hcon
  obtain ⟨j, hj1, hjd⟩ := dvd_trace_pow_three_of_glCard C hpnat hdvd hdetp h3
  -- `t (k+j)` is a strictly larger prime divisible by `p`: contradiction
  have hgt : t k < t (k + j) := by
    have h1 := hmono' k hk0
    have h2 := hle (k + 1) (by omega) (j - 1)
    have he : k + 1 + (j - 1) = k + j := by omega
    rw [he] at h2
    omega
  have hqpos : 0 < t (k + j) := lt_trans htpos hgt
  have hqprime : Prime (t (k + j)) := hprime (k + j) (by omega)
  obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (k + j) := ⟨(t (k + j)).toNat, Int.toNat_of_nonneg hqpos.le⟩
  have hqnat : q.Prime := by
    rw [Int.prime_iff_natAbs_prime] at hqprime
    simpa [← hqv] using hqprime
  have hdq : p ∣ q := by
    have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hjd
    exact_mod_cast this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hqnat p hdq) with h | h
  · exact hpnat.one_lt.ne' h
  · omega

/-! ### 3-adic valuation of `t^s − 1` (infrastructure for step 3) -/

section ThreeAdicValuation

private lemma fact_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

attribute [local instance] fact_three

/-- The geometric sum identity in `ℕ`, subtraction-free. -/
private lemma geom_nat (v m : ℕ) :
    (v + 1) ^ m = (∑ i ∈ Finset.range m, (v + 1) ^ i) * v + 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ, ih]; ring

/-- If `u ≡ 1 [MOD 3]` and `3 ∤ m`, then `v₃(u^m − 1) = v₃(u − 1)`. -/
private lemma padicValNat_pow_sub_one_of_not_dvd {u m : ℕ} (hu : 1 ≤ u) (h1 : 3 ∣ u - 1)
    (hm : ¬ (3 ∣ m)) : padicValNat 3 (u ^ m - 1) = padicValNat 3 (u - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 ⊢
  set S := ∑ i ∈ Finset.range m, (v + 1) ^ i with hS
  have hgeom := geom_nat v m
  rw [← hS] at hgeom
  have hsub : (v + 1) ^ m - 1 = S * v := by omega
  rcases Nat.eq_zero_or_pos v with hv | hv
  · simp [hsub, hv]
  have hSm : S % 3 = m % 3 := by
    have : ∀ i, (v + 1) ^ i % 3 = 1 % 3 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
          rw [pow_succ, Nat.mul_mod, ih]
          omega
    rw [hS, Finset.sum_nat_mod]
    simp only [this]
    rw [← Finset.sum_nat_mod]
    simp [Finset.sum_const, Finset.card_range, Nat.mul_mod]
  have hS3 : ¬ (3 ∣ S) := by
    intro h
    exact hm (by omega)
  have hSne : S ≠ 0 := by
    intro h; rw [h] at hS3; exact hS3 ⟨0, rfl⟩
  rw [hsub, padicValNat.mul hSne hv.ne', padicValNat.eq_zero_of_not_dvd hS3]
  omega

/-- The cube step of lifting the exponent at `3`. -/
private lemma padicValNat_cube_le {z : ℕ} (hz : ¬ (3 ∣ z)) :
    padicValNat 3 (z ^ 3 - 1) ≤ padicValNat 3 (z - 1) + 1 := by
  rcases Nat.lt_or_ge z 2 with h | h
  · interval_cases z
    · simp at hz
    · simp
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hw : w ≠ 0 := by omega
  have hid : (w + 1) ^ 3 - 1 = w * ((w + 1) ^ 2 + (w + 1) + 1) := by
    have : (w + 1) ^ 3 = w * ((w + 1) ^ 2 + (w + 1) + 1) + 1 := by ring
    omega
  set Q := (w + 1) ^ 2 + (w + 1) + 1 with hQ
  have hQne : Q ≠ 0 := by positivity
  have hQ9 : ¬ (9 ∣ Q) := by
    have hkey : ∀ r < 9, r % 3 ≠ 0 → ((r ^ 2 + r + 1) % 9) ≠ 0 := by decide
    have hz9 : (w + 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have hz3 : ((w + 1) % 9) % 3 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : (3:ℕ) ∣ 9)]
      omega
    have := hkey _ hz9 hz3
    intro hdvd
    apply this
    have hbase : (w + 1) ≡ (w + 1) % 9 [MOD 9] := (Nat.mod_modEq (w + 1) 9).symm
    have hmod : Q % 9 = (((w + 1) % 9) ^ 2 + ((w + 1) % 9) + 1) % 9 :=
      ((hbase.pow 2).add hbase).add_right 1
    omega
  have hQle : padicValNat 3 Q ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : (3:ℕ) ^ 2 ∣ Q := (padicValNat_dvd_iff_le hQne).2 hc
    exact hQ9 (by norm_num at this ⊢; exact this)
  rw [hid, padicValNat.mul hw hQne]
  omega

/-- Iterating the cube step: `v₃(y^(3^w) − 1) ≤ v₃(y − 1) + w`. -/
private lemma padicValNat_pow_three_pow_le {y : ℕ} (hy : ¬ (3 ∣ y)) (w : ℕ) :
    padicValNat 3 (y ^ 3 ^ w - 1) ≤ padicValNat 3 (y - 1) + w := by
  induction w with
  | zero => simp
  | succ w ih =>
      have hz : ¬ (3 ∣ y ^ 3 ^ w) := by
        intro h
        exact hy (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
      have := padicValNat_cube_le hz
      have he : y ^ 3 ^ (w + 1) = (y ^ 3 ^ w) ^ 3 := by
        rw [← pow_mul, pow_succ]
      rw [he]
      omega

/-- **The bound.**  For `3 ∤ t` and `s ≥ 1`, `v₃(t^s − 1) ≤ v₃(t^2 − 1) + v₃(s)`. -/
private lemma padicValNat_pow_sub_one_le {t s : ℕ} (ht : ¬ (3 ∣ t)) (ht2 : 2 ≤ t)
    (hs : 1 ≤ s) :
    padicValNat 3 (t ^ s - 1) ≤ padicValNat 3 (t ^ 2 - 1) + padicValNat 3 s := by
  -- first pass to the even exponent `2s`
  have hA : 1 ≤ t ^ s := Nat.one_le_pow _ _ (by omega)
  have hstep : padicValNat 3 (t ^ s - 1) ≤ padicValNat 3 (t ^ (2 * s) - 1) := by
    obtain ⟨a, ha⟩ : ∃ a, t ^ s = a + 1 := ⟨t ^ s - 1, by omega⟩
    have hid : t ^ (2 * s) - 1 = a * (a + 2) := by
      have h1 : t ^ (2 * s) = (t ^ s) ^ 2 := by rw [← pow_mul, mul_comm]
      have h2 : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
      rw [h1, ha]; omega
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [hid, h, ha]
    · rw [hid, ha]
      simp only [Nat.add_sub_cancel]
      rw [padicValNat.mul h.ne' (by omega)]
      omega
  -- write `2 * s = 3 ^ w * m` with `3 ∤ m`; note `m` is even, so the base `t ^ m` is `≡ 1 mod 3`
  set w := padicValNat 3 s with hw
  have hspos : s ≠ 0 := by omega
  have hdvd : 3 ^ w ∣ s := pow_padicValNat_dvd
  obtain ⟨m₀, hm₀⟩ := hdvd
  have hm₀3 : ¬ (3 ∣ m₀) := by
    intro ⟨c, hc⟩
    have : 3 ^ (w + 1) ∣ s := ⟨c, by rw [hm₀, hc]; ring⟩
    have := (padicValNat_dvd_iff_le hspos).1 this
    omega
  have h2s : 2 * s = 3 ^ w * (2 * m₀) := by rw [hm₀]; ring
  have hm3 : ¬ (3 ∣ 2 * m₀) := by
    intro h
    exact hm₀3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h))
  set u := t ^ (2 * m₀) with hu
  have hune : ¬ (3 ∣ u) := by
    intro h
    exact ht (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
  have hu1 : 1 ≤ u := Nat.one_le_pow _ _ (by omega)
  have hpow : t ^ (2 * s) = u ^ 3 ^ w := by
    rw [hu, ← pow_mul, h2s]; ring_nf
  have hkey := padicValNat_pow_three_pow_le hune w
  rw [← hpow] at hkey
  -- `v₃(u − 1) ≤ v₃(t^2 − 1)`
  have hdvd3 : 3 ∣ t ^ 2 - 1 := by
    have : t % 3 = 1 ∨ t % 3 = 2 := by omega
    have h2 : t ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      rcases this with h | h <;> rw [h] <;> norm_num
    have : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hfin : padicValNat 3 (u - 1) = padicValNat 3 (t ^ 2 - 1) := by
    rw [hu]
    have he : t ^ (2 * m₀) = (t ^ 2) ^ m₀ := by rw [← pow_mul]
    rw [he]
    exact padicValNat_pow_sub_one_of_not_dvd (Nat.one_le_pow _ _ (by omega)) hdvd3 hm₀3
  omega

end ThreeAdicValuation

/-- **The `glCard` bound.**  If neither `t − 1` nor `t + 1` is divisible by `3 ^ e`, then
`v₃ |GL_n(𝔽_t)|` is bounded by the constant `n * (2 * e + n)`. -/
private lemma padicValNat_glCard_le {n t e : ℕ} (ht : ¬ (3 ∣ t)) (ht2 : 2 ≤ t)
    (h1 : ¬ (3 ^ e ∣ (t - 1))) (h2 : ¬ (3 ^ e ∣ (t + 1))) :
    padicValNat 3 (glCard n t) ≤ n * (2 * e + n) := by
  haveI := fact_three
  -- the 3-part of `t ^ 2 − 1`
  have ht1 : 1 ≤ t - 1 := by omega
  have hsq : t ^ 2 - 1 = (t - 1) * (t + 1) := by
    have : t ^ 2 = (t - 1) * (t + 1) + 1 := by
      obtain ⟨w, rfl⟩ : ∃ w, t = w + 2 := ⟨t - 2, by omega⟩
      have hw : w + 2 - 1 = w + 1 := by omega
      rw [hw]; ring
    omega
  have hv1 : padicValNat 3 (t - 1) < e := by
    by_contra hc
    exact h1 ((padicValNat_dvd_iff_le (by omega)).2 (by omega))
  have hv2 : padicValNat 3 (t + 1) < e := by
    by_contra hc
    exact h2 ((padicValNat_dvd_iff_le (by omega)).2 (by omega))
  have hsqv : padicValNat 3 (t ^ 2 - 1) ≤ 2 * e := by
    rw [hsq, padicValNat.mul (by omega) (by omega)]
    omega
  -- each factor
  have hfac : ∀ i : Fin n, padicValNat 3 (t ^ n - t ^ (i : ℕ)) ≤ 2 * e + n := by
    intro i
    obtain ⟨c, hc⟩ : ∃ c, n = (i : ℕ) + c := ⟨n - (i : ℕ), by omega⟩
    have hc1 : 1 ≤ c := by have := i.isLt; omega
    have hsplit : t ^ n - t ^ (i : ℕ) = t ^ (i : ℕ) * (t ^ c - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, ← hc]
    have hti : ¬ (3 ∣ t ^ (i : ℕ)) := by
      intro h
      exact ht (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    have htc : 1 ≤ t ^ c - 1 := by
      have : t ^ 1 ≤ t ^ c := Nat.pow_le_pow_right (by omega) hc1
      simp only [pow_one] at this
      omega
    rw [hsplit, padicValNat.mul (by positivity) (by omega),
      padicValNat.eq_zero_of_not_dvd hti]
    have hb := padicValNat_pow_sub_one_le ht ht2 hc1
    have hlog : padicValNat 3 c ≤ n := by
      refine le_trans (padicValNat_le_nat_log c) ?_
      exact le_trans (Nat.log_le_self 3 c) (by omega)
    omega
  -- assemble the product
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), t ^ n - t ^ (i : ℕ) ≠ 0 := by
    intro i _
    have : t ^ (i : ℕ) < t ^ n := Nat.pow_lt_pow_right (by omega) i.isLt
    omega
  have hprod : padicValNat 3 (glCard n t) = ∑ i : Fin n, padicValNat 3 (t ^ n - t ^ (i : ℕ)) := by
    rw [glCard, ← Nat.factorization_def _ (by norm_num), Nat.factorization_prod hne,
      Finset.sum_apply']
    exact Finset.sum_congr rfl fun i _ => Nat.factorization_def _ (by norm_num)
  rw [hprod]
  calc ∑ i : Fin n, padicValNat 3 (t ^ n - t ^ (i : ℕ))
      ≤ ∑ _i : Fin n, (2 * e + n) := Finset.sum_le_sum fun i _ => hfac i
    _ = n * (2 * e + n) := by simp [mul_comm]

/-- **Step 3.**  Under the Gauss congruence, a trace sequence `tr C^(3^k)` that is eventually prime
and increasing converges to `±1` in `ℤ₃`. -/
theorem threeAdic_pm_one (hG : GaussCongruenceTrace) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0) {k₀ : ℕ}
    (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (C ^ (3 ^ k)).trace ≡ 1 [ZMOD 3 ^ e] ∨ (C ^ (3 ^ k)).trace ≡ -1 [ZMOD 3 ^ e] := by
  haveI := fact_three
  intro e
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  -- the residue of `t k` modulo `3 ^ e` is eventually constant (Gauss congruence)
  have hgauss : ∀ k, ((3 : ℤ) ^ (k + 1)) ∣ t (k + 1) - t k := by
    intro k
    have := hG n C 3 k (by norm_num)
    push_cast at this ⊢
    exact this
  have hconst : ∀ k, e ≤ k → ∀ l, k ≤ l → t l ≡ t k [ZMOD 3 ^ e] := by
    intro k hk l hl
    induction l, hl using Nat.le_induction with
    | base => rfl
    | succ l hl ih =>
        refine Int.ModEq.trans ?_ ih
        have hd : ((3 : ℤ) ^ e) ∣ t (l + 1) - t l :=
          dvd_trans (pow_dvd_pow 3 (by omega)) (hgauss l)
        exact (Int.modEq_iff_dvd.2 (by simpa using dvd_neg.2 hd))
  -- pick a large index
  obtain ⟨K₂, hK₂⟩ := lt_padicValNat_glCard C hdet hprime hmono
  obtain ⟨K₃, hK₃0, hK₃'⟩ := trace_eventually_gt C hmono 3
  have hK₃ : ∀ k ≥ K₃, (3 : ℤ) < t k := hK₃'
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = max (max K₂ K₃) (max e (n * (2 * e + n) + 1)) := ⟨_, rfl⟩
  have hk₁K₂ : K₂ ≤ k₁ := by omega
  have hk₁K₃ : K₃ ≤ k₁ := by omega
  have hk₁e : e ≤ k₁ := by omega
  have hk₁n : n * (2 * e + n) < k₁ := by omega
  have hk₁k₀ : k₀ ≤ k₁ := le_trans hK₃0 hk₁K₃
  -- the witness value
  have htgt : (3 : ℤ) < t k₁ := hK₃ k₁ hk₁K₃
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = t k₁ := ⟨(t k₁).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hT4 : 4 ≤ T := by omega
  have hTtoNat : (t k₁).toNat = T := by omega
  have hTprime : T.Prime := by
    have := hprime k₁ hk₁k₀
    have hnat : (t k₁).natAbs = T := by omega
    rw [Int.prime_iff_natAbs_prime, hnat] at this
    exact this
  have hT3 : ¬ (3 ∣ T) := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hTprime 3 h)
    omega
  -- the key claim at `k₁`
  have hclaim : t k₁ ≡ 1 [ZMOD 3 ^ e] ∨ t k₁ ≡ -1 [ZMOD 3 ^ e] := by
    by_contra hc
    push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hcast3 : (((3:ℕ) ^ e : ℕ) : ℤ) = (3 : ℤ) ^ e := by push_cast; ring
    have h1 : ¬ ((3:ℕ) ^ e ∣ (T - 1)) := by
      intro h
      apply hc1
      refine Int.ModEq.symm (Int.modEq_iff_dvd.2 ?_)
      have := Int.natCast_dvd_natCast.2 h
      rw [hcast3, Nat.cast_sub (by omega)] at this
      simpa [hT] using this
    have h2 : ¬ ((3:ℕ) ^ e ∣ (T + 1)) := by
      intro h
      apply hc2
      refine Int.ModEq.symm (Int.modEq_iff_dvd.2 ?_)
      have hd := Int.natCast_dvd_natCast.2 h
      rw [hcast3] at hd
      push_cast at hd
      rw [hT] at hd
      simpa using hd
    have hbound := padicValNat_glCard_le (n := n) (e := e) hT3 (by omega) h1 h2
    have := hK₂ k₁ hk₁K₂
    rw [hTtoNat] at this
    omega
  refine ⟨k₁, fun k hk => ?_⟩
  have := hconst k₁ hk₁e k hk
  rcases hclaim with h | h
  · exact Or.inl (this.trans h)
  · exact Or.inr (this.trans h)

/-! ### The integer companion matrix of a monic cubic (infrastructure for step 4) -/

section Companion

/-- The companion matrix of `X³ + aX² + bX + c`, acting on `ℤ[X]/(f)` in the basis `1, X, X²`. -/
def companion3 (a b c : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, -c; 1, 0, -b; 0, 1, -a]

@[simp] lemma companion3_det (a b c : ℤ) : (companion3 a b c).det = -c := by
  simp [companion3, Matrix.det_fin_three]

@[simp] lemma companion3_trace (a b c : ℤ) : (companion3 a b c).trace = -a := by
  simp [companion3, Matrix.trace_fin_three]

lemma companion3_sq (a b c : ℤ) :
    companion3 a b c ^ 2 = !![0, -c, c * a; 0, -b, -c + b * a; 1, -a, -b + a * a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion3, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[simp] lemma companion3_trace_sq (a b c : ℤ) :
    (companion3 a b c ^ 2).trace = a ^ 2 - 2 * b := by
  rw [companion3_sq, Matrix.trace_fin_three]
  simp
  ring

/-- Cayley–Hamilton for the companion matrix, by direct computation. -/
lemma companion3_cube (a b c : ℤ) :
    companion3 a b c ^ 3 =
      -(a • companion3 a b c ^ 2) - b • companion3 a b c - c • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  rw [pow_succ, companion3_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.neg_apply, Matrix.intCast_apply, Matrix.diagonal_apply,
      companion3_sq] <;> ring

/-- The trace sequence of the companion matrix satisfies the defining linear recurrence. -/
lemma companion3_trace_rec (a b c : ℤ) (N : ℕ) :
    ((companion3 a b c) ^ (N + 3)).trace =
      -a * ((companion3 a b c) ^ (N + 2)).trace - b * ((companion3 a b c) ^ (N + 1)).trace
        - c * ((companion3 a b c) ^ N).trace := by
  set C := companion3 a b c with hC
  have h : C ^ (N + 3) = -(a • C ^ (N + 2)) - b • C ^ (N + 1) - c • C ^ N := by
    have h3 : C ^ (N + 3) = C ^ N * C ^ 3 := by rw [← pow_add]
    rw [h3, hC, companion3_cube]
    simp only [mul_sub, Matrix.mul_smul, mul_neg, ← hC]
    rw [show C ^ N * C ^ 2 = C ^ (N + 2) by rw [← pow_add], show C ^ N * C = C ^ (N + 1) by
      rw [← pow_succ]]
    simp
  rw [h]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_neg, smul_eq_mul]
  ring

/-- **The key identity.**  If `x, y, z` are the roots of `X³ + aX² + bX + c` (given by their Vieta
relations), then `tr (companion3 a b c)^N = xᴺ + yᴺ + zᴺ`. -/
lemma companion3_trace_pow {a b c : ℤ} {x y z : ℂ}
    (h1 : x + y + z = -(a : ℂ)) (h2 : x * y + x * z + y * z = (b : ℂ))
    (h3 : x * y * z = -(c : ℂ)) (N : ℕ) :
    (((companion3 a b c) ^ N).trace : ℂ) = x ^ N + y ^ N + z ^ N := by
  have hroot : ∀ w : ℂ, w = x ∨ w = y ∨ w = z →
      w ^ 3 = -(a : ℂ) * w ^ 2 - (b : ℂ) * w - (c : ℂ) := by
    rintro w (rfl | rfl | rfl)
    · linear_combination w ^ 2 * h1 - w * h2 + h3
    · linear_combination w ^ 2 * h1 - w * h2 + h3
    · linear_combination w ^ 2 * h1 - w * h2 + h3
  have hstep : ∀ (w : ℂ), w = x ∨ w = y ∨ w = z → ∀ N : ℕ,
      w ^ (N + 3) = -(a : ℂ) * w ^ (N + 2) - (b : ℂ) * w ^ (N + 1) - (c : ℂ) * w ^ N := by
    intro w hw N
    have hc := hroot w hw
    have he : w ^ (N + 3) = w ^ N * w ^ 3 := by ring
    rw [he, hc]; ring
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp; norm_num
    | 1 =>
        rw [pow_one, companion3_trace]
        push_cast
        linear_combination -h1
    | 2 =>
        rw [companion3_trace_sq]
        push_cast
        linear_combination ((a : ℂ) - x - y - z) * h1 + 2 * h2
    | (N + 3) =>
        have e0 := ih N (by omega)
        have e1 := ih (N + 1) (by omega)
        have e2 := ih (N + 2) (by omega)
        rw [companion3_trace_rec]
        push_cast
        rw [e0, e1, e2, hstep x (Or.inl rfl) N, hstep y (Or.inr (Or.inl rfl)) N,
          hstep z (Or.inr (Or.inr rfl)) N]
        ring

end Companion

/-- **Vieta for a cubic Pisot number.**  The minimal polynomial of `β` over `ℤ` is
`X³ + aX² + bX + c`, whose complex roots are `β, u, v`.

TODO: proved next lap.  Route: `minpoly.isIntegrallyClosed_eq_field_fractions'` puts the minimal
polynomial over `ℤ`; it is monic of degree 3 and splits over `ℂ` with root multiset
`β ::ₘ otherConj β = {β, u, v}` (`card_otherConj_add_one`), so
`eq_prod_roots_of_monic_of_splits_id` expands it as `(X − β)(X − u)(X − v)` and the coefficients
give the three relations.  `c ≠ 0` because an irreducible cubic has nonzero constant term. -/
private lemma exists_vieta_of_cubic_pisot {β : ℝ} (hP : IsPisot β)
    (h3 : (minpoly ℚ β).natDegree = 3) {u v : ℂ} (huv : otherConj β = {u, v}) :
    ∃ a b c : ℤ, c ≠ 0 ∧ (β : ℂ) + u + v = -(a : ℂ) ∧
      (β : ℂ) * u + (β : ℂ) * v + u * v = (b : ℂ) ∧ (β : ℂ) * u * v = -(c : ℂ) := by
  sorry

/-- **Step 4: if the least Mills constant is algebraic, its primes tend to `±1` in `ℤ₃`.** -/
theorem mills_threeAdic (hGc : GaussCongruenceTrace)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) (halg : IsAlgebraic ℚ A) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨ (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e] := by
  obtain ⟨⟨hA1, hAm⟩, hmin⟩ := hA
  have hA : IsMinMills A := ⟨⟨hA1, hAm⟩, hmin⟩
  -- Saito's dichotomy; the transcendental branch contradicts `halg`
  rcases transcendental_or_pisot hB hM hD hG hA with htr | ⟨m, hm, hP, h3⟩
  · exact absurd halg htr
  set β : ℝ := A ^ ((3:ℕ) ^ m) with hβdef
  have hint : IsIntegral ℚ β := hP.2.1.tower_top
  -- the two other conjugates
  have hc2 : Multiset.card (otherConj β) = 2 := by
    have := card_otherConj_add_one hint; omega
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.1 hc2
  obtain ⟨a, b, c, hcne, hvi1, hvi2, hvi3⟩ := exists_vieta_of_cubic_pisot hP h3 huv
  obtain ⟨C, hCdef⟩ : ∃ C, C = companion3 a b c := ⟨_, rfl⟩
  have hdet : C.det ≠ 0 := by rw [hCdef, companion3_det]; omega
  have htrace : ∀ N : ℕ, (((C ^ N).trace : ℤ) : ℂ) = (β : ℂ) ^ N + u ^ N + v ^ N := by
    intro N; rw [hCdef]; exact companion3_trace_pow hvi1 hvi2 hvi3 N
  -- the Mills digit facts
  have h36 := saito_lemma36C (c := 3) hB hM (by norm_num) hA
  have hμ0 : (0:ℝ) < (19 * ((3:ℕ):ℝ)) / 40 - 1 := by norm_num
  have hK0 : (0:ℝ) < (2:ℝ) ^ ((19 * ((3:ℕ):ℝ)) / 40) := Real.rpow_pos_of_pos (by norm_num) _
  have hfrac : ∀ᶠ k : ℕ in atTop, A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2 := by
    filter_upwards [decay_of_lemma36C (c := 3) (by norm_num) hA1 hAm h36,
      eventually_rpow_neg_lt (c := 3) hA1 (by norm_num) hμ0 hK0 (by norm_num : (0:ℝ) < 1 / 2)]
      with k hk hk2
    exact lt_of_le_of_lt hk.2 hk2
  have hcube : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊) ^ 3 < ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊ := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact mdigitC_pow_lt (c := 3) (by norm_num) hA1 hAm j
  -- the eventually negative conjugate power sum
  obtain ⟨i₀, hi₀⟩ := pair_pow_sum_re_neg hA1 hP huv hcube hfrac hm
  -- identify `tr C^(3^i)` with the Mills prime `⌊A^(3^(m+i))⌋₊`
  have hfloor : ∀ i ≥ i₀, ((C ^ ((3:ℕ) ^ i)).trace : ℤ) = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ) := by
    intro i hi
    obtain ⟨σ, hsu, hσneg, hσabs, hA2, -⟩ := hi₀ i hi
    have hbeta : (β : ℝ) ^ ((3:ℕ) ^ i) = A ^ ((3:ℕ) ^ (m + i)) := by
      rw [hβdef, ← pow_mul, ← pow_add]
    have hreal : (((C ^ ((3:ℕ) ^ i)).trace : ℤ) : ℝ) = A ^ ((3:ℕ) ^ (m + i)) + σ := by
      have h := htrace ((3:ℕ) ^ i)
      rw [add_assoc, hsu] at h
      have h2 : (((C ^ ((3:ℕ) ^ i)).trace : ℤ) : ℂ) =
          (((A ^ ((3:ℕ) ^ (m + i)) + σ : ℝ)) : ℂ) := by
        rw [h, ← hbeta]
        push_cast
        ring
      exact_mod_cast h2
    -- `σ ∈ (−1/2, 0)`, so the floor of `A^(3^(m+i))` is the trace
    have hTpos : (0:ℝ) < ((C ^ ((3:ℕ) ^ i)).trace : ℤ) := by
      rw [hreal]
      have : |σ| < 1 / 2 := hσabs
      have := abs_lt.1 this
      linarith
    obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = ((C ^ ((3:ℕ) ^ i)).trace : ℤ) :=
      ⟨((C ^ ((3:ℕ) ^ i)).trace).toNat, Int.toNat_of_nonneg (by exact_mod_cast hTpos.le)⟩
    have hTr : (T : ℝ) = A ^ ((3:ℕ) ^ (m + i)) + σ := by
      rw [← hreal]; exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hT
    have habs := abs_lt.1 hσabs
    have hfl : ⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ = T := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> [linarith; linarith]
    rw [hfl, ← hT]
  -- primality and monotonicity of the trace sequence
  have hprime : ∀ k ≥ i₀, Prime ((C ^ ((3:ℕ) ^ k)).trace) := by
    intro k hk
    rw [hfloor k hk]
    have : Prime ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ := hAm ⟨m + k, by omega⟩
    exact_mod_cast Nat.prime_iff_prime_int.1 (Nat.prime_iff.2 this)
  have hmono : ∀ k ≥ i₀, (C ^ ((3:ℕ) ^ k)).trace < (C ^ ((3:ℕ) ^ (k + 1))).trace := by
    intro k hk
    rw [hfloor k hk, hfloor (k + 1) (by omega)]
    have hcu := hcube (m + k) (by omega)
    have hk2 : 2 ≤ ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ := (Nat.prime_iff.2 (hAm ⟨m + k, by omega⟩)).two_le
    have hmk : m + (k + 1) = (m + k) + 1 := by omega
    rw [hmk]
    have : ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ < ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 3 := by
      calc ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ = ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 1 := (pow_one _).symm
        _ < ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    exact_mod_cast lt_trans this hcu
  -- apply step 3
  intro e
  obtain ⟨K, hK⟩ := threeAdic_pm_one hGc C hdet hprime hmono e
  refine ⟨m + max K i₀, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = m + i := ⟨k - m, by omega⟩
  have hi : i ≥ max K i₀ := by omega
  have := hK i (by omega)
  rwa [hfloor i (by omega)] at this

/-- **Step 5.**  If for some `e` infinitely many Mills primes avoid `±1 mod 3^e`, the least Mills
constant is transcendental. -/
theorem transcendental_of_not_pm_one (hGc : GaussCongruenceTrace)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) {e : ℕ}
    (h : ∃ᶠ k in atTop, ¬ ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e])) :
    Transcendental ℚ A := by
  by_contra hc
  rw [Transcendental, not_not] at hc
  obtain ⟨K, hK⟩ := mills_threeAdic hGc hB hM hD hG hA hc e
  have hev : ∀ᶠ k : ℕ in atTop, ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e]) := eventually_atTop.2 ⟨K, hK⟩
  obtain ⟨k, hk1, hk2⟩ := (h.and_eventually hev).exists
  exact hk1 hk2

end LeanFormalizations.Mills.ThreeAdic
