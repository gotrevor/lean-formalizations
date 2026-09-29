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
  have growth : ∀ k, k₀ ≤ k → t k₀ + ((k : ℤ) - (k₀ : ℤ)) ≤ t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have := hmono' k hk
        push_cast
        push_cast at ih
        omega
  have unbounded : ∀ B : ℤ, ∃ K, k₀ ≤ K ∧ ∀ k ≥ K, B < t k := by
    intro B
    refine ⟨k₀ + (B - t k₀ + 1).toNat, by omega, ?_⟩
    intro k hk
    have := growth k (by omega)
    have h2 : ((k₀ + (B - t k₀ + 1).toNat : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    push_cast at h2
    omega
  obtain ⟨K, hK0, hKB⟩ := unbounded |C.det|
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
