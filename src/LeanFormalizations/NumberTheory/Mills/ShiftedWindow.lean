/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMills

/-!
# Phase 46: the 3-adic window for prime traces along `3^n − 2` (first sub-node of `ShiftedTraceRigidity`)

`PROOF-THEOREM-E.md` Step 3 in Lean, for an arbitrary `3 × 3` integer matrix.  If
`tr C^(3^n − 2)` is prime for all large `n` (and grows), then for all large `n` it is `≡ ±1`
modulo `3^(n/3 − 1)`.

## Route
1. For large `n`, put `p = |tr C^(3^n − 2)|`, a prime.  If `padicValNat 3 (glCard 3 p) ≤ n`, then
   (`exists_entry_pow_congr_mul`-style: the order of `C` mod `p` divides `3^n(3^(kj) − 1)` for a
   suitable `j ≥ 1` and all `k`) `p ∣ tr C^(3^(n+kj) − 2) − tr C^(3^n − 2)`, via
   `TheoremDGround.dvd_trace_sub_of_orderOf_dvd`.  So `p` divides a later prime trace of strictly
   larger absolute value (growth; use a large `k`): contradiction.  Hence
   `n < padicValNat 3 (glCard 3 p)`.
2. `TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard` gives `i ∈ {1, 2, 3}` with
   `3^(n/3) ∣ p^i − 1`.
   - `i = 1`: done.
   - `i = 2`: `3 ∤` one of `p ∓ 1`, since they differ by 2.
   - `i = 3`: `p³ ≡ 1 (mod 3^e)` gives `p ≡ 1 (mod 3^(e−1))`, as `p² + p + 1 ≡ 3 (mod 9)` when `p ≡ 1 (mod 3)`, and `p ≡ 2 (mod 3)` is impossible.
3. Transfer from `p = |t|` to `t` (signs: `±1` is symmetric).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.ShiftedWindow

open LeanFormalizations.Mills.ThreeAdic Filter Matrix

/-! ### Elementary arithmetic helpers -/

/-- `B(s+1) − 2 − (B − 2) = B·s` for `B ≥ 2`. -/
lemma sub_two_sub_two (B s : ℕ) (hB : 2 ≤ B) : B * (s + 1) - 2 - (B - 2) = B * s := by
  have h : B * (s + 1) = B * s + B := by ring
  omega

/-- No residue mod `9` satisfies `y² + y + 1 = 0`; hence `9 ∤ p² + p + 1` for every `p`. -/
lemma nine_not_dvd_sq_add_self_add_one (p : ℕ) : ¬ (9 ∣ p ^ 2 + p + 1) := by
  intro hd
  have hz : ((p ^ 2 + p + 1 : ℕ) : ZMod 9) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  revert hz
  generalize ((p : ZMod 9)) = y
  revert y
  decide

/-- The `3`-adic valuation of `p² + p + 1` is at most `1`. -/
lemma factorization_three_sq_add_self_add_one_le (p : ℕ) :
    (p ^ 2 + p + 1).factorization 3 ≤ 1 := by
  by_contra hcon
  have hne : p ^ 2 + p + 1 ≠ 0 := by positivity
  have hdvd : 3 ^ 2 ∣ p ^ 2 + p + 1 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).2 (by omega)
  exact nine_not_dvd_sq_add_self_add_one p (by norm_num at hdvd ⊢; exact hdvd)

/-- **Step 2 (the pure arithmetic of the window).**  If `3^e ∣ p^i − 1` for some `1 ≤ i ≤ 3` and
`p` is not divisible by `3`, then `p ≡ ±1 (mod 3^(e−1))`. -/
lemma dvd_sub_or_add_of_dvd_pow_sub_one {p e i : ℕ} (hp2 : 2 ≤ p)
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) (h : 3 ^ e ∣ p ^ i - 1) :
    3 ^ (e - 1) ∣ p - 1 ∨ 3 ^ (e - 1) ∣ p + 1 := by
  have hstep : 3 ^ (e - 1) ∣ 3 ^ e := pow_dvd_pow 3 (by omega)
  interval_cases i
  · -- `i = 1`
    left
    exact hstep.trans (by simpa using h)
  · -- `i = 2`: `3` cannot divide both `p − 1` and `p + 1`
    have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hp2
      have h1 : p - 1 = s + 1 := by omega
      have e1 : (p - 1) * (p + 1) + 1 = p ^ 2 := by rw [h1, hs]; ring
      exact Nat.sub_eq_of_eq_add e1.symm
    rw [hfac] at h
    have hor : ¬ (3 ∣ p - 1) ∨ ¬ (3 ∣ p + 1) := by
      by_contra hc
      push_neg at hc
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
      omega
    rcases hor with hnd | hnd
    · right
      have hcop : Nat.Coprime (3 ^ e) (p - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
      exact hstep.trans (hcop.dvd_of_dvd_mul_left h)
    · left
      have hcop : Nat.Coprime (3 ^ e) (p + 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
      exact hstep.trans (hcop.dvd_of_dvd_mul_right h)
  · -- `i = 3`: `v₃(p² + p + 1) ≤ 1`, so `v₃(p − 1) ≥ e − 1`
    left
    have hfac : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hp2
      have h1 : p - 1 = s + 1 := by omega
      have e1 : (p - 1) * (p ^ 2 + p + 1) + 1 = p ^ 3 := by rw [h1, hs]; ring
      exact Nat.sub_eq_of_eq_add e1.symm
    rw [hfac] at h
    have hA : p - 1 ≠ 0 := by omega
    have hB : p ^ 2 + p + 1 ≠ 0 := by positivity
    have hprod : ((p - 1) * (p ^ 2 + p + 1)).factorization 3
        = (p - 1).factorization 3 + (p ^ 2 + p + 1).factorization 3 := by
      rw [Nat.factorization_mul hA hB]; rfl
    have hle : e ≤ ((p - 1) * (p ^ 2 + p + 1)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by positivity)).1 h
    have hB1 := factorization_three_sq_add_self_add_one_le p
    rw [hprod] at hle
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hA).2 (by omega)

/-! ### The order of a matrix mod `p` along the tower -/

/-- If `v_c(|GL_d(𝔽_p)|) ≤ m` then there is a period `j ≥ 1` such that every element of
`GL_d(𝔽_p)` has order dividing `c^m (c^(kj) − 1)` for every `k ≥ 1`. -/
lemma exists_period_orderOf_dvd (d : ℕ) {p c m : ℕ} [Fact p.Prime] (hc : c.Prime)
    (hv : padicValNat c (glCard d p) ≤ m) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ, ∀ u : GL (Fin d) (ZMod p),
      orderOf u ∣ c ^ m * (c ^ (k * j) - 1) := by
  obtain ⟨N, hN⟩ : ∃ N, N = glCard d p := ⟨_, rfl⟩
  have hcard : Nat.card (GL (Fin d) (ZMod p)) = glCard d p := by
    rw [Matrix.card_GL_field]; simp [glCard, ZMod.card]
  have hNpos : 0 < N := by rw [hN, ← hcard]; exact Nat.card_pos
  have hNne : N ≠ 0 := hNpos.ne'
  obtain ⟨v, hvdef⟩ : ∃ v, v = padicValNat c N := ⟨_, rfl⟩
  have hvm : v ≤ m := by rw [hvdef, hN]; exact hv
  obtain ⟨M, hM⟩ : ∃ M, M = N / c ^ v := ⟨_, rfl⟩
  have hfac : N.factorization c = v := by rw [hvdef, Nat.factorization_def _ hc]
  have hsplit : c ^ v * M = N := by
    have hmul := Nat.ordProj_mul_ordCompl_eq_self N c
    rw [hfac] at hmul
    rw [hM, hfac] at *
    exact hmul
  have hMdvd : ¬ (c ∣ M) := by
    have hnd := Nat.not_dvd_ordCompl hc hNne
    rw [hfac] at hnd
    rwa [hM]
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hsplit; exact absurd hsplit.symm hNne
    · exact h
  refine ⟨Nat.totient M, Nat.totient_pos.2 hMpos, fun k u => ?_⟩
  have hordN : orderOf u ∣ N := by
    rw [hN, ← hcard]; exact orderOf_dvd_natCard u
  refine hordN.trans ?_
  rw [← hsplit]
  refine mul_dvd_mul (pow_dvd_pow c hvm) ?_
  -- `M ∣ c^(k·j) − 1`
  have hcop : Nat.Coprime c M := (Nat.Prime.coprime_iff_not_dvd hc).2 hMdvd
  have hmod : c ^ Nat.totient M ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcop
  have hmod' : c ^ (k * Nat.totient M) ≡ 1 [MOD M] := by
    have : c ^ (k * Nat.totient M) = (c ^ Nat.totient M) ^ k := by
      rw [← pow_mul, mul_comm]
    rw [this]
    simpa using hmod.pow k
  have h1 : 1 ≤ c ^ (k * Nat.totient M) := Nat.one_le_pow _ _ hc.pos
  exact (Nat.modEq_iff_dvd' h1).1 hmod'.symm

/-! ### The frozen statement -/

theorem window_of_eventually_prime (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    (hgrow : Tendsto (fun n : ℕ => |(C ^ (3 ^ n - 2)).trace|) atTop atTop)
    (hprime : ∀ᶠ n in atTop, Prime (C ^ (3 ^ n - 2)).trace) :
    ∀ᶠ n in atTop, (3 : ℤ) ^ (n / 3 - 1) ∣ (C ^ (3 ^ n - 2)).trace - 1 ∨
      (3 : ℤ) ^ (n / 3 - 1) ∣ (C ^ (3 ^ n - 2)).trace + 1 := by
  classical
  -- thresholds: eventual primality, and growth past `|det C| + 4`
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hprime
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop (|C.det| + 4))
  filter_upwards [eventually_ge_atTop (max (max N0 N1) 1)] with n hn
  have hnN0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hpr : Prime (C ^ (3 ^ n - 2)).trace := hN0 n hnN0
  have hb : |C.det| + 4 ≤ |(C ^ (3 ^ n - 2)).trace| := hN1 n hnN1
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = (C ^ (3 ^ n - 2)).trace.natAbs := ⟨_, rfl⟩
  have hpp : p.Prime := by rw [hpdef]; exact Int.prime_iff_natAbs_prime.1 hpr
  have habs : |(C ^ (3 ^ n - 2)).trace| = (p : ℤ) := by
    rw [hpdef]; exact Int.abs_eq_natAbs _
  have hdnn : (0:ℤ) ≤ |C.det| := abs_nonneg _
  have hp4 : (4:ℤ) ≤ (p : ℤ) := by rw [← habs]; linarith
  have hp2 : 2 ≤ p := by exact_mod_cast (by linarith : (2:ℤ) ≤ (p:ℤ))
  have hp3 : p ≠ 3 := by
    intro h
    rw [h] at hp4; norm_num at hp4
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro hdvd
    have h2 : (p : ℤ) ∣ |C.det| := (dvd_abs _ _).2 hdvd
    have := Int.le_of_dvd (abs_pos.2 hdet) h2
    linarith
  -- Step 1: the `3`-adic valuation of `|GL₃(𝔽_p)|` must exceed `n`
  have hval : n < padicValNat 3 (glCard 3 p) := by
    by_contra hcon
    push_neg at hcon
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨j, hj1, hj⟩ := exists_period_orderOf_dvd 3 Nat.prime_three hcon
    obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop ((p : ℤ) + 1))
    obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = max N0 N2 := ⟨_, rfl⟩
    obtain ⟨n', hn'def⟩ : ∃ n' : ℕ, n' = n + K * j := ⟨_, rfl⟩
    have hKj : K ≤ K * j := Nat.le_mul_of_pos_right _ hj1
    have hn'K : K ≤ n' := by omega
    have hprime' : Prime (C ^ (3 ^ n' - 2)).trace := hN0 n' (by rw [hKdef] at hn'K; omega)
    have hbig' : (p : ℤ) + 1 ≤ |(C ^ (3 ^ n' - 2)).trace| :=
      hN2 n' (by rw [hKdef] at hn'K; omega)
    -- the exponent difference is `3^n (3^(K j) − 1)`
    have hB2 : 2 ≤ 3 ^ n := le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
    have hs1 : (1 : ℕ) ≤ 3 ^ (K * j) := Nat.one_le_pow _ _ (by norm_num)
    have key := sub_two_sub_two (3 ^ n) (3 ^ (K * j) - 1) hB2
    have heq : 3 ^ n * (3 ^ (K * j) - 1 + 1) = 3 ^ n' := by
      rw [Nat.sub_add_cancel hs1, hn'def, pow_add]
    rw [heq] at key
    have hbb : 3 ^ n - 2 ≤ 3 ^ n' - 2 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 2
    have hdv : (p : ℤ) ∣ (C ^ (3 ^ n' - 2)).trace - (C ^ (3 ^ n - 2)).trace :=
      TheoremDGround.dvd_trace_sub_of_orderOf_dvd C hpp hdetp hbb
        (fun D _ => by rw [key]; exact hj K D)
    have hdvn : (p : ℤ) ∣ (C ^ (3 ^ n - 2)).trace := by
      rw [hpdef]; exact Int.natAbs_dvd.2 dvd_rfl
    have hdvn' : (p : ℤ) ∣ (C ^ (3 ^ n' - 2)).trace := by
      have := dvd_add hdv hdvn
      simpa using this
    -- `p` divides a strictly larger prime: impossible
    have hq : ((C ^ (3 ^ n' - 2)).trace.natAbs).Prime := Int.prime_iff_natAbs_prime.1 hprime'
    have hpq : p ∣ (C ^ (3 ^ n' - 2)).trace.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hdvn'
      simpa using this
    have heqpq : p = (C ^ (3 ^ n' - 2)).trace.natAbs :=
      (Nat.prime_dvd_prime_iff_eq hpp hq).1 hpq
    have habs' : |(C ^ (3 ^ n' - 2)).trace| = ((C ^ (3 ^ n' - 2)).trace.natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [habs', ← heqpq] at hbig'
    linarith
  -- Step 2: the window lemma plus the elementary arithmetic
  obtain ⟨i, hi1, hi3, hdvdi⟩ :=
    TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard Nat.prime_three hpp hp3
      (by norm_num) hval
  have hone : 1 ≤ p ^ i := Nat.one_le_pow _ _ hpp.pos
  have hdvdN : 3 ^ (n / 3) ∣ p ^ i - 1 := by
    have hc : ((p ^ i - 1 : ℕ) : ℤ) = (p : ℤ) ^ i - 1 := by
      rw [Nat.cast_sub hone]; push_cast; ring
    have hz : ((3 ^ (n / 3) : ℕ) : ℤ) ∣ ((p ^ i - 1 : ℕ) : ℤ) := by
      rw [hc]; push_cast; exact hdvdi
    exact_mod_cast hz
  have hwin := dvd_sub_or_add_of_dvd_pow_sub_one hp2 hi1 hi3 hdvdN
  -- Step 3: transfer from `p = |t|` to `t`
  have hsign : (C ^ (3 ^ n - 2)).trace = (p : ℤ) ∨ (C ^ (3 ^ n - 2)).trace = -(p : ℤ) :=
    (abs_eq (by positivity)).1 habs
  have hp1 : 1 ≤ p := by omega
  rcases hwin with hw | hw
  · have hwz : (3 : ℤ) ^ (n / 3 - 1) ∣ (p : ℤ) - 1 := by
      have hc : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by rw [Nat.cast_sub hp1]; push_cast; ring
      have hz : ((3 ^ (n / 3 - 1) : ℕ) : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hw
      rw [hc] at hz; exact_mod_cast hz
    rcases hsign with hs | hs
    · exact Or.inl (by rw [hs]; exact hwz)
    · refine Or.inr ?_
      have : (C ^ (3 ^ n - 2)).trace + 1 = -((p : ℤ) - 1) := by rw [hs]; ring
      rw [this]; exact dvd_neg.2 hwz
  · have hwz : (3 : ℤ) ^ (n / 3 - 1) ∣ (p : ℤ) + 1 := by
      have hz : ((3 ^ (n / 3 - 1) : ℕ) : ℤ) ∣ ((p + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hw
      push_cast at hz; exact_mod_cast hz
    rcases hsign with hs | hs
    · exact Or.inr (by rw [hs]; exact hwz)
    · refine Or.inl ?_
      have : (C ^ (3 ^ n - 2)).trace - 1 = -((p : ℤ) + 1) := by rw [hs]; ring
      rw [this]; exact dvd_neg.2 hwz

end LeanFormalizations.Mills.ShiftedWindow
