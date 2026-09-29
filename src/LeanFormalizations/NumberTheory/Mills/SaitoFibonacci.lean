/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SharedConjecture

/-!
# Saito's Problem 1.8: `F(2^n) + h` is composite infinitely often (phase 32)

K. Saito, *Intervals without primes near an iterated linear recurrence sequence*,
arXiv:2504.14968, Problem 1.8: *"Let (F(n)) be the Fibonacci sequence.  Let h be an arbitrary
integer.  Prove or disprove that the numbers F(2^n) + h are composite for infinitely many n."*

We prove it for every `h`, unconditionally.  Full argument: `PROBE-SAITO-FIBONACCI.md`.

## Route
- **Odd `h`**: `fib_two_pow_odd`, so `F(2^n) + h` is even and eventually `> 2`.
- **`h = 0`**: `Nat.fib_dvd` gives `F(2^n) ∣ F(2^(n+1))`, with `1 < F(2^n) < F(2^(n+1))` for `n ≥ 2`.
- **Even `h ≠ 0`**: assume `p_n = F(2^n) + h` is prime for all `n ≥ n₀`.
  1. `exists_fib_two_pow_congr`: the phase-29/30 mechanism for the matrix `A = !![1,1;1,0]`,
     with `F(N) = (A^N) 0 1` (mathlib: `Matrix.fib`-style lemmas, or prove by induction).  Adapt
     the proof of `SharedConjecture.exists_trace_pow_congr`, which already shows
     `D^(c^(m+j)) = D^(c^m)` over `ZMod p`; read off entry `(0,1)` instead of the trace.
     `det A = -1`, so `p ∤ det A` is free.
  2. Hence (as in `lt_padicValNat_glCard_prime_base`) `n < padicValNat 2 (glCard 2 p_n)` for all
     large `n`: otherwise `p_n ∣ p_(n+j)` with `p_(n+j) > p_n` prime.
  3. `two_pow_dvd_sub_or_add_of_lt_padicValNat`: `glCard 2 p = (p^2-1)(p^2-p) = p(p-1)^2(p+1)`,
     and for odd `p` one of `v₂(p-1)`, `v₂(p+1)` is `1`, so `p ≡ ±1 (mod 2^(n/2))`.
  4. `two_pow_dvd_fib_two_pow_succ_add`: `F(2^(n+1)) + F(2^n) = F(2^n)(L(2^n)+1)` where
     `L(m) = 2F(m+1) - F(m)` (from `Nat.fib_two_mul`), and `v₂(L(2^n)+1) ≥ n+1` by induction via
     `L(2^(n+1)) + 1 = (L(2^n) - 1)(L(2^n) + 1)`, `L(2^n) - 1 ≡ 2 (mod 4)`.  Work in `ℤ`.
  5. Add steps 3 at `n` and `n+1`, use step 4: `s + s' ≡ 2h (mod 2^(n/2))`, `s, s' ∈ {±1}`.
     `h` even ⟹ `s + s' = 0` (as `±2 ≢ 0 mod 4`) ⟹ `2^(n/2) ∣ 2h` for all large `n` ⟹ `h = 0`.

Frozen: every statement below, everything in `ThreeAdic.lean`, `SharedConjecture.lean`,
`Projective.lean`, and all of `Literature/`.  Helper lemmas may be added freely (private or not).
-/

namespace LeanFormalizations.Mills.SaitoFibonacci

open LeanFormalizations.Mills.ThreeAdic Filter

/-! ### Helper: the Lucas companion and the 2-adic sign flip -/

/-- The Lucas number `L m = 2 F(m+1) − F(m)`, as an integer. -/
private def lucas (m : ℕ) : ℤ := 2 * Nat.fib (m + 1) - Nat.fib m

private lemma cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := m))
      rw [h]
      rw [pow_succ]
      ring_nf
      ring_nf at ih
      linarith [ih]

private lemma fib_two_mul_int (m : ℕ) :
    (Nat.fib (2 * m) : ℤ) = Nat.fib m * lucas m := by
  have hle : Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
    have := Nat.fib_mono (show m ≤ m + 1 by omega)
    omega
  have := Nat.fib_two_mul m
  rw [lucas]
  rw [this]
  push_cast [Nat.cast_sub hle]
  ring

private lemma lucas_two_mul (m : ℕ) : lucas (2 * m) = lucas m ^ 2 - 2 * (-1) ^ m := by
  have h1 : (Nat.fib (2 * m + 1) : ℤ) = (Nat.fib (m + 1) : ℤ) ^ 2 + (Nat.fib m : ℤ) ^ 2 := by
    rw [Nat.fib_two_mul_add_one]; push_cast; ring
  have h2 := fib_two_mul_int m
  have hc := cassini m
  simp only [lucas] at *
  rw [h1, h2]
  nlinarith [hc]

/-- `F(2^n)` is odd for every `n`. -/
theorem fib_two_pow_odd (n : ℕ) : Odd (Nat.fib (2 ^ n)) := by
  have hcop : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by decide)
  have h : Nat.gcd (Nat.fib (2 ^ n)) (Nat.fib 3) = 1 := by
    rw [← Nat.fib_gcd, hcop]
    rfl
  have h2 : Nat.fib 3 = 2 := by decide
  rw [h2] at h
  rcases Nat.even_or_odd (Nat.fib (2 ^ n)) with he | ho
  · exfalso
    have : (2 : ℕ) ∣ Nat.gcd (Nat.fib (2 ^ n)) 2 := Nat.dvd_gcd he.two_dvd dvd_rfl
    omega
  · exact ho

/-- `v₂(L(2^n) + 1) ≥ n + 1` for `n ≥ 1`: the engine of the sign flip. -/
private lemma two_pow_dvd_lucas_two_pow_add_one (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ lucas (2 ^ n) + 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
      have : lucas (2 ^ 1) = 3 := by decide
      rw [this]; norm_num
  | succ n hn ih =>
      have heven : (-1 : ℤ) ^ (2 ^ n) = 1 := by
        refine Even.neg_one_pow ?_
        exact (Nat.even_pow.2 ⟨even_iff_two_dvd.2 dvd_rfl, by omega⟩)
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have hsq : lucas (2 ^ (n + 1)) = lucas (2 ^ n) ^ 2 - 2 := by
        rw [hpow, lucas_two_mul, heven]; ring
      have hfac : lucas (2 ^ (n + 1)) + 1 = (lucas (2 ^ n) - 1) * (lucas (2 ^ n) + 1) := by
        rw [hsq]; ring
      obtain ⟨c, hc⟩ := ih
      have h4 : (4 : ℤ) ∣ lucas (2 ^ n) + 1 := by
        refine Dvd.dvd.trans ?_ ⟨c, hc⟩
        have : (4 : ℤ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega)
      obtain ⟨d, hd⟩ := h4
      have h2 : (2 : ℤ) ∣ lucas (2 ^ n) - 1 := ⟨2 * d - 1, by linarith⟩
      obtain ⟨e, he⟩ := h2
      rw [hfac, he, hc]
      exact ⟨e * c, by ring⟩

/-- **The sign flip.**  `F(2^(n+1)) ≡ -F(2^n) (mod 2^(n+1))` for `n ≥ 1`. -/
theorem two_pow_dvd_fib_two_pow_succ_add (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ (Nat.fib (2 ^ (n + 1)) : ℤ) + Nat.fib (2 ^ n) := by
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hid : (Nat.fib (2 ^ (n + 1)) : ℤ) + Nat.fib (2 ^ n)
      = Nat.fib (2 ^ n) * (lucas (2 ^ n) + 1) := by
    rw [hpow, fib_two_mul_int]; ring
  rw [hid]
  exact Dvd.dvd.mul_left (two_pow_dvd_lucas_two_pow_add_one n hn) _

/-! ### Helper: the Fibonacci matrix, and the entrywise form of the phase-30 mechanism -/

/-- `A = !![1,1;1,0]`. -/
private def fibMat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

private lemma fibMat_pow (N : ℕ) :
    fibMat ^ N = !![(Nat.fib (N + 1) : ℤ), (Nat.fib N : ℤ);
                    (Nat.fib N : ℤ), (Nat.fib (N + 1) : ℤ) - (Nat.fib N : ℤ)] := by
  induction N with
  | zero =>
      norm_num
      exact Matrix.one_fin_two
  | succ N ih =>
      have hf : (Nat.fib (N + 2) : ℤ) = (Nat.fib N : ℤ) + (Nat.fib (N + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := N))
      rw [pow_succ, ih, fibMat, Matrix.mul_fin_two]
      rw [show N + 1 + 1 = N + 2 from rfl, hf]
      norm_num
      ring_nf

private lemma fibMat_det : fibMat.det = -1 := by
  simp [fibMat, Matrix.det_fin_two_of]

/-- Entrywise version of `SharedConjecture.exists_trace_pow_congr` (same proof, reading off a
matrix entry instead of the trace). -/
private lemma exists_entry_pow_congr {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m c : ℕ}
    (hp : p.Prime) (hc : c.Prime) (hdet : ¬ (p : ℤ) ∣ C.det)
    (hv : padicValNat c (glCard n p) ≤ m) :
    ∃ j, 1 ≤ j ∧ ∀ a b : Fin n,
      (p : ℤ) ∣ ((C ^ (c ^ (m + j))) a b - (C ^ (c ^ m)) a b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hf
  set D : Matrix (Fin n) (Fin n) (ZMod p) := f.mapMatrix C with hD
  have hent : ∀ (N : ℕ) (a b : Fin n), (((C ^ N) a b : ℤ) : ZMod p) = (D ^ N) a b := by
    intro N a b
    rw [hD, ← map_pow]
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, hf]
  have hdetD : IsUnit D.det := by
    have hmd : D.det = f C.det := by rw [hD]; exact (RingHom.map_det f C).symm
    rw [hmd]
    refine Ne.isUnit ?_
    simpa [hf, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdet
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det D).2 hdetD
  have hcard : Nat.card (GL (Fin n) (ZMod p)) = glCard n p := by
    rw [Matrix.card_GL_field]
    simp [glCard, ZMod.card]
  obtain ⟨N, hN⟩ : ∃ N, N = glCard n p := ⟨_, rfl⟩
  have hNpos : 0 < N := by rw [hN, ← hcard]; exact Nat.card_pos
  have hNne : N ≠ 0 := hNpos.ne'
  have huN : u ^ N = 1 := by rw [hN, ← hcard]; exact pow_card_eq_one'
  obtain ⟨v, hvdef⟩ : ∃ v, v = padicValNat c N := ⟨_, rfl⟩
  have hvm : v ≤ m := by rw [hvdef, hN]; exact hv
  obtain ⟨M, hM⟩ : ∃ M, M = N / c ^ v := ⟨_, rfl⟩
  have hfac : N.factorization c = v := by rw [hvdef, Nat.factorization_def _ hc]
  have hsplit : c ^ v * M = N := by
    have := Nat.ordProj_mul_ordCompl_eq_self N c
    rw [hfac] at this
    rw [hM, hfac] at *
    exact this
  have hMdvd : ¬ (c ∣ M) := by
    have := Nat.not_dvd_ordCompl hc hNne
    rw [hfac] at this
    rwa [hM]
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hsplit; exact absurd hsplit.symm hNne
    · exact h
  set g := u ^ (c ^ m) with hg
  have hgM : g ^ M = 1 := by
    rw [hg, ← pow_mul]
    have : N ∣ c ^ m * M := by
      rw [← hsplit]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow c hvm) M
    obtain ⟨d, hd⟩ := this
    rw [hd, pow_mul, huN, one_pow]
  set j := Nat.totient M with hj
  have hjpos : 1 ≤ j := Nat.totient_pos.2 hMpos
  have hcop : Nat.Coprime c M := (Nat.Prime.coprime_iff_not_dvd hc).2 hMdvd
  have hmod : c ^ j ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcop
  obtain ⟨s, hs⟩ : ∃ s, c ^ j = 1 + M * s := by
    have h1 : 1 ≤ c ^ j := Nat.one_le_pow _ _ hc.pos
    obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨d, by omega⟩
  have hgfix : g ^ (c ^ j) = g := by
    rw [hs, pow_add, pow_one, pow_mul, hgM, one_pow, mul_one]
  refine ⟨j, hjpos, ?_⟩
  have key : D ^ (c ^ (m + j)) = D ^ (c ^ m) := by
    have : (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (c ^ (m + j)) =
        (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (c ^ m) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
      congr 1
      rw [pow_add, pow_mul, ← hg, hgfix]
    rwa [hu] at this
  intro a b
  have hz : ((((C ^ (c ^ (m + j))) a b - (C ^ (c ^ m)) a b : ℤ)) : ZMod p) = 0 := by
    push_cast
    rw [hent, hent, key]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz

/-- **The mechanism** (prime as modulus): if `v₂|GL₂(𝔽_p)| ≤ m`, the sequence `F(2^k) mod p`
returns to `F(2^m) mod p`. -/
theorem exists_fib_two_pow_congr {p m : ℕ} (hp : p.Prime)
    (hv : padicValNat 2 (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (Nat.fib (2 ^ (m + j)) : ℤ) - Nat.fib (2 ^ m) := by
  have hdet : ¬ (p : ℤ) ∣ fibMat.det := by
    rw [fibMat_det]
    intro hdd
    have : (p : ℤ) ∣ 1 := (dvd_neg.mp hdd)
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos this
    have := hp.two_le
    omega
  obtain ⟨j, hj1, hj⟩ := exists_entry_pow_congr fibMat hp Nat.prime_two hdet hv
  refine ⟨j, hj1, ?_⟩
  have h := hj 0 1
  rw [fibMat_pow, fibMat_pow] at h
  simpa using h

/-! ### Helper: the `2`-part of `|GL₂(𝔽_p)|` -/

private lemma factorization_two_eq_one {x : ℕ} (hx : x % 4 = 2) : x.factorization 2 = 1 := by
  have hx0 : x ≠ 0 := by omega
  have h1 : (2 : ℕ) ^ 1 ∣ x := by simpa using (by omega : (2 : ℕ) ∣ x)
  have h2 : ¬ ((2 : ℕ) ^ 2 ∣ x) := by
    intro hd
    have : (4 : ℕ) ∣ x := by simpa [pow_two] using hd
    omega
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hx0).1 h1
  by_contra hne
  exact h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hx0).2 (by omega))

/-- `v₂|GL₂(𝔽_p)| = 2 v₂(p−1) + v₂(p+1)` for an odd prime `p`. -/
private lemma padicValNat_glCard_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat 2 (glCard 2 p) = 2 * (p - 1).factorization 2 + (p + 1).factorization 2 := by
  have hodd : ¬ (2 ∣ p) := fun h => hp2 ((Nat.Prime.eq_one_or_self_of_dvd hp 2 h).resolve_left
    (by norm_num)).symm
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p <;> simp_all
    · exact h
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hq1 : p - 1 = r := by omega
  have he1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h : p ^ 2 = (p - 1) * (p + 1) + 1 := by rw [hq1, hr]; ring
    omega
  have he2 : p ^ 2 - p = p * (p - 1) := by
    have h : p ^ 2 = p * (p - 1) + p := by rw [hq1, hr]; ring
    omega
  have hg : glCard 2 p = ((p - 1) * (p + 1)) * (p * (p - 1)) := by
    rw [glCard, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [he1, he2]
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  have hnep : p ≠ 0 := by omega
  have hfp : p.factorization 2 = 0 := by
    simp [Nat.factorization_eq_zero_iff, hodd]
  have := Nat.factorization_def (glCard 2 p) Nat.prime_two
  rw [← this, hg]
  rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul hne1 hne2, Nat.factorization_mul hnep hne1]
  simp [hfp]
  omega

/-- A large `2`-part of `|GL₂(𝔽_p)|` forces `p ≡ ±1` modulo a large power of `2`. -/
theorem two_pow_dvd_sub_or_add_of_lt_padicValNat {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : k < padicValNat 2 (glCard 2 p)) :
    (2 : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (2 : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  have hodd : ¬ (2 ∣ p) := fun h => hp2 ((Nat.Prime.eq_one_or_self_of_dvd hp 2 h).resolve_left
    (by norm_num)).symm
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p <;> simp_all
    · exact h
  set a := (p - 1).factorization 2 with ha
  set b := (p + 1).factorization 2 with hb
  have hv := padicValNat_glCard_two hp hp2
  rw [hv] at hk
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  -- both `p ± 1` are even
  have ha1 : 1 ≤ a := by
    rw [ha]
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne1).1 ?_
    simpa using (by omega : (2 : ℕ) ∣ p - 1)
  have hb1 : 1 ≤ b := by
    rw [hb]
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne2).1 ?_
    simpa using (by omega : (2 : ℕ) ∣ p + 1)
  -- one of them is exactly `1`
  have hmin : a = 1 ∨ b = 1 := by
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h | h
    · exact Or.inr (by rw [hb]; exact factorization_two_eq_one (by omega))
    · exact Or.inl (by rw [ha]; exact factorization_two_eq_one (by omega))
  have hcast1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [this]
    ring
  have hcast2 : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  rcases hmin with h | h
  · -- `a = 1`, so `k ≤ b + 1` and `k / 2 ≤ b`
    right
    have hkb : k / 2 ≤ b := by omega
    have : (2 : ℕ) ^ (k / 2) ∣ p + 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne2).2 (by rw [← hb]; exact hkb)
    rw [← hcast2]
    exact_mod_cast Int.natCast_dvd_natCast.2 this
  · -- `b = 1`, so `k ≤ 2a` and `k / 2 ≤ a`
    left
    have hka : k / 2 ≤ a := by omega
    have : (2 : ℕ) ^ (k / 2) ∣ p - 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne1).2 (by rw [← ha]; exact hka)
    rw [← hcast1]
    exact_mod_cast Int.natCast_dvd_natCast.2 this

/-- **Saito's Problem 1.8 (arXiv:2504.14968), answered.**  For every integer `h`, `F(2^n) + h`
is not prime for infinitely many `n`. -/
theorem fib_two_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (2 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.SaitoFibonacci
