/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciAllPrimes

/-!
# Phase 40: prime-free intervals around `F(2^n)` — Dubickas's (D1) for a NON-reversible tower

Saito (arXiv:2504.14968) extends Dubickas's covering theorem (D1) and prime-free intervals (D2)
to compositions `R₀ ∘ R₁ ∘ ⋯` of linear recurrences, but only when the inner sequences are
**reversible**; `2^n` is not, and he writes *"We desire to remove the reversibility."*  This file
does it for Fibonacci along `2^n` (Theorem C of `ROADMAP-PRIME-TOWERS.md`):

  for every `H` there are `m`, `L ≥ 1` and primes `p_h` (`|h| ≤ H`) with
  `p_h ∣ F(2^(L k + m)) + h` for all `k`, hence `[F(2^n) − H, F(2^n) + H]` is prime-free for all
  large `n ≡ m (mod L)`.

Concrete instance (`scripts/fib-d1-demo.py`): `H = 6`, `m = 4`, `L = 60`, primes
`{2, 3, 23, 197, 983, 991}`.

## Route
1. `five_mul_fib_two_pow_sq`: `2^(n+1) ∣ 5 F(2^n)^2 + 3` for `n ≥ 1`.  From `5F(N)² = L(N)² − 4`
   (`N` even; Cassini / `LucasPrimePow.lucasL`) and `2^(n+1) ∣ L(2^n) + 1` (phase 32's
   `two_pow_dvd_lucas_two_pow_add_one`, or reprove).
2. `exists_good_prime_factor`: for `n` large relative to `|h|` (explicitly: `2^(n/2 − 1) > 5(|h|+1)² + 3`
   suffices), `F(2^n) + h` has a prime factor `p` with `padicValNat 2 (glCard 2 p) ≤ n`.
   Otherwise every prime factor `q` (odd, since `2` itself is good: `glCard 2 2 = 6`) satisfies
   `q ≡ ±1 (mod 2^(n/2))` (`two_pow_dvd_sub_or_add_of_lt_padicValNat`), so the product
   `F(2^n) + h ≡ ±1 (mod 2^(n/2))`; with step 1 this gives `2^(n/2) ∣ 5(h ∓ 1)² + 3`, too big.
3. `dvd_fib_two_pow_add_of_good`: a good prime `p ∣ F(2^m) + h` divides `F(2^(m + k j)) + h` for all
   `k`, for some `j ≥ 1`.  Strengthen `SaitoFibonacci.exists_entry_pow_congr`'s proof (it shows
   `D^(c^(m+j)) = D^(c^m)` over `ZMod p`; iterate).
4. `fib_two_pow_covering`: choose `m` large for all `|h| ≤ H` at once (step 2), `L = ∏ j_h` (or lcm).
5. `fib_two_pow_prime_free`: for `k ≥ 1`, `F(2^(Lk+m)) + h > p_h`, so it is not prime.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.FibonacciCovering

open LeanFormalizations.Mills.ThreeAdic Filter

/-! ### Step 0: local copies of the Fibonacci/Lucas identities

`SaitoFibonacci` keeps `lucas`, `cassini`, `fib_two_mul_int`, `fib_two_pow_odd`-style helpers
`private`, so we reprove what we need here (the header sanctions this).  Only two identities are
used: `F(2m) = F(m) L(m)` and `L(m)² = 5 F(m)² + 4(−1)^m`. -/

/-- The Lucas number `L m = 2 F(m+1) − F(m)`, as an integer. -/
def lucasInt (m : ℕ) : ℤ := 2 * Nat.fib (m + 1) - Nat.fib m

lemma fib_cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := m))
      rw [h, pow_succ]
      ring_nf
      ring_nf at ih
      linarith [ih]

lemma lucasInt_sq (m : ℕ) : lucasInt m ^ 2 = 5 * (Nat.fib m : ℤ) ^ 2 + 4 * (-1) ^ m := by
  have hc := fib_cassini m
  simp only [lucasInt]
  nlinarith [hc]

lemma fib_two_mul_int (m : ℕ) : (Nat.fib (2 * m) : ℤ) = Nat.fib m * lucasInt m := by
  have hle : Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
    have := Nat.fib_mono (show m ≤ m + 1 by omega)
    omega
  have h := Nat.fib_two_mul m
  rw [lucasInt, h]
  push_cast [Nat.cast_sub hle]
  ring

lemma fib_two_pow_lt' {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    Nat.fib (2 ^ m) < Nat.fib (2 ^ n) := by
  have h2m : 2 ≤ 2 ^ m := Nat.one_lt_two_pow_iff.2 (by omega)
  have h2n : 2 ≤ 2 ^ n := Nat.one_lt_two_pow_iff.2 (by omega)
  exact Nat.fib_strictMonoOn (Set.mem_Ici.2 h2m) (Set.mem_Ici.2 h2n)
    (Nat.pow_lt_pow_right (by norm_num) hmn)

lemma le_fib_two_pow' {n : ℕ} (hn : 5 ≤ n) : n ≤ Nat.fib (2 ^ n) :=
  le_trans (Nat.le_fib_self hn) (Nat.fib_mono (Nat.le_of_lt Nat.lt_two_pow_self))

/-! ### Step 1: the non-integrality certificate `2^(n+1) ∣ 5 F(2^n)² + 3`

This is the `c = 2` case of the roadmap's certificate list: `5 F(2^n)² = L(2^n)² − 4` and
`L(2^n) → −1` 2-adically, so a 2-adic limit `λ` of `F(2^n)` satisfies `5λ² = −3`, which has no
solution in `ℤ₂` — the quantitative form being exactly the divisibility below. -/

theorem five_mul_fib_two_pow_sq (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ 5 * (Nat.fib (2 ^ n) : ℤ) ^ 2 + 3 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have heven : (-1 : ℤ) ^ (2 ^ n) = 1 :=
        Even.neg_one_pow (Nat.even_pow.2 ⟨even_iff_two_dvd.2 dvd_rfl, by omega⟩)
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have hdouble : (Nat.fib (2 ^ (n + 1)) : ℤ) = Nat.fib (2 ^ n) * lucasInt (2 ^ n) := by
        rw [hpow, fib_two_mul_int]
      obtain ⟨F, hF⟩ : ∃ F : ℤ, F = (Nat.fib (2 ^ n) : ℤ) := ⟨_, rfl⟩
      obtain ⟨L, hL⟩ : ∃ L : ℤ, L = lucasInt (2 ^ n) := ⟨_, rfl⟩
      have hsq : L ^ 2 = 5 * F ^ 2 + 4 := by rw [hL, hF, lucasInt_sq, heven]; ring
      obtain ⟨c, hc⟩ := ih
      have hX : 5 * F ^ 2 = 2 ^ (n + 1) * c - 3 := by rw [hF]; linarith [hc]
      refine ⟨(2 ^ n * c - 1) * c, ?_⟩
      have hgoal : 5 * (Nat.fib (2 ^ (n + 1)) : ℤ) ^ 2 + 3 = (5 * F ^ 2 + 1) * (5 * F ^ 2 + 3) := by
        rw [hdouble, ← hF, ← hL]; linear_combination (5 * F ^ 2) * hsq
      rw [hgoal, hX]
      have hp1 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      have hp2 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n := by rw [pow_succ, pow_succ]; ring
      rw [hp1, hp2]; ring

/-! ### Step 2: every value near `F(2^n)` has a prime factor with a small 2-part

If every prime factor `q` of `F(2^n) + h` had `n < v₂|GL₂(𝔽_q)|`, then each such `q` would be
`≡ ±1 (mod 2^(n/2))`; the set of such residues is multiplicatively closed, so the product
`F(2^n) + h` itself is `≡ ±1`, i.e. `F(2^n) ≡ s − h`.  Step 1 then forces
`2^(n/2) ∣ 5(s−h)² + 3`, and the right-hand side is a fixed nonzero integer. -/

/-- The residues `±1 (mod 2^e)`, as a predicate on `ℤ`. -/
def PmOne (e : ℕ) (x : ℤ) : Prop := (2 : ℤ) ^ e ∣ x - 1 ∨ (2 : ℤ) ^ e ∣ x + 1

lemma PmOne.one (e : ℕ) : PmOne e 1 := Or.inl (by simp)

lemma PmOne.mul {e : ℕ} {x y : ℤ} (hx : PmOne e x) (hy : PmOne e y) : PmOne e (x * y) := by
  obtain ⟨s, hs, hsd⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (2 : ℤ) ^ e ∣ x - s := by
    rcases hx with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  obtain ⟨t, ht, htd⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ (2 : ℤ) ^ e ∣ y - t := by
    rcases hy with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  have hkey : (2 : ℤ) ^ e ∣ x * y - s * t := by
    have h : x * y - s * t = y * (x - s) + s * (y - t) := by ring
    rw [h]
    exact dvd_add (hsd.mul_left _) (htd.mul_left _)
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact Or.inl (by simpa using hkey)
  · exact Or.inr (by simpa using hkey)
  · exact Or.inr (by simpa using hkey)
  · exact Or.inl (by simpa using hkey)

/-- A natural number all of whose prime factors are `≡ ±1 (mod 2^e)` is itself `≡ ±1`. -/
lemma PmOne.of_prime_factors (e : ℕ) :
    ∀ N : ℕ, 1 ≤ N → (∀ q : ℕ, q.Prime → q ∣ N → PmOne e (q : ℤ)) → PmOne e (N : ℤ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      intro hN hfac
      rcases eq_or_lt_of_le hN with h1 | h1
      · rw [← h1]; simpa using PmOne.one e
      · have hN1 : N ≠ 1 := by omega
        have hmf : (N.minFac).Prime := Nat.minFac_prime hN1
        obtain ⟨M, hM⟩ := N.minFac_dvd
        have hMpos : 1 ≤ M := by
          rcases Nat.eq_zero_or_pos M with h | h
          · rw [h, Nat.mul_zero] at hM; omega
          · exact h
        have hMlt : M < N := by
          have h2 : 2 ≤ N.minFac := hmf.two_le
          have h3 : 2 * M ≤ N := by rw [hM]; exact Nat.mul_le_mul_right M h2
          exact lt_of_lt_of_le (show M < 2 * M by omega) h3
        have hrec : PmOne e (M : ℤ) :=
          ih M hMlt hMpos (fun q hq hqd => hfac q hq (hM ▸ Dvd.dvd.mul_left hqd _))
        have hmfp : PmOne e (N.minFac : ℤ) := hfac _ hmf N.minFac_dvd
        have : ((N : ℤ)) = (N.minFac : ℤ) * (M : ℤ) := by
          rw [← Nat.cast_mul, ← hM]
        rw [this]
        exact hmfp.mul hrec

/-- `2` is always a "good" prime: `|GL₂(𝔽₂)| = 6` has 2-part `2`. -/
lemma padicValNat_glCard_two_two : padicValNat 2 (glCard 2 2) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : glCard 2 2 = 2 * 3 := by decide
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- A value near `F(2^n)` has a prime factor whose `GL₂` order has a small `2`-part. -/
theorem exists_good_prime_factor (h : ℤ) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (Nat.fib (2 ^ n) : ℤ) + h ∧
      padicValNat 2 (glCard 2 p) ≤ n := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ s : ℤ, (s = 1 ∨ s = -1) → 5 * (s - h) ^ 2 + 3 ≤ (B : ℤ) := by
    refine ⟨(5 * (1 + |h|) ^ 2 + 3).toNat, fun s hs => ?_⟩
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    have h1 : |s - h| ≤ 1 + |h| := by
      calc |s - h| ≤ |s| + |h| := abs_sub _ _
      _ = 1 + |h| := by rw [habs]
    have h2 : (s - h) ^ 2 ≤ (1 + |h|) ^ 2 := by
      nlinarith [sq_abs (s - h), abs_nonneg (s - h), abs_nonneg h, h1]
    have h3 : (0 : ℤ) ≤ 5 * (1 + |h|) ^ 2 + 3 := by positivity
    have := Int.toNat_of_nonneg h3
    omega
  refine eventually_atTop.2 ⟨max 5 (2 * B + 2 * h.natAbs + 8), fun n hn => ?_⟩
  have hn5 : 5 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : 2 * B + 2 * h.natAbs + 8 ≤ n := le_trans (le_max_right _ _) hn
  set e : ℕ := n / 2 with he
  have heB : B < 2 ^ e := by
    have h1 : B + 1 ≤ e := by omega
    have h2 : e < 2 ^ e := Nat.lt_two_pow_self
    omega
  have hen : e ≤ n + 1 := by omega
  by_contra hcon
  -- every prime factor is odd and has a large 2-part, hence is `≡ ±1 (mod 2^e)`
  have hfac : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (Nat.fib (2 ^ n) : ℤ) + h → PmOne e (q : ℤ) := by
    intro q hq hqd
    have hvq : ¬ (padicValNat 2 (glCard 2 q) ≤ n) := fun hv => hcon ⟨q, hq, hqd, hv⟩
    have hq2 : q ≠ 2 := by
      intro h2
      rw [h2, padicValNat_glCard_two_two] at hvq
      omega
    exact SaitoFibonacci.two_pow_dvd_sub_or_add_of_lt_padicValNat hq hq2 (by omega)
  -- so `F(2^n) + h ≡ ±1 (mod 2^e)`
  have hfibbig : (h.natAbs : ℤ) < (Nat.fib (2 ^ n) : ℤ) := by
    have h1 : (n : ℤ) ≤ (Nat.fib (2 ^ n) : ℤ) := by exact_mod_cast le_fib_two_pow' hn5
    have h2 : (h.natAbs : ℤ) + 8 ≤ (n : ℤ) := by
      have : (2 * B + 2 * h.natAbs + 8 : ℕ) ≤ n := hnB
      have h3 : ((2 * B + 2 * h.natAbs + 8 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast this
      push_cast at h3
      omega
    omega
  have hval : (0 : ℤ) < (Nat.fib (2 ^ n) : ℤ) + h := by
    have h4 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have h5 : -|h| ≤ h := neg_abs_le h
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = (Nat.fib (2 ^ n) : ℤ) + h :=
    ⟨((Nat.fib (2 ^ n) : ℤ) + h).toNat, by omega⟩
  have hM1 : 1 ≤ M := by
    have : (0 : ℤ) < (M : ℤ) := by rw [hM]; exact hval
    exact_mod_cast this
  have hpm : PmOne e (M : ℤ) := PmOne.of_prime_factors e M hM1 (by
    intro q hq hqd
    exact hfac q hq (by rw [← hM]; exact_mod_cast Int.natCast_dvd_natCast.2 hqd))
  rw [hM] at hpm
  -- step 1 now bounds `2^e`
  obtain ⟨s, hs, hsd⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (2 : ℤ) ^ e ∣ (Nat.fib (2 ^ n) : ℤ) + h - s := by
    rcases hpm with hq | hq
    · exact ⟨1, Or.inl rfl, hq⟩
    · exact ⟨-1, Or.inr rfl, by simpa [sub_neg_eq_add] using hq⟩
  have hcert : (2 : ℤ) ^ e ∣ 5 * (Nat.fib (2 ^ n) : ℤ) ^ 2 + 3 :=
    dvd_trans (pow_dvd_pow 2 hen) (five_mul_fib_two_pow_sq n (by omega))
  have hfinal : (2 : ℤ) ^ e ∣ 5 * (s - h) ^ 2 + 3 := by
    obtain ⟨d, hd⟩ := hsd
    have hrw : (Nat.fib (2 ^ n) : ℤ) = (s - h) + 2 ^ e * d := by linarith [hd]
    obtain ⟨u, hu⟩ := hcert
    refine ⟨u - (5 * (2 * (s - h) * d + 2 ^ e * d ^ 2)), ?_⟩
    have : 5 * (Nat.fib (2 ^ n) : ℤ) ^ 2 + 3
        = 5 * (s - h) ^ 2 + 3 + 2 ^ e * (5 * (2 * (s - h) * d + 2 ^ e * d ^ 2)) := by
      rw [hrw]; ring
    rw [this] at hu
    linarith [hu]
  have hpos : (0 : ℤ) < 5 * (s - h) ^ 2 + 3 := by positivity
  have hle := Int.le_of_dvd hpos hfinal
  have := hB s hs
  have hBz : (B : ℤ) < (2 : ℤ) ^ e := by exact_mod_cast heB
  omega


/-! ### Step 3: the mechanism, strengthened to every multiple of the period

`SaitoFibonacci.exists_entry_pow_congr` produces one `j` with `D^(c^(m+j)) = D^(c^m)` over
`ZMod p`.  Its proof goes through `g := u^(c^m)` in `GLₙ(𝔽_p)` and `g^(c^j) = g`; that relation
**iterates**, so `g^(c^(k j)) = g` for every `k`, hence `D^(c^(m + k j)) = D^(c^m)`.  This is the
strengthening the covering argument needs: one prime must serve the whole arithmetic progression
`n ≡ m (mod j)`, not just a single later index. -/

lemma exists_entry_pow_congr_mul {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m c : ℕ}
    (hp : p.Prime) (hc : c.Prime) (hdet : ¬ (p : ℤ) ∣ C.det)
    (hv : padicValNat c (glCard n p) ≤ m) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ, ∀ a b : Fin n,
      (p : ℤ) ∣ ((C ^ (c ^ (m + k * j))) a b - (C ^ (c ^ m)) a b) := by
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
  set g := u ^ (c ^ m) with hg
  have hgM : g ^ M = 1 := by
    rw [hg, ← pow_mul]
    have hdd : N ∣ c ^ m * M := by
      rw [← hsplit]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow c hvm) M
    obtain ⟨d, hd⟩ := hdd
    rw [hd, pow_mul, huN, one_pow]
  set j := Nat.totient M with hj
  have hjpos : 1 ≤ j := Nat.totient_pos.2 hMpos
  have hcop : Nat.Coprime c M := (Nat.Prime.coprime_iff_not_dvd hc).2 hMdvd
  have hmod : c ^ j ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcop
  obtain ⟨s, hs⟩ : ∃ s, c ^ j = 1 + M * s := by
    have h1 : 1 ≤ c ^ j := Nat.one_le_pow _ _ hc.pos
    obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨d, by omega⟩
  -- the single-step fixed-point relation …
  have hgfix : g ^ (c ^ j) = g := by
    rw [hs, pow_add, pow_one, pow_mul, hgM, one_pow, mul_one]
  -- … iterated over all multiples of `j`
  have hgfixk : ∀ k : ℕ, g ^ (c ^ (k * j)) = g := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hexp : c ^ ((k + 1) * j) = c ^ (k * j) * c ^ j := by
          rw [← pow_add]; congr 1; ring
        rw [hexp, pow_mul, ih, hgfix]
  refine ⟨j, hjpos, ?_⟩
  intro k
  have key : D ^ (c ^ (m + k * j)) = D ^ (c ^ m) := by
    have hun : (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (c ^ (m + k * j)) =
        (u : Matrix (Fin n) (Fin n) (ZMod p)) ^ (c ^ m) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
      congr 1
      rw [pow_add, pow_mul, ← hg, hgfixk k]
    rwa [hu] at hun
  intro a b
  have hz : ((((C ^ (c ^ (m + k * j))) a b - (C ^ (c ^ m)) a b : ℤ)) : ZMod p) = 0 := by
    push_cast
    rw [hent, hent, key]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz

/-- `A = !![1,1;1,0]`, the Fibonacci matrix (local copy; `SaitoFibonacci.fibMat` is private). -/
def fibMat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

lemma fibMat_pow (N : ℕ) :
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

lemma fibMat_det : fibMat.det = -1 := by
  simp [fibMat, Matrix.det_fin_two_of]

/-- **Step 3.**  A good prime dividing `F(2^m) + h` divides `F(2^(m + k j)) + h` for every `k`. -/
theorem dvd_fib_two_pow_add_of_good {p m : ℕ} {h : ℤ} (hp : p.Prime)
    (hv : padicValNat 2 (glCard 2 p) ≤ m) (hd : (p : ℤ) ∣ (Nat.fib (2 ^ m) : ℤ) + h) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ, (p : ℤ) ∣ (Nat.fib (2 ^ (m + k * j)) : ℤ) + h := by
  have hdet : ¬ (p : ℤ) ∣ fibMat.det := by
    rw [fibMat_det]
    intro hdd
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdd)
    have := hp.two_le
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast this
    omega
  obtain ⟨j, hj1, hj⟩ := exists_entry_pow_congr_mul fibMat hp Nat.prime_two hdet hv
  refine ⟨j, hj1, fun k => ?_⟩
  have hjk : (p : ℤ) ∣ (Nat.fib (2 ^ (m + k * j)) : ℤ) - (Nat.fib (2 ^ m) : ℤ) := by
    have hx := hj k 0 1
    rw [fibMat_pow, fibMat_pow] at hx
    simpa using hx
  have hsum := dvd_add hjk hd
  have : (Nat.fib (2 ^ (m + k * j)) : ℤ) - (Nat.fib (2 ^ m) : ℤ)
      + ((Nat.fib (2 ^ m) : ℤ) + h) = (Nat.fib (2 ^ (m + k * j)) : ℤ) + h := by ring
  rwa [this] at hsum

/-- **(D1) for Fibonacci along the non-reversible tower `2^n`.** -/
theorem fib_two_pow_covering (H : ℕ) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (2 ^ (L * k + m)) : ℤ) + h := by
  classical
  set S : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ) with hS
  have hmemS : ∀ h : ℤ, |h| ≤ (H : ℤ) → h ∈ S := by
    intro h hh
    rw [hS, Finset.mem_Icc]
    have := abs_le.1 hh
    exact ⟨this.1, this.2⟩
  -- one index `m` works for every shift at once (finitely many shifts)
  have hall : ∀ᶠ n in atTop, ∀ h ∈ S, ∃ q : ℕ, q.Prime ∧
      (q : ℤ) ∣ (Nat.fib (2 ^ n) : ℤ) + h ∧ padicValNat 2 (glCard 2 q) ≤ n :=
    (Filter.eventually_all_finset S).2 (fun h _ => exists_good_prime_factor h)
  obtain ⟨m, hm⟩ := eventually_atTop.1 hall
  have hm0 := hm m le_rfl
  -- choose the good prime, and its period, for each shift
  set Q : ℤ → ℕ → Prop := fun h q => q.Prime ∧ (q : ℤ) ∣ (Nat.fib (2 ^ m) : ℤ) + h ∧
    padicValNat 2 (glCard 2 q) ≤ m with hQ
  set P : ℤ → ℕ := fun h => if hh : ∃ q, Q h q then hh.choose else 2 with hP
  have hPspec : ∀ h ∈ S, Q h (P h) := by
    intro h hh
    have hex : ∃ q, Q h q := hm0 h hh
    rw [hP]
    simp only [dif_pos hex]
    exact hex.choose_spec
  set R : ℤ → ℕ → Prop := fun h j => 1 ≤ j ∧
    ∀ k : ℕ, (P h : ℤ) ∣ (Nat.fib (2 ^ (m + k * j)) : ℤ) + h with hR
  set J : ℤ → ℕ := fun h => if hh : ∃ j, R h j then hh.choose else 1 with hJ
  have hJspec : ∀ h ∈ S, R h (J h) := by
    intro h hh
    obtain ⟨hpr, hpd, hpv⟩ := hPspec h hh
    have hex : ∃ j, R h j := dvd_fib_two_pow_add_of_good hpr hpv hpd
    rw [hJ]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hJpos : ∀ h : ℤ, 1 ≤ J h := by
    intro h
    rw [hJ]
    by_cases hh : ∃ j, R h j
    · simp only [dif_pos hh]; exact hh.choose_spec.1
    · simp only [dif_neg hh]
      exact le_refl 1
  -- `L` is any common multiple of the periods; the product is the cheapest one
  refine ⟨m, ∏ h ∈ S, J h, ?_, P, ?_⟩
  · exact Finset.one_le_prod' (fun h _ => hJpos h)
  intro h hh
  have hhS : h ∈ S := hmemS h hh
  obtain ⟨hpr, hpd, hpv⟩ := hPspec h hhS
  refine ⟨hpr, fun k => ?_⟩
  obtain ⟨d, hd⟩ : J h ∣ ∏ h' ∈ S, J h' := Finset.dvd_prod_of_mem J hhS
  have hkey := (hJspec h hhS).2 (d * k)
  have hidx : m + d * k * J h = (∏ h' ∈ S, J h') * k + m := by
    rw [hd]; ring
  rwa [hidx] at hkey

/-- **Prime-free intervals of any fixed length around `F(2^n)`, infinitely often.** -/
theorem fib_two_pow_prime_free (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (2 ^ n) : ℤ) + h) := by
  obtain ⟨m, L, hL, p, hp⟩ := fib_two_pow_covering H
  rw [frequently_atTop]
  intro a
  set K : ℕ := max a (H + 5) + 1 with hK
  refine ⟨L * (K + 1) + m, ?_, ?_⟩
  · have h1 : K + 1 ≤ L * (K + 1) := Nat.le_mul_of_pos_left _ hL
    have h2 : a ≤ K := by rw [hK]; omega
    omega
  intro h hh
  obtain ⟨hpr, hpd⟩ := hp h hh
  have hKH : H + 5 ≤ K := by rw [hK]; omega
  have h1 : K ≤ L * K := Nat.le_mul_of_pos_left _ hL
  have hn1 : H + 5 ≤ L * K + m := by omega
  have hlt12 : L * K + m < L * (K + 1) + m := by
    have hexp : L * (K + 1) = L * K + L := by ring
    omega
  -- the value at `k = K` is positive and strictly smaller than the value at `k = K + 1`
  have hfibge : ((L * K + m : ℕ) : ℤ) ≤ (Nat.fib (2 ^ (L * K + m)) : ℤ) := by
    exact_mod_cast le_fib_two_pow' (by omega)
  have hHle : (H : ℤ) ≤ ((L * K + m : ℕ) : ℤ) := by exact_mod_cast (by omega : H ≤ L * K + m)
  have habs := abs_le.1 hh
  have hA1 : (0 : ℤ) < (Nat.fib (2 ^ (L * K + m)) : ℤ) + h := by omega
  have hgrow : (Nat.fib (2 ^ (L * K + m)) : ℤ) < (Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) := by
    exact_mod_cast fib_two_pow_lt' (show 1 ≤ L * K + m by omega) hlt12
  intro hprime
  -- `p h` divides the (assumed prime) value at `k = K + 1`, hence equals it
  have hd2 := hpd (K + 1)
  have hd1 := hpd K
  have hnat : ((Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) + h).natAbs.Prime :=
    Int.prime_iff_natAbs_prime.1 hprime
  have hdnat : p h ∣ ((Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd2
    simpa using this
  have hpeq : p h = ((Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    rcases hnat.eq_one_or_self_of_dvd _ hdnat with hx | hx
    · exact absurd hx hpr.one_lt.ne'
    · exact hx
  have hA2 : (0 : ℤ) < (Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) + h := by omega
  have hpval : ((p h : ℤ)) = (Nat.fib (2 ^ (L * (K + 1) + m)) : ℤ) + h := by
    rw [hpeq]; omega
  have hple : ((p h : ℤ)) ≤ (Nat.fib (2 ^ (L * K + m)) : ℤ) + h := Int.le_of_dvd hA1 hd1
  omega

end LeanFormalizations.Mills.FibonacciCovering
