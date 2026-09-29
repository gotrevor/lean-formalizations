/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ThreeAdic

/-!
# One conjecture behind Fermat and Mills (phase 30)

Fermat numbers `F_k = 2^(2^k) + 1 = tr diag(2,1)^(2^k)`.  Mills primes, if Mills' constant `A` is
algebraic, are `⌊A^(3^(m+k))⌋ = tr C^(3^k)` for the companion matrix `C` of a cubic Pisot number
(phase 29, inside `mills_threeAdic`).  Both are **double-exponential trace sequences**
`tr C^(c^k) + h`.  Neither question is known to imply the other: the bases (2 vs 3) and the
eigenvalue structures differ, and no transfer is known.  But one conjecture implies both.

`DoubleExpTraceComposite` (Ren, 2026-09-29, stated here; not from the literature):
for every square integer matrix `C`, base `c ≥ 2` and shift `h`, if `|tr C^(c^k) + h| → ∞` then
`tr C^(c^k) + h` is composite (not prime) for infinitely many `k`.  The growth hypothesis is
needed: eigenvalues `λ, −λ` with `c` odd make the trace `0`, so the sequence is `h`, possibly a
constant prime.  The standard heuristic (a number of size `X` is prime with probability about
`1/log X`, and `Σ 1/c^k` converges) predicts even that only finitely many terms are prime.

Phase 29 proves the conjecture's `c = 3`, `h = 0` case whenever the `3`-adic limit is not `±1`.
`lt_padicValNat_glCard_prime_base` below generalizes phase 29's unconditional step to any prime
base `c` and shift `h`.

## Route
- `fermat_of_doubleExpTraceComposite`: `C = diag(2,1)`, `c = 2`, `h = 0`; `tr C^(2^k) = F_k → ∞`.
- `mills_transcendental_of_doubleExpTraceComposite`: by contradiction, assume `A` is algebraic.
  Reuse the glue inside `mills_threeAdic` (Saito's Pisot branch, `companion3`, `hfloor`: eventually
  `tr C^(3^i) = ⌊A^(3^(m+i))⌋`, which is prime by `IsMills`).  Factor it out as a lemma first.
  Then the conjecture with `c = 3`, `h = 0` gives a composite floor.
- `lt_padicValNat_glCard_prime_base`: copy `dvd_trace_pow_three_of_glCard` and
  `lt_padicValNat_glCard` with `3` replaced by a prime `c` and the trace shifted by `h`.  The
  argument is unchanged: `c^j ≡ 1 (mod M)` for `j = φ(M)` when `c ∤ M`.

Frozen: every statement below, everything in `ThreeAdic.lean`, all of `Literature/`.
-/

namespace LeanFormalizations.Mills.SharedConjecture

open LeanFormalizations.Literature LeanFormalizations.Mills.ThreeAdic Matrix Filter

/-- **Conjecture (Ren, 2026-09-29).**  Double-exponential trace sequences are composite infinitely
often, once they grow. -/
def DoubleExpTraceComposite : Prop :=
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) (h : ℤ), 2 ≤ c →
    Tendsto (fun k : ℕ => |(C ^ (c ^ k)).trace + h|) atTop atTop →
    ∃ᶠ k in atTop, ¬ Prime ((C ^ (c ^ k)).trace + h)

/-! ### Sequence growth helpers -/

private lemma seq_growth {t : ℕ → ℤ} {k₀ : ℕ} (hmono : ∀ k ≥ k₀, t k < t (k + 1)) :
    ∀ k, k₀ ≤ k → t k₀ + ((k : ℤ) - (k₀ : ℤ)) ≤ t k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      have := hmono k hk
      push_cast
      push_cast at ih
      omega

private lemma seq_le {t : ℕ → ℤ} {k₀ : ℕ} (hmono : ∀ k ≥ k₀, t k < t (k + 1)) :
    ∀ a, k₀ ≤ a → ∀ d, t a ≤ t (a + d) := by
  intro a ha d
  induction d with
  | zero => simp
  | succ d ih =>
      have := hmono (a + d) (by omega)
      have he : a + (d + 1) = (a + d) + 1 := by omega
      rw [he]; omega

private lemma seq_eventually_gt {t : ℕ → ℤ} {k₀ : ℕ} (hmono : ∀ k ≥ k₀, t k < t (k + 1))
    (B : ℤ) : ∃ K, k₀ ≤ K ∧ ∀ k ≥ K, B < t k := by
  refine ⟨k₀ + (B - t k₀ + 1).toNat, by omega, ?_⟩
  intro k hk
  have h1 := seq_growth hmono k (by omega)
  have h2 : ((k₀ + (B - t k₀ + 1).toNat : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  push_cast at h2
  omega

private lemma tendsto_abs_atTop_of_mono {t : ℕ → ℤ} {k₀ : ℕ}
    (hmono : ∀ k ≥ k₀, t k < t (k + 1)) : Tendsto (fun k => |t k|) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨K, -, hK⟩ := seq_eventually_gt hmono B
  exact eventually_atTop.2 ⟨K, fun k hk => le_trans (hK k hk).le (le_abs_self _)⟩

/-! ### Step 1 for a general prime base: the trace sequence is periodic mod `p` -/

/-- **Generalised phase-29 step 1.**  If the prime `p` does not divide `det C` and
`v_c |GL_n(𝔽_p)| ≤ m`, then `tr C^(c^(m+j)) ≡ tr C^(c^m) (mod p)` for some `j ≥ 1`.

The shift `h` of `DoubleExpTraceComposite` is invisible here: the conclusion is a congruence
between two traces, so `+ h` cancels. -/
theorem exists_trace_pow_congr {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m c : ℕ}
    (hp : p.Prime) (hc : c.Prime) (hdet : ¬ (p : ℤ) ∣ C.det)
    (hv : padicValNat c (glCard n p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ ((C ^ (c ^ (m + j))).trace - (C ^ (c ^ m)).trace) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hf
  set D : Matrix (Fin n) (Fin n) (ZMod p) := f.mapMatrix C with hD
  have htr : ∀ N : ℕ, ((C ^ N).trace : ZMod p) = (D ^ N).trace := by
    intro N
    rw [hD, ← map_pow]
    simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply, hf]
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
  have hz : (((C ^ (c ^ (m + j))).trace - (C ^ (c ^ m)).trace : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [htr, htr, key]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz

/-- The conjecture implies infinitely many composite Fermat numbers. -/
theorem fermat_of_doubleExpTraceComposite (hC : DoubleExpTraceComposite) :
    ∃ᶠ k in atTop, ¬ (Nat.fermatNumber k).Prime := by
  set C : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal ![2, 1] with hCdef
  have htr : ∀ N : ℕ, (C ^ N).trace = 2 ^ N + 1 := by
    intro N
    rw [hCdef, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hgrow : Tendsto (fun k : ℕ => |(C ^ ((2:ℕ) ^ k)).trace + (0:ℤ)|) atTop atTop := by
    rw [tendsto_atTop]
    intro B
    refine eventually_atTop.2 ⟨B.toNat, fun k hk => ?_⟩
    have h1 : B ≤ (k : ℤ) := by
      have : (B.toNat : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      omega
    have h2 : k < 2 ^ k := Nat.lt_two_pow_self
    have h3 : k ≤ 2 ^ ((2:ℕ) ^ k) := by
      have : k < 2 ^ k := h2
      exact le_trans this.le (Nat.pow_le_pow_right (by norm_num) h2.le)
    have h4 : (k : ℤ) ≤ 2 ^ ((2:ℕ) ^ k) := by exact_mod_cast h3
    rw [htr]
    rw [abs_of_nonneg (by positivity)]
    omega
  have := hC 2 C 2 0 (by norm_num) hgrow
  refine this.mono fun k hk hfp => hk ?_
  rw [htr, add_zero]
  have : ((Nat.fermatNumber k : ℕ) : ℤ) = 2 ^ ((2:ℕ) ^ k) + 1 := by
    simp [Nat.fermatNumber]
  rw [← this]
  exact Nat.prime_iff_prime_int.1 hfp

/-- The conjecture implies that the least Mills constant is transcendental. -/
theorem mills_transcendental_of_doubleExpTraceComposite (hC : DoubleExpTraceComposite)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) : Transcendental ℚ A := by
  by_contra hcon
  rw [Transcendental, not_not] at hcon
  obtain ⟨C, m, i₀, hdet, hfloor, hprime, hmono⟩ :=
    exists_companion_of_algebraic_mills hB hM hD hG hA hcon
  have hmono0 : ∀ k ≥ i₀, (C ^ ((3:ℕ) ^ k)).trace + (0:ℤ) <
      (C ^ ((3:ℕ) ^ (k + 1))).trace + (0:ℤ) := by
    intro k hk; simpa using hmono k hk
  have hgrow : Tendsto (fun k : ℕ => |(C ^ ((3:ℕ) ^ k)).trace + (0:ℤ)|) atTop atTop :=
    tendsto_abs_atTop_of_mono hmono0
  have hfreq := hC 3 C 3 0 (by norm_num) hgrow
  have hev : ∀ᶠ k : ℕ in atTop, Prime ((C ^ ((3:ℕ) ^ k)).trace + (0:ℤ)) :=
    eventually_atTop.2 ⟨i₀, fun k hk => by simpa using hprime k hk⟩
  obtain ⟨k, hk1, hk2⟩ := (hfreq.and_eventually hev).exists
  exact hk1 hk2

/-- Phase 29's unconditional step for any prime base `c` and shift `h`: if `tr C^(c^k) + h` is
prime and strictly increasing from some point on, then `v_c |GL_n(𝔽_{t_k})| > k` for all large
`k`. -/
theorem lt_padicValNat_glCard_prime_base {n c : ℕ} (hc : c.Prime) (C : Matrix (Fin n) (Fin n) ℤ)
    (hdet : C.det ≠ 0) (h : ℤ) {k₀ : ℕ}
    (hprime : ∀ k ≥ k₀, Prime ((C ^ (c ^ k)).trace + h))
    (hmono : ∀ k ≥ k₀, (C ^ (c ^ k)).trace + h < (C ^ (c ^ (k + 1))).trace + h) :
    ∃ K, ∀ k ≥ K, k < padicValNat c (glCard n ((C ^ (c ^ k)).trace + h).toNat) := by
  set t : ℕ → ℤ := fun k => (C ^ (c ^ k)).trace + h with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  obtain ⟨K, hK0, hKB⟩ := seq_eventually_gt hmono' |C.det|
  refine ⟨K, ?_⟩
  intro k hk
  have hk0 : k₀ ≤ k := le_trans hK0 hk
  by_contra hcon
  push_neg at hcon
  have htpos : 0 < t k := lt_of_le_of_lt (abs_nonneg _) (hKB k hk)
  have htprime : Prime (t k) := hprime k hk0
  obtain ⟨p, hpv⟩ : ∃ p : ℕ, (p : ℤ) = t k := ⟨(t k).toNat, Int.toNat_of_nonneg htpos.le⟩
  have hpnat : p.Prime := by
    rw [Int.prime_iff_natAbs_prime] at htprime
    simpa [← hpv] using htprime
  have hptoNat : (t k).toNat = p := by omega
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro hdd
    have h1 : (p : ℤ) ≤ |C.det| := Int.le_of_dvd (abs_pos.2 hdet) ((dvd_abs _ _).2 hdd)
    have := hKB k hk
    omega
  have hvle : padicValNat c (glCard n p) ≤ k := by rw [← hptoNat]; exact hcon
  obtain ⟨j, hj1, hjd⟩ := exists_trace_pow_congr C hpnat hc hdetp hvle
  have hjd' : (p : ℤ) ∣ t (k + j) - t k := by
    rw [ht]; simpa using hjd
  have hdq0 : (p : ℤ) ∣ t (k + j) := by
    have : (p : ℤ) ∣ t k := by rw [hpv]
    simpa using dvd_add hjd' this
  have hgt : t k < t (k + j) := by
    have h1 := hmono' k hk0
    have h2 := seq_le hmono' (k + 1) (by omega) (j - 1)
    have he : k + 1 + (j - 1) = k + j := by omega
    rw [he] at h2
    omega
  have hqpos : 0 < t (k + j) := lt_trans htpos hgt
  have hqprime : Prime (t (k + j)) := hprime (k + j) (by omega)
  obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (k + j) :=
    ⟨(t (k + j)).toNat, Int.toNat_of_nonneg hqpos.le⟩
  have hqnat : q.Prime := by
    rw [Int.prime_iff_natAbs_prime] at hqprime
    simpa [← hqv] using hqprime
  have hdq : p ∣ q := by
    have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hdq0
    exact_mod_cast this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hqnat p hdq) with hh | hh
  · exact hpnat.one_lt.ne' hh
  · omega

end LeanFormalizations.Mills.SharedConjecture
