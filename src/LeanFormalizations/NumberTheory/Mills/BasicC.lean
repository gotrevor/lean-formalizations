/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The Mills construction for a general exponent `c ≥ 2`

A verbatim generalisation of `Mills/Basic.lean` from the exponent `3` to an arbitrary integer
`c ≥ 2`.  Saito (2024) needs it for `ξ_c`, the least `A > 1` with `⌊A^(c^n)⌋` prime for every
`n ≥ 1` (`IsMillsC c`, `Mills/Transcendental.lean`).

Nothing here is new mathematics: the nested-interval engine never used `3` for anything except
(i) `m ≤ m^c`, (ii) `(m+1)^c − 1` being composite, and (iii) `(x^c)^(c^(k+1))⁻¹ = x^(c^k)⁻¹`.
Only (ii) needed a new proof: for `c = 3` the old file factored `(n+1)³ − 1` by hand, whereas in
general one observes `n ∣ (n+1)^c − 1` because `n + 1 ≡ 1 [MOD n]`.

The statements are phrased in raw `∀ n : ℕ+, Prime ⌊A ^ (c ^ n)⌋₊` form rather than via
`IsMillsC`, so that this file need not import `Transcendental.lean` (which defines `IsMillsC`
and would create a cycle); the two are definitionally equal.
-/
import Mathlib

namespace LeanFormalizations.Mills

/-- The analytic input for exponent `c`: from `N` on, every gap between consecutive `c`-th
powers contains a prime. -/
def PrimeBetweenPowsFrom (c N : ℕ) : Prop :=
  ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ n ^ c < p ∧ p < (n + 1) ^ c

/-- `(n+1)^c − 1` is composite for `n ≥ 2`, `c ≥ 2` (it is divisible by `n`), so a prime below
`(n+1)^c` is at most `(n+1)^c − 2`. -/
theorem prime_add_one_lt_pow {n p c : ℕ} (hn : 2 ≤ n) (hc : 2 ≤ c) (hp : p.Prime)
    (hlt : p < (n + 1) ^ c) : p + 1 < (n + 1) ^ c := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with h | h
  · exact h
  exfalso
  -- `n ∣ (n+1)^c − 1 = p`
  have hmod : (n + 1) ^ c ≡ 1 ^ c [MOD n] := Nat.ModEq.pow c (by simp [Nat.ModEq, Nat.add_mod])
  rw [one_pow] at hmod
  have hge : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have hdvd : n ∣ (n + 1) ^ c - 1 := (Nat.modEq_iff_dvd' hge).1 hmod.symm
  have hpe : p = (n + 1) ^ c - 1 := by omega
  rw [← hpe] at hdvd
  rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | h2
  · omega
  · -- `p = n`, but `p + 1 = (n+1)^c ≥ (n+1)² > n + 1`
    have : (n + 1) ^ 2 ≤ (n + 1) ^ c := Nat.pow_le_pow_right (by omega) hc
    nlinarith [h, h2]

section Construction

variable {c N : ℕ} (hc : 2 ≤ c) (h : PrimeBetweenPowsFrom c N)

private noncomputable def powStep (m : ℕ) : ℕ := if hm : N ≤ m then (h m hm).choose else 2

include hc h in
private lemma powStep_spec {m : ℕ} (hm : N ≤ m) (hm2 : 2 ≤ m) :
    (powStep h m).Prime ∧ m ^ c < powStep h m ∧ powStep h m + 1 < (m + 1) ^ c := by
  have hs := (h m hm).choose_spec
  have he : powStep h m = (h m hm).choose := by rw [powStep, dif_pos hm]
  rw [he]
  exact ⟨hs.1, hs.2.1, prime_add_one_lt_pow hm2 hc hs.1 hs.2.2⟩

/-- The chain started at a chosen `m₀`: `m₀`, then a prime strictly between the `c`-th powers of
the previous term and its successor, forever. -/
private noncomputable def powSeq (m₀ : ℕ) : ℕ → ℕ
  | 0 => m₀
  | k + 1 => powStep h (powSeq m₀ k)

variable {m₀ : ℕ} (hm₀ : max N 2 ≤ m₀)

include hc h hm₀ in
private lemma powSeq_ge (k : ℕ) : max N 2 ≤ powSeq h m₀ k := by
  induction k with
  | zero => exact hm₀
  | succ k ih =>
      have hN : N ≤ powSeq h m₀ k := le_trans (le_max_left _ _) ih
      have h2 : 2 ≤ powSeq h m₀ k := le_trans (le_max_right _ _) ih
      obtain ⟨hq, hlo, _⟩ := powStep_spec hc h hN h2
      have : powSeq h m₀ k ≤ (powSeq h m₀ k) ^ c := Nat.le_self_pow (by omega) _
      show max N 2 ≤ powStep h (powSeq h m₀ k)
      omega

include hc h hm₀ in
private lemma powSeq_prime_succ (k : ℕ) : (powSeq h m₀ (k + 1)).Prime := by
  have ih := powSeq_ge hc h hm₀ k
  exact (powStep_spec hc h (le_trans (le_max_left _ _) ih) (le_trans (le_max_right _ _) ih)).1

include hc h hm₀ in
private lemma powSeq_lower (k : ℕ) : (powSeq h m₀ k) ^ c < powSeq h m₀ (k + 1) := by
  have hge := powSeq_ge hc h hm₀ k
  exact (powStep_spec hc h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.1

include hc h hm₀ in
private lemma powSeq_upper (k : ℕ) : powSeq h m₀ (k + 1) + 1 < (powSeq h m₀ k + 1) ^ c := by
  have hge := powSeq_ge hc h hm₀ k
  exact (powStep_spec hc h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.2

/-- Left endpoints of the nested intervals in `A`-space. -/
private noncomputable def muC (m₀ k : ℕ) : ℝ :=
  (powSeq h m₀ k : ℝ) ^ (((c ^ k : ℕ) : ℝ))⁻¹
/-- Right endpoints of the nested intervals in `A`-space. -/
private noncomputable def nuC (m₀ k : ℕ) : ℝ :=
  ((powSeq h m₀ k : ℝ) + 1) ^ (((c ^ k : ℕ) : ℝ))⁻¹

include hc in
private lemma expC_pos (k : ℕ) : (0:ℝ) < (((c ^ k : ℕ) : ℝ))⁻¹ := by
  have : 0 < c ^ k := Nat.pow_pos (by omega)
  positivity

include hc in
/-- `(x^c) ^ (c^(k+1))⁻¹ = x ^ (c^k)⁻¹`. -/
private lemma pow_root_step {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ c) ^ (((c ^ (k+1) : ℕ) : ℝ))⁻¹ = x ^ (((c ^ k : ℕ) : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast x c, ← Real.rpow_mul hx]
  congr 1
  have hcne : ((c : ℕ) : ℝ) ≠ 0 := by positivity
  have hk : ((c ^ k : ℕ) : ℝ) ≠ 0 := by
    have : 0 < c ^ k := Nat.pow_pos (by omega)
    positivity
  push_cast
  field_simp
  ring

include hc h hm₀ in
private lemma muC_lt_succ (k : ℕ) : muC h m₀ k < muC h m₀ (k + 1) := by
  have hbase : (0:ℝ) ≤ ((powSeq h m₀ k : ℝ)) ^ c := by positivity
  have hlt : ((powSeq h m₀ k : ℝ)) ^ c < (powSeq h m₀ (k+1) : ℝ) := by
    have := powSeq_lower hc h hm₀ k; exact_mod_cast this
  have := Real.rpow_lt_rpow hbase hlt (expC_pos hc (k+1))
  rwa [pow_root_step hc (by positivity) k] at this

include hc h hm₀ in
private lemma nuC_succ_lt (k : ℕ) : nuC h m₀ (k + 1) < nuC h m₀ k := by
  have hbase : (0:ℝ) ≤ (powSeq h m₀ (k+1) : ℝ) + 1 := by positivity
  have hlt : (powSeq h m₀ (k+1) : ℝ) + 1 < ((powSeq h m₀ k : ℝ) + 1) ^ c := by
    have := powSeq_upper hc h hm₀ k
    have hcc : ((powSeq h m₀ (k+1) + 1 : ℕ) : ℝ) < (((powSeq h m₀ k + 1) ^ c : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcc; linarith
  have := Real.rpow_lt_rpow hbase hlt (expC_pos hc (k+1))
  rwa [pow_root_step hc (by positivity) k] at this

include hc h in
private lemma muC_lt_nuC (k : ℕ) : muC h m₀ k < nuC h m₀ k :=
  Real.rpow_lt_rpow (by positivity) (by linarith) (expC_pos hc k)

include hc h hm₀ in
private lemma muC_le_nuC (m k : ℕ) : muC h m₀ m ≤ nuC h m₀ k := by
  have hmono : Monotone (muC h m₀) :=
    monotone_nat_of_le_succ fun n => (muC_lt_succ hc h hm₀ n).le
  have hanti : Antitone (nuC h m₀) :=
    antitone_nat_of_succ_le fun n => (nuC_succ_lt hc h hm₀ n).le
  rcases le_total m k with hmk | hmk
  · exact le_trans (hmono hmk) (muC_lt_nuC hc h k).le
  · exact le_trans (muC_lt_nuC hc h m).le (hanti hmk)

include hc h hm₀ in
private lemma muC_bddAbove : BddAbove (Set.range (muC h m₀)) :=
  ⟨nuC h m₀ 0, by rintro _ ⟨m, rfl⟩; exact muC_le_nuC hc h hm₀ m 0⟩

include hc h in
private lemma pow_muC (k : ℕ) : (muC h m₀ k) ^ (c ^ k) = (powSeq h m₀ k : ℝ) := by
  refine Real.rpow_inv_natCast_pow (by positivity) ?_
  have : 0 < c ^ k := Nat.pow_pos (by omega)
  omega

include hc h in
private lemma pow_nuC (k : ℕ) : (nuC h m₀ k) ^ (c ^ k) = (powSeq h m₀ k : ℝ) + 1 := by
  refine Real.rpow_inv_natCast_pow (by positivity) ?_
  have : 0 < c ^ k := Nat.pow_pos (by omega)
  omega

include hc h hm₀ in
private lemma floor_pow_iSupC (k : ℕ) :
    ⌊(⨆ n, muC h m₀ n) ^ (c ^ k)⌋₊ = powSeq h m₀ k := by
  set A : ℝ := ⨆ n, muC h m₀ n with hA
  have hlo : muC h m₀ k < A :=
    lt_of_lt_of_le (muC_lt_succ hc h hm₀ k) (le_ciSup (muC_bddAbove hc h hm₀) (k+1))
  have hhi : A < nuC h m₀ k :=
    lt_of_le_of_lt (ciSup_le fun m => muC_le_nuC hc h hm₀ m (k+1)) (nuC_succ_lt hc h hm₀ k)
  have hmupos : (0:ℝ) ≤ muC h m₀ k := by unfold muC; positivity
  have hck : 0 < c ^ k := Nat.pow_pos (by omega)
  have h1 : (powSeq h m₀ k : ℝ) < A ^ (c ^ k) := by
    rw [← pow_muC hc h k]; exact pow_lt_pow_left₀ hlo hmupos (by omega)
  have h2 : A ^ (c ^ k) < (powSeq h m₀ k : ℝ) + 1 := by
    rw [← pow_nuC hc h k]
    exact pow_lt_pow_left₀ hhi (le_of_lt (lt_of_le_of_lt hmupos hlo)) (by omega)
  have hnn : (0:ℝ) ≤ A ^ (c ^ k) := le_trans (Nat.cast_nonneg _) h1.le
  rw [Nat.floor_eq_iff hnn]
  exact ⟨h1.le, h2⟩

include hc h hm₀ in
private lemma iSup_muC_lt : (⨆ n, muC h m₀ n) < (m₀ : ℝ) + 1 := by
  have h0 : nuC h m₀ 0 = (m₀ : ℝ) + 1 := by simp [nuC, powSeq]
  have := lt_of_le_of_lt (ciSup_le fun m => muC_le_nuC hc h hm₀ m 1) (nuC_succ_lt hc h hm₀ 0)
  rwa [h0] at this

include hc h hm₀ in
private lemma le_iSup_muC : (m₀ : ℝ) ≤ ⨆ n, muC h m₀ n := by
  have h0 : muC h m₀ 0 = (m₀ : ℝ) := by simp [muC, powSeq]
  have := le_ciSup (muC_bddAbove hc h hm₀) 0
  rwa [h0] at this

end Construction

/-- **Mills' theorem for exponent `c`**, conditional on primes between consecutive `c`-th
powers: starting the chain at any `m₀ ≥ max N 2` gives such a number in `[m₀, m₀ + 1)`. -/
theorem exists_millsC_lt_of_primeBetweenPows {c N m₀ : ℕ} (hc : 2 ≤ c)
    (h : PrimeBetweenPowsFrom c N) (hm₀ : max N 2 ≤ m₀) :
    ∃ A, 1 < A ∧ (∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) ∧ A < (m₀ : ℝ) + 1 := by
  have h2 : (2:ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast le_trans (le_max_right N 2) hm₀
  refine ⟨⨆ n, muC h m₀ n, ?_, fun n => ?_, iSup_muC_lt hc h hm₀⟩
  · have := le_iSup_muC hc h hm₀; linarith
  · obtain ⟨k, hk⟩ : ∃ k, ((n : ℕ)) = k + 1 := ⟨(n : ℕ) - 1, by have h : 0 < (n : ℕ) := n.2; omega⟩
    rw [hk, floor_pow_iSupC hc h hm₀ (k + 1)]
    exact (powSeq_prime_succ hc h hm₀ k).prime

/-- **Mills' theorem for exponent `c`**, existence form. -/
theorem exists_millsC_of_primeBetweenPows {c N : ℕ} (hc : 2 ≤ c)
    (h : PrimeBetweenPowsFrom c N) :
    ∃ A : ℝ, A > 1 ∧ (∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) := by
  obtain ⟨A, hA1, hA, -⟩ := exists_millsC_lt_of_primeBetweenPows hc h (le_refl (max N 2))
  exact ⟨A, hA1, hA⟩

end LeanFormalizations.Mills
