/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The self-similar sieve class and the exact Buchstab identity (phase E5, layer A)

A *problem* is an integer interval `[lo, lo + N)` with one excluded class `r q (mod q)` per prime
`q < z`; `sift lo N r z` counts its survivors.  The class is self-similar: the survivors of the
sieve by primes `q < p` that lie in the excluded class mod `p` are, after `k = r p + p j`, the
survivors of another problem of length `≈ N/p` sifted by primes `< p` (`sub_problem`).  With the
exact Buchstab identity (`sift_buchstab`) this gives the two inequalities on the extremal counts
`siftMin`, `siftMax` that drive the whole linear-sieve analysis (`siftMin_buchstab`,
`siftMax_buchstab`).
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset

/-- `k` survives the sieve by the primes `q < z` with excluded classes `r q (mod q)`. -/
def Survives (r : ℕ → ℤ) (z : ℕ) (k : ℤ) : Prop :=
  ∀ q, q.Prime → q < z → ¬ (q : ℤ) ∣ k - r q

open Classical in
/-- Number of survivors in `[lo, lo + N)`. -/
noncomputable def sift (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z : ℕ) : ℕ :=
  ((Ico lo (lo + N)).filter (Survives r z)).card

open Classical in
/-- Survivors of the sieve by primes `< p` lying in the excluded class mod `p`. -/
noncomputable def hit (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (p : ℕ) : ℕ :=
  ((Ico lo (lo + N)).filter (fun k => Survives r p k ∧ (p : ℤ) ∣ k - r p)).card

lemma survives_succ (r : ℕ → ℤ) (z : ℕ) (k : ℤ) :
    Survives r (z + 1) k ↔ Survives r z k ∧ (z.Prime → ¬ (z : ℤ) ∣ k - r z) := by
  constructor
  · intro h
    exact ⟨fun q hq hqz => h q hq (by omega), fun hz => h z hz (by omega)⟩
  · rintro ⟨h1, h2⟩ q hq hqz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hqz with h | h
    · exact h1 q hq h
    · subst h; exact h2 hq

lemma sift_succ (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z : ℕ) :
    sift lo N r z = sift lo N r (z + 1) + (if z.Prime then hit lo N r z else 0) := by
  classical
  unfold sift hit
  split_ifs with hz
  · rw [← card_union_of_disjoint]
    · congr 1
      ext k
      simp only [mem_filter, mem_union, survives_succ]
      constructor
      · rintro ⟨hk, hs⟩
        by_cases hd : (z : ℤ) ∣ k - r z
        · exact Or.inr ⟨hk, hs, hd⟩
        · exact Or.inl ⟨hk, hs, fun _ => hd⟩
      · rintro (⟨hk, hs, _⟩ | ⟨hk, hs, _⟩) <;> exact ⟨hk, hs⟩
    · rw [disjoint_filter]
      intro k _ h1 h2
      exact ((survives_succ r z k).mp h1).2 hz h2.2
  · simp only [add_zero]
    congr 1
    ext k
    simp only [mem_filter, survives_succ]
    exact ⟨fun ⟨hk, hs⟩ => ⟨hk, hs, fun h => absurd h hz⟩, fun ⟨hk, hs, _⟩ => ⟨hk, hs⟩⟩

/-- **Buchstab's identity**, exact: `S(w) = S(z) + Σ_{w ≤ p < z} S(A_p, p)`. -/
theorem sift_buchstab (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) {w z : ℕ} (hwz : w ≤ z) :
    sift lo N r w = sift lo N r z + ∑ p ∈ (Ico w z).filter Nat.Prime, hit lo N r p := by
  induction z, hwz using Nat.le_induction with
  | base => simp
  | succ z hwz ih =>
    rw [ih, sift_succ lo N r z, Nat.Ico_succ_right_eq_insert_Ico hwz, filter_insert]
    split_ifs with hz
    · rw [sum_insert (by simp)]; ring
    · simp

lemma sift_le (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z : ℕ) : sift lo N r z ≤ N := by
  classical
  unfold sift
  refine (card_filter_le _ _).trans ?_
  simp

lemma sift_two (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) : sift lo N r 2 = N := by
  classical
  unfold sift
  rw [filter_true_of_mem]
  · simp
  · intro k _ q hq hq2
    exact absurd hq.two_le (by omega)

/-- Inverse of a prime `p` modulo a smaller prime `q`. -/
lemma exists_inv_mod {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    ∃ u v : ℤ, u * p + v * q = 1 := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hc)

/-- The transported excluded classes. -/
noncomputable def subClass (r : ℕ → ℤ) (p : ℕ) (q : ℕ) : ℤ :=
  if h : p.Prime ∧ q.Prime ∧ q < p then (exists_inv_mod h.1 h.2.1 h.2.2).choose * (r q - r p)
  else 0

lemma dvd_iff_subClass (r : ℕ → ℤ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (j : ℤ) : (q : ℤ) ∣ (r p + p * j) - r q ↔ (q : ℤ) ∣ j - subClass r p q := by
  have h := (exists_inv_mod hp hq hqp).choose_spec
  set u := (exists_inv_mod hp hq hqp).choose
  obtain ⟨v, hv⟩ := h
  have hs : subClass r p q = u * (r q - r p) := by
    simp [subClass, hp, hq, hqp, u]
  rw [hs]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨u * c + v * j, by linear_combination (-1 : ℤ) * j * hv + u * hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨p * c - v * (r q - r p), ?_⟩
    linear_combination (p : ℤ) * hc + (r q - r p) * hv

lemma survives_sub (r : ℕ → ℤ) {p : ℕ} (hp : p.Prime) (j : ℤ) :
    Survives r p (r p + p * j) ↔ Survives (subClass r p) p j := by
  constructor
  · intro h q hq hqp
    rw [← dvd_iff_subClass r hp hq hqp]; exact h q hq hqp
  · intro h q hq hqp
    rw [dvd_iff_subClass r hp hq hqp]; exact h q hq hqp

/-- **Self-similarity.**  `S(A_p, p)` is the count of another problem, of length `N' ≈ N/p`. -/
theorem hit_eq_sift (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) {p : ℕ} (hp : p.Prime) :
    ∃ lo' : ℤ, ∃ N' : ℕ, N' * p ≤ N + p ∧ N ≤ (N' + 1) * p ∧
      hit lo N r p = sift lo' N' (subClass r p) p := by
  classical
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  set a : ℤ := r p - lo
  set b : ℤ := lo + N - r p - 1
  set A : ℤ := a / p
  set B : ℤ := b / p
  have ha := Int.mul_ediv_add_emod a p
  have hb := Int.mul_ediv_add_emod b p
  have ha1 := Int.emod_nonneg a hp0.ne'
  have hb1 := Int.emod_nonneg b hp0.ne'
  have ha2 := Int.emod_lt_of_pos a hp0
  have hb2 := Int.emod_lt_of_pos b hp0
  refine ⟨-A, (B + 1 + A).toNat, ?_, ?_, ?_⟩
  · rcases le_or_gt 0 (B + 1 + A) with h | h
    · have : ((B + 1 + A).toNat : ℤ) = B + 1 + A := Int.toNat_of_nonneg h
      have : (((B + 1 + A).toNat * p : ℕ) : ℤ) ≤ ((N + p : ℕ) : ℤ) := by
        push_cast; rw [this]; nlinarith
      exact_mod_cast this
    · rw [Int.toNat_of_nonpos h.le]; omega
  · rcases le_or_gt 0 (B + 1 + A) with h | h
    · have e : ((B + 1 + A).toNat : ℤ) = B + 1 + A := Int.toNat_of_nonneg h
      have : ((N : ℕ) : ℤ) ≤ ((((B + 1 + A).toNat + 1) * p : ℕ) : ℤ) := by
        push_cast; rw [e]; nlinarith
      exact_mod_cast this
    · rw [Int.toNat_of_nonpos h.le]
      have : B + 1 + A ≤ -1 := by omega
      have : ((N : ℕ) : ℤ) ≤ (p : ℤ) := by nlinarith
      simpa using this
  · unfold hit sift
    have hinj : Function.Injective (fun j : ℤ => r p + p * j) := by
      intro x y hxy; simp only at hxy
      exact mul_left_cancel₀ hp0.ne' (by linarith)
    refine Eq.trans ?_ (card_image_of_injective _ hinj)
    congr 1
    refine Finset.ext fun k => ?_
    simp only [mem_filter, mem_image, mem_Ico]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hs, ⟨c, hc⟩⟩
      refine ⟨c, ⟨⟨?_, ?_⟩, ?_⟩, by linarith⟩
      · have : -c ≤ A := by
          rw [Int.le_ediv_iff_mul_le hp0]; nlinarith
        linarith
      · have : c ≤ B := by
          rw [Int.le_ediv_iff_mul_le hp0]; nlinarith
        omega
      · rw [← survives_sub r hp]
        have : r p + p * c = k := by linarith
        rwa [this]
    · rintro ⟨j, ⟨⟨hj1, hj2⟩, hs⟩, rfl⟩
      have hjB : j ≤ B := by omega
      have h1 : -j ≤ A := by linarith
      rw [Int.le_ediv_iff_mul_le hp0] at h1 hjB
      refine ⟨⟨by nlinarith, by nlinarith⟩, (survives_sub r hp j).mpr hs, ⟨j, by ring⟩⟩

/-- The least survivor count over all problems of length `N` sifted by the primes `< z`. -/
noncomputable def siftMin (N z : ℕ) : ℕ := sInf {c | ∃ lo r, c = sift lo N r z}

/-- The largest survivor count over all problems of length `N` sifted by the primes `< z`. -/
noncomputable def siftMax (N z : ℕ) : ℕ := sSup {c | ∃ lo r, c = sift lo N r z}

lemma siftMin_le (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z : ℕ) : siftMin N z ≤ sift lo N r z :=
  Nat.sInf_le ⟨lo, r, rfl⟩

lemma bddAbove_sift (N z : ℕ) : BddAbove {c | ∃ lo r, c = sift lo N r z} :=
  ⟨N, by rintro c ⟨lo, r, rfl⟩; exact sift_le lo N r z⟩

lemma le_siftMax (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z : ℕ) : sift lo N r z ≤ siftMax N z :=
  le_csSup (bddAbove_sift N z) ⟨lo, r, rfl⟩

lemma exists_sift_eq_siftMin (N z : ℕ) : ∃ lo r, sift lo N r z = siftMin N z := by
  obtain ⟨lo, r, h⟩ := Nat.sInf_mem (s := {c | ∃ lo r, c = sift lo N r z}) ⟨_, 0, fun _ => 0, rfl⟩
  exact ⟨lo, r, h.symm⟩

lemma siftMax_le (N z : ℕ) : siftMax N z ≤ N :=
  csSup_le ⟨_, 0, fun _ => 0, rfl⟩ (by rintro c ⟨lo, r, rfl⟩; exact sift_le lo N r z)

lemma sift_mono_length (lo : ℤ) {N M : ℕ} (h : N ≤ M) (r : ℕ → ℤ) (z : ℕ) :
    sift lo N r z ≤ sift lo M r z := by
  classical
  unfold sift
  refine card_le_card (filter_subset_filter _ (Ico_subset_Ico le_rfl ?_))
  have : (N : ℤ) ≤ M := by exact_mod_cast h
  linarith

lemma siftMax_mono {N M : ℕ} (h : N ≤ M) (z : ℕ) : siftMax N z ≤ siftMax M z :=
  csSup_le ⟨_, 0, fun _ => 0, rfl⟩ (by
    rintro c ⟨lo, r, rfl⟩; exact (sift_mono_length lo h r z).trans (le_siftMax lo M r z))

lemma siftMin_mono {N M : ℕ} (h : N ≤ M) (z : ℕ) : siftMin N z ≤ siftMin M z := by
  obtain ⟨lo, r, hr⟩ := exists_sift_eq_siftMin M z
  rw [← hr]
  exact (siftMin_le lo N r z).trans (sift_mono_length lo h r z)

lemma hit_le_siftMax (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) {p : ℕ} (hp : p.Prime) :
    hit lo N r p ≤ siftMax (N / p + 1) p := by
  obtain ⟨lo', N', h1, _, h3⟩ := hit_eq_sift lo N r hp
  rw [h3]
  refine (le_siftMax _ _ _ _).trans (siftMax_mono ?_ p)
  have : N' ≤ (N + p) / p := (Nat.le_div_iff_mul_le hp.pos).mpr h1
  rwa [Nat.add_div_right _ hp.pos] at this

lemma siftMin_le_hit (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) {p : ℕ} (hp : p.Prime) :
    siftMin (N / p - 1) p ≤ hit lo N r p := by
  obtain ⟨lo', N', _, h2, h3⟩ := hit_eq_sift lo N r hp
  rw [h3]
  refine (siftMin_mono ?_ p).trans (siftMin_le _ _ _ _)
  have : N / p ≤ N' + 1 := (Nat.div_le_iff_le_mul_add_pred hp.pos).mpr (by nlinarith)
  omega

/-- **Buchstab, lower form**: `S⁻(N, w) ≤ S⁻(N, z) + Σ_{w ≤ p < z} S⁺(N/p + 1, p)`. -/
theorem siftMin_buchstab (N : ℕ) {w z : ℕ} (hwz : w ≤ z) :
    siftMin N w ≤ siftMin N z + ∑ p ∈ (Ico w z).filter Nat.Prime, siftMax (N / p + 1) p := by
  obtain ⟨lo, r, hr⟩ := exists_sift_eq_siftMin N z
  rw [← hr]
  refine (siftMin_le lo N r w).trans ?_
  rw [sift_buchstab lo N r hwz]
  gcongr with p hp
  exact hit_le_siftMax lo N r (mem_filter.mp hp).2

/-- **Buchstab, upper form**: `S⁺(N, z) + Σ_{w ≤ p < z} S⁻(N/p − 1, p) ≤ S⁺(N, w)`. -/
theorem siftMax_buchstab (N : ℕ) {w z : ℕ} (hwz : w ≤ z) :
    siftMax N z + ∑ p ∈ (Ico w z).filter Nat.Prime, siftMin (N / p - 1) p ≤ siftMax N w := by
  obtain ⟨lo, r, hr⟩ := Nat.sSup_mem (s := {c | ∃ lo r, c = sift lo N r z})
    ⟨_, 0, fun _ => 0, rfl⟩ (bddAbove_sift N z)
  change siftMax N z = _ at hr
  rw [hr]
  refine le_trans ?_ (le_siftMax lo N r w)
  rw [sift_buchstab lo N r hwz]
  gcongr with p hp
  exact siftMin_le_hit lo N r (mem_filter.mp hp).2

end LeanFormalizations.Erdos385.LinearSieve
