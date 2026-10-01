/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Erdos385

/-!
# Erdős #385 over `F_q[T]` (phase E1, function-field half)

The analogue Will Sawin posed in the comments on Tao's 2024-08-19 post: for monic `f` of degree
`n`, find a reducible monic `g ≠ f` of the same degree with every irreducible factor of degree
`> deg(f − g)`.  `DOOR-FF-ERDOS-385.md` closes this route; this file records its conclusions.

## Frozen statements (do not edit; prove them)

* `ffGood_of_eval_ne_zero`: a non-root `a` of `f` gives the degree-0 witness `g = f − f(a)`.
* `X_pow_card_sub_X_dvd_of_not_ffGood` (**the degeneracy finding**): a bad `f` of degree `≥ 2`
  vanishes on all of `F_q`, so `T^q − T ∣ f`.  The function-field cousin of Lemma R.
* `card_le_natDegree_of_not_ffGood`: hence every bad `f` has degree `≥ q`.
* `ffGood_of_natDegree_lt_card`: so the (i) analogue is trivial once `q > deg f`.
* `ffWitness_of_BBR` (wiring edge): BBR Thm 2.3 gives, for `q ≥ q₀(k, m)`, a witness whose
  factors all have degree `> m`, for every monic `f` of degree `k > 2m + 2`.  This is the
  large-`q` content (the (ii) / top analogues), since (i) is already trivial there.
* `ffGood_of_ffWitness`: a depth-`m` witness is a witness.

`FF385 K` (the fixed-field (i) analogue) is a `def … : Prop` node: open, and stuck at the
square-root barrier (`Literature.Gorodetsky2018Thm11` is nontrivial only for `h > n/2`).

Data: `scripts/erdos385-ff-probe.py` (exhaustive for `q ∈ {2,3,5,7}`, small degrees; bad `f`
exist over `F_2` up to degree 16 and none from 17 to 25).

## Route

* `ffGood_of_eval_ne_zero`: `g = f − C (f.eval a)` is monic of the same degree, has the root `a`,
  so is reducible when `2 ≤ deg`; `f − g` is a nonzero constant, of `natDegree 0`, and every
  irreducible factor has `natDegree ≥ 1`.
* Divisibility: all `a` are roots, the `X − C a` are pairwise coprime, so their product divides
  `f`; `FiniteField.roots_X_pow_card_sub_X` identifies the product with `X^q − X`.
* BBR edge: `a = m + 1`, `b = k − m − 1`; the count is `≥ q^{m+1}/(ab) − C q^{m+1/2} ≥ 2` for large
  `q`, and at most one shift gives `g = f`.
-/

open Polynomial

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

variable {K : Type*} [Field K]

/-- `f` is good: some reducible monic `g ≠ f` of the same degree has every irreducible factor of
degree `> deg(f − g)`.  The analogue of `F(n) > n`. -/
def FFGood (f : K[X]) : Prop :=
  ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧ ¬ Irreducible g ∧ g ≠ f ∧
    ∀ P : K[X], Irreducible P → P ∣ g → (f - g).natDegree < P.natDegree

/-- A depth-`m` witness: `deg(f − g) ≤ m` and every irreducible factor of `g` has degree `> m`. -/
def FFWitness (f : K[X]) (m : ℕ) : Prop :=
  ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧ ¬ Irreducible g ∧ g ≠ f ∧
    (f - g).natDegree ≤ m ∧ ∀ P : K[X], Irreducible P → P ∣ g → m < P.natDegree

/-- **The fixed-field (i) analogue** (open): every monic `f` of large degree is good. -/
def FF385 (K : Type*) [Field K] : Prop :=
  ∃ n₀ : ℕ, ∀ f : K[X], f.Monic → n₀ ≤ f.natDegree → FFGood f

theorem ffGood_of_ffWitness {f : K[X]} {m : ℕ} (h : FFWitness f m) : FFGood f := by
  obtain ⟨g, hg, hd, hi, hne, hm, hP⟩ := h
  exact ⟨g, hg, hd, hi, hne, fun P hPi hPg => lt_of_le_of_lt hm (hP P hPi hPg)⟩

theorem ffGood_of_eval_ne_zero {f : K[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {a : K}
    (ha : f.eval a ≠ 0) : FFGood f := by
  refine ⟨f - C (f.eval a), ?_, natDegree_sub_C, ?_, ?_, ?_⟩
  · apply hf.sub_of_left
    rw [degree_C ha, degree_eq_natDegree hf.ne_zero]; exact_mod_cast (by omega : 0 < f.natDegree)
  · intro hirr
    have := degree_eq_one_of_irreducible_of_root hirr (x := a) (by simp)
    rw [degree_eq_natDegree hirr.ne_zero, natDegree_sub_C] at this
    norm_cast at this; omega
  · intro h
    have : C (f.eval a) = 0 := by linear_combination -h
    exact ha (C_eq_zero.mp this)
  · intro P hP _
    rw [sub_sub_cancel, natDegree_C]; exact hP.natDegree_pos

/-- **The degeneracy finding.**  A bad `f` vanishes on all of `F_q`. -/
theorem X_pow_card_sub_X_dvd_of_not_ffGood [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (h : ¬ FFGood f) : (X ^ Fintype.card K - X : K[X]) ∣ f := by
  classical
  have hroot : ∀ a : K, f.eval a = 0 := fun a => by
    by_contra ha; exact h (ffGood_of_eval_ne_zero hf hd ha)
  have hq : (X ^ Fintype.card K - X : K[X]).Monic := by
    apply monic_X_pow_sub; rw [degree_X]; exact_mod_cast Fintype.one_lt_card
  have heq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq (by
    rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq _
      Fintype.one_lt_card]; rfl)
  rw [← heq, Multiset.prod_X_sub_C_dvd_iff_le_roots hf.ne_zero, FiniteField.roots_X_pow_card_sub_X,
    Multiset.le_iff_subset Finset.univ.nodup]
  intro a _
  rw [mem_roots hf.ne_zero]; exact hroot a

theorem card_le_natDegree_of_not_ffGood [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (h : ¬ FFGood f) : Fintype.card K ≤ f.natDegree := by
  have := natDegree_le_of_dvd (X_pow_card_sub_X_dvd_of_not_ffGood hf hd h) hf.ne_zero
  rwa [FiniteField.X_pow_card_sub_X_natDegree_eq _ Fintype.one_lt_card] at this

/-- The (i) analogue is trivial once the field is larger than the degree. -/
theorem ffGood_of_natDegree_lt_card [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (hq : f.natDegree < Fintype.card K) : FFGood f := by
  by_contra h; exact absurd (card_le_natDegree_of_not_ffGood hf hd h) (by omega)

theorem shortIntervalPoly_coeff_shift {L : Type*} [Field L] (m : ℕ) (c : Fin (m + 1) → L)
    (i : Fin (m + 1)) : (∑ j : Fin (m + 1), C (c j) * X ^ (j : ℕ)).coeff i = c i := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg]; exact fun h => hj (Fin.ext h.symm)
  · simp

theorem natDegree_eq_of_irreducible_dvd {L : Type*} [Field L] {P A : L[X]} (hP : Irreducible P)
    (hA : Irreducible A) (h : P ∣ A) : P.natDegree = A.natDegree := by
  obtain ⟨u, hu⟩ := hP.associated_of_dvd hA h
  rw [← hu, natDegree_mul hP.ne_zero (Units.ne_zero u), natDegree_eq_zero_of_isUnit u.isUnit,
    add_zero]

theorem real_count_ge_two {t s ab Cc N : ℝ} (hab : 0 < ab) (ht : 1 ≤ t)
    (hs : ab * (|Cc| + 2) ≤ s) (hN : |N - t * s / ab| ≤ Cc * t) : 2 ≤ N := by
  have h1 : t * (|Cc| + 2) ≤ t * s / ab := by
    rw [le_div_iff₀ hab]; nlinarith
  have := (abs_le.mp hN).1
  have : Cc ≤ |Cc| := le_abs_self Cc
  nlinarith


/-- **Wiring edge: BBR ⇒ large-`q` depth-`m` witnesses.** -/
theorem ffWitness_of_BBR (hBBR : BBR2015Thm23TwoFactor) {k m : ℕ} (hm : 3 ≤ m)
    (hk : 2 * m + 3 ≤ k) :
    ∃ q₀ : ℕ, ∀ (L : Type) [Field L] [Fintype L], q₀ ≤ Fintype.card L →
      ∀ f : L[X], f.Monic → f.natDegree = k → FFWitness f m := by
  obtain ⟨Cc, hC⟩ := hBBR k m (m + 1) (k - m - 1) hm (by omega) (by omega) (by omega) (by omega)
  set ab : ℝ := ((m + 1 : ℕ) : ℝ) * ((k - m - 1 : ℕ) : ℝ) with hab_def
  have hab : 0 < ab := by
    rw [hab_def]; apply mul_pos <;> exact_mod_cast (by omega)
  refine ⟨⌈(ab * (|Cc| + 2)) ^ 2⌉₊ + 1, fun L _ _ hq f hf hfk => ?_⟩
  classical
  set q : ℝ := (Fintype.card L : ℝ) with hq_def
  have hq1 : 1 ≤ q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hq0 : 0 ≤ q := by linarith
  have hsq : ab * (|Cc| + 2) ≤ Real.sqrt q := by
    apply Real.le_sqrt_of_sq_le
    have := Nat.le_ceil ((ab * (|Cc| + 2)) ^ 2)
    have : ((⌈(ab * (|Cc| + 2)) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ q := by rw [hq_def]; exact_mod_cast hq
    push_cast at this; linarith
  have hsplit : q ^ (m + 1) = q ^ ((m : ℝ) + 1 / 2) * Real.sqrt q := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith), ← Real.rpow_natCast]; push_cast; ring_nf
  have hcount := hC L f hf hfk
  rw [hsplit] at hcount
  have hcast : (((m + 1 : ℕ) : ℝ) * ((k - m - 1 : ℕ) : ℝ)) = ab := rfl
  have h2 : 2 ≤ (Nat.card {c : Fin (m + 1) → L //
      IsTwoPrimeType (m + 1) (k - m - 1) (shortIntervalPoly f m c)} : ℝ) :=
    real_count_ge_two (t := q ^ ((m:ℝ) + 1/2)) hab (Real.one_le_rpow hq1 (by positivity)) hsq (by
      rw [← hq_def] at hcount; rw [mul_div_assoc] at hcount ⊢; exact hcount)
  have h2' : 1 < Nat.card {c : Fin (m + 1) → L //
      IsTwoPrimeType (m + 1) (k - m - 1) (shortIntervalPoly f m c)} := by exact_mod_cast h2
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩, hne⟩ := (Finite.one_lt_card_iff_nontrivial.mp h2').exists_pair_ne
  have key : ∃ c, IsTwoPrimeType (m + 1) (k - m - 1) (shortIntervalPoly f m c) ∧
      shortIntervalPoly f m c ≠ f := by
    by_contra hcon; push Not at hcon
    apply hne; congr 1; funext i
    have e1 := congrArg (fun p => (p - f).coeff i) (hcon c₁ h₁)
    have e2 := congrArg (fun p => (p - f).coeff i) (hcon c₂ h₂)
    simp only [shortIntervalPoly, add_sub_cancel_left, sub_self,
      shortIntervalPoly_coeff_shift] at e1 e2
    rw [e1, e2]
  obtain ⟨c, ⟨A, B, hAm, hBm, hA, hB, hAd, hBd, hg⟩, hgf⟩ := key
  have hsh : (∑ j : Fin (m + 1), C (c j) * X ^ (j : ℕ)).degree < ((m + 1 : ℕ) : WithBot ℕ) :=
    degree_sum_fin_lt _
  have hlt : (∑ j : Fin (m + 1), C (c j) * X ^ (j : ℕ)).degree < f.degree := by
    refine hsh.trans_le ?_
    rw [degree_eq_natDegree hf.ne_zero, hfk]; exact_mod_cast (by omega)
  refine ⟨shortIntervalPoly f m c, hf.add_of_left hlt, ?_, ?_, hgf, ?_, ?_⟩
  · exact (natDegree_add_eq_left_of_degree_lt hlt).trans rfl
  · rw [hg]; intro hirr
    rcases hirr.isUnit_or_isUnit rfl with h | h
    · exact hA.not_isUnit h
    · exact hB.not_isUnit h
  · simp only [shortIntervalPoly, sub_add_cancel_left, natDegree_neg]
    by_cases h0 : (∑ j : Fin (m + 1), C (c j) * X ^ (j : ℕ)) = 0
    · rw [h0, natDegree_zero]; omega
    · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h0).mpr hsh)
  · intro P hP hPg
    rw [hg] at hPg
    rcases hP.prime.dvd_or_dvd hPg with h | h
    · rw [natDegree_eq_of_irreducible_dvd hP hA h, hAd]; omega
    · rw [natDegree_eq_of_irreducible_dvd hP hB h, hBd]; omega

end LeanFormalizations.Erdos385
