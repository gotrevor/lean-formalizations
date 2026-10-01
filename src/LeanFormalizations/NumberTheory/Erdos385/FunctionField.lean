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
  sorry

theorem ffGood_of_eval_ne_zero {f : K[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {a : K}
    (ha : f.eval a ≠ 0) : FFGood f := by
  sorry

/-- **The degeneracy finding.**  A bad `f` vanishes on all of `F_q`. -/
theorem X_pow_card_sub_X_dvd_of_not_ffGood [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (h : ¬ FFGood f) : (X ^ Fintype.card K - X : K[X]) ∣ f := by
  sorry

theorem card_le_natDegree_of_not_ffGood [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (h : ¬ FFGood f) : Fintype.card K ≤ f.natDegree := by
  sorry

/-- The (i) analogue is trivial once the field is larger than the degree. -/
theorem ffGood_of_natDegree_lt_card [Fintype K] {f : K[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree) (hq : f.natDegree < Fintype.card K) : FFGood f := by
  sorry

/-- **Wiring edge: BBR ⇒ large-`q` depth-`m` witnesses.** -/
theorem ffWitness_of_BBR (hBBR : BBR2015Thm23TwoFactor) {k m : ℕ} (hm : 3 ≤ m)
    (hk : 2 * m + 3 ≤ k) :
    ∃ q₀ : ℕ, ∀ (L : Type) [Field L] [Fintype L], q₀ ≤ Fintype.card L →
      ∀ f : L[X], f.Monic → f.natDegree = k → FFWitness f m := by
  sorry

end LeanFormalizations.Erdos385
