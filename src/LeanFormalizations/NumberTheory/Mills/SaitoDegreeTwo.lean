/-
# Saito §4, Lemmas 4.2 and 4.3: the degree-two Pisot alternative

For `b ∈ {3, 4}` the Claim of Lemma 4.1 does not close by itself (`μ = 19c/40 − 1` is `9/10`
at `c = 4` and `17/40` at `c = 3`), and one is left with `ξ^(C_m)` a Pisot number of degree 2
(and, at `c = 3`, degree 3 as well — that case is Saito's open Remark 4.4).  This file kills
degree 2.

## The structural observation that makes it cheap

A Pisot number `β` of degree 2 has exactly one other conjugate, and that conjugate is a **real**
number `w`, with no field theory needed to see it: `β + Σ_{j≥2} β_j` is a rational integer
`t₁` (`pisot_conjPowSum_add_mem_int` at `n = 1`), and the sum over a one-element multiset is its
element, so the conjugate is literally `t₁ − β : ℝ`.  Everything downstream — `βw ∈ ℤ`,
`w^n > 0` for even `n`, the cubing recurrence — is then real arithmetic.
-/
import LeanFormalizations.NumberTheory.Mills.SaitoPisot

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature Filter Polynomial

/-- **A degree-2 Pisot number's other conjugate is a real number `w` with `|w| < 1`.** -/
theorem exists_real_conj_of_natDegree_two {β : ℝ} (hβ : IsPisot β)
    (hdeg : (minpoly ℚ β).natDegree = 2) :
    ∃ w : ℝ, otherConj β = {(w : ℂ)} ∧ |w| < 1 ∧ (∃ t : ℤ, β + w = (t : ℝ)) := by
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hcard : Multiset.card (otherConj β) = 1 := by
    have := card_otherConj_add_one halg
    omega
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 hcard
  -- the sum over the singleton is `z`
  obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ 1
  have hsum : conjPowSum β 1 = z := by
    simp [conjPowSum, hz]
  rw [hsum, pow_one] at ht
  refine ⟨(t : ℝ) - β, ?_, ?_, ⟨t, by ring⟩⟩
  · have hzr : z = (((t : ℝ) - β : ℝ) : ℂ) := by
      push_cast
      linear_combination ht
    rw [hz, hzr]
  · have hmem : z ∈ otherConj β := by rw [hz]; simp
    have := hβ.2.2 z hmem
    have hzr : z = (((t : ℝ) - β : ℝ) : ℂ) := by
      push_cast
      linear_combination ht
    rw [hzr, Complex.norm_real, Real.norm_eq_abs] at this
    exact this

/-- For a degree-2 Pisot number, the `n`-th conjugate power sum is just `wⁿ`. -/
theorem conjPowSum_eq_of_natDegree_two {β w : ℝ} (hw : otherConj β = {(w : ℂ)}) (n : ℕ) :
    conjPowSum β n = ((w ^ n : ℝ) : ℂ) := by
  simp [conjPowSum, hw]

/-- `βⁿ + wⁿ` is a rational integer for every `n`. -/
theorem pow_add_pow_mem_int {β w : ℝ} (hβ : IsPisot β) (hw : otherConj β = {(w : ℂ)}) (n : ℕ) :
    ∃ t : ℤ, β ^ n + w ^ n = (t : ℝ) := by
  obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ n
  rw [conjPowSum_eq_of_natDegree_two hw n] at ht
  refine ⟨t, ?_⟩
  have h : ((β ^ n + w ^ n : ℝ) : ℂ) = ((t : ℤ) : ℂ) := by
    push_cast
    push_cast at ht
    linear_combination ht
  exact_mod_cast h

end LeanFormalizations.Mills
