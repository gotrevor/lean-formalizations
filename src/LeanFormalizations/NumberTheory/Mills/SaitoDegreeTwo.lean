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


/-- **Saito (2024), Lemma 4.3, case `b = 4`** (here: `c` even).  No power `A^(c^(m+1))` of a
Mills-like number can be a Pisot number of degree 2 when `c` is even.

Saito's argument, sharpened so that Lemma 4.2 is not needed as a separate step: take `n = cʲ`,
which is even.  Then `w ⁿ > 0`, so the rational integer `t = βⁿ + wⁿ` strictly exceeds `βⁿ`,
hence `t ≥ ⌊βⁿ⌋ + 1` and `wⁿ = t − βⁿ > 1 − 1/2 = 1/2` once the fractional part of `βⁿ` is
`< 1/2` — contradicting `|w| < 1`. -/
theorem not_pisot_two_of_even {A : ℝ} (hA1 : 1 < A) {c : ℕ} (hc : 2 ≤ c) (hceven : 2 ∣ c)
    {m : ℕ} (hβ : IsPisot (A ^ (c ^ (m + 1))))
    (hcard : Multiset.card (otherConj (A ^ (c ^ (m + 1)))) = 1)
    (hfrac : ∀ᶠ k : ℕ in atTop, A ^ (c ^ k) - (⌊A ^ (c ^ k)⌋₊ : ℝ) < 1 / 2) :
    False := by
  have hA0 : (0:ℝ) < A := by linarith
  set β : ℝ := A ^ (c ^ (m + 1)) with hβdef
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hdeg : (minpoly ℚ β).natDegree = 2 := by
    have := card_otherConj_add_one halg
    omega
  obtain ⟨w, hw, hw1, -⟩ := exists_real_conj_of_natDegree_two hβ hdeg
  -- `w ≠ 0`, because `|N(β)| ≥ 1`
  have hprod : 1 ≤ β * |w| := by
    have h := pisot_one_le_prod_norm hβ
    rwa [hw, Multiset.map_singleton, Multiset.prod_singleton, Complex.norm_real,
      Real.norm_eq_abs] at h
  have hβ0 : (0:ℝ) < β := by linarith [hβ.1]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hprod
    simp at hprod
    linarith
  -- choose `j` large
  have htend : Filter.Tendsto (fun n : ℕ => |w| ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg w) hw1
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 2)))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfrac
  set j : ℕ := max 1 (max N k₀) with hj
  have hjpow : j ≤ c ^ j := (Nat.lt_pow_self (by omega)).le
  set n : ℕ := c ^ j with hn
  have hnN : N ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hjpow
  have hjk₀ : k₀ ≤ j := le_trans (le_max_right _ _) (le_max_right _ _)
  have hj1 : 1 ≤ j := le_max_left _ _
  -- `n` is even
  have hneven : Even n := by
    rw [hn]
    exact (even_iff_two_dvd).2 (dvd_pow hceven (by omega))
  -- `βⁿ = A^(c^(m+1+j))`
  have hβpow : β ^ n = A ^ (c ^ (m + 1 + j)) := by
    rw [hβdef, hn, ← pow_mul, ← pow_add]
  -- the integer `t = βⁿ + wⁿ`
  obtain ⟨t, ht⟩ := pow_add_pow_mem_int hβ hw n
  have hwpos : 0 < w ^ n := hneven.pow_pos hw0
  -- fractional part of `βⁿ` is `< 1/2`
  have hfr := hk₀ (m + 1 + j) (by omega)
  rw [← hβpow] at hfr
  have hfl : ((⌊β ^ n⌋₊ : ℕ) : ℝ) ≤ β ^ n := Nat.floor_le (by positivity)
  -- `t > βⁿ ≥ ⌊βⁿ⌋`, so `t ≥ ⌊βⁿ⌋ + 1`
  have htgt : (⌊β ^ n⌋₊ : ℝ) < (t : ℝ) := by linarith
  have htge : ((⌊β ^ n⌋₊ : ℕ) : ℤ) < t := by exact_mod_cast htgt
  have htge' : ((⌊β ^ n⌋₊ : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by
    have : ((⌊β ^ n⌋₊ : ℕ) : ℤ) + 1 ≤ t := by omega
    exact_mod_cast this
  -- so `wⁿ > 1/2`, contradicting `|w|ⁿ < 1/2`
  have hbig : (1:ℝ) / 2 < w ^ n := by linarith
  have hsmall : |w| ^ n < 1 / 2 := hN n hnN
  have : w ^ n ≤ |w| ^ n := by
    rw [← abs_pow]
    exact le_abs_self _
  linarith

end LeanFormalizations.Mills
