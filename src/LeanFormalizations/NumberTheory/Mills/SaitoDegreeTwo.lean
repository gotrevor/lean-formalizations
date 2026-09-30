/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

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


/-- **`βw ∈ ℤ` for a degree-2 Pisot number.**  `βw = ∏ (−root) = Q(0) = (minpoly ℤ β).coeff 0`.
Same computation as `pisot_one_le_prod_norm`, but keeping the value instead of its modulus. -/
theorem pisot_two_prod_mem_int {β w : ℝ} (hβ : IsPisot β) (hw : otherConj β = {(w : ℂ)}) :
    ∃ P : ℤ, β * w = (P : ℝ) := by
  obtain ⟨hβ1, hint, -⟩ := hβ
  have halg : IsIntegral ℚ β := hint.tower_top
  set p : ℚ[X] := minpoly ℚ β with hp
  have hmonic : p.Monic := minpoly.monic halg
  set Q : ℂ[X] := p.map (algebraMap ℚ ℂ) with hQ
  have hQm : Q.Monic := hmonic.map _
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hfac : Q = (Q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hQm
  have heval : Q.eval 0 = (Q.roots.map fun a => -a).prod := by
    conv_lhs => rw [hfac]
    rw [eval_multiset_prod, Multiset.map_map]
    simp
  have hmapZ : p = (minpoly ℤ β).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hc0 : Q.eval 0 = (((minpoly ℤ β).coeff 0 : ℤ) : ℂ) := by
    rw [hQ, eval_map, eval₂_at_zero, hmapZ, coeff_map]
    simp
  have hmem : (β : ℂ) ∈ Q.roots := by
    rw [hQ, ← aroots_def, mem_aroots]
    refine ⟨minpoly.ne_zero halg, ?_⟩
    have h1 : (aeval ((algebraMap ℝ ℂ) β)) p = algebraMap ℝ ℂ ((aeval β) p) :=
      aeval_algebraMap_apply ℂ β p
    simpa [hp, minpoly.aeval] using h1
  have hcons : Q.roots = (β : ℂ) ::ₘ otherConj β := by
    rw [otherConj, ← hp, aroots_def, ← hQ]
    exact (Multiset.cons_erase hmem).symm
  rw [hcons, hw] at heval
  refine ⟨(minpoly ℤ β).coeff 0, ?_⟩
  have hC : ((β : ℂ)) * ((w : ℂ)) = (((minpoly ℤ β).coeff 0 : ℤ) : ℂ) := by
    rw [← hc0, heval]
    simp
  have : ((β * w : ℝ) : ℂ) = ((((minpoly ℤ β).coeff 0 : ℤ) : ℝ) : ℂ) := by
    push_cast
    exact hC
  exact_mod_cast this

/-- **Saito (2024), Lemma 4.3, case `b = 3`.**  No power `A^(3^(m+1))` of a Mills number can be a
Pisot number of degree 2.

The mechanism is the Dickson/Newton identity at `b = 3`: with `t_n = βⁿ + wⁿ ∈ ℤ` and
`P = βw ∈ ℤ`,

    t_{3n} = t_n³ − 3 Pⁿ t_n,

so `t_n ∣ t_{3n}`.  Along `n = 3ʲ` both `t_n` and `t_{3n}` are digits of `A` — hence *primes* —
and `t_{3n} > t_n³ > t_n`, so a prime properly divides a prime.  Contradiction. -/
theorem not_pisot_two_of_cube {A : ℝ} (hA1 : 1 < A) {m : ℕ}
    (hβ : IsPisot (A ^ ((3:ℕ) ^ (m + 1))))
    (hcard : Multiset.card (otherConj (A ^ ((3:ℕ) ^ (m + 1)))) = 1)
    (hprime : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊).Prime)
    (hcube : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊) ^ 3 < ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊)
    (hfrac : ∀ᶠ k : ℕ in atTop, A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2) :
    False := by
  have hA0 : (0:ℝ) < A := by linarith
  set β : ℝ := A ^ ((3:ℕ) ^ (m + 1)) with hβdef
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hdeg : (minpoly ℚ β).natDegree = 2 := by
    have := card_otherConj_add_one halg
    omega
  obtain ⟨w, hw, hw1, -⟩ := exists_real_conj_of_natDegree_two hβ hdeg
  obtain ⟨P, hP⟩ := pisot_two_prod_mem_int hβ hw
  -- pick `j` large enough that `|w|^(3ʲ) < 1/2` and the fractional parts are small
  have htend : Filter.Tendsto (fun n : ℕ => |w| ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg w) hw1
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 2)))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfrac
  set j : ℕ := max N k₀ with hj
  have hjpow : j ≤ (3:ℕ) ^ j := (Nat.lt_pow_self (by norm_num)).le
  set n : ℕ := (3:ℕ) ^ j with hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hjpow
  have hnN3 : N ≤ 3 * n := by omega
  have hjk₀ : k₀ ≤ j := le_max_right _ _
  -- the two indices of `A` involved
  have hβn : β ^ n = A ^ ((3:ℕ) ^ (m + 1 + j)) := by
    rw [hβdef, hn, ← pow_mul, ← pow_add]
  have hβ3n : β ^ (3 * n) = A ^ ((3:ℕ) ^ (m + 1 + j + 1)) := by
    rw [hβdef, hn, ← pow_mul]
    congr 1
    ring
  -- `t_N = ⌊β^N⌋₊` whenever `|w^N| < 1/2` and `frac(β^N) < 1/2`
  have key : ∀ N' : ℕ, ∀ k : ℕ, 1 ≤ k → β ^ N' = A ^ ((3:ℕ) ^ k) → N ≤ N' → k₀ ≤ k →
      ∀ t : ℤ, β ^ N' + w ^ N' = (t : ℝ) → t = (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) := by
    intro N' k hk hEq hNN' hkk t ht
    have hfr := hk₀ k hkk
    rw [← hEq] at hfr
    have hfl : ((⌊β ^ N'⌋₊ : ℕ) : ℝ) ≤ β ^ N' := by
      rw [hEq]; exact Nat.floor_le (by positivity)
    have hsmall : |w ^ N'| < 1 / 2 := by
      rw [abs_pow]; exact hN N' hNN'
    have habs := abs_lt.1 hsmall
    have hlo : ((⌊β ^ N'⌋₊ : ℕ) : ℝ) - 1 < (t : ℝ) := by
      rw [← ht]; linarith
    have hhi : (t : ℝ) < ((⌊β ^ N'⌋₊ : ℕ) : ℝ) + 1 := by
      rw [← ht]
      have : β ^ N' - ((⌊β ^ N'⌋₊ : ℕ) : ℝ) < 1/2 := by rw [hEq] at hfr ⊢; linarith
      linarith
    have h1 : ((⌊β ^ N'⌋₊ : ℕ) : ℤ) - 1 < t := by exact_mod_cast hlo
    have h2 : t < ((⌊β ^ N'⌋₊ : ℕ) : ℤ) + 1 := by exact_mod_cast hhi
    have : t = ((⌊β ^ N'⌋₊ : ℕ) : ℤ) := by omega
    rw [this, hEq]
  obtain ⟨t, ht⟩ := pow_add_pow_mem_int hβ hw n
  obtain ⟨s, hs⟩ := pow_add_pow_mem_int hβ hw (3 * n)
  have htval : t = (⌊A ^ ((3:ℕ) ^ (m + 1 + j))⌋₊ : ℤ) :=
    key n (m + 1 + j) (by omega) hβn hnN (by omega) t ht
  have hsval : s = (⌊A ^ ((3:ℕ) ^ (m + 1 + j + 1))⌋₊ : ℤ) :=
    key (3 * n) (m + 1 + j + 1) (by omega) hβ3n hnN3 (by omega) s hs
  -- the Dickson identity `t³ = s + 3Pⁿ t`
  have hident : (t : ℝ) ^ 3 = (s : ℝ) + 3 * ((P : ℝ)) ^ n * (t : ℝ) := by
    have hPn : ((P : ℝ)) ^ n = β ^ n * w ^ n := by
      rw [← hP, mul_pow]
    rw [← ht, ← hs, hPn, show 3 * n = n * 3 by ring, pow_mul, pow_mul]
    ring
  have hidentZ : t ^ 3 = s + 3 * P ^ n * t := by
    have : ((t ^ 3 : ℤ) : ℝ) = ((s + 3 * P ^ n * t : ℤ) : ℝ) := by push_cast; exact hident
    exact_mod_cast this
  -- `t ∣ s`, but `t` and `s` are distinct primes
  have hdvd : t ∣ s := by
    have : s = t ^ 3 - 3 * P ^ n * t := by omega
    rw [this]
    exact dvd_sub (dvd_pow_self t (by norm_num)) (Dvd.dvd.mul_left dvd_rfl _)
  set u : ℕ := ⌊A ^ ((3:ℕ) ^ (m + 1 + j))⌋₊ with hu
  set v : ℕ := ⌊A ^ ((3:ℕ) ^ (m + 1 + j + 1))⌋₊ with hv
  have hup : u.Prime := hprime (m + 1 + j) (by omega)
  have hvp : v.Prime := hprime (m + 1 + j + 1) (by omega)
  have hlt : u ^ 3 < v := hcube (m + 1 + j) (by omega)
  have hdvdN : u ∣ v := by
    have : (u : ℤ) ∣ (v : ℤ) := by rw [← htval, ← hsval]; exact hdvd
    exact_mod_cast this
  have hu2 : 2 ≤ u := hup.two_le
  have huv : u < v := by
    have : u < u ^ 3 := by
      have := Nat.pow_lt_pow_right hu2 (show 1 < 3 by norm_num)
      simpa using this
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hvp u hdvdN) with h | h
  · omega
  · omega

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
