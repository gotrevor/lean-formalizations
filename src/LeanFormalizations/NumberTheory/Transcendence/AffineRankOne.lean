/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Rank-one matrices of affine forms

The algebraic core of Roy's strong six exponentials theorem under Schanuel.  If three
`K`-linearly independent *affine* polynomials `P₀, P₁, P₂` (degree `≤ 1`, i.e.
`aff a b = a + ∑ bₖXₖ`) satisfy `Qᵢ Pⱼ = Qⱼ Pᵢ` for affine `Q₀, Q₁, Q₂`, then the ratio is a
*constant*: `Qⱼ = c·Pⱼ` for a single `c ∈ K`.

The proof is a derivation argument: applying `pderiv k` to `QᵢPⱼ = QⱼPᵢ` turns the
"multiplier" `Q/P` into something whose `k`-th partial is `Tₖ/P₀²` with
`Tₖ = (∂ₖQ₀)P₀ − (∂ₖP₀)Q₀`.  If some `Tₖ ≠ 0` the three `Pⱼ` are forced into a
two-dimensional space, contradicting independence; if every `Tₖ` vanishes then `Q₀ = c·P₀`
and cancelling `P₀` in the domain `MvPolynomial (Fin n) K` spreads it to every `j`.

No unique factorization is used, which is why this works over an arbitrary variable set.
-/
import Mathlib

namespace LeanFormalizations.AffineRankOne

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The affine form `a + ∑ₖ bₖ Xₖ`. -/
noncomputable def aff (a : K) (b : Fin n → K) : MvPolynomial (Fin n) K :=
  C a + ∑ k, C (b k) * X k

@[simp] theorem pderiv_aff (a : K) (b : Fin n → K) (k : Fin n) :
    pderiv k (aff a b) = C (b k) := by
  classical
  simp only [aff, map_add, pderiv_C, zero_add, map_sum, Derivation.leibniz, pderiv_C,
    pderiv_X, smul_zero, zero_add]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h; simp at h

/-- An affine form with all coefficients zero is the constant `a`. -/
theorem aff_eq_C_of_b_eq_zero {a : K} {b : Fin n → K} (hb : ∀ k, b k = 0) :
    aff a b = C a := by
  simp [aff, hb]


/-- A `K`-linear relation among three `K`-linearly independent polynomials is trivial. -/
theorem eq_zero_of_rel {P : Fin 3 → MvPolynomial (Fin n) K} (hind : LinearIndependent K P)
    (c0 c1 c2 : K) (h : C c0 * P 0 + C c1 * P 1 + C c2 * P 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  have h' : ∑ i : Fin 3, (![c0, c1, c2] i) • P i = 0 := by
    rw [Fin.sum_univ_three]
    simpa [smul_eq_C_mul] using h
  have hz := Fintype.linearIndependent_iff.1 hind _ h'
  exact ⟨hz 0, hz 1, hz 2⟩

/-- Once the ratio is constant on the `0`-th column it is constant everywhere: cancel `P₀`. -/
theorem forall_eq_of_zero {P Q : Fin 3 → MvPolynomial (Fin n) K} (hP0 : P 0 ≠ 0)
    (hcross : ∀ i j, Q i * P j = Q j * P i) {c : K} (h0 : Q 0 = C c * P 0) :
    ∀ j, Q j = C c * P j := by
  intro j
  have h := hcross j 0
  have hz : (Q j - C c * P j) * P 0 = 0 := by
    rw [h0] at h; linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hP0)

/-- **The rank-one criterion for affine forms.**  If `P₀, P₁, P₂` are `K`-linearly independent
affine polynomials and `Q₀, Q₁, Q₂` are affine with `Qᵢ Pⱼ = Qⱼ Pᵢ`, then `Qⱼ = c·Pⱼ` for a
single constant `c ∈ K`. -/
theorem const_ratio (pa qa : Fin 3 → K) (pb qb : Fin 3 → Fin n → K)
    (hind : LinearIndependent K (fun j => aff (pa j) (pb j)))
    (hcross : ∀ i j, aff (qa i) (qb i) * aff (pa j) (pb j)
        = aff (qa j) (qb j) * aff (pa i) (pb i)) :
    ∃ c : K, ∀ j, aff (qa j) (qb j) = C c * aff (pa j) (pb j) := by
  classical
  set P : Fin 3 → MvPolynomial (Fin n) K := fun j => aff (pa j) (pb j) with hPdef
  set Q : Fin 3 → MvPolynomial (Fin n) K := fun j => aff (qa j) (qb j) with hQdef
  have hP0 : P 0 ≠ 0 := hind.ne_zero 0
  have hcross' : ∀ i j : Fin 3, Q i * P j = Q j * P i := hcross
  have hPp : ∀ (j : Fin 3) (k : Fin n), pderiv k (P j) = C (pb j k) := fun j k => pderiv_aff _ _ _
  have hQp : ∀ (j : Fin 3) (k : Fin n), pderiv k (Q j) = C (qb j k) := fun j k => pderiv_aff _ _ _
  -- (★) differentiate the cross relation
  have hstar : ∀ (k : Fin n) (i j : Fin 3),
      C (qb i k) * P j + C (pb j k) * Q i = C (qb j k) * P i + C (pb i k) * Q j := by
    intro k i j
    have h := congrArg (pderiv k) (hcross' i j)
    rw [Derivation.leibniz, Derivation.leibniz, hPp, hPp, hQp, hQp, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul] at h
    linear_combination h
  -- (†) the key identity; `T k` is `P₀² ∂ₖ(Q₀/P₀)`
  have hdag : ∀ (k : Fin n) (j : Fin 3),
      (C (qb 0 k) * P 0 - C (pb 0 k) * Q 0) * P j
        = P 0 * (C (qb j k) * P 0 - C (pb j k) * Q 0) := by
    intro k j
    have h1 := hstar k 0 j
    have h2 := hcross' j 0
    linear_combination P 0 * h1 + C (pb 0 k) * h2
  by_cases hT : ∀ k : Fin n, C (qb 0 k) * P 0 - C (pb 0 k) * Q 0 = 0
  · -- every `Tₖ` vanishes: `Q₀` is a constant multiple of `P₀`
    have hzero : ∃ c : K, Q 0 = C c * P 0 := by
      by_cases hb : ∀ k, pb 0 k = 0
      · have hP0C : P 0 = C (pa 0) := aff_eq_C_of_b_eq_zero hb
        have hpa : pa 0 ≠ 0 := fun h => hP0 (by rw [hP0C, h, map_zero])
        have hq : ∀ k, qb 0 k = 0 := by
          intro k
          have h := hT k
          rw [hb k, map_zero, zero_mul, sub_zero, hP0C, ← map_mul] at h
          have := (MvPolynomial.C_eq_zero).1 h
          exact (mul_eq_zero.1 this).resolve_right hpa
        have hQ0C : Q 0 = C (qa 0) := aff_eq_C_of_b_eq_zero hq
        refine ⟨qa 0 / pa 0, ?_⟩
        rw [hQ0C, hP0C, ← map_mul, div_mul_cancel₀ _ hpa]
      · push_neg at hb
        obtain ⟨k, hk⟩ := hb
        refine ⟨qb 0 k / pb 0 k, ?_⟩
        have hCk : (C (pb 0 k) : MvPolynomial (Fin n) K) ≠ 0 := by
          simpa using hk
        have h := hT k
        have hmul : (C (pb 0 k) : MvPolynomial (Fin n) K) * C (qb 0 k / pb 0 k) = C (qb 0 k) := by
          rw [← map_mul]; congr 1; field_simp
        have : C (pb 0 k) * (Q 0 - C (qb 0 k / pb 0 k) * P 0) = 0 := by
          linear_combination -h - P 0 * hmul
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hCk)
    obtain ⟨c, hc⟩ := hzero
    exact ⟨c, forall_eq_of_zero hP0 hcross' hc⟩
  · -- some `Tₖ ≠ 0`: the three `Pⱼ` collapse into a plane, contradicting independence
    exfalso
    push_neg at hT
    obtain ⟨k, hTk⟩ := hT
    set T : MvPolynomial (Fin n) K := C (qb 0 k) * P 0 - C (pb 0 k) * Q 0 with hTdef
    have hTR : ∀ j : Fin 3, T * (C (pb 0 k) * P j - C (pb j k) * P 0)
        = (C (pb 0 k) * C (qb j k) - C (qb 0 k) * C (pb j k)) * P 0 ^ 2 := by
      intro j
      have h1 := hdag k j
      have h2 := hdag k 0
      rw [← hTdef] at h1 h2
      linear_combination C (pb 0 k) * h1 - C (pb j k) * h2
    by_cases hb0 : pb 0 k = 0
    · -- `T = C (qb 0 k) * P₀`, and `P₀` cancels out of (†)
      have hq0 : qb 0 k ≠ 0 := by
        intro h
        apply hTk
        rw [hTdef, h, hb0, map_zero, zero_mul, zero_mul, sub_zero]
      have hcan : ∀ j : Fin 3,
          C (qb 0 k) * P j = C (qb j k) * P 0 - C (pb j k) * Q 0 := by
        intro j
        have h := hdag k j
        rw [hb0, map_zero, zero_mul, sub_zero] at h
        have hz : P 0 * (C (qb 0 k) * P j - (C (qb j k) * P 0 - C (pb j k) * Q 0)) = 0 := by
          linear_combination h
        exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left hP0)
      by_cases hb1 : pb 1 k = 0
      · have h := hcan 1
        rw [hb1, map_zero, zero_mul, sub_zero] at h
        have := (eq_zero_of_rel hind (-(qb 1 k)) (qb 0 k) 0
          (by simp only [map_neg, map_zero]; linear_combination h)).2.1
        exact hq0 this
      · have h1 := hcan 1
        have h2 := hcan 2
        have hrel : C (pb 1 k * qb 2 k - pb 2 k * qb 1 k) * P 0
            + C (pb 2 k * qb 0 k) * P 1 + C (-(pb 1 k * qb 0 k)) * P 2 = 0 := by
          simp only [map_sub, map_mul, map_neg]
          linear_combination C (pb 2 k) * h1 - C (pb 1 k) * h2
        have := (eq_zero_of_rel hind _ _ _ hrel).2.2
        rw [neg_eq_zero] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hb1 h
        · exact hq0 h
    · have hTR1 := hTR 1
      have hTR2 := hTR 2
      have hkey : (C (pb 0 k) * C (qb 2 k) - C (qb 0 k) * C (pb 2 k))
            * (C (pb 0 k) * P 1 - C (pb 1 k) * P 0)
          = (C (pb 0 k) * C (qb 1 k) - C (qb 0 k) * C (pb 1 k))
            * (C (pb 0 k) * P 2 - C (pb 2 k) * P 0) := by
        have hz : T * ((C (pb 0 k) * C (qb 2 k) - C (qb 0 k) * C (pb 2 k))
              * (C (pb 0 k) * P 1 - C (pb 1 k) * P 0)
            - (C (pb 0 k) * C (qb 1 k) - C (qb 0 k) * C (pb 1 k))
              * (C (pb 0 k) * P 2 - C (pb 2 k) * P 0)) = 0 := by
          linear_combination (C (pb 0 k) * C (qb 2 k) - C (qb 0 k) * C (pb 2 k)) * hTR1
            - (C (pb 0 k) * C (qb 1 k) - C (qb 0 k) * C (pb 1 k)) * hTR2
        exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left hTk)
      set μ1 : K := pb 0 k * qb 1 k - qb 0 k * pb 1 k with hμ1
      set μ2 : K := pb 0 k * qb 2 k - qb 0 k * pb 2 k with hμ2
      have hlin : C (μ1 * pb 2 k - μ2 * pb 1 k) * P 0 + C (μ2 * pb 0 k) * P 1
          + C (-(μ1 * pb 0 k)) * P 2 = 0 := by
        simp only [hμ1, hμ2, map_sub, map_mul, map_neg]
        linear_combination hkey
      obtain ⟨-, hc1, hc2⟩ := eq_zero_of_rel hind _ _ _ hlin
      have hμ1z : μ1 = 0 := by
        rw [neg_eq_zero] at hc2
        exact (mul_eq_zero.1 hc2).resolve_right hb0
      have hR1 : C (pb 0 k) * P 1 - C (pb 1 k) * P 0 = 0 := by
        have h := hTR 1
        rw [show (C (pb 0 k) * C (qb 1 k) - C (qb 0 k) * C (pb 1 k) : MvPolynomial (Fin n) K)
            = C μ1 by simp [hμ1, map_sub, map_mul], hμ1z, map_zero, zero_mul] at h
        exact (mul_eq_zero.1 h).resolve_left hTk
      have := (eq_zero_of_rel hind (-(pb 1 k)) (pb 0 k) 0
          (by simp only [map_neg, map_zero]; linear_combination hR1)).2.1
      exact hb0 this

end LeanFormalizations.AffineRankOne
