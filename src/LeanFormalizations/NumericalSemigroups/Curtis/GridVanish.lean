/-
# A grid-vanishing lemma for 2-variable polynomials over an infinite field

For an infinite field `K`, a polynomial `G ∈ K[X₀,X₁]` of total degree `≤ n` that
vanishes on a "staircase"
grid — `n+1` distinct first coordinates `aᵢ`, and for each `aᵢ` a set of `n+1`
distinct second coordinates `bᵢⱼ` — is identically zero.

This replaces Curtis's projective/limit argument (and its Lemma 1, Dirichlet +
Farey adjacency) with elementary double root-counting: each row forces the
`X₀ := aᵢ` specialization to vanish identically in `X₁`; then the `n+1` distinct
`aᵢ` force the `X₁ := b` specialization to vanish identically in `X₀`; then
`MvPolynomial.funext` over the infinite field K finishes.
-/
import Mathlib

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis

variable {K : Type*} [Field K]

/-- `eval ![a,b] G` factors as: specialize `X₀ := a` to a univariate polynomial in
`X₁`, then evaluate at `b`. -/
theorem eval_eq_evalRow (G : MvPolynomial (Fin 2) K) (a b : K) :
    eval ![a, b] G
      = Polynomial.eval b (aeval ![Polynomial.C a, Polynomial.X] G) := by
  have h : ((Polynomial.evalRingHom b).comp
        (aeval ![Polynomial.C a, Polynomial.X] :
          MvPolynomial (Fin 2) K →ₐ[K] Polynomial K).toRingHom)
      = (eval ![a, b] : MvPolynomial (Fin 2) K →+* K) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; fin_cases i <;> simp
  simpa using (DFunLike.congr_fun h G).symm

/-- `eval ![a,b] G` factors as: specialize `X₁ := b` to a univariate polynomial in
`X₀`, then evaluate at `a`. -/
theorem eval_eq_evalCol (G : MvPolynomial (Fin 2) K) (a b : K) :
    eval ![a, b] G
      = Polynomial.eval a (aeval ![Polynomial.X, Polynomial.C b] G) := by
  have h : ((Polynomial.evalRingHom a).comp
        (aeval ![Polynomial.X, Polynomial.C b] :
          MvPolynomial (Fin 2) K →ₐ[K] Polynomial K).toRingHom)
      = (eval ![a, b] : MvPolynomial (Fin 2) K →+* K) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; fin_cases i <;> simp
  simpa using (DFunLike.congr_fun h G).symm

/-- The `X₀ := a` specialization has univariate degree at most `G.totalDegree`. -/
theorem natDegree_evalRow_le (G : MvPolynomial (Fin 2) K) (a : K) :
    (aeval ![Polynomial.C a, Polynomial.X] G).natDegree ≤ G.totalDegree := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [aeval_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero, zero_add,
    Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  calc m 1 ≤ m 0 + m 1 := Nat.le_add_left _ _
    _ = m.sum (fun _ e => e) := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    _ ≤ G.totalDegree := le_totalDegree hm

/-- The `X₁ := b` specialization has univariate degree at most `G.totalDegree`. -/
theorem natDegree_evalCol_le (G : MvPolynomial (Fin 2) K) (b : K) :
    (aeval ![Polynomial.X, Polynomial.C b] G).natDegree ≤ G.totalDegree := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [aeval_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one,
    Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero, add_zero]
  calc m 0 ≤ m 0 + m 1 := Nat.le_add_right _ _
    _ = m.sum (fun _ e => e) := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    _ ≤ G.totalDegree := le_totalDegree hm

/-- **Grid-vanishing lemma.** If `G ∈ K[X₀,X₁]` has total degree `≤ n`, and there
are `n+1` distinct values `aᵢ` and, for each `i`, `n+1` distinct values `bᵢⱼ` with
`G(aᵢ, bᵢⱼ) = 0`, then `G = 0`. -/
theorem grid_vanish [Infinite K] (G : MvPolynomial (Fin 2) K) (n : ℕ) (hn : G.totalDegree ≤ n)
    (a : Fin (n + 1) → K) (ha : Function.Injective a)
    (b : Fin (n + 1) → Fin (n + 1) → K) (hb : ∀ i, Function.Injective (b i))
    (h0 : ∀ i j, eval ![a i, b i j] G = 0) : G = 0 := by
  -- Row step: each `X₀ := aᵢ` specialization vanishes identically.
  have hrow : ∀ i, aeval ![Polynomial.C (a i), Polynomial.X] G = 0 := by
    intro i
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (hb i)
    · intro j; rw [← eval_eq_evalRow]; exact h0 i j
    · rw [Fintype.card_fin]
      exact Nat.lt_succ_of_le ((natDegree_evalRow_le G (a i)).trans hn)
  -- Hence the whole row vanishes for every second coordinate.
  have hrow' : ∀ i, ∀ y : K, eval ![a i, y] G = 0 := by
    intro i y; rw [eval_eq_evalRow, hrow i, Polynomial.eval_zero]
  -- Column step: each `X₁ := y` specialization vanishes identically (uses the `aᵢ`).
  have hcol : ∀ y : K, aeval ![Polynomial.X, Polynomial.C y] G = 0 := by
    intro y
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ha
    · intro i; rw [← eval_eq_evalCol]; exact hrow' i y
    · rw [Fintype.card_fin]
      exact Nat.lt_succ_of_le ((natDegree_evalCol_le G y).trans hn)
  -- So `G` vanishes everywhere; `funext` over the infinite field K finishes.
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  rw [hx, eval_eq_evalCol, hcol, Polynomial.eval_zero]

end LeanFormalizations.NumericalSemigroups.Curtis
