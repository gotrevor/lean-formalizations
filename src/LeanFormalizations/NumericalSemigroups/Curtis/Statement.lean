/-
# Curtis (1990): the Frobenius number has no closed formula for n ≥ 3

Frank Curtis, *On formulas for the Frobenius number of a numerical semigroup*,
Math. Scand. **67** (1990), 190–192.

This file is the **designated audit surface**: the two load-bearing statements,
written to be checked against the paper. The two definitions they reference
(`IsAdmissible`, `evalPoint`) live in `Defs.lean` — audit those too. The proofs
are delegated to `Engine.lean`; the statements here are definitionally identical
to what is proved.

For n = 2 the Frobenius number is `m*n - m - n` (Sylvester; in mathlib as
`frobeniusNumber_pair`). Curtis proves that for n = 3 — and hence all n ≥ 3 —
no such closed form exists. His theorem is in fact stronger than "not a
polynomial": the Frobenius number of a triple is **not even algebraic** over its
generators (its graph lies on no proper hypersurface). The familiar "no finite
set of formulas" statement is then a one-line corollary.

## Status
- `no_polynomial_relation` — the main theorem, **PROVED** and axiom-clean
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
- `no_finite_polynomial_formula` — **PROVED** (corollary of the main theorem).
- `no_finite_polynomial_formula_of_algebra` / `_int` / `_rat` — the corollary for
  formulas with coefficients in any ℂ-algebra, in particular ℤ and ℚ: there is no
  finite list of *integer* (or *rational*) polynomials computing the Frobenius
  number of a triple. This is the form that answers the usual question.
- `no_finite_polynomial_formula_multivar` — the **`n ≥ 3` generalization** (the
  paper's title): no formula in `n` variables either, by reduction to `n = 3`.

Faithfulness of the definitions is anchored in `Anchors.lean` (concrete witness
`⟨3,7,8⟩`, Frobenius number `5`).
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Engine

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis

/-- **Curtis's theorem (1990).** There is no nonzero polynomial
`F ∈ ℂ[X₁, X₂, X₃, Y]` that vanishes on the graph of the Frobenius number over
the admissible family `A`. Equivalently: the Frobenius number of a triple is not
algebraic over its generators. -/
theorem no_polynomial_relation :
    ¬ ∃ F : MvPolynomial (Fin 4) ℂ, F ≠ 0 ∧
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        eval (evalPoint s₁ s₂ s₃ g) F = 0 :=
  no_polynomial_relation_engine

/-- **Corollary.** No finite list of polynomials `f₀, …, f_{k-1} ∈ ℂ[X₁,X₂,X₃]`
computes the Frobenius number piecewise (some `fᵢ` equal to `g` on every
admissible triple). Curtis's proof: `F = ∏ (fᵢ − Y)` would vanish on the graph,
contradicting `no_polynomial_relation`. -/
theorem no_finite_polynomial_formula :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℂ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] (f i) = (g : ℂ) :=
  no_finite_polynomial_formula_engine

/-- **Corollary, coefficients in any ℂ-algebra `R`.** No finite list of polynomials
`f₀, …, f_{k-1} ∈ R[X₁,X₂,X₃]` computes the Frobenius number of a triple. Proof:
push each `fᵢ` along `algebraMap R ℂ` to a complex polynomial computing the same
values (the generators are natural numbers, and `algebraMap` preserves them), then
apply `no_finite_polynomial_formula`. -/
theorem no_finite_polynomial_formula_of_algebra {R : Type*} [CommRing R] [Algebra R ℂ] :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) R),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : R), (s₂ : R), (s₃ : R)] (f i) = (g : R) := by
  rintro ⟨k, f, hf⟩
  apply no_finite_polynomial_formula
  refine ⟨k, fun i => MvPolynomial.map (algebraMap R ℂ) (f i), ?_⟩
  intro s₁ s₂ s₃ g hadm hfrob
  obtain ⟨i, hi⟩ := hf s₁ s₂ s₃ g hadm hfrob
  refine ⟨i, ?_⟩
  rw [eval_map]
  have hpt : (![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] : Fin 3 → ℂ)
      = (algebraMap R ℂ) ∘ ![(s₁ : R), (s₂ : R), (s₃ : R)] := by
    funext j; fin_cases j <;> simp
  rw [hpt, ← eval₂_comp, hi]
  simp

/-- **Corollary, integer coefficients.** No finite list of *integer* polynomials
computes the Frobenius number of a triple. -/
theorem no_finite_polynomial_formula_int :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℤ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℤ), (s₂ : ℤ), (s₃ : ℤ)] (f i) = (g : ℤ) :=
  no_finite_polynomial_formula_of_algebra

/-- **Corollary, rational coefficients.** No finite list of *rational* polynomials
computes the Frobenius number of a triple. -/
theorem no_finite_polynomial_formula_rat :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℚ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℚ), (s₂ : ℚ), (s₃ : ℚ)] (f i) = (g : ℚ) :=
  no_finite_polynomial_formula_of_algebra

/-- **Curtis's theorem for `n ≥ 3` generators** (the paper's title). For every
`n ≥ 3` there is no finite list of polynomials `f₀,…,f_{k-1} ∈ ℂ[X₀,…,X_{n-1}]`
computing the Frobenius number over the family of `n`-tuples of generators whose
numerical semigroup is that of an admissible triple. Since every such semigroup
arises as `Set.range s` for some `n`-tuple `s` (pad the triple with repeats), a
formula valid for *all* `n`-generator semigroups would in particular work here —
so this impossibility implies the general one.

Proof: a hypothetical `n`-variable formula, precomposed with the fixed padding
substitution `X_j ↦ X_{min(j,2)}`, becomes a 3-variable formula computing the same
Frobenius numbers on admissible triples (realized by the padded tuple
`s_j = [a,b,c]_{min(j,2)}`), contradicting `no_finite_polynomial_formula`. -/
theorem no_finite_polynomial_formula_multivar (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin n) ℂ),
      ∀ (s : Fin n → ℕ) (g : ℕ),
        (∃ a b c, IsAdmissible a b c ∧ Set.range s = {a, b, c}) →
        FrobeniusNumber g (Set.range s) →
        ∃ i, eval (fun j => (s j : ℂ)) (f i) = (g : ℂ) := by
  rintro ⟨k, f, hf⟩
  apply no_finite_polynomial_formula
  -- the fixed padding substitution `Fin n → ℂ[X₀,X₁,X₂]`, `X_j ↦ X_{min(j,2)}`
  set ψ : Fin n → MvPolynomial (Fin 3) ℂ :=
    fun j => if (j : ℕ) = 0 then X 0 else if (j : ℕ) = 1 then X 1 else X 2 with hψ
  refine ⟨k, fun i => aeval ψ (f i), ?_⟩
  intro a b c g hadm hfrob
  -- the padded `n`-tuple of generators with `Set.range = {a,b,c}`
  set s : Fin n → ℕ := fun j => if (j : ℕ) = 0 then a else if (j : ℕ) = 1 then b else c with hs
  have h0 : s ⟨0, by omega⟩ = a := by simp [hs]
  have h1 : s ⟨1, by omega⟩ = b := by simp [hs]
  have h2 : s ⟨2, by omega⟩ = c := by simp [hs]
  have hrange : Set.range s = {a, b, c} := by
    apply Set.eq_of_subset_of_subset
    · rintro v ⟨j, rfl⟩
      simp only [hs]
      split_ifs <;> simp
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, h0⟩
      · exact ⟨⟨1, by omega⟩, h1⟩
      · exact ⟨⟨2, by omega⟩, h2⟩
  obtain ⟨i, hi⟩ := hf s g ⟨a, b, c, hadm, hrange⟩ (by rwa [hrange])
  refine ⟨i, ?_⟩
  show (eval ![(a : ℂ), (b : ℂ), (c : ℂ)]) (aeval ψ (f i)) = (g : ℂ)
  rw [← aeval_eq_eval (f := ![(a : ℂ), (b : ℂ), (c : ℂ)]), comp_aeval_apply]
  have hsub : (fun j => (aeval ![(a : ℂ), (b : ℂ), (c : ℂ)]) (ψ j))
      = (fun j => (s j : ℂ)) := by
    funext j
    simp only [hψ, hs]
    split_ifs <;> simp
  rw [hsub, aeval_eq_eval, hi]

end LeanFormalizations.NumericalSemigroups.Curtis
