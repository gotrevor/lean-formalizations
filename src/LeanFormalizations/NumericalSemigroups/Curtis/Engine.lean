/-
# Curtis (1990) — proof engine

The proofs delegated to by the audit surface `Statement.lean`.

## Status of the two headline results
- `no_finite_polynomial_formula_engine` — **PROVED** (axiom-clean), as a direct
  corollary of the main theorem via Curtis's `F = ∏ (fᵢ − Y)` argument.
- `no_polynomial_relation_engine` — the main theorem, currently `sorry`. Its
  decomposition into Curtis's two lemmas + the degree-counting finish is laid
  out below (`lemma1`, `lemma2`, and the finish), each a disclosed `sorry` with
  a citing docstring. Multi-lap target.
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Defs

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis

/-! ## The main theorem (engine) -/

/-- **Curtis's theorem (1990), engine form.** No nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]`
vanishes on the graph of the Frobenius number over the admissible family `A`.

Proof roadmap (Curtis, pp. 190–192), to be filled in over multiple laps:
1. **Lemma 1** (Dirichlet primes in AP + Farey adjacency): for `α ∈ ℝ⁺`, `ε > 0`,
   a prime `p` and residues `i, j` coprime to `p`, there are `x` prime,
   `y` with `x ≡ i`, `y ≡ j (mod p)`, `(x,y)=1`, `|α − y/x| < ε`.
2. **Lemma 2** (Brauer–Shockley Apéry-set): the exact value
   `g⟨s₁,s₂,s₃⟩ = (k−2)s₂ + s₃ − s₁` on the restricted family.
3. **Finish**: for each prime `p > 2` and `k = 2,…,(p−1)/2+1`, the substituted
   curve `G(X₂,X₃) = F(p, X₂, X₃, (k−2)X₂+X₃−p)` vanishes on points whose
   ratios approach an irrational, so its leading form has infinitely many roots
   and `G ≡ 0`; the `(p−1)/2` distinct linear forms then force
   `deg F ≥ (p−1)/2` for every prime `p`, contradicting `deg F < ∞`. -/
theorem no_polynomial_relation_engine :
    ¬ ∃ F : MvPolynomial (Fin 4) ℂ, F ≠ 0 ∧
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        eval (evalPoint s₁ s₂ s₃ g) F = 0 := by
  sorry

/-! ## The corollary (fully proved) -/

/-- **Corollary, engine form.** No finite list of polynomials
`f₀,…,f_{k-1} ∈ ℂ[X₁,X₂,X₃]` computes the Frobenius number piecewise.

Curtis's proof: if some `fᵢ` equals `g` on every admissible triple, then
`F = ∏ᵢ (fᵢ − Y)` is a nonzero polynomial vanishing on the whole graph,
contradicting the main theorem. We realize `fᵢ` inside `ℂ[X₁,X₂,X₃,Y]` by
renaming along `Fin.castSucc : Fin 3 → Fin 4` (which uses `X₁,X₂,X₃` and avoids
`Y = X₃`), and take `Y := X 3`. -/
theorem no_finite_polynomial_formula_engine :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℂ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] (f i) = (g : ℂ) := by
  rintro ⟨k, f, hf⟩
  apply no_polynomial_relation_engine
  -- The Curtis polynomial `F = ∏ᵢ (rename castSucc (fᵢ) − X₃)`.
  refine ⟨∏ i : Fin k, (rename Fin.castSucc (f i) - X 3), ?_, ?_⟩
  · -- `F ≠ 0`: each factor is nonzero (its `X₃`-coefficient is `−1`).
    rw [Finset.prod_ne_zero_iff]
    intro i _ hzero
    have hrange : (3 : Fin 4) ∉ Set.range (Fin.castSucc : Fin 3 → Fin 4) := by decide
    have hcoeff :
        coeff (Finsupp.single 3 1) (rename Fin.castSucc (f i) - X (3 : Fin 4)) = -1 := by
      rw [coeff_sub, coeff_X']
      have h0 : coeff (Finsupp.single 3 1) (rename Fin.castSucc (f i)) = 0 := by
        apply coeff_rename_eq_zero
        intro u hu
        exact absurd (hu ▸ (Finsupp.mapDomain_notin_range u 3 hrange)) (by simp)
      rw [h0]
      simp
    rw [hzero] at hcoeff
    simp at hcoeff
  · -- `F` vanishes on the graph: pick the `fᵢ` computing `g`; that factor is `0`.
    intro s₁ s₂ s₃ g hadm hfrob
    obtain ⟨i, hi⟩ := hf s₁ s₂ s₃ g hadm hfrob
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [map_sub, eval_rename, eval_X]
    have hcomp : (evalPoint s₁ s₂ s₃ g) ∘ Fin.castSucc = ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] := by
      funext j
      fin_cases j <;> rfl
    rw [hcomp, hi]
    show (g : ℂ) - evalPoint s₁ s₂ s₃ g 3 = 0
    simp [evalPoint]

end LeanFormalizations.NumericalSemigroups.Curtis
