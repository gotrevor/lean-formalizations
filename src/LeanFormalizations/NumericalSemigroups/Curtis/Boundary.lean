/-
# Curtis (1990) — boundary checks and a refuted candidate formula

Independent faithfulness cross-checks for the headline `no_polynomial_relation`
(and its corollaries in `Statement.lean`). Curtis's theorem is a *boundary*
phenomenon: for `n = 2` generators a closed Frobenius formula exists (Sylvester),
and the whole content of the paper is that this breaks at `n = 3`. The two checks
here exhibit both sides of that boundary on concrete, externally-known facts:

1. `n2_polynomial_relation_exists` — the `n = 2` analogue of `no_polynomial_relation`
   is **true**: a single nonzero polynomial DOES vanish on the whole 2-generator
   graph (Sylvester's `X₀·X₁ − X₀ − X₁ − Y`). This shows the impossibility at
   `n = 3` is genuine teeth, not a vacuous "no formula for anything" artifact —
   the very same shape of statement is *false* one dimension down.

2. `symmetric_guess_not_a_formula` — a tangible witness that the abstract `¬∃`
   has bite: the natural "extend Sylvester symmetrically" degree-2 guess
   `Σ XᵢXⱼ − Σ Xᵢ` already disagrees with the true Frobenius number at the
   admissible triple `⟨3,7,8⟩` (it gives `83`, not `5`).
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Anchors
import LeanFormalizations.NumericalSemigroups.Curtis.Statement

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis.Boundary

open LeanFormalizations.NumericalSemigroups.Curtis

/-- **n = 2 boundary check (contrast with `no_polynomial_relation`).** For TWO
generators a single nonzero polynomial DOES vanish on the entire graph of the
Frobenius number: by Sylvester / Chicken-McNugget (`frobeniusNumber_pair`) the
Frobenius number of a coprime pair `{a, b}` is `a·b − a − b`, so the graph
`{(a, b, g)}` lies on the hypersurface `X₀·X₁ − X₀ − X₁ − Y = 0`.

This is the exact `n = 2` analogue of `no_polynomial_relation`, and here it is
**true** — Curtis's theorem is precisely the statement that it becomes *false*
(impossible) at `n = 3`. Demonstrates the headline's content sits exactly at the
`n = 2` / `n = 3` line. -/
theorem n2_polynomial_relation_exists :
    ∃ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 ∧
      ∀ a b g : ℕ, 1 < a → 1 < b → Nat.Coprime a b →
        FrobeniusNumber g {a, b} →
        eval ![(a : ℂ), (b : ℂ), (g : ℂ)] F = 0 := by
  refine ⟨X 0 * X 1 - X 0 - X 1 - X 2, ?_, ?_⟩
  · -- nonzero: it evaluates to `-1` at the point `(0, 0, 1)`
    intro h
    apply_fun (eval ![(0 : ℂ), 0, 1]) at h
    simp [eval_sub, eval_mul, eval_X] at h
  · intro a b g ha hb hcop hg
    -- uniqueness of the Frobenius number pins `g = a*b - a - b`
    have hpair : FrobeniusNumber (a * b - a - b) {a, b} := frobeniusNumber_pair hcop ha hb
    have huniq : g = a * b - a - b := hg.isLUB.unique hpair.isLUB
    have hab : a + b ≤ a * b := add_le_mul ha hb
    subst huniq
    simp only [eval_sub, eval_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [show a * b - a - b = a * b - (a + b) from by omega, Nat.cast_sub hab, Nat.cast_mul]
    push_cast
    ring

/-- **A concrete refuted candidate formula.** Makes the abstract impossibility
`no_polynomial_relation` tangible: the natural symmetric degree-2 guess
`X₀X₁ + X₁X₂ + X₀X₂ − X₀ − X₁ − X₂` (the obvious way to "extend Sylvester to three
variables") is NOT a Frobenius formula — it already disagrees with the true value
at the admissible triple `⟨3,7,8⟩`, evaluating to `3·7 + 7·8 + 3·8 − 3 − 7 − 8 = 83`
rather than the actual Frobenius number `5`. -/
theorem symmetric_guess_not_a_formula :
    ∃ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ ∧ FrobeniusNumber g {s₁, s₂, s₃} ∧
      eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)]
          (X 0 * X 1 + X 1 * X 2 + X 0 * X 2 - X 0 - X 1 - X 2 : MvPolynomial (Fin 3) ℂ)
        ≠ (g : ℂ) := by
  refine ⟨3, 7, 8, 5, Anchors.isAdmissible_3_7_8, Anchors.frobeniusNumber_3_7_8, ?_⟩
  simp only [eval_sub, eval_add, eval_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **General refutation corollary.** The "constructive" form of the impossibility:
*every* single candidate polynomial `f ∈ ℂ[X₀,X₁,X₂]` is refuted — there is an
admissible triple on which `f`'s value disagrees with the true Frobenius number.
(`symmetric_guess_not_a_formula` is the special case where the witnessing triple is
exhibited explicitly as `⟨3,7,8⟩`.) Proof: a candidate `f` that never failed would
be a one-element formula menu (`k = 1`), contradicting `no_finite_polynomial_formula`. -/
theorem no_single_polynomial_formula (f : MvPolynomial (Fin 3) ℂ) :
    ∃ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ ∧ FrobeniusNumber g {s₁, s₂, s₃} ∧
      eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] f ≠ (g : ℂ) := by
  by_contra h
  push_neg at h
  apply no_finite_polynomial_formula
  exact ⟨1, fun _ => f, fun s₁ s₂ s₃ g ha hf => ⟨0, h s₁ s₂ s₃ g ha hf⟩⟩

end LeanFormalizations.NumericalSemigroups.Curtis.Boundary
