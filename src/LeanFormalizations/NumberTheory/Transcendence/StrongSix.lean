/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Roy's strong six exponentials theorem under Schanuel's conjecture

`𝓛̃ = LogAlgSpan` is the `ℚ̄`-span of `1` together with all logarithms of nonzero algebraic
numbers.  Roy's theorem says: if `x : Fin 2 → ℂ` and `y : Fin 3 → ℂ` are each linearly
independent over `ℚ̄`, then some `xᵢyⱼ` lies outside `𝓛̃`.

Route (assuming all six products lie in `𝓛̃`):

1. finitely many logarithms suffice for the six products, and by `exists_linearIndependent`
   they may be taken `ℚ`-linearly independent: a family `μ : Fin n → ℂ` with `exp (μ k)`
   algebraic and `μ` `ℚ`-linearly independent, such that every product lies in the `ℚ̄`-span
   of `1, μ₀, …, μₙ₋₁`;
2. Schanuel makes `μ` algebraically independent over `ℚ`, hence (`extendScalars`) over `ℚ̄`,
   so `aeval μ : MvPolynomial (Fin n) ℚ̄ → ℂ` is *injective*;
3. the six products therefore lift to **affine polynomials** `Pⱼ = x₀yⱼ`, `Qⱼ = x₁yⱼ`
   satisfying `QᵢPⱼ = QⱼPᵢ`, with `P` `ℚ̄`-linearly independent (from `y` and `x₀ ≠ 0`);
4. `AffineRankOne.const_ratio` forces `Qⱼ = c·Pⱼ` for a constant `c ∈ ℚ̄`, i.e. `x₁ = c·x₀`,
   contradicting the `ℚ̄`-independence of `x`.

Step 4 is where `ℚ̄`-independence is essential; with only `ℚ`-independence the statement is
false, see `ExponentialsKnown.not_strongSixExponentialsOverQ`.
-/
import LeanFormalizations.Literature.ExponentialsKnown
import LeanFormalizations.NumberTheory.Transcendence.Exponentials
import LeanFormalizations.NumberTheory.Transcendence.AffineRankOne

namespace LeanFormalizations.StrongSix

open LeanFormalizations.Literature LeanFormalizations.Schanuel LeanFormalizations.Exponentials
open LeanFormalizations.AffineRankOne
open Complex MvPolynomial

/-- `ℚ̄`, the field of algebraic numbers, as an intermediate field of `ℂ/ℚ`. -/
local notation "𝔸" => algebraicClosure ℚ ℂ

/-- The set of logarithms of nonzero algebraic numbers (branch-free: `exp ℓ` is algebraic). -/
def LogSet : Set ℂ := {ℓ | IsAlgebraic ℚ (Complex.exp ℓ)}

theorem mem_span_of_mem_logAlgSpan {z : ℂ} (hz : z ∈ LogAlgSpan) :
    z ∈ Submodule.span 𝔸 (insert (1 : ℂ) LogSet) := by
  obtain ⟨n, β, ℓ, hβ, hℓ, rfl⟩ := hz
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
  · have : β 0 = (⟨β 0, mem_algebraicClosure_iff.2 (hβ 0)⟩ : 𝔸) • (1 : ℂ) := by
      rw [Algebra.smul_def]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · have : β i.succ * ℓ i = (⟨β i.succ, mem_algebraicClosure_iff.2 (hβ i.succ)⟩ : 𝔸) • ℓ i := rfl
    rw [this]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ (hℓ i)))


set_option maxHeartbeats 1000000 in
/-- **Basis extraction.**  Finitely many elements of `𝓛̃` all lie in the `ℚ̄`-affine span of a
single *`ℚ`-linearly independent* finite family of logarithms of algebraic numbers. -/
theorem exists_logBasis {ι : Type} [Fintype ι] (z : ι → ℂ) (hz : ∀ i, z i ∈ LogAlgSpan) :
    ∃ (n : ℕ) (μ : Fin n → ℂ), LinearIndependent ℚ μ ∧
      (∀ k, IsAlgebraic ℚ (Complex.exp (μ k))) ∧
      ∀ i, z i ∈ Submodule.span 𝔸 (insert (1 : ℂ) (Set.range μ)) := by
  classical
  obtain ⟨T, hTsub, hTspan, hTli⟩ := exists_linearIndependent ℚ LogSet
  have hLT : insert (1 : ℂ) LogSet ⊆ (Submodule.span 𝔸 (insert (1 : ℂ) T) : Set ℂ) := by
    rintro w hw
    rcases hw with rfl | hw
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · have h1 : w ∈ Submodule.span ℚ T := by
        rw [hTspan]; exact Submodule.subset_span hw
      have h2 : Submodule.span ℚ T ≤ (Submodule.span 𝔸 (insert (1 : ℂ) T)).restrictScalars ℚ :=
        Submodule.span_le.2 fun v hv =>
          Submodule.subset_span (Set.mem_insert_of_mem _ hv)
      exact h2 h1
  have hz' : ∀ i, z i ∈ Submodule.span 𝔸 (insert (1 : ℂ) T) := fun i =>
    Submodule.span_le.2 hLT (mem_span_of_mem_logAlgSpan (hz i))
  choose F hFsub hFmem using fun i => Submodule.mem_span_finite_of_mem_span (hz' i)
  set G : Finset ℂ := Finset.univ.biUnion F with hG
  have hGsub : ↑G ⊆ insert (1 : ℂ) T := by
    intro w hw
    simp only [hG, Finset.coe_biUnion, Finset.mem_coe, Finset.mem_univ, Set.iUnion_true,
      Set.mem_iUnion] at hw
    obtain ⟨i, hi⟩ := hw
    exact hFsub i hi
  set S : Finset ℂ := G.filter (· ∈ T) with hS
  have hSsub : ∀ w ∈ S, w ∈ T := by
    intro w hw
    simpa [hS] using (Finset.mem_filter.1 hw).2
  have hGS : ↑G ⊆ insert (1 : ℂ) (↑S : Set ℂ) := by
    intro w hw
    rcases hGsub hw with h | h
    · exact Set.mem_insert_iff.2 (Or.inl h)
    · exact Set.mem_insert_of_mem _
        (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hw, h⟩))
  have hzS : ∀ i, z i ∈ Submodule.span 𝔸 (insert (1 : ℂ) (↑S : Set ℂ)) := by
    intro i
    refine Submodule.span_mono ?_ (hFmem i)
    intro w hw
    refine hGS ?_
    simp only [hG, Finset.coe_biUnion, Finset.mem_coe, Finset.mem_univ, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨i, hw⟩
  -- index `S` by `Fin S.card`
  refine ⟨S.card, fun k => ((S.equivFin.symm k : ℂ)), ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun k : Fin S.card =>
        (⟨(S.equivFin.symm k : ℂ), hSsub _ (S.equivFin.symm k).2⟩ : T)) := by
      intro a b hab
      have h1 : (S.equivFin.symm a : ℂ) = (S.equivFin.symm b : ℂ) := by
        simpa using congrArg (fun t : T => (t : ℂ)) hab
      exact S.equivFin.symm.injective (Subtype.ext h1)
    exact hTli.comp _ hinj
  · intro k
    exact hTsub (hSsub _ (S.equivFin.symm k).2)
  · intro i
    have hrange : Set.range (fun k : Fin S.card => ((S.equivFin.symm k : ℂ))) = (↑S : Set ℂ) := by
      ext w
      constructor
      · rintro ⟨k, rfl⟩; exact (S.equivFin.symm k).2
      · intro hw
        refine ⟨S.equivFin ⟨w, hw⟩, ?_⟩
        show ((S.equivFin.symm (S.equivFin ⟨w, hw⟩) : ↥S) : ℂ) = w
        rw [Equiv.symm_apply_apply]
    rw [hrange]
    exact hzS i

end LeanFormalizations.StrongSix
