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


/-- Affine coordinates for a member of the `ℚ̄`-affine span of `μ`. -/
theorem exists_aff_of_mem {n : ℕ} {μ : Fin n → ℂ} {z : ℂ}
    (hz : z ∈ Submodule.span 𝔸 (insert (1 : ℂ) (Set.range μ))) :
    ∃ (a : 𝔸) (b : Fin n → 𝔸), z = (a : ℂ) + ∑ k, (b k : ℂ) * μ k := by
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨a, w, hw, rfl⟩ := hz
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔸).1 hw
  refine ⟨a, b, ?_⟩
  rw [← hb]
  simp [Algebra.smul_def]

/-- `aeval μ` sends the affine polynomial `aff a b` to `a + ∑ bₖμₖ`. -/
theorem aeval_aff {n : ℕ} (μ : Fin n → ℂ) (a : 𝔸) (b : Fin n → 𝔸) :
    aeval μ (aff a b) = (a : ℂ) + ∑ k, (b k : ℂ) * μ k := by
  simp [aff]

set_option maxHeartbeats 1000000 in
/-- **Roy's strong six exponentials theorem, under Schanuel's conjecture.** -/
theorem strongSix (hS : SchanuelConjecture) : StrongSixExponentials := by
  classical
  intro x y hx hy
  have hx' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) x := hx
  have hy' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) y := hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, μ, hμli, hμexp, hμmem⟩ :=
    exists_logBasis (fun p : Fin 2 × Fin 3 => x p.1 * y p.2) (fun p => hcon p.1 p.2)
  have hind : AlgebraicIndependent ℚ μ := algebraicIndependent_of_exp_isAlgebraic hS μ hμli hμexp
  have halg : Algebra.IsAlgebraic ℚ (↥(algebraicClosure ℚ ℂ)) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hindK : AlgebraicIndependent (↥(algebraicClosure ℚ ℂ)) μ :=
    hind.extendScalars (↥(algebraicClosure ℚ ℂ))
  have hinj : Function.Injective (aeval μ : MvPolynomial (Fin n) 𝔸 →ₐ[𝔸] ℂ) := hindK
  choose a b hab using fun p : Fin 2 × Fin 3 => exists_aff_of_mem (hμmem p)
  set pa : Fin 3 → 𝔸 := fun j => a (0, j) with hpa
  set pb : Fin 3 → Fin n → 𝔸 := fun j => b (0, j) with hpb
  set qa : Fin 3 → 𝔸 := fun j => a (1, j) with hqa
  set qb : Fin 3 → Fin n → 𝔸 := fun j => b (1, j) with hqb
  have hPval : ∀ j, aeval μ (aff (pa j) (pb j)) = x 0 * y j := fun j => by
    rw [aeval_aff]; exact (hab (0, j)).symm
  have hQval : ∀ j, aeval μ (aff (qa j) (qb j)) = x 1 * y j := fun j => by
    rw [aeval_aff]; exact (hab (1, j)).symm
  -- the cross relations
  have hcross : ∀ i j : Fin 3, aff (qa i) (qb i) * aff (pa j) (pb j)
      = aff (qa j) (qb j) * aff (pa i) (pb i) := by
    intro i j
    refine hinj ?_
    rw [map_mul, map_mul, hPval, hPval, hQval, hQval]
    ring
  -- `P` is `ℚ̄`-linearly independent
  have hx0 : x 0 ≠ 0 := hx'.ne_zero 0
  have hPind : LinearIndependent 𝔸 (fun j => aff (pa j) (pb j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ j, (g j : ℂ) * (x 0 * y j) = 0 := by
      have := congrArg (aeval μ) hg
      rw [map_sum, map_zero] at this
      simpa [Algebra.smul_def, hPval] using this
    have h1 : ∑ j, g j • y j = 0 := by
      have hx0' : x 0 ≠ 0 := hx0
      have : x 0 * ∑ j, (g j : ℂ) * y j = 0 := by
        rw [Finset.mul_sum]; rw [← h0]; apply Finset.sum_congr rfl; intro j _; ring
      have h2 : ∑ j, (g j : ℂ) * y j = 0 := (mul_eq_zero.1 this).resolve_left hx0'
      simpa [Algebra.smul_def] using h2
    exact Fintype.linearIndependent_iff.1 hy' g h1
  obtain ⟨c, hc⟩ := const_ratio pa qa pb qb hPind hcross
  -- `x₁ = c·x₀`, contradicting the `ℚ̄`-independence of `x`
  have hxc : x 1 = (c : ℂ) * x 0 := by
    have h := congrArg (aeval μ) (hc 0)
    rw [hQval, map_mul, hPval, aeval_C] at h
    have h' : x 1 * y 0 = (c : ℂ) * (x 0 * y 0) := h
    have hy0 : y 0 ≠ 0 := hy'.ne_zero 0
    have hz : (x 1 - (c : ℂ) * x 0) * y 0 = 0 := by linear_combination h'
    exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hy0)
  have hsum : ∑ i, (![c, -1] : Fin 2 → 𝔸) i • x i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def]
    have h1 : (algebraMap (↥𝔸) ℂ) c = (c : ℂ) := rfl
    have h2 : (algebraMap (↥𝔸) ℂ) (-1 : 𝔸) = (-1 : ℂ) := by
      rw [map_neg, map_one]
    rw [h1, h2, hxc]
    ring
  have hzero := Fintype.linearIndependent_iff.1 hx' _ hsum
  have : (-1 : 𝔸) = 0 := by simpa using hzero 1
  exact absurd this (by simp)

end LeanFormalizations.StrongSix
