/-
# Power sums / symmetric functions of the roots of a monic integer polynomial are integers

This file discharges **fact (a)** of the π-Lindemann reduction (`PiLindemann.lean`): the
sum `∑_{r ∈ f.aroots ℂ} aeval r g` of any integer polynomial `g` over the complex roots of
a **monic** integer polynomial `f` is an integer (`sum_aeval_roots_int`). This is exactly the
`monic_rootsum` hypothesis of `hsum_of_monic_rootsum` (and hence of
`subsetSum_relation_impossible`).

The chain is Vieta + Newton's identities:
* `roots_esymm_int` — the elementary symmetric functions `esymm j` of `f.aroots ℂ` are
  integers (Vieta, `coeff_eq_esymm_roots_of_card`);
* `power_sum_int` — the power sums `∑ rᵏ` are integers (Newton's identities,
  `MvPolynomial.psum_eq_mul_esymm_sub_sum`, strong induction);
* `sum_aeval_roots_int` — hence `∑ g(r)` is an integer for any `g ∈ ℤ[X]`.

**Provenance.** This proof was produced by Harmonic's Aristotle auto-formalizer (job
`9a19f72e`, prompt archived at `tools/aristotle/pi-sum-aeval-roots-int-prompt.txt`) and then
**independently verified in this repository's kernel** (Lean v4.29.1 / our mathlib pin):
`#print axioms sum_aeval_roots_int = [propext, Classical.choice, Quot.sound]` (no `sorry`, no
added axiom). Ported verbatim into the project namespace.
-/
-- This file is an Aristotle-ported proof verified under `import Mathlib`; we keep that
-- broad import (rather than the project's usual targeted imports) to match the exact
-- environment in which it was kernel-verified axiom-clean.
import Mathlib
import LeanFormalizations.NumberTheory.Transcendence.PiLindemann

open Polynomial

namespace LeanFormalizations.Transcendence

/-- The elementary symmetric functions of the complex roots (with multiplicity) of a
monic integer polynomial are integers (Vieta's formulas). -/
theorem roots_esymm_int (f : Polynomial Int) (hf : f.Monic) (j : ℕ) :
    ∃ m : ℤ, (f.aroots Complex).esymm j = (m : Complex) := by
  set fC : Polynomial ℂ := f.map (algebraMap ℤ ℂ) with hfC_eq
  by_cases hj : j > f.natDegree
  · use 0; simp [Multiset.esymm]
    rw [Multiset.map_eq_zero.mpr] <;> norm_num
    exact Multiset.eq_zero_of_forall_notMem fun x hx => by
      have := Multiset.mem_powersetCard.mp hx
      linarith [Multiset.card_le_card this.1,
        show Multiset.card (f.aroots ℂ) ≤ f.natDegree from by
          erw [Polynomial.aroots]
          exact le_trans (Polynomial.card_roots' _)
            (by erw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] ; aesop)]
  · have h_coeff : fC.coeff (f.natDegree - j) = fC.leadingCoeff *
        (-1) ^ (f.natDegree - (f.natDegree - j)) *
          fC.roots.esymm (f.natDegree - (f.natDegree - j)) := by
      convert Polynomial.coeff_eq_esymm_roots_of_card _ _
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] ; aesop
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] ; aesop
      · exact IsAlgClosed.card_roots_eq_natDegree
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> aesop
    simp_all +decide [Polynomial.coeff_map, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    simp_all +decide [Nat.sub_sub_self hj, Polynomial.aroots_def]
    exact ⟨f.coeff (f.natDegree - j) * (-1) ^ j, by push_cast [h_coeff] ; ring_nf; aesop⟩

/-- The `k`-th power sum of the complex roots (with multiplicity) of a monic integer
polynomial is an integer. -/
theorem power_sum_int (f : Polynomial Int) (hf : f.Monic) (k : ℕ) :
    ∃ m : ℤ, ((f.aroots Complex).map (fun r => r ^ k)).sum = (m : Complex) := by
  set S := (f.aroots (Complex))
  set d := S.card with hd
  obtain ⟨v, hv⟩ : ∃ v : Fin d → ℂ, Multiset.ofList (List.ofFn v) = S := by
    obtain ⟨l, hl⟩ : ∃ l : List ℂ, l.length = d ∧ Multiset.ofList l = S := by
      exact ⟨S.toList, by simpa, by simp⟩
    use fun i => l[i]!
    convert hl.2
    refine' List.ext_get _ _ <;> aesop
  have h_ind : ∀ k, ∃ m : ℤ, (MvPolynomial.aeval v (MvPolynomial.psum (Fin d) ℤ k)) = m := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    by_cases hk : 0 < k <;> simp_all +decide [MvPolynomial.psum_eq_mul_esymm_sub_sum]
    · have h_esymm_int :
          ∀ n, ∃ m : ℤ, (MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℤ n)) = m := by
        intro n
        have := roots_esymm_int f hf n
        simp_all +decide [MvPolynomial.aeval_esymm_eq_multiset_esymm]
        exact this
      choose! m hm using h_esymm_int; choose! n hn using ih; simp_all +decide
      rw [Finset.sum_congr rfl fun x hx => by rw [hn _ <| by aesop]] ; norm_cast ; aesop
    · exact ⟨_, rfl⟩
  convert h_ind k
  simp +decide [← hv, MvPolynomial.psum]
  rw [List.sum_ofFn] ; rfl

/-- **The sum of an integer polynomial `g` evaluated over the complex roots (with
multiplicity) of a MONIC integer polynomial `f` is an integer.** Discharges the
`monic_rootsum` hypothesis of `PiLindemann.hsum_of_monic_rootsum` /
`subsetSum_relation_impossible`. -/
theorem sum_aeval_roots_int (f : Polynomial Int) (hf : f.Monic) (g : Polynomial Int) :
    ∃ N : Int,
      ((f.aroots Complex).map (fun r => Polynomial.aeval r g)).sum = (N : Complex) := by
  have h_eval : ∀ r : ℂ, (aeval r) g
      = ∑ i ∈ Finset.range (g.natDegree + 1), (g.coeff i : ℂ) * r ^ i := by
    simp +decide [Polynomial.aeval_eq_sum_range]
  have h_sum : ((f.aroots ℂ).map (fun r => (aeval r) g)).sum
      = ∑ i ∈ Finset.range (g.natDegree + 1),
          ((f.aroots ℂ).map (fun r => (g.coeff i : ℂ) * r ^ i)).sum := by
    induction' (f.aroots ℂ) using Multiset.induction_on with x s ih <;>
      simp_all +decide [Finset.sum_add_distrib]
  have h_power_sum : ∀ i : ℕ, ∃ m : ℤ, ((f.aroots ℂ).map (fun r => r ^ i)).sum = (m : ℂ) :=
    fun i => power_sum_int f hf i
  choose m hm using h_power_sum; simp_all +decide [Multiset.sum_map_mul_left]
  exact ⟨∑ x ∈ Finset.range (g.natDegree + 1), g.coeff x * m x, by push_cast; rfl⟩

/-! ### Fact (a) discharged: the conjugate-relation impossibility, no longer hypothetical

With `sum_aeval_roots_int` proven, the `monic_rootsum` hypothesis of
`subsetSum_relation_impossible` is satisfied unconditionally. Only the conjugate-polynomial
existence `hFroots` (the symmetric-function construction, fact (b)) remains. -/

/-- **`subsetSum_relation_impossible`, with fact (a) discharged.** Given a "conjugate"
family `θ` over `s` with `e^{θ k₀} = -1`, it is contradictory for an *integer* polynomial
`F` (with `F.eval 0 ≠ 0`) to have complex roots exactly the nonzero subset-sums `σ_t`. The
monic root-sum integrality is now supplied by `sum_aeval_roots_int`; the **sole** remaining
hypothesis is the conjugate-polynomial existence `hFroots` (fact (b), the symmetric-function
construction over the conjugates of `iπ`). -/
theorem subsetSum_relation_impossible_of_conjugatePoly
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℂ)
    (k₀ : ι) (hk₀ : k₀ ∈ s) (hval : Complex.exp (θ k₀) = -1)
    (F : Polynomial ℤ) (hF0 : F.eval 0 ≠ 0)
    (hFroots : F.aroots ℂ
        = (s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0)).val.map
            (fun t => ∑ k ∈ t, θ k)) :
    False :=
  subsetSum_relation_impossible s θ k₀ hk₀ hval
    (fun G hG q => sum_aeval_roots_int G hG q) F hF0 hFroots

end LeanFormalizations.Transcendence
