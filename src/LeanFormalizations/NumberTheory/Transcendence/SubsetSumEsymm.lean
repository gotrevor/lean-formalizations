/-
# The subset-sum `esymm` is rational — the last open fact of π-Lindemann

This file supplies the single remaining input of `MonicRootSums.transcendental_pi_of_subsetSumEsymm`:
for `θ : Fin n → ℂ` the complex roots of a monic `G : ℚ[X]`, the elementary symmetric
functions of the multiset of all subset-sums `{∑_{k∈t} θ k}` are rational
(`subsetSum_esymm_rational`). This is the **fundamental theorem of symmetric polynomials**
applied to the subset-sums: the family is symmetric in `θ`, so its `esymm` is a polynomial in
the elementary symmetric functions of `θ` (= ± coefficients of `G`, Vieta), hence rational.

**Provenance.** Produced by Harmonic's Aristotle auto-formalizer (job `b7252abe`, prompt
`tools/aristotle/pi-subsetsum-esymm-submitted.txt`) and **independently kernel-verified** in
this repo (Lean v4.29.1): `#print axioms subsetSum_esymm_rational = [propext,
Classical.choice, Quot.sound]` (no `sorry`, no added axiom). Ported verbatim. The four helper
lemmas (`ringHom_map_multiset_esymm`, `subsetSum_esymm_isSymmetric`, `esymm_theta_mem_range`,
`aeval_mem_range`) coincide with the local roadmap independently developed this lap.
-/
import Mathlib

open scoped BigOperators Nat Classical
open Polynomial

namespace LeanFormalizations.Transcendence.SubsetSumEsymm

open MvPolynomial Multiset Finset

/-- A ring homomorphism commutes with `Multiset.esymm`. -/
lemma ringHom_map_multiset_esymm {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (s : Multiset R) (m : ℕ) :
    f (s.esymm m) = (s.map f).esymm m := by
  unfold Multiset.esymm
  induction' s using Multiset.induction_on with a s ih generalizing m
  · cases m <;> simp +decide
  · rcases m with ( _ | m ) <;> simp_all +decide [ Multiset.powersetCard_cons ]
    simp +decide [ ← ih, Multiset.sum_map_mul_left ]

/-- The `m`-th elementary symmetric function of the subset-sums of the variables `X k`
(`k : Fin n`) is a symmetric polynomial. -/
lemma subsetSum_esymm_isSymmetric (n m : ℕ) :
    (((Finset.univ.powerset : Finset (Finset (Fin n))).val.map
        (fun t => Finset.sum t (fun k => MvPolynomial.X k))
        : Multiset (MvPolynomial (Fin n) ℚ)).esymm m).IsSymmetric := by
  intro e
  set f : MvPolynomial (Fin n) ℚ →+* MvPolynomial (Fin n) ℚ := (MvPolynomial.rename e).toRingHom
  show f _ = _
  rw [ringHom_map_multiset_esymm f _ m]
  congr 1
  simp +zetaDelta at *
  convert Multiset.map_univ_val_equiv ( Equiv.finsetCongr e ) using 2
  constructor <;> intro h <;> simp_all +decide
  · exact Multiset.map_univ_val_equiv ( Equiv.finsetCongr e )
  · conv_rhs => rw [ ← h ] ; simp +decide [ Finset.sum_map ]

/-- Vieta: the elementary symmetric functions of the complex roots `theta` of a monic
rational polynomial `G` are rational. -/
lemma esymm_theta_mem_range (n : ℕ) (theta : Fin n → ℂ) (G : Polynomial ℚ)
    (hGmonic : G.Monic)
    (hroots : (G.map (algebraMap ℚ ℂ)).roots
      = (Finset.univ : Finset (Fin n)).val.map theta)
    (i : ℕ) :
    ((Finset.univ : Finset (Fin n)).val.map theta).esymm i ∈ Set.range (algebraMap ℚ ℂ) := by
  by_cases hi_le_d : i ≤ G.natDegree
  · have h_vieta : Multiset.esymm (Multiset.map theta (Finset.univ.val)) i = (-1 : ℂ) ^ i * Polynomial.coeff (G.map (algebraMap ℚ ℂ)) (G.natDegree - i) := by
      have h_coeff_eq_esymm_roots : Polynomial.coeff (G.map (algebraMap ℚ ℂ)) (G.natDegree - i) = Polynomial.leadingCoeff (G.map (algebraMap ℚ ℂ)) * (-1)^(G.natDegree - (G.natDegree - i)) * Multiset.esymm (G.map (algebraMap ℚ ℂ)).roots (G.natDegree - (G.natDegree - i)) := by
        convert Polynomial.coeff_eq_esymm_roots_of_card _ _ using 1
        all_goals try infer_instance
        · rw [ Polynomial.natDegree_map_of_leadingCoeff_ne_zero ] ; aesop
        · exact IsAlgClosed.card_roots_eq_natDegree
        · rw [ Polynomial.natDegree_map ] ; omega
      simp_all +decide [ Nat.sub_sub_self hi_le_d ]
      by_cases hi : Even i <;> simp_all +decide
    exact ⟨ ( -1 ) ^ i * G.coeff ( G.natDegree - i ), by aesop ⟩
  · rw [ ← hroots, Multiset.esymm ]
    rw [ Multiset.sum_eq_zero ] <;> norm_num
    intro x y hy hy' hx; have := Polynomial.card_roots' ( Polynomial.map ( algebraMap ℚ ℂ ) G ) ; simp_all +decide
    exact absurd ( Multiset.card_le_card hy ) ( by simpa [ hy', List.length_ofFn ] using by linarith )

/-- Evaluating a rational multivariate polynomial at all-rational points yields a rational
number. -/
lemma aeval_mem_range {n : ℕ} (g : Fin n → ℂ) (q : MvPolynomial (Fin n) ℚ)
    (hg : ∀ i, g i ∈ Set.range (algebraMap ℚ ℂ)) :
    (aeval g q : ℂ) ∈ Set.range (algebraMap ℚ ℂ) := by
  choose f hf using hg
  use MvPolynomial.eval f q; induction q using MvPolynomial.induction_on <;> aesop

end LeanFormalizations.Transcendence.SubsetSumEsymm

namespace LeanFormalizations.Transcendence

open SubsetSumEsymm MvPolynomial in
/-- **The subset-sum `esymm` is rational** (fundamental theorem of symmetric polynomials).
The single remaining input to `transcendental_pi_of_subsetSumEsymm`. Verified axiom-clean. -/
theorem subsetSum_esymm_rational (n : ℕ) (theta : Fin n → ℂ) (G : Polynomial ℚ)
    (hGmonic : G.Monic)
    (hroots : (G.map (algebraMap ℚ ℂ)).roots
      = (Finset.univ : Finset (Fin n)).val.map theta)
    (j : ℕ) :
    (((Finset.univ.powerset : Finset (Finset (Fin n))).val.map
        (fun t => Finset.sum t (fun k => theta k))).esymm j)
      ∈ Set.range (algebraMap ℚ ℂ) := by
  set M : Multiset (MvPolynomial (Fin n) ℚ) := ((Finset.univ.powerset : Finset (Finset (Fin n))).val.map (fun t => Finset.sum t (fun k => MvPolynomial.X k)))
  set p : MvPolynomial (Fin n) ℚ := M.esymm j
  have h_eval : MvPolynomial.aeval theta p = (Multiset.map (fun t => ∑ k ∈ t, theta k) (Finset.univ.powerset : Finset (Finset (Fin n))).val).esymm j := by
    convert ringHom_map_multiset_esymm ( MvPolynomial.aeval theta ).toRingHom M j using 1
    simp +zetaDelta at *
    congr 1
    simp +zetaDelta [Multiset.map_map, Function.comp, map_sum]
  obtain ⟨q, hq⟩ : ∃ q : MvPolynomial (Fin n) ℚ, MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i + 1)) q = p := by
    have h_surjective : Function.Surjective (MvPolynomial.esymmAlgHom (Fin n) ℚ n) := by
      apply MvPolynomial.esymmAlgHom_surjective; norm_num
    obtain ⟨ q, hq ⟩ := h_surjective ⟨ p,
      (MvPolynomial.mem_symmetricSubalgebra p).mpr (SubsetSumEsymm.subsetSum_esymm_isSymmetric n j) ⟩
    generalize_proofs at *
    exact ⟨ q, by simpa [ MvPolynomial.esymmAlgHom_apply ] using congr_arg Subtype.val hq ⟩
  have h_comp : MvPolynomial.aeval theta p = MvPolynomial.aeval (fun i : Fin n => MvPolynomial.aeval theta (MvPolynomial.esymm (Fin n) ℚ (i + 1))) q := by
    rw [ ← hq, MvPolynomial.comp_aeval_apply ]
  have h_aeval_esymm : ∀ i : Fin n, MvPolynomial.aeval theta (MvPolynomial.esymm (Fin n) ℚ (i + 1)) = (Finset.univ.val.map theta).esymm (i + 1) := by
    intro i; exact (by
    convert MvPolynomial.aeval_esymm_eq_multiset_esymm ( Fin n ) ℚ ( i + 1 ) theta using 1)
  have h_aeval_mem_range : MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map theta).esymm (i + 1)) q ∈ Set.range (algebraMap ℚ ℂ) := by
    apply SubsetSumEsymm.aeval_mem_range
    exact fun i => SubsetSumEsymm.esymm_theta_mem_range n theta G hGmonic hroots _
  aesop

end LeanFormalizations.Transcendence
