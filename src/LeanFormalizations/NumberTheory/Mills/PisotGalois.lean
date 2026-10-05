/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsLarge
import LeanFormalizations.NumberTheory.Mills.SaitoPisot

/-!
# Phase 62, lap 3: two Galois facts about the conjugates of a Pisot number

Let `β` be a Pisot number, `f` its integer minimal polynomial.  Both facts come from one move:
an automorphism `σ` of the algebraic numbers sending some conjugate to `β`, after which every
other conjugate has modulus `< 1`.

* `pow_ne_pow_of_roots`: distinct conjugates `γ ≠ δ` have `γ^P ≠ δ^P` for `P ≥ 1`
  (if `σ γ = β` then `σ δ` is a conjugate `≠ β` with `|σ δ|^P = β^P > 1`).
* `eq_or_eq_conj_of_norm_eq` (**Mignotte-lite**): two conjugates `γ, δ ≠ β` of equal modulus have
  `δ ∈ {γ, γ̄}`.  Otherwise `ρ = γγ̄ = δδ̄` is a nonzero algebraic integer each of whose
  conjugates `σρ = σγ·σγ̄ = σδ·σδ̄` has modulus `< 1` (at most one of the four factors is `β`),
  so the product of its conjugates, a nonzero integer, has modulus `< 1`.
-/

namespace LeanFormalizations.Mills.PisotGalois

open Polynomial LeanFormalizations.Literature LeanFormalizations.Mills
open LeanFormalizations.Mills.TheoremDMixed LeanFormalizations.Mills.ShiftedMillsLarge

/-- The inclusion of the algebraic numbers into `ℂ`. -/
noncomputable abbrev ι : AlgQ →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom

theorem ι_injective : Function.Injective ι := fun _ _ h => Subtype.ext h

/-- A complex root of a monic integer polynomial lifts to a root in the algebraic numbers. -/
theorem exists_lift {f : ℤ[X]} (hf : f.Monic) {z : ℂ}
    (hz : (f.map (Int.castRingHom ℂ)).eval z = 0) :
    ∃ z' : AlgQ, ι z' = z ∧ (f.map (Int.castRingHom AlgQ)).eval z' = 0 := by
  have halg : IsAlgebraic ℚ z := by
    refine ⟨f.map (Int.castRingHom ℚ), (hf.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
        RingHom.ext fun n => by simp]
    exact hz
  refine ⟨⟨z, (mem_algebraicClosure_iff).2 halg⟩, rfl, ?_⟩
  apply ι_injective
  rw [eval_map_int_hom ι f, map_zero]
  exact hz

/-- Automorphisms permute the roots. -/
theorem eval_conj_root {f : ℤ[X]} (σ : AlgQ ≃ₐ[ℚ] AlgQ) {x : AlgQ}
    (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    (f.map (Int.castRingHom AlgQ)).eval (σ x) = 0 := by
  have h := eval_map_int_hom (σ.toAlgHom.toRingHom) f x
  rw [hx, map_zero] at h
  exact h.symm

/-- The image in `ℂ` of a root in the algebraic numbers is a root. -/
theorem eval_ι_root {f : ℤ[X]} {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    (f.map (Int.castRingHom ℂ)).eval (ι x) = 0 := by
  rw [← eval_map_int_hom ι f, hx, map_zero]

/-- Complex conjugation permutes the complex roots of an integer polynomial. -/
theorem eval_conj_complex {f : ℤ[X]} {z : ℂ} (hz : (f.map (Int.castRingHom ℂ)).eval z = 0) :
    (f.map (Int.castRingHom ℂ)).eval (starRingEnd ℂ z) = 0 := by
  rw [← eval_map_int_hom (starRingEnd ℂ) f, hz, map_zero]

/-- `β` is a complex root of its integer minimal polynomial. -/
theorem eval_beta (β : ℝ) : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval (β : ℂ) = 0 := by
  have h := eval_map_int_hom Complex.ofRealHom (minpoly ℤ β) β
  have h0 : ((minpoly ℤ β).map (Int.castRingHom ℝ)).eval β = 0 := by
    have := minpoly.aeval ℤ β
    rwa [aeval_def, algebraMap_int_eq, ← eval_map] at this
  rw [h0, map_zero] at h
  exact h.symm

/-- The Pisot property for complex roots of the integer minimal polynomial. -/
theorem norm_lt_one_of_root {β : ℝ} (hβ : IsPisot β) {z : ℂ}
    (hz : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval z = 0) (hne : z ≠ β) : ‖z‖ < 1 :=
  minpoly_int_conj_small hβ z
    ((mem_roots ((minpoly_int_monic hβ.2.1).map _).ne_zero).2 hz) hne

theorem int_degree_pos {β : ℝ} (hβ : IsPisot β) : 1 ≤ (minpoly ℤ β).natDegree :=
  minpoly.natDegree_pos hβ.2.1

/-- **Distinct conjugates have distinct powers.** -/
theorem pow_ne_pow_of_roots {β : ℝ} (hβ : IsPisot β) {γ δ : ℂ}
    (hγ : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval γ = 0)
    (hδ : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval δ = 0) (hne : γ ≠ δ) {P : ℕ}
    (hP : 1 ≤ P) : γ ^ P ≠ δ ^ P := by
  intro heq
  set f := minpoly ℤ β with hf
  have hint := hβ.2.1
  have hmon : f.Monic := minpoly_int_monic hint
  have hirr : Irreducible f := minpoly_int_irreducible hint
  have hd : 1 ≤ f.natDegree := int_degree_pos hβ
  have hβ1 : 1 < β := hβ.1
  have hbig : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).eval z = 0 → z ^ P = (β : ℂ) ^ P →
      z = β := by
    intro z hz hzP
    by_contra hzβ
    have h1 := norm_lt_one_of_root hβ hz hzβ
    have h2 : ‖z‖ ^ P = β ^ P := by
      rw [← norm_pow, hzP, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h3 : ‖z‖ ^ P < 1 := pow_lt_one₀ (norm_nonneg _) h1 (by omega)
    have h4 : 1 < β ^ P := one_lt_pow₀ hβ1 (by omega)
    linarith
  by_cases hγβ : γ = β
  · have : δ = β := hbig δ hδ (by rw [← heq, hγβ])
    exact hne (hγβ.trans this.symm)
  obtain ⟨γ', hγ'ι, hγ'⟩ := exists_lift hmon hγ
  obtain ⟨δ', hδ'ι, hδ'⟩ := exists_lift hmon hδ
  obtain ⟨β', hβ'ι, hβ'⟩ := exists_lift hmon (eval_beta β)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_roots f hmon hirr hd hγ' hβ'
  have hz := eval_ι_root (eval_conj_root σ hδ')
  have hpow : δ' ^ P = γ' ^ P := ι_injective (by rw [map_pow, map_pow, hδ'ι, hγ'ι, heq])
  have hzP : ι (σ δ') ^ P = (β : ℂ) ^ P := by
    rw [← map_pow, ← map_pow σ, hpow, map_pow, hσ, map_pow, hβ'ι]
  have hzβ := hbig _ hz hzP
  have h' : σ δ' = σ γ' := by
    rw [hσ]; exact ι_injective (by rw [hzβ, hβ'ι])
  have := σ.injective h'
  exact hne (by rw [← hγ'ι, ← hδ'ι, this])

/-- A nonempty multiset of reals in `[0, 1)` has product `< 1`. -/
theorem multiset_prod_lt_one {s : Multiset ℝ} (hs : s ≠ 0) (h : ∀ x ∈ s, 0 ≤ x ∧ x < 1) :
    s.prod < 1 := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a t ih =>
    have ha := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x ∧ x < 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.prod_cons]
    by_cases ht0 : t = 0
    · rw [ht0, Multiset.prod_zero, mul_one]; exact ha.2
    · have htp : 0 ≤ t.prod := Multiset.prod_nonneg fun x hx => (ht x hx).1
      have := ih ht0 ht
      nlinarith

/-- A monic integer polynomial of positive degree with nonzero constant term has a complex root
of modulus `≥ 1`. -/
theorem exists_root_one_le_norm {g : ℤ[X]} (hmon : g.Monic) (hdeg : 1 ≤ g.natDegree)
    (h0 : g.coeff 0 ≠ 0) :
    ∃ z : ℂ, (g.map (Int.castRingHom ℂ)).eval z = 0 ∧ 1 ≤ ‖z‖ := by
  set Q := g.map (Int.castRingHom ℂ) with hQ
  have hQm : Q.Monic := hmon.map _
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hfac : Q = (Q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hQm
  have heval : Q.eval 0 = (Q.roots.map fun a => -a).prod := by
    conv_lhs => rw [hfac]
    rw [eval_multiset_prod, Multiset.map_map]
    simp
  have hc0 : Q.eval 0 = ((g.coeff 0 : ℤ) : ℂ) := by
    rw [hQ, eval_map, eval₂_at_zero]
    simp
  have hone : (1 : ℝ) ≤ ‖Q.eval 0‖ := by
    rw [hc0, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs h0
  have hprod : ‖Q.eval 0‖ = (Q.roots.map (‖·‖)).prod := by
    rw [heval, norm_multiset_prod_neg]
  have hcard : Multiset.card Q.roots = g.natDegree := by
    rw [← hmon.natDegree_map (Int.castRingHom ℂ)]
    exact (Polynomial.splits_iff_card_roots.1 hsplit)
  by_contra hcon
  push Not at hcon
  have hne : Q.roots.map (‖·‖) ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    rw [Multiset.card_map, hcard, Multiset.card_zero] at this
    omega
  have hlt := multiset_prod_lt_one hne (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    refine ⟨norm_nonneg _, hcon z ?_⟩
    exact (mem_roots hQm.ne_zero).1 hz)
  linarith

/-- **Mignotte-lite.**  Two conjugates `γ, δ` of a Pisot number `β` with `|γ| = |δ|` satisfy
`δ = γ` or `δ = γ̄`. -/
theorem eq_or_eq_conj_of_norm_eq {β : ℝ} (hβ : IsPisot β) {γ δ : ℂ}
    (hγ : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval γ = 0)
    (hδ : ((minpoly ℤ β).map (Int.castRingHom ℂ)).eval δ = 0)
    (hn : ‖γ‖ = ‖δ‖) : δ = γ ∨ δ = starRingEnd ℂ γ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set f := minpoly ℤ β with hf
  have hint := hβ.2.1
  have hmon : f.Monic := minpoly_int_monic hint
  have hirrf : Irreducible f := minpoly_int_irreducible hint
  have hdf : 1 ≤ f.natDegree := int_degree_pos hβ
  set γb := starRingEnd ℂ γ with hγbd
  set δb := starRingEnd ℂ δ with hδbd
  have hγb : (f.map (Int.castRingHom ℂ)).eval γb = 0 := eval_conj_complex hγ
  have hδb : (f.map (Int.castRingHom ℂ)).eval δb = 0 := eval_conj_complex hδ
  -- the four are pairwise distinct across the two pairs
  have d1 : γ ≠ δ := fun h => h1 h.symm
  have d2 : γ ≠ δb := fun h => h2 (by rw [hγbd, h, hδbd, Complex.conj_conj])
  have d3 : γb ≠ δ := fun h => h2 h.symm
  have d4 : γb ≠ δb := fun h => d1 ((starRingEnd ℂ).injective h)
  -- `ρ = γγ̄ = δδ̄ ≠ 0`
  have hρ : γ * γb = δ * δb := by
    rw [hγbd, hδbd, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hn]
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact d1 (by rw [h0]; exact (norm_eq_zero.1 hn.symm).symm)
  have hρ0 : γ * γb ≠ 0 := mul_ne_zero hγ0 (by rw [hγbd]; exact (_root_.map_ne_zero _).2 hγ0)
  -- lift to the algebraic numbers
  obtain ⟨γ', hγ'ι, hγ'⟩ := exists_lift hmon hγ
  obtain ⟨γb', hγb'ι, hγb'⟩ := exists_lift hmon hγb
  obtain ⟨δ', hδ'ι, hδ'⟩ := exists_lift hmon hδ
  obtain ⟨δb', hδb'ι, hδb'⟩ := exists_lift hmon hδb
  set ρ' := γ' * γb' with hρ'
  have hρδ : δ' * δb' = ρ' := ι_injective (by
    rw [map_mul, map_mul, hδ'ι, hδb'ι, hγ'ι, hγb'ι, hρ])
  have hρ'0 : ρ' ≠ 0 := by
    intro h0
    apply hρ0
    rw [← hγ'ι, ← hγb'ι, ← map_mul, ← hρ', h0, map_zero]
  have hintr : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → IsIntegral ℤ x := by
    intro x hx
    refine ⟨f, hmon, ?_⟩
    rw [eval₂_eq_eval_map, show algebraMap ℤ AlgQ = Int.castRingHom AlgQ from
      RingHom.ext_int _ _]
    exact hx
  have hρint : IsIntegral ℤ ρ' := (hintr _ hγ').mul (hintr _ hγb')
  set g := minpoly ℤ ρ' with hg
  have hgmon : g.Monic := minpoly.monic hρint
  have hgirr : Irreducible g := (minpoly.prime_of_isIntegrallyClosed hρint).irreducible
  have hgdeg : 1 ≤ g.natDegree := minpoly.natDegree_pos hρint
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h0
    have hmapQ : minpoly ℚ ρ' = g.map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hρint
    have : (minpoly ℚ ρ').coeff 0 = 0 := by rw [hmapQ, coeff_map, h0, map_zero]
    exact minpoly.coeff_zero_ne_zero hρint.tower_top hρ'0 this
  have hρroot : (g.map (Int.castRingHom AlgQ)).eval ρ' = 0 := by
    have := minpoly.aeval ℤ ρ'
    rwa [aeval_def, show algebraMap ℤ AlgQ = Int.castRingHom AlgQ from RingHom.ext_int _ _,
      ← eval_map] at this
  obtain ⟨z, hz, hz1⟩ := exists_root_one_le_norm hgmon hgdeg hg0
  obtain ⟨z', hz'ι, hz'⟩ := exists_lift hgmon hz
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_roots g hgmon hgirr hgdeg hρroot hz'
  -- the four images
  set a := ι (σ γ') with ha
  set b := ι (σ γb') with hb
  set c := ι (σ δ') with hc
  set d := ι (σ δb') with hd
  have hzab : z = a * b := by rw [← hz'ι, ← hσ, hρ', map_mul, map_mul]
  have hzcd : z = c * d := by rw [← hz'ι, ← hσ, ← hρδ, map_mul, map_mul]
  have hroot : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 →
      (f.map (Int.castRingHom ℂ)).eval (ι (σ x)) = 0 :=
    fun x hx => eval_ι_root (eval_conj_root σ hx)
  have hdist : ∀ x y : AlgQ, ι x ≠ ι y → ι (σ x) ≠ ι (σ y) := by
    intro x y hxy h
    exact hxy (congrArg ι (σ.injective (ι_injective h)))
  have hac : a ≠ c := hdist _ _ (by rw [hγ'ι, hδ'ι]; exact d1)
  have had : a ≠ d := hdist _ _ (by rw [hγ'ι, hδb'ι]; exact d2)
  have hbc : b ≠ c := hdist _ _ (by rw [hγb'ι, hδ'ι]; exact d3)
  have hbd : b ≠ d := hdist _ _ (by rw [hγb'ι, hδb'ι]; exact d4)
  have hpair : ∀ x y : ℂ, (f.map (Int.castRingHom ℂ)).eval x = 0 →
      (f.map (Int.castRingHom ℂ)).eval y = 0 → x ≠ β → y ≠ β → ‖x * y‖ < 1 := by
    intro x y hx hy hxβ hyβ
    rw [norm_mul]
    have := norm_lt_one_of_root hβ hx hxβ
    have := norm_lt_one_of_root hβ hy hyβ
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hlt : ‖z‖ < 1 := by
    by_cases hab : a ≠ β ∧ b ≠ β
    · rw [hzab]; exact hpair _ _ (hroot _ hγ') (hroot _ hγb') hab.1 hab.2
    · have hcβ : c ≠ β := by
        intro hcβ
        rcases not_and_or.1 hab with h | h
        · exact hac ((not_not.1 h).trans hcβ.symm)
        · exact hbc ((not_not.1 h).trans hcβ.symm)
      have hdβ : d ≠ β := by
        intro hdβ
        rcases not_and_or.1 hab with h | h
        · exact had ((not_not.1 h).trans hdβ.symm)
        · exact hbd ((not_not.1 h).trans hdβ.symm)
      rw [hzcd]; exact hpair _ _ (hroot _ hδ') (hroot _ hδb') hcβ hdβ
  linarith

end LeanFormalizations.Mills.PisotGalois
