/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385, phase E4: residues mod `y#` as independent residue vectors (CRT counting)

`s ↦ (s mod p)_{p ≤ y}` is a bijection `[0, y#) → ∏_{p ≤ y} [0, p)`; split the primes into `L` and
its complement, and count.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open Finset

/-- The primes `≤ y`, as in `primorial`. -/
def ps (y : ℕ) : Finset ℕ := (range (y + 1)).filter Nat.Prime

theorem primorial_eq_prod_ps (y : ℕ) : primorial y = ∏ p ∈ ps y, p := rfl

theorem pos_of_mem_ps {y p : ℕ} (h : p ∈ ps y) : 0 < p :=
  (mem_filter.1 h).2.pos

/-- The residue vector of `s` over a set `L` of primes `≤ y`. -/
def resVec {y : ℕ} (L : Finset ℕ) (hL : L ⊆ ps y) (s : ℕ) : ∀ p : L, Fin p :=
  fun p => ⟨s % p, Nat.mod_lt _ (pos_of_mem_ps (hL p.2))⟩

theorem eq_of_mod_eq_ps {y s s' : ℕ} (hs : s < primorial y) (hs' : s' < primorial y)
    (h : ∀ p ∈ ps y, s % p = s' % p) : s = s' := by
  wlog hle : s ≤ s' generalizing s s'
  · exact (this hs' hs (fun p hp => (h p hp).symm) (by omega)).symm
  have hdvd : primorial y ∣ s' - s := by
    rw [primorial_eq_prod_ps]
    refine Finset.prod_primes_dvd _ (fun p hp => (mem_filter.1 hp).2.prime) fun p hp => ?_
    exact (Nat.modEq_iff_dvd' hle).1 (h p hp)
  have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

/-- **CRT counting.** -/
theorem card_filter_range_primorial (y : ℕ) (L : Finset ℕ) (hL : L ⊆ ps y)
    (Φ : (∀ p : L, Fin p) → (∀ p : ↥(ps y \ L), Fin p) → Prop) [∀ u v, Decidable (Φ u v)] :
    ((range (primorial y)).filter fun s =>
        Φ (resVec L hL s) (resVec (ps y \ L) sdiff_subset s)).card =
      ∑ u, (univ.filter fun v => Φ u v).card := by
  set g : ℕ → (∀ p : L, Fin p) × (∀ p : ↥(ps y \ L), Fin p) :=
    fun s => (resVec L hL s, resVec (ps y \ L) sdiff_subset s) with hg
  have hinj : Set.InjOn g (range (primorial y)) := by
    intro s hs s' hs' hss
    simp only [coe_range, Set.mem_Iio] at hs hs'
    refine eq_of_mod_eq_ps hs hs' fun p hp => ?_
    by_cases hpL : p ∈ L
    · have := congrArg (fun z => (z.1 ⟨p, hpL⟩ : ℕ)) hss
      simpa [hg, resVec] using this
    · have := congrArg (fun z => (z.2 ⟨p, mem_sdiff.2 ⟨hp, hpL⟩⟩ : ℕ)) hss
      simpa [hg, resVec] using this
  have hcardP : Fintype.card ((∀ p : L, Fin p) × (∀ p : ↥(ps y \ L), Fin p)) = primorial y := by
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [prod_coe_sort L (fun p => p), prod_coe_sort (ps y \ L) (fun p => p), mul_comm,
      prod_sdiff hL, primorial_eq_prod_ps]
  have himage : (range (primorial y)).image g = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_range, hcardP]
  calc ((range (primorial y)).filter fun s => Φ (g s).1 (g s).2).card
      = (((range (primorial y)).filter fun s => Φ (g s).1 (g s).2).image g).card :=
        (card_image_of_injOn (hinj.mono (by intro x hx; simp at hx ⊢; exact hx.1))).symm
    _ = (univ.filter fun z : (∀ p : L, Fin p) × (∀ p : ↥(ps y \ L), Fin p) => Φ z.1 z.2).card := by
        rw [← himage, filter_image]
    _ = ∑ u, (univ.filter fun v => Φ u v).card := by
        rw [card_filter, Fintype.sum_prod_type]
        exact sum_congr rfl fun u _ => (card_filter _ _).symm

end LeanFormalizations.Erdos385.Exceptional
