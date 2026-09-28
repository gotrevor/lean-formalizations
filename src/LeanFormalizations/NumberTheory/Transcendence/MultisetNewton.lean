/-
# Newton's identities for a multiset, and integrality of `k! · eₖ`

Mathlib has Newton's identities only for `MvPolynomial σ R` over a `Fintype` (`mul_esymm_eq_sum`).
The Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`) needs them for the multiset of conjugate
powers `β₁^N, …, β_d^N`, whose power sums are rational integers (`pisot_conjPowSum_add_mem_int`)
but whose elementary symmetric functions are not directly available.  Transporting the
`MvPolynomial` identity along `aeval` of an enumeration of the multiset gives

    k · esymm s k = (−1)^(k+1) · Σ_{i+j=k, i<k} (−1)^i · esymm s i · psum s j,

and hence `k! · esymm s k ∈ ℤ` as soon as every power sum `psum s j`, `j ≤ k`, is in `ℤ`.

## Status: SORRY-FREE
-/
import Mathlib

namespace LeanFormalizations.Transcendence

open Finset MvPolynomial

/-- The `n`-th power sum of a multiset. -/
noncomputable def _root_.Multiset.psum {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) : R :=
  (s.map (· ^ n)).sum

theorem _root_.Multiset.psum_def {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    s.psum n = (s.map (· ^ n)).sum := rfl

/-- Any multiset is the image of `Finset.univ.val` under an enumeration. -/
theorem exists_fin_enum {R : Type*} (s : Multiset R) :
    ∃ (d : ℕ) (f : Fin d → R), (Finset.univ : Finset (Fin d)).val.map f = s := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep s
  refine ⟨l.length, l.get, ?_⟩
  have h1 : (Finset.univ : Finset (Fin l.length)).val = (List.finRange l.length : List _) := rfl
  rw [h1]
  have : ((List.finRange l.length : List (Fin l.length)).map l.get : List R) = l := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  exact congrArg _ this

/-- **Newton's identities for a multiset.** -/
theorem multiset_mul_esymm_eq_sum {R : Type*} [CommRing R] (s : Multiset R) (k : ℕ) :
    (k : R) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k}, (-1) ^ a.1 * s.esymm a.1 * s.psum a.2 := by
  classical
  obtain ⟨d, f, hf⟩ := exists_fin_enum s
  have hps : ∀ n : ℕ, (MvPolynomial.aeval f) (MvPolynomial.psum (Fin d) R n) = s.psum n := by
    intro n
    rw [Multiset.psum_def, ← hf, Multiset.map_map, MvPolynomial.psum, map_sum, Finset.sum]
    simp [Function.comp_def]
  have hmain := MvPolynomial.mul_esymm_eq_sum (Fin d) R k
  have h2 := congrArg (MvPolynomial.aeval f) hmain
  simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hf, hps] at h2
  exact h2

/-- Being a rational integer, as a predicate on a commutative ring. -/
def IsRatInt {R : Type*} [CommRing R] (x : R) : Prop := ∃ z : ℤ, x = (z : R)

theorem IsRatInt.add {R : Type*} [CommRing R] {x y : R} (hx : IsRatInt x) (hy : IsRatInt y) :
    IsRatInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; ring⟩

theorem IsRatInt.mul {R : Type*} [CommRing R] {x y : R} (hx : IsRatInt x) (hy : IsRatInt y) :
    IsRatInt (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by push_cast; ring⟩

theorem IsRatInt.neg {R : Type*} [CommRing R] {x : R} (hx : IsRatInt x) : IsRatInt (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by push_cast; ring⟩

theorem IsRatInt.zero {R : Type*} [CommRing R] : IsRatInt (0 : R) := ⟨0, by simp⟩

theorem IsRatInt.natCast {R : Type*} [CommRing R] (n : ℕ) : IsRatInt (n : R) := ⟨n, by simp⟩

theorem IsRatInt.sum {R : Type*} [CommRing R] {ι : Type*} (t : Finset ι) (g : ι → R)
    (h : ∀ i ∈ t, IsRatInt (g i)) : IsRatInt (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using IsRatInt.zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-- **`k! · eₖ` is a rational integer** when all the power sums `p_j`, `j ≤ k`, are. -/
theorem multiset_isRatInt_factorial_mul_esymm {R : Type*} [CommRing R] (s : Multiset R) :
    ∀ k : ℕ, (∀ j ≤ k, IsRatInt (s.psum j)) → IsRatInt ((k.factorial : R) * s.esymm k) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hp
    match k, ih, hp with
    | 0, _, _ => simpa [Multiset.esymm] using IsRatInt.natCast (R := R) 1
    | (m + 1), ih, hp =>
      have hmain := multiset_mul_esymm_eq_sum s (m + 1)
      have hfac : ((m + 1).factorial : R) = (m.factorial : R) * ((m + 1 : ℕ) : R) := by
        rw [Nat.factorial_succ]; push_cast; ring
      set F : Finset (ℕ × ℕ) := {a ∈ Finset.antidiagonal (m + 1) | a.1 < m + 1} with hF
      have key : IsRatInt ((m.factorial : R) *
          ∑ a ∈ F, (-1 : R) ^ a.1 * s.esymm a.1 * s.psum a.2) := by
        rw [Finset.mul_sum]
        refine IsRatInt.sum _ _ fun a ha => ?_
        rw [hF, Finset.mem_filter, Finset.mem_antidiagonal] at ha
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨c, hc⟩ : a.1.factorial ∣ m.factorial :=
          Nat.factorial_dvd_factorial (by omega)
        have hrw : (m.factorial : R) * ((-1 : R) ^ a.1 * s.esymm a.1 * s.psum a.2)
            = ((c : R) * (-1 : R) ^ a.1) * (((a.1.factorial : ℕ) : R) * s.esymm a.1)
              * s.psum a.2 := by
          rw [hc]; push_cast; ring
        rw [hrw]
        refine IsRatInt.mul (IsRatInt.mul ?_ ?_) (hp a.2 (by omega))
        · exact (IsRatInt.natCast c).mul ⟨(-1) ^ a.1, by push_cast; ring⟩
        · exact ih a.1 (by omega) fun j hj => hp j (by omega)
      rw [hfac, mul_assoc, hmain]
      have hrw2 : (m.factorial : R) * ((-1 : R) ^ (m + 1 + 1) *
            ∑ a ∈ F, (-1 : R) ^ a.1 * s.esymm a.1 * s.psum a.2)
          = (-1 : R) ^ (m + 1 + 1) * ((m.factorial : R) *
            ∑ a ∈ F, (-1 : R) ^ a.1 * s.esymm a.1 * s.psum a.2) := by ring
      rw [hrw2]
      exact IsRatInt.mul ⟨(-1) ^ (m + 1 + 1), by push_cast; ring⟩ key

end LeanFormalizations.Transcendence
