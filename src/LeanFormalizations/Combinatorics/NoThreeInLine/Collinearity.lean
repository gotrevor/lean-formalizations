/-
# Collinearity ↔ determinant, for the real plane

Two bridge lemmas connecting `Collinear ℝ` (the faithful predicate) to the elementary
`2 × 2` determinant criterion, which is what the combinatorial proofs actually compute with.

* `collinear_imp_det3_zero` — collinear triple ⇒ determinant vanishes. Used in the Erdős
  lower bound (we derive a contradiction from collinearity of parabola points).
* `collinear_of_eq_snd` — three points sharing a `y`-coordinate are collinear. Used in the
  `2N` upper bound (three points in one row are collinear).

Both go through `collinear_iff_of_mem`, sidestepping the general
linear-dependence ↔ determinant machinery.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace LeanFormalizations.NoThreeInLine

open scoped Affine

/-- The (signed) `2 × 2` determinant of the vectors `q - p` and `r - p`. It vanishes
iff `p, q, r` are collinear. -/
def det3 (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

/-- A collinear triple has vanishing determinant. -/
theorem collinear_imp_det3_zero {p q r : ℝ × ℝ}
    (h : Collinear ℝ ({p, q, r} : Set (ℝ × ℝ))) : det3 p q r = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert p _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨cq, hq⟩ := hv q (by simp)
  obtain ⟨cr, hr⟩ := hv r (by simp)
  have hq1 : q.1 - p.1 = cq * v.1 := by
    rw [hq]; simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  have hq2 : q.2 - p.2 = cq * v.2 := by
    rw [hq]; simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
  have hr1 : r.1 - p.1 = cr * v.1 := by
    rw [hr]; simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  have hr2 : r.2 - p.2 = cr * v.2 := by
    rw [hr]; simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
  simp only [det3, hq1, hq2, hr1, hr2]; ring

/-- **Converse: a vanishing determinant forces collinearity.** Together with
`collinear_imp_det3_zero` this gives the exact criterion `Collinear ℝ {P,Q,R} ↔ det3 P Q R = 0`. -/
theorem det3_zero_imp_collinear {P Q R : ℝ × ℝ} (h : det3 P Q R = 0) :
    Collinear ℝ ({P, Q, R} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert P _)]
  by_cases hQ1 : Q.1 - P.1 = 0
  · by_cases hQ2 : Q.2 - P.2 = 0
    · -- Q = P : direction R − P works
      have hQeq : Q = P := Prod.ext (by linarith) (by linarith)
      refine ⟨R - P, fun x hx => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp [hQeq]⟩
      · exact ⟨1, by simp⟩
    · -- vertical line : Q.1 = P.1 and the determinant forces R.1 = P.1
      have hR1 : R.1 - P.1 = 0 := by
        have hd : (Q.1 - P.1) * (R.2 - P.2) - (R.1 - P.1) * (Q.2 - P.2) = 0 := h
        rw [hQ1, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at hd
        exact hd.resolve_right hQ2
      refine ⟨Q - P, fun x hx => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(x.2 - P.2) / (Q.2 - P.2), ?_⟩
        apply Prod.ext
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
          rw [hQ1]; ring_nf; linarith
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
          field_simp
          ring
  · -- generic : direction Q − P, coefficient from the first coordinate
    refine ⟨Q - P, fun x hx => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨(x.1 - P.1) / (Q.1 - P.1), ?_⟩
      apply Prod.ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
        field_simp
        ring
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
        have hd : (Q.1 - P.1) * (x.2 - P.2) - (x.1 - P.1) * (Q.2 - P.2) = 0 := h
        field_simp
        linear_combination hd

/-- The exact collinearity criterion: `Collinear ℝ {P,Q,R} ↔ det3 P Q R = 0`. -/
theorem collinear_iff_det3_zero {P Q R : ℝ × ℝ} :
    Collinear ℝ ({P, Q, R} : Set (ℝ × ℝ)) ↔ det3 P Q R = 0 :=
  ⟨collinear_imp_det3_zero, det3_zero_imp_collinear⟩

/-- Three points sharing a `y`-coordinate lie on a (horizontal) line. -/
theorem collinear_of_eq_snd {p q r : ℝ × ℝ}
    (hpq : p.2 = q.2) (hqr : q.2 = r.2) :
    Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert p _)]
  refine ⟨(1, 0), ?_⟩
  intro x hx
  refine ⟨x.1 - p.1, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hx2 : x.2 = p.2 := by rcases hx with h | h | h <;> subst h <;> simp_all
  apply Prod.ext
  · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one]; ring
  · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, zero_add]
    exact hx2

/-- Alias for `det3_zero_imp_collinear`, the name used by the sheared-hyperbola (HJSW)
construction in `NoThreeInLine.Shear.*`. Same statement; kept so both no-three-in-line
developments share this one core lemma. -/
theorem collinear_of_det3_zero {p q r : ℝ × ℝ} (h : det3 p q r = 0) :
    Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) :=
  det3_zero_imp_collinear h

end LeanFormalizations.NoThreeInLine
