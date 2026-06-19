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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

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

/-- **Converse:** a vanishing determinant forces collinearity (in the real plane). Together with
`collinear_imp_det3_zero` this makes `det3 = 0 ⟺ Collinear ℝ` — the basis of the decidable
certificate `decNoThree` (`Anchors.lean`). -/
theorem collinear_of_det3_zero {p q r : ℝ × ℝ} (h : det3 p q r = 0) :
    Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert p _)]
  by_cases hq : q = p
  · -- degenerate: `q = p`, so the direction `r - p` works.
    refine ⟨r - p, fun x hx => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by subst hq; simp⟩
    · exact ⟨1, by simp only [vadd_eq_add, one_smul]; abel⟩
  · -- generic: direction `q - p ≠ 0`; `r - p` is a multiple of it by the determinant relation.
    refine ⟨q - p, fun x hx => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp only [vadd_eq_add, one_smul]; abel⟩
    · have hne : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
        by_contra hc
        rw [not_or, not_not, not_not, sub_eq_zero, sub_eq_zero] at hc
        exact hq (Prod.ext hc.1 hc.2)
      have hdet : (q.1 - p.1) * (x.2 - p.2) - (x.1 - p.1) * (q.2 - p.2) = 0 := h
      rcases hne with h1 | h2
      · refine ⟨(x.1 - p.1) / (q.1 - p.1), Prod.ext ?_ ?_⟩
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
          field_simp; ring
        · have key : (x.1 - p.1) / (q.1 - p.1) * (q.2 - p.2) = x.2 - p.2 := by
            rw [div_mul_eq_mul_div, div_eq_iff h1]; linear_combination -hdet
          simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub, key]
          ring
      · refine ⟨(x.2 - p.2) / (q.2 - p.2), Prod.ext ?_ ?_⟩
        · have key : (x.2 - p.2) / (q.2 - p.2) * (q.1 - p.1) = x.1 - p.1 := by
            rw [div_mul_eq_mul_div, div_eq_iff h2]; linear_combination hdet
          simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub, key]
          ring
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
          field_simp; ring

end LeanFormalizations.NoThreeInLine
