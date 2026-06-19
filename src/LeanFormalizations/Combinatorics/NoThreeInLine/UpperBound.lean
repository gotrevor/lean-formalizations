/-
# The `2N` upper bound (pigeonhole)

The only fully general, fully proven theorem of the no-three-in-line problem: a grid set
with no three collinear has at most `2N` points. Three points in a single row share a
`y`-coordinate, hence are collinear; so each of the `N` rows holds at most `2` points.

This is `Green72.allowedSetSize_le` (a `sorry` stub in `formal-conjectures`), here proven.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Collinearity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- In a no-three-collinear grid set, each row (fixed `y`-coordinate) holds at most two
points: three would be collinear on a horizontal line. -/
theorem row_card_le_two {s : Finset (ℕ × ℕ)} (h3 : NoThreeCollinear s) (y : ℕ) :
    (s.filter (fun p => p.2 = y)).card ≤ 2 := by
  by_contra hc
  rw [not_le, Finset.two_lt_card_iff] at hc
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hc
  rw [Finset.mem_filter] at hp hq hr
  have hcol : Collinear ℝ ({toReal p, toReal q, toReal r} : Set (ℝ × ℝ)) := by
    refine collinear_of_eq_snd ?_ ?_
    · simp only [toReal]; rw [hp.2, hq.2]
    · simp only [toReal]; rw [hq.2, hr.2]
  rcases h3 p hp.1 q hq.1 r hr.1 hcol with h | h | h
  · exact hpq h
  · exact hpr h
  · exact hqr h

/-- **The `2N` upper bound.** Any set of grid points (in `[0,N) × [0,N)`) with no three
collinear has at most `2N` points. -/
theorem card_le_two_mul {N : ℕ} {s : Finset (ℕ × ℕ)}
    (hg : IsGridSet N s) (h3 : NoThreeCollinear s) : s.card ≤ 2 * N := by
  have hmap : ∀ p ∈ s, p.2 ∈ Finset.range N := fun p hp => Finset.mem_range.mpr (hg p hp).2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc ∑ y ∈ Finset.range N, (s.filter (fun p => p.2 = y)).card
      ≤ ∑ _y ∈ Finset.range N, 2 := Finset.sum_le_sum (fun y _ => row_card_le_two h3 y)
    _ = 2 * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-- The grid maximum is at most `2N`. -/
theorem maxNoThreeInLine_le {N : ℕ} : maxNoThreeInLine N ≤ 2 * N := by
  apply csSup_le
  · exact ⟨0, ∅, by simp [IsGridSet, NoThreeCollinear]⟩
  · rintro n ⟨s, rfl, hg, h3⟩
    exact card_le_two_mul hg h3

/-- The defining set of `maxNoThreeInLine N` is bounded above (needed to read the `sSup`). -/
theorem bddAbove_grid (N : ℕ) :
    BddAbove {n | ∃ s : Finset (ℕ × ℕ), n = s.card ∧ IsGridSet N s ∧ NoThreeCollinear s} := by
  refine ⟨2 * N, ?_⟩
  rintro n ⟨s, rfl, hg, h3⟩
  exact card_le_two_mul hg h3

end LeanFormalizations.NoThreeInLine
