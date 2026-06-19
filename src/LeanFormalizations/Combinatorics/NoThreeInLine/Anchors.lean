/-
# Decidable certificate for `NoThreeCollinear`, and witness anchors

`NoThreeCollinear s` is a statement about `Collinear ℝ` over the real plane — not directly
decidable. But collinearity of a *triple* is equivalent to vanishing of the integer `2×2`
determinant (`detZ`), which IS decidable on a concrete `Finset`. So:

* `decNoThree s` — the decidable predicate "every triple of distinct points of `s` has nonzero
  integer determinant".
* `decNoThree_imp` — `decNoThree s → NoThreeCollinear s` (a genuine certificate, via
  `collinear_imp_det3_zero`: a collinear triple has `detZ = 0`).

This lets `decide` / `native_decide` certify that an explicit configuration has no three in line —
an anti-vacuity anchor, kept OFF the headline axiom path. It is also the experimental tool used to
search for / validate the HJSW covering construction (`Hyperbola.lean`).
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- The integer `2×2` determinant of `q - p` and `r - p`. Vanishes iff `p, q, r` are collinear
over `ℝ` (it is the integer model of `det3 ∘ toReal`). -/
def detZ (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((r.1 : ℤ) - p.1) * ((q.2 : ℤ) - p.2)

/-- `det3` over `ℝ` on embedded grid points is the cast of the integer `detZ`. -/
theorem det3_toReal_eq_detZ (p q r : ℕ × ℕ) :
    det3 (toReal p) (toReal q) (toReal r) = (detZ p q r : ℝ) := by
  simp only [det3, toReal, detZ]; push_cast; ring

/-- The decidable mirror of `NoThreeCollinear`: every triple of pairwise-distinct points of `s`
has nonzero integer determinant. -/
def decNoThree (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p ≠ q → p ≠ r → q ≠ r → detZ p q r ≠ 0

instance (s : Finset (ℕ × ℕ)) : Decidable (decNoThree s) := by
  unfold decNoThree; infer_instance

/-- **The certificate.** A configuration whose every distinct triple has nonzero determinant has
no three collinear. (Collinearity ⇒ `det3 = 0` ⇒ `detZ = 0`, contradicting the hypothesis; so any
collinear triple repeats a point.) -/
theorem decNoThree_imp {s : Finset (ℕ × ℕ)} (h : decNoThree s) : NoThreeCollinear s := by
  intro p hp q hq r hr hcol
  by_contra hne
  rw [not_or, not_or] at hne
  obtain ⟨hpq, hpr, hqr⟩ := hne
  have hdet : det3 (toReal p) (toReal q) (toReal r) = 0 := collinear_imp_det3_zero hcol
  rw [det3_toReal_eq_detZ] at hdet
  exact h p hp q hq r hr hpq hpr hqr (by exact_mod_cast hdet)

/-- **The certificate is exact:** `decNoThree` is logically equivalent to `NoThreeCollinear`. The
forward direction uses `collinear_of_det3_zero` (a vanishing determinant *is* collinearity), so a
`decNoThree` computation neither over- nor under-reports — in particular a `decide`-`false` is a
genuine proof that the configuration *does* have three in line. -/
theorem decNoThree_iff (s : Finset (ℕ × ℕ)) : decNoThree s ↔ NoThreeCollinear s := by
  refine ⟨decNoThree_imp, fun h p hp q hq r hr hpq hpr hqr hz => ?_⟩
  have hcol : Collinear ℝ ({toReal p, toReal q, toReal r} : Set (ℝ × ℝ)) :=
    collinear_of_det3_zero (by rw [det3_toReal_eq_detZ]; exact_mod_cast hz)
  rcases h p hp q hq r hr hcol with h | h | h
  · exact hpq h
  · exact hpr h
  · exact hqr h

/-- Consequently `NoThreeCollinear` is decidable on a concrete `Finset` — so `decide` /
`native_decide` can settle it directly. -/
instance (s : Finset (ℕ × ℕ)) : Decidable (NoThreeCollinear s) :=
  decidable_of_iff _ (decNoThree_iff s)

/-! ### Concrete witness anchor: the HJSW count `3(p−1)` at `p = 5`

An explicit `12`-point configuration in the `10 × 10` grid with no three collinear — a genuine
instance of `hjsw_lower` (`3·(5−1) = 12 ≤ maxNoThreeInLine (2·5)`), found by exhaustive search over
the `xy ≡ 1 (mod 5)` rectangle-corner family and certified here by `native_decide` on `decNoThree`.
This is an anti-vacuity lock: it witnesses that the count is achievable and that `decNoThree_imp`
fires end-to-end. It uses `native_decide`, so its axiom set is intentionally NOT the bare base — it
is OFF the headline path (the general theorem must be a `Collinear ℝ` proof, not a finite check). -/
def witness5 : Finset (ℕ × ℕ) :=
  {(6, 1), (1, 6), (6, 6), (2, 3), (2, 8), (7, 8), (3, 2), (3, 7), (8, 7), (9, 4), (4, 9), (9, 9)}

theorem witness5_card : witness5.card = 12 := by decide

theorem witness5_grid : IsGridSet 10 witness5 := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness5_noThree : NoThreeCollinear witness5 :=
  decNoThree_imp (by native_decide)

/-- **HJSW count, verified instance at `p = 5`:** the `10 × 10` grid admits `12 = 3·(5−1)` points
with no three collinear. (A `native_decide`-certified witness; off the headline axiom path.) -/
theorem hjsw_lower_five : 3 * (5 - 1) ≤ maxNoThreeInLine (2 * 5) :=
  le_csSup (bddAbove_grid 10) ⟨witness5, witness5_card.symm, witness5_grid, witness5_noThree⟩

/-! ### Concrete witness anchor: the HJSW count `3(p−1)` at `p = 7`

A `19`-point configuration in the `14 × 14` grid with no three collinear (found by greedy search,
certified by `native_decide`), giving the HJSW count `3·(7−1) = 18 ≤ maxNoThreeInLine 14` with one to
spare. The single modular hyperbola cannot reach `18` at `p = 7` (see `Hyperbola.lean` / `PLAN.md`);
this witness confirms the count is nonetheless achievable in the `14 × 14` grid. Off the headline
axiom path (`native_decide`). -/
def witness7 : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (2, 4), (3, 2), (3, 9), (4, 2), (4, 11), (5, 7), (5, 8),
    (6, 13), (7, 11), (8, 5), (8, 6), (11, 8), (12, 3), (13, 9)}

theorem witness7_card : witness7.card = 19 := by decide

theorem witness7_grid : IsGridSet 14 witness7 := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness7_noThree : NoThreeCollinear witness7 :=
  decNoThree_imp (by native_decide)

/-- **HJSW count, verified instance at `p = 7`:** the `14 × 14` grid admits `≥ 18 = 3·(7−1)` points
with no three collinear (the `19`-point `witness7`). -/
theorem hjsw_lower_seven : 3 * (7 - 1) ≤ maxNoThreeInLine (2 * 7) := by
  have h : 19 ≤ maxNoThreeInLine (2 * 7) :=
    le_csSup (bddAbove_grid (2 * 7)) ⟨witness7, witness7_card.symm, witness7_grid, witness7_noThree⟩
  exact le_trans (by norm_num) h

end LeanFormalizations.NoThreeInLine
