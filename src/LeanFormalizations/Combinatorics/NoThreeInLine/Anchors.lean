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
import LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola

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

/-! ### Concrete witness anchor: the HJSW count `3(p−1)` at `p = 11`

An exact `30 = 3·(11−1)`-point configuration in the `22 × 22` grid with no three collinear (greedy
search under a spread-out ordering, certified by `native_decide`). Notably the count is NOT reachable
by row-major greed here — it took a diversified order — consistent with the HJSW count being a real
construction, not a trivial packing. Off the headline axiom path. -/
def witness11 : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 15), (7, 4), (8, 19), (3, 14), (9, 3), (10, 18), (16, 7), (0, 8), (20, 5), (21, 20),
    (2, 7), (5, 21), (7, 20), (2, 15), (6, 13), (20, 21), (1, 8), (9, 4), (5, 14), (14, 17), (16, 16),
    (13, 10), (14, 2), (15, 17), (10, 12), (17, 1), (17, 9), (4, 9), (6, 16)}

theorem witness11_card : witness11.card = 30 := by decide

theorem witness11_grid : IsGridSet 22 witness11 := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness11_noThree : NoThreeCollinear witness11 :=
  decNoThree_imp (by native_decide)

/-- **HJSW count, verified instance at `p = 11`:** the `22 × 22` grid admits `30 = 3·(11−1)` points
with no three collinear. -/
theorem hjsw_lower_eleven : 3 * (11 - 1) ≤ maxNoThreeInLine (2 * 11) := by
  have h : 30 ≤ maxNoThreeInLine (2 * 11) :=
    le_csSup (bddAbove_grid (2 * 11))
      ⟨witness11, witness11_card.symm, witness11_grid, witness11_noThree⟩
  exact le_trans (by norm_num) h

/-! ### Concrete witness anchor: the HJSW count `3(p−1)` at `p = 13`

An exact `36 = 3·(13−1)`-point configuration in the `26 × 26` grid with no three collinear (greedy,
diversified ordering, `native_decide`-certified). Off the headline axiom path. -/
def witness13 : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 15), (7, 4), (8, 19), (3, 14), (9, 3), (10, 18), (16, 7), (0, 8), (1, 23), (20, 5),
    (21, 20), (2, 7), (3, 22), (23, 19), (12, 25), (14, 24), (2, 15), (6, 13), (5, 6), (13, 25),
    (7, 5), (8, 20), (15, 24), (5, 14), (14, 17), (21, 6), (18, 0), (23, 13), (18, 8), (19, 23),
    (17, 9), (17, 17), (19, 16), (15, 3), (4, 2)}

theorem witness13_card : witness13.card = 36 := by decide

theorem witness13_grid : IsGridSet 26 witness13 := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness13_noThree : NoThreeCollinear witness13 :=
  decNoThree_imp (by native_decide)

/-- **HJSW count, verified instance at `p = 13`:** the `26 × 26` grid admits `36 = 3·(13−1)` points
with no three collinear. -/
theorem hjsw_lower_thirteen : 3 * (13 - 1) ≤ maxNoThreeInLine (2 * 13) := by
  have h : 36 ≤ maxNoThreeInLine (2 * 13) :=
    le_csSup (bddAbove_grid (2 * 13))
      ⟨witness13, witness13_card.symm, witness13_grid, witness13_noThree⟩
  exact le_trans (by norm_num) h

/-! ### Structured witness: the SHEARED-HYPERBOLA construction at `p = 7`

Unlike `witness7` (greedy), this `18 = 3·(7−1)`-point config is the **lift-of-a-base** construction
that is the current lead for the general `hjsw_lower` (see `Hyperbola.lean`): every point's residue
mod `7` lies on the sheared hyperbola `y·(2x+1) ≡ 1 (mod 7)` (base
`{(0,1),(1,5),(2,3),(3,0),(4,4),(5,2),(6,6)}`), and the 18 points are a selection of the base's `4·7`
lifts into the `14 × 14` grid that avoids every slope-`±1` triple. `native_decide`-certified, off the
headline axiom path; it anchors the construction family in the kernel (the plain hyperbola `xy≡1`,
`|B|=6`, cannot reach `18`). -/
def witness7_shear : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 8), (1, 12), (2, 3), (2, 10), (4, 11), (5, 2), (5, 9), (6, 13), (7, 1), (8, 12),
    (9, 3), (10, 0), (11, 4), (11, 11), (12, 2), (12, 9), (13, 6)}

theorem witness7_shear_card : witness7_shear.card = 18 := by decide

theorem witness7_shear_grid : IsGridSet 14 witness7_shear := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness7_shear_noThree : NoThreeCollinear witness7_shear :=
  decNoThree_imp (by native_decide)

/-- **HJSW count via the sheared-hyperbola construction at `p = 7`:** the `14 × 14` grid admits
`18 = 3·(7−1)` points with no three collinear, drawn from the lifts of `y·(2x+1) ≡ 1 (mod 7)`. -/
theorem hjsw_lower_seven_shear : 3 * (7 - 1) ≤ maxNoThreeInLine (2 * 7) :=
  le_csSup (bddAbove_grid (2 * 7))
    ⟨witness7_shear, witness7_shear_card.symm, witness7_shear_grid, witness7_shear_noThree⟩

/-! ### Structured witnesses: the **uniform** drop-pole + 3-of-4 sheared construction at `p = 11, 13`

These extend `witness7_shear` to a *uniform* description of the sheared-hyperbola family, the current
lead for the general `hjsw_lower`. The selection rule, refined this lap (see `PENDING_WORK.md` Path B
/ `Hyperbola.lean`), is:

> **drop the pole base point `(p−1)/2` entirely, then keep exactly 3 of the 4 lifts of every other
> base point** (i.e. break exactly one of each base point's two slope-`±1` corner pairs — the
> diagonal `{(r,s),(r+p,s+p)}` or the antidiagonal `{(r+p,s),(r,s+p)}`).

This gives exactly `3·(p−1)` points and was verified feasible at `p = 7,11,13,17,19`. (It strictly
replaces the prior baton's "non-uniform 3,2,3,1,3,4,3" framing — a uniform per-point count of 3
exists.) The single open crux is now the *orientation* (which pair each point breaks); the explicit
selections below are concrete instances, `native_decide`-certified, off the headline axiom path. -/
def witness11_shear : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 12), (1, 4), (1, 15), (2, 9), (2, 20), (3, 8), (3, 19), (4, 5), (4, 16), (6, 17),
    (7, 3), (8, 2), (9, 7), (9, 18), (10, 21), (11, 1), (12, 15), (13, 20), (14, 19), (15, 5),
    (17, 6), (17, 17), (18, 3), (18, 14), (19, 2), (19, 13), (20, 18), (21, 10), (21, 21)}

theorem witness11_shear_card : witness11_shear.card = 30 := by decide

theorem witness11_shear_grid : IsGridSet 22 witness11_shear := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness11_shear_noThree : NoThreeCollinear witness11_shear :=
  decNoThree_imp (by native_decide)

/-- **HJSW count via the uniform sheared construction at `p = 11`:** the `22 × 22` grid admits
`30 = 3·(11−1)` points (drop pole + 3-of-4 lifts of `y·(2x+1) ≡ 1 (mod 11)`) with no three
collinear. -/
theorem hjsw_lower_eleven_shear : 3 * (11 - 1) ≤ maxNoThreeInLine (2 * 11) :=
  le_csSup (bddAbove_grid (2 * 11))
    ⟨witness11_shear, witness11_shear_card.symm, witness11_shear_grid, witness11_shear_noThree⟩

def witness13_shear : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 14), (1, 9), (1, 22), (2, 8), (2, 21), (3, 2), (3, 15), (4, 3), (4, 16), (5, 6),
    (5, 19), (7, 20), (8, 23), (9, 24), (10, 5), (11, 4), (12, 25), (13, 1), (14, 22), (15, 21),
    (16, 2), (17, 3), (18, 6), (20, 7), (20, 20), (21, 10), (21, 23), (22, 11), (22, 24), (23, 5),
    (23, 18), (24, 4), (24, 17), (25, 12), (25, 25)}

theorem witness13_shear_card : witness13_shear.card = 36 := by decide

theorem witness13_shear_grid : IsGridSet 26 witness13_shear := by
  intro p hp; fin_cases hp <;> exact ⟨by decide, by decide⟩

theorem witness13_shear_noThree : NoThreeCollinear witness13_shear :=
  decNoThree_imp (by native_decide)

/-- **HJSW count via the uniform sheared construction at `p = 13`:** the `26 × 26` grid admits
`36 = 3·(13−1)` points (drop pole + 3-of-4 lifts of `y·(2x+1) ≡ 1 (mod 13)`) with no three
collinear. -/
theorem hjsw_lower_thirteen_shear : 3 * (13 - 1) ≤ maxNoThreeInLine (2 * 13) :=
  le_csSup (bddAbove_grid (2 * 13))
    ⟨witness13_shear, witness13_shear_card.symm, witness13_shear_grid, witness13_shear_noThree⟩

/-! ### ⭐ The general closed-form sheared construction `shearSel p`

The closed-form selection rule (see `SELECTION-RULE-FOUND.md` / `Hyperbola.lean`) defines
`shearSel p`. The general `card`/`grid` facts are proven axiom-clean in `Hyperbola.lean`; the
`native_decide` instances below certify `NoThreeCollinear (shearSel p)` in our kernel at
`p = 7, 11, 13` (off the headline axiom path — the general theorem uses a `Collinear ℝ` argument). -/
theorem shearSel_seven_card : (shearSel 7).card = 18 := by native_decide

theorem shearSel_seven_grid : IsGridSet 14 (shearSel 7) :=
  shearSel_grid (p := 7) (by decide)

theorem shearSel_seven_noThree : NoThreeCollinear (shearSel 7) :=
  decNoThree_imp (by native_decide)

/-- **HJSW count via the closed-form sheared construction at `p = 7`.** -/
theorem hjsw_lower_seven_shearSel : 3 * (7 - 1) ≤ maxNoThreeInLine (2 * 7) :=
  le_csSup (bddAbove_grid (2 * 7))
    ⟨shearSel 7, shearSel_seven_card.symm, shearSel_seven_grid, shearSel_seven_noThree⟩

theorem shearSel_eleven_card : (shearSel 11).card = 30 := by native_decide

theorem shearSel_eleven_noThree : NoThreeCollinear (shearSel 11) :=
  decNoThree_imp (by native_decide)

theorem shearSel_thirteen_card : (shearSel 13).card = 36 := by native_decide

theorem shearSel_thirteen_noThree : NoThreeCollinear (shearSel 13) :=
  decNoThree_imp (by native_decide)

end LeanFormalizations.NoThreeInLine
