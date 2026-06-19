/-
# The HJSW pinwheel: scaffolding for the `3(p−1)` construction

Hall–Jackson–Sudbery–Wild (J. Combin. Theory Ser. A 18 (1975) 336–341, Theorem 2) realize
`3(p−1)` no-three-in-line points in the `2p × 2p` grid — density `3/2`, the best *proven* constant.

## The structure of the construction (and what is mechanical vs. the crux)

Take the full modular hyperbola `H(k,p) = {(x,y) : x·y ≡ k (mod p)}` inside `[0,2p)²` with
`x, y ≢ 0`. For each nonzero residue `r ∈ [1,p)` put `s = (k·r⁻¹) mod p ∈ [1,p)`; the class of `r`
occupies the **four corners** of a `p × p` square:
```
(r, s)        (r+p, s)
(r, s+p)      (r+p, s+p)
```
The construction keeps **three of the four** corners per class (discarding one), giving
`3 · (p−1) = 3(N−2)/2` points where `N = 2p`.

**Two facts are independent of *which* corner is dropped** — they are mechanical and proved here
for an arbitrary drop-rule `drop : ℕ → Fin 4`:
* `pinwheel_card` : the set has exactly `3(p−1)` points;
* `pinwheel_grid` : it lies in the `2p × 2p` grid.

**The crux is the drop-rule itself.** A line of slope `0` or `∞` is *automatically* safe: each row
`y = h` (resp. column `x = h`) meets only the unique class whose `y`-residue (resp. `x`-residue) is
`h mod p`, so it carries at most that class's two corners — never three (this is
`row_unique_class` / `col_unique_class` below). The **only** danger is a line of slope `±1`, and the
general HJSW Lemma (`hyperbola_line_two_congruent`) shows any collinear triple has two congruent
points — necessarily the surviving diagonal of one class. So no-three-in-line reduces to a finite
slope-`±1` *incidence* check: choosing `drop` (the "pinwheel" family assignment) so that the surviving
diagonal of each class extends through no kept corner of another class. The two classes sharing a
slope-`±1` line are the two roots of a quadratic (`r² + Dr − k ≡ 0`), swapped by the anti-diagonal
reflection `σ : (x,y) ↦ (p−y, p−x)` (`pin_reflection_swaps_roots`); HJSW's family rule sends them to
complementary slope-families. Formalizing that assignment + the incidence check is the remaining work
(`pinwheel_exists_noThree`, currently the lone disclosed `sorry`).
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.HyperbolaLine
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- The four corners of the class of residue `r`: `(r,s), (r+p,s), (r,s+p), (r+p,s+p)` with
`s = (k·r⁻¹) mod p`. Indexed by `Fin 4` via the two bits of `i` (`x`-copy `= i.val % 2`,
`y`-copy `= i.val / 2`): `0 ↦ (r,s)`, `1 ↦ (r+p,s)`, `2 ↦ (r,s+p)`, `3 ↦ (r+p,s+p)`. -/
def pinCorner (p k r : ℕ) (i : Fin 4) : ℕ × ℕ :=
  ((if i.val % 2 = 0 then r else r + p),
   (if i.val < 2 then hyperbolaY p k r else hyperbolaY p k r + p))

/-- The kept corners for residue `r`: all four except the one indexed by `drop r`. -/
def pinKeep (p k : ℕ) (drop : ℕ → Fin 4) (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ.erase (drop r)).image (pinCorner p k r)

/-- **The HJSW pinwheel point set** (drop-rule `drop`): three corners of each nonzero residue
class, inside the `2p × 2p` grid. -/
def pinwheel (p k : ℕ) (drop : ℕ → Fin 4) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 p).biUnion (pinKeep p k drop)

/-- The first coordinate of any corner is `r` or `r + p`. -/
theorem pinCorner_fst (p k r : ℕ) (i : Fin 4) :
    (pinCorner p k r i).1 = r ∨ (pinCorner p k r i).1 = r + p := by
  simp only [pinCorner]; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The second coordinate of any corner is `s` or `s + p` (`s = hyperbolaY p k r`). -/
theorem pinCorner_snd (p k r : ℕ) (i : Fin 4) :
    (pinCorner p k r i).2 = hyperbolaY p k r ∨
      (pinCorner p k r i).2 = hyperbolaY p k r + p := by
  simp only [pinCorner]; split
  · exact Or.inl rfl
  · exact Or.inr rfl

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- The four corners of a class are pairwise distinct (`p > 0`), so `pinCorner` is injective. -/
theorem pinCorner_injective {p k r : ℕ} (hp : 0 < p) : Function.Injective (pinCorner p k r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [pinCorner, Prod.ext_iff] <;> omega

/-- Each kept set has exactly three points. -/
theorem pinKeep_card {p k : ℕ} (drop : ℕ → Fin 4) {r : ℕ} (hp : 0 < p) :
    (pinKeep p k drop r).card = 3 := by
  rw [pinKeep, Finset.card_image_of_injective _ (pinCorner_injective hp),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rfl

/-- Every kept point of residue `r` has first coordinate `≡ r (mod p)`. -/
theorem pinKeep_fst_mod {p k : ℕ} (drop : ℕ → Fin 4) {r : ℕ} (hr : r < p)
    {x : ℕ × ℕ} (hx : x ∈ pinKeep p k drop r) : x.1 % p = r := by
  rw [pinKeep, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rcases pinCorner_fst p k r i with h | h
  · rw [h, Nat.mod_eq_of_lt hr]
  · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-- Distinct residues give disjoint kept sets (different `x`-residue). -/
theorem pinKeep_disjoint {p k : ℕ} (drop : ℕ → Fin 4) {a b : ℕ}
    (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    Disjoint (pinKeep p k drop a) (pinKeep p k drop b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact hab ((pinKeep_fst_mod drop ha hxa).symm.trans (pinKeep_fst_mod drop hb hxb))

/-- **The pinwheel has `3(p−1)` points** — for *any* drop-rule. Three kept corners per class,
`p−1` disjoint classes. -/
theorem pinwheel_card {p k : ℕ} (drop : ℕ → Fin 4) (hp : 0 < p) :
    (pinwheel p k drop).card = 3 * (p - 1) := by
  rw [pinwheel, Finset.card_biUnion (fun a ha b hb hab =>
        pinKeep_disjoint drop (Finset.mem_Ico.mp ha).2 (Finset.mem_Ico.mp hb).2 hab)]
  rw [Finset.sum_congr rfl (fun r _ => pinKeep_card drop hp)]
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  omega

/-- **The pinwheel lies in the `2p × 2p` grid** — for any drop-rule. -/
theorem pinwheel_grid {p k : ℕ} (drop : ℕ → Fin 4) (hp : 0 < p) :
    IsGridSet (2 * p) (pinwheel p k drop) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  intro x hx
  rw [pinwheel, Finset.mem_biUnion] at hx
  obtain ⟨r, hr, hxk⟩ := hx
  simp only [Finset.mem_Ico] at hr
  rw [pinKeep, Finset.mem_image] at hxk
  obtain ⟨i, _, rfl⟩ := hxk
  have hsy : hyperbolaY p k r < p := ZMod.val_lt _
  refine ⟨?_, ?_⟩
  · rcases pinCorner_fst p k r i with h | h <;> rw [h] <;> omega
  · rcases pinCorner_snd p k r i with h | h <;> rw [h] <;> omega

/-! ### Membership + hyperbola-relation plumbing (for the cross-class slope-±1 proof)

Helpers exposing, for a pinwheel point, its residue class `r`, corner index `i`, and the defining
hyperbola relation `x·y ≡ k`. These feed `hyperbola_line_two_congruent` (which needs each point on
the full hyperbola) in the eventual no-three proof. -/

/-- A pinwheel point is a kept corner of some nonzero residue class. -/
theorem mem_pinwheel {p k : ℕ} {drop : ℕ → Fin 4} {x : ℕ × ℕ} (hx : x ∈ pinwheel p k drop) :
    ∃ r, 1 ≤ r ∧ r < p ∧ ∃ i, i ≠ drop r ∧ x = pinCorner p k r i := by
  rw [pinwheel, Finset.mem_biUnion] at hx
  obtain ⟨r, hr, hxk⟩ := hx
  rw [pinKeep, Finset.mem_image] at hxk
  obtain ⟨i, hi, rfl⟩ := hxk
  simp only [Finset.mem_Ico] at hr
  rw [Finset.mem_erase] at hi
  exact ⟨r, hr.1, hr.2, i, hi.1, rfl⟩

/-- The first coordinate of any corner has residue `r` (`r + p ≡ r`). -/
theorem pinCorner_xres (p k r : ℕ) (i : Fin 4) :
    ((pinCorner p k r i).1 : ZMod p) = (r : ZMod p) := by
  rcases pinCorner_fst p k r i with h | h <;> rw [h] <;> push_cast [ZMod.natCast_self] <;> ring

/-- The second coordinate of any corner has residue `s = hyperbolaY p k r` (`s + p ≡ s`). -/
theorem pinCorner_yres (p k r : ℕ) (i : Fin 4) :
    ((pinCorner p k r i).2 : ZMod p) = (hyperbolaY p k r : ZMod p) := by
  rcases pinCorner_snd p k r i with h | h <;> rw [h] <;> push_cast [ZMod.natCast_self] <;> ring

/-- Every pinwheel corner satisfies the hyperbola relation `x·y ≡ k (mod p)`. -/
theorem pinCorner_rel {p k r : ℕ} [Fact p.Prime] (hr0 : (r : ZMod p) ≠ 0) (i : Fin 4) :
    ((pinCorner p k r i).1 : ZMod p) * ((pinCorner p k r i).2 : ZMod p) = (k : ZMod p) := by
  rw [pinCorner_xres, pinCorner_yres]; exact hyperbola_xy_eq hr0

/-! ### A no-three subcase: three corners of one class are never collinear

If a collinear pinwheel triple has all three points in the *same* class, they are three of the four
corners of a `p × p` rectangle — a right triangle of area `p²/2 ≠ 0`, never collinear. This
discharges the "two-congruent-points' third point is again in their class" subcase of the no-three
argument (the cross-class subcases are the slope-`±1` crux). -/

set_option linter.unreachableTactic false in
/-- Three pairwise-distinct corners of a single class are not collinear (`det3 = ±p² ≠ 0`). -/
theorem pinCorner_not_collinear {p k r : ℕ} (hp : 0 < p) {i j l : Fin 4}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ¬ Collinear ℝ ({toReal (pinCorner p k r i), toReal (pinCorner p k r j),
      toReal (pinCorner p k r l)} : Set (ℝ × ℝ)) := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  intro hcol
  have hd := collinear_imp_det3_zero hcol
  simp only [toReal, det3, pinCorner] at hd
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp_all only [ne_eq, not_true_eq_false, Fin.reduceEq] <;>
    · push_cast at hd
      nlinarith [hd, hp', mul_pos hp' hp']

/-- A nonzero residue `r ∈ [1,p)` is nonzero in `ZMod p`. -/
private theorem res_ne_zero {p r : ℕ} (hr1 : 1 ≤ r) (hr2 : r < p) : (r : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; have := Nat.le_of_dvd hr1 hd; omega

/-- **The reduction entry point.** Any collinear triple of pinwheel points has two with equal
`x`-residue — i.e. two lie in the SAME residue class (the general HJSW Lemma applied to the pinwheel).
With `pinCorner_not_collinear` (same-class impossible) this pins every collinear triple to the
cross-class slope-`±1` configuration the drop-rule must defeat. -/
theorem pinwheel_collinear_same_xres {p k : ℕ} (hp : p.Prime) (hk : (k : ZMod p) ≠ 0)
    {drop : ℕ → Fin 4} {P Q R : ℕ × ℕ}
    (hP : P ∈ pinwheel p k drop) (hQ : Q ∈ pinwheel p k drop) (hR : R ∈ pinwheel p k drop)
    (hcol : Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ))) :
    (P.1 : ZMod p) = Q.1 ∨ (P.1 : ZMod p) = R.1 ∨ (Q.1 : ZMod p) = R.1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨rP, hP1, hP2, iP, _, rfl⟩ := mem_pinwheel hP
  obtain ⟨rQ, hQ1, hQ2, iQ, _, rfl⟩ := mem_pinwheel hQ
  obtain ⟨rR, hR1, hR2, iR, _, rfl⟩ := mem_pinwheel hR
  exact hyperbola_line_x_residue_eq hk
    (pinCorner_rel (res_ne_zero hP1 hP2) iP) (pinCorner_rel (res_ne_zero hQ1 hQ2) iQ)
    (pinCorner_rel (res_ne_zero hR1 hR2) iR) hcol

/-- **Slope-0 safety.** Two pinwheel points sharing a `y`-coordinate have the same `x`-residue, hence
lie in the same class. (The `y`-residue determines the class: `s ↦ r = k·s⁻¹`.) Combined with
`pinCorner_not_collinear`, a horizontal line never carries a *cross-class* pair — so the cross-class
crux is purely slope-`±1`. The slope-∞ analogue is trivial (equal `x`-coordinate ⇒ equal `x`-residue). -/
theorem pinwheel_eq_snd_eq_xres {p k : ℕ} (hp : p.Prime) (hk : (k : ZMod p) ≠ 0)
    {drop : ℕ → Fin 4} {P Q : ℕ × ℕ}
    (hP : P ∈ pinwheel p k drop) (hQ : Q ∈ pinwheel p k drop) (hsnd : P.2 = Q.2) :
    (P.1 : ZMod p) = (Q.1 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨rP, hP1, hP2, iP, _, rfl⟩ := mem_pinwheel hP
  obtain ⟨rQ, hQ1, hQ2, iQ, _, rfl⟩ := mem_pinwheel hQ
  have hy : (hyperbolaY p k rP : ZMod p) = (hyperbolaY p k rQ : ZMod p) := by
    have h2 : ((pinCorner p k rP iP).2 : ZMod p) = ((pinCorner p k rQ iQ).2 : ZMod p) :=
      congrArg (fun n : ℕ => (n : ZMod p)) hsnd
    rwa [pinCorner_yres, pinCorner_yres] at h2
  have relP := pinCorner_rel (k := k) (res_ne_zero hP1 hP2) iP
  have relQ := pinCorner_rel (k := k) (res_ne_zero hQ1 hQ2) iQ
  rw [pinCorner_xres, pinCorner_yres] at relP
  rw [pinCorner_xres, pinCorner_yres] at relQ
  have hsP : (hyperbolaY p k rP : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at relP; exact hk relP.symm
  rw [pinCorner_xres, pinCorner_xres]
  exact mul_right_cancel₀ hsP (by rw [relP, hy, relQ])

/-! ### Reduction of the headline to the crux

The mechanical `card`/`grid` facts wire any no-three pinwheel straight into the bound. What remains
is to exhibit a drop-rule making the pinwheel no-three-collinear — and by `pinwheel_collinear_same_xres`,
`pinwheel_eq_snd_eq_xres` + `pinCorner_not_collinear` that is now exactly the cross-class slope-`±1`
incidence. -/

/-- **Crux (disclosed).** There is a drop-rule whose pinwheel is no-three-in-line. This is the HJSW
slope-`±1` incidence argument (Theorem 2, pp. 339–340): the family assignment routes the two roots of
each slope-line quadratic to complementary slope-families. The mechanical scaffolding
(`pinwheel_card`, `pinwheel_grid`) and the load-bearing algebra (`hyperbola_line_two_congruent`) are
in place; the finite incidence check is the remaining work. -/
theorem pinwheel_exists_noThree {p k : ℕ} (hp : p.Prime) (hk : (k : ZMod p) ≠ 0) :
    ∃ drop : ℕ → Fin 4, NoThreeCollinear (pinwheel p k drop) := by
  sorry

/-- **The HJSW `3(p−1)` lower bound (existence form).** For prime `p` the `2p × 2p` grid carries
`3(p−1)` points with no three collinear — modulo the slope-incidence crux
`pinwheel_exists_noThree`. -/
theorem hjsw_pinwheel_exists {p : ℕ} (hp : p.Prime) :
    ∃ s : Finset (ℕ × ℕ), IsGridSet (2 * p) s ∧ NoThreeCollinear s ∧ s.card = 3 * (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : ((1 : ℕ) : ZMod p) ≠ 0 := by rw [Nat.cast_one]; exact one_ne_zero
  obtain ⟨drop, hdrop⟩ := pinwheel_exists_noThree hp hk
  exact ⟨pinwheel p 1 drop, pinwheel_grid drop hp.pos, hdrop, pinwheel_card drop hp.pos⟩

/-- **The HJSW `3(p−1)` lower bound** (modulo the crux): `maxNoThreeInLine (2p) ≥ 3(p−1)`. With a
prime `p ≈ N/2` this is the `(3/2 − ε)N` constant. -/
theorem three_mul_pred_le_maxNoThreeInLine {p : ℕ} (hp : p.Prime) :
    3 * (p - 1) ≤ maxNoThreeInLine (2 * p) := by
  obtain ⟨s, hg, h3, hc⟩ := hjsw_pinwheel_exists hp
  exact le_csSup (bddAbove_grid (2 * p)) ⟨s, hc.symm, hg, h3⟩

end LeanFormalizations.NoThreeInLine
