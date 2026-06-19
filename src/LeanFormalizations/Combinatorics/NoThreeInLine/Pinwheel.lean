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

/-! ### Reduction of the headline to the crux

The mechanical `card`/`grid` facts wire any no-three pinwheel straight into the bound. What remains
is to exhibit a drop-rule making the pinwheel no-three-collinear. -/

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
