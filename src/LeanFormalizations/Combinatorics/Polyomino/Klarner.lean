/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Klarner's constant: the growth rate of polyominoes

`A(n)` (`Polyomino.count n`) is the number of **fixed** polyominoes with `n` cells: finite,
edge-connected sets of unit squares in `ℤ²`, counted up to translation (rotations and reflections
count as different).  OEIS A001168: `1, 2, 6, 19, 63, 216, 760, …`.

**Klarner's constant** `λ = lim A(n)^{1/n}` exists (Klarner 1967, by Fekete's lemma applied to
`A(m) A(n) ≤ A(m + n)`).  Its value is unknown: numerically `λ ≈ 4.0625696 ± 5·10⁻⁷`
(Jensen 2003, series extrapolation, not rigorous).  Rigorously `4.00253 < λ ≤ 4.5238`, both
bounds computer-assisted.  Nothing is known about its arithmetic nature: not irrationality, not
transcendence, not even whether it has a closed form.

Source of the question: Numberphile, *Pentominoes and other Polyominoes* (2024,
`youtu.be/ONdgXYEBihA`).

## Layout

* Definitions: `gridGraph`, `IsPolyomino`, `IsAnchored`, `count`, `klarner`.
* Known theorems, proof deferred (`sorry`): finiteness, the small anchors `count 1..5`,
  supermultiplicativity, the exponential upper bound, `tendsto_klarner`.
* Literature inputs as hypothesis `Prop`s: `LowerBoundBRS2016`, `UpperBoundBui2025`,
  `MadrasRatioLimit`.
* Open conjecture nodes: `KlarnerIrrational`, `KlarnerTranscendental`, `KlarnerAsymptotic`.
* Proved: `KlarnerTranscendental → KlarnerIrrational`; the two literature bounds give
  `⌊λ⌋ = 4`.

## Encoding choices

A translation class is represented by its unique **anchored** member, the one whose
lexicographically least cell is the origin.  `count` uses `Set.ncard`, which is `0` on an
infinite set, so `count_finite` is what makes `count` mean what it says; the anchors
`count_one` … `count_five` are the faithfulness check against OEIS A001168.
`klarner` is defined as `⨆ n, A(n+1)^{1/(n+1)}`, which equals the limit because `A` is
supermultiplicative (Fekete); `tendsto_klarner` records that equivalence.
-/

namespace LeanFormalizations.Polyomino

open Filter Topology

/-- The square grid: cells of `ℤ²` are adjacent when they share an edge. -/
def gridGraph : SimpleGraph (ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun p q h => by rwa [abs_sub_comm q.1, abs_sub_comm q.2]⟩
  loopless := ⟨fun p h => by simp at h⟩

/-- A polyomino: a nonempty finite set of cells whose induced grid graph is connected
(`SimpleGraph.Connected` includes nonemptiness). -/
def IsPolyomino (s : Finset (ℤ × ℤ)) : Prop :=
  (SimpleGraph.induce (s : Set (ℤ × ℤ)) gridGraph).Connected

/-- The canonical member of a translation class: its lexicographically least cell is `(0, 0)`. -/
def IsAnchored (s : Finset (ℤ × ℤ)) : Prop :=
  ((0 : ℤ), (0 : ℤ)) ∈ s ∧ ∀ p ∈ s, toLex ((0 : ℤ), (0 : ℤ)) ≤ toLex p

/-- The anchored polyominoes with `n` cells, one per fixed polyomino. -/
def anchored (n : ℕ) : Set (Finset (ℤ × ℤ)) :=
  {s | s.card = n ∧ IsPolyomino s ∧ IsAnchored s}

/-- `A(n)`: the number of fixed polyominoes with `n` cells (OEIS A001168). -/
noncomputable def count (n : ℕ) : ℕ := (anchored n).ncard

/-- **Klarner's constant** `λ`, as `sup_n A(n)^{1/n}` over `n ≥ 1`.  Equal to
`lim A(n)^{1/n}` by `tendsto_klarner`. -/
noncomputable def klarner : ℝ := ⨆ n : ℕ, (count (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1))

/-! ## Known theorems, proof deferred -/

/-- Finitely many anchored polyominoes of each size: every cell lies within distance `n` of
the origin, so `anchored n` sits inside the finite powerset of a box.  Confidence 99%. -/
theorem anchored_finite (n : ℕ) : (anchored n).Finite := by sorry

/-- OEIS A001168 anchor: the monomino. -/
theorem count_one : count 1 = 1 := by sorry

/-- OEIS A001168 anchor: horizontal and vertical dominoes. -/
theorem count_two : count 2 = 2 := by sorry

/-- OEIS A001168 anchor: 2 straight + 4 bent trominoes. -/
theorem count_three : count 3 = 6 := by sorry

/-- OEIS A001168 anchor: the five free tetrominoes give 2 + 1 + 8 + 4 + 4 = 19 fixed. -/
theorem count_four : count 4 = 19 := by sorry

/-- OEIS A001168 anchor: the twelve free pentominoes give 63 fixed. -/
theorem count_five : count 5 = 63 := by sorry

theorem count_pos {n : ℕ} (hn : 0 < n) : 0 < count n := by sorry

/-- **Supermultiplicativity** (Klarner 1967; the argument shown in the Numberphile video).
English proof: given `P` with `m` cells and `Q` with `n` cells, translate `Q` so its
bottom-left cell (leftmost in the bottom row) sits immediately right of `P`'s top-right cell
(rightmost in the top row).  The union is a polyomino with `m + n` cells, and `P`, `Q` can be
recovered from it, so the map is injective.  Confidence 99%. -/
theorem count_mul_le (m n : ℕ) : count m * count n ≤ count (m + n) := by sorry

/-- An exponential upper bound, `A(n) ≤ Cⁿ`.  Eden (1961) gives `λ ≤ 27/4`; any `C` suffices
here.  Confidence 99%. -/
theorem exists_count_le_pow : ∃ C : ℝ, ∀ n, (count n : ℝ) ≤ C ^ n := by sorry

/-- **Klarner's theorem**: `A(n)^{1/n} → λ`.  English proof: `u n = -log A(n)` is subadditive
by `count_mul_le` and bounded below by `-n log C` by `exists_count_le_pow`, so mathlib's Fekete
lemma (`Subadditive.tendsto_lim`) gives convergence of `u n / n`; for a subadditive sequence the
limit is `inf u n / n`, which is `-log klarner`.  Confidence 99%. -/
theorem tendsto_klarner :
    Tendsto (fun n : ℕ => (count n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 klarner) := by sorry

/-! ## Literature inputs (cited, never axioms) -/

/-- **Barequet, Rote, Shalah**, *λ > 4: an improved lower bound on the growth constant of
polyominoes*, Comm. ACM (2016); EuroComb 2015.  Computer-assisted (twisted
cylinders, run 2013); they report `λ > 4.00253`, the computation reaching `4.002537727`. -/
def LowerBoundBRS2016 : Prop := (4.00253 : ℝ) < klarner

/-- **Vuong Bui**, *How to bound Klarner's constant without (a huge number of) Klarner–Rivest
twigs*, arXiv:2511.00461 (2025, rev. 2026): `λ ≤ 4.5238`, improving Barequet–Shalah 2022
(`4.5252`) and Klarner–Rivest 1973 (`4.649551`). -/
def UpperBoundBui2025 : Prop := klarner ≤ (4.5238 : ℝ)

/-- **Madras**, *A pattern theorem for lattice clusters*, arXiv:math/9902161 (1999):
the ratio limit `A(n+1)/A(n) → λ` exists. -/
def MadrasRatioLimit : Prop :=
  Tendsto (fun n : ℕ => (count (n + 1) : ℝ) / count n) atTop (𝓝 klarner)

/-- The two literature bounds pin the leading digit: `⌊λ⌋ = 4`. -/
theorem floor_klarner (hlo : LowerBoundBRS2016) (hhi : UpperBoundBui2025) :
    ⌊klarner⌋ = 4 := by
  unfold LowerBoundBRS2016 at hlo
  unfold UpperBoundBui2025 at hhi
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-! ## Open conjectures

No mechanism is known for any of these.  Not even irrationality of `λ` is proved, and the
only rigorous information is the bracket `(4.00253, 4.5238]`.

Known-false-sibling warning for any proposed mechanism: growth constants of lattice objects
can be **algebraic**.  The connective constant of self-avoiding walks on the honeycomb lattice
is `√(2 + √2)` (Duminil-Copin–Smirnov, Ann. of Math. 2012).  A transcendence argument must
therefore use something the honeycomb walk lacks; "it is a lattice growth constant" is not
enough. -/

/-- Open: `λ` is irrational. -/
def KlarnerIrrational : Prop := Irrational klarner

/-- Open: `λ` is transcendental over `ℚ`. -/
def KlarnerTranscendental : Prop := Transcendental ℚ klarner

/-- Open: the conjectured asymptotic `A(n) ~ C λⁿ / n`, i.e. the polynomial correction has
exponent `θ = 1`.  Numerically `C ≈ 0.3169` (series analysis; the value quoted in the Numberphile video).  Proving even the
exponent would be new; the Numberphile video states it as the hypothesis. -/
def KlarnerAsymptotic : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (count n : ℝ))
      (fun n : ℕ => C * klarner ^ n / n)

theorem KlarnerTranscendental.irrational (h : KlarnerTranscendental) : KlarnerIrrational :=
  Transcendental.irrational h

end LeanFormalizations.Polyomino
