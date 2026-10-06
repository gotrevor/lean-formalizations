/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Combinatorics.Polyomino.LowerCorrection

/-!
# The bridge profile: how many polyominoes split `k + (N − k)` along one edge?

`G(N, k)` (`bridgeSplitCount N k`) counts fixed `N`-cell polyominoes having a bridge (one grid
adjacency whose removal disconnects them) with exactly `k` cells on one side.  The halving
count is the middle column, `H(2m) = G(2m, m)` (`halvableCount_eq_bridgeSplitCount`).

## What the enumeration shows (`scripts/polyomino-halving profile`, N ≤ 20, 2026-10-06)

* `G(N, k)/A(N)` falls smoothly from `≈ 1` at `k = 1` to `≈ 0.47` at `k = N/2` (N = 18:
  1.000, 0.957, 0.898, 0.842, 0.798, 0.761, 0.739, 0.696, 0.467).  For fixed `k` it rises with
  `N`, as the pattern theorem predicts (a pendant `k`-cell piece is a local pattern).
* Each step `k → k+1` loses little, and the loss concentrates at **both ends**: the fit
  `G(N,k+1) ≥ ((k/(k+1)) · ((N−2k)/(N−2k+2)))^K · G(N,k)` holds with `K ≤ 0.504` on every
  step for even `N ≤ 20`.  Away from the last step `K ≤ 0.152`; the last step into the exact
  half (a symmetry crowding) has `K` = 0.357, 0.406, 0.441, 0.464, 0.480, 0.493, 0.504 for
  N = 8..20, increments shrinking (0.049 → 0.011).
* `κ(k, N−k) = B(N,k) / (A(k) A(N−k))`, the number of single-contact gluings per pair of
  pieces (`B` counts bridges), is nearly **independent of `k`** for `k ≥ 3` and grows linearly
  in `N` (≈ 14.6 for every `3 ≤ k ≤ 8` at N = 18; half that at `k = N/2`, the ordered-pair
  factor; ≈ 15.6 for `4 ≤ k ≤ 9` at N = 20).  Bridges have linear density, ≈ 0.79 per cell.

## The chain

```
PendantFraction ∧ ProfileStep ⟹ HalvingFractionPoly ⟹ DoublingReverse ⟹ PolyLowerCorrection
```

`ProfileStep`'s two factors telescope exactly: `∏ k/(k+1) = 1/m` and
`∏ (N−2k)/(N−2k+2) = 2/N`, so `G(2m, m) ≥ G(2m, 1) · (2/(mN))^K`.

## Circularity check (the lesson of `polyLower_iff_doublingReverse`)

`ProfileStep` is a statement about the **shape of a typical polyomino**, not about the
growth of `A`; it does not follow from `PolyLowerCorrection` in any evident way.  The tempting
gluing-side reading does not help: `H(2m) = 4m² V A(m)²` with `V` the single-contact success
rate of random root-to-root gluings, and any lower bound on `H` routed through `V` needs
`A(2m) ≤ poly · A(m)²` again (Maze row "gluing-side lower bounds on the halving count").

## Mechanism for `ProfileStep` (proposed, unproved)

**Switching.**  Move one leaf cell of the large side to a free single-contact spot on the
small side: `k`-splits become `(k+1)`-splits.  Double counting the moves gives the exact
identity `G(N,k) · E_k[out] = G(N,k+1) · E_{k+1}[in]`, so the step ratio is a ratio of
expectations, with no concentration needed.  Out-degree ≈ (leaves of the large side) ×
(spots on the small side), in-degree ≈ (leaves of the small side) × (spots on the large side),
which gives the shape `(1 − O(1/k))(1 + O(1/(N−k)))`.  **Missing input:** leaf and spot
densities of the two ensembles agree to relative error `O(1/k + 1/(N−2k))`, i.e. a rate in the
pattern theorem.  No such rate is known.

**Sibling test (random trees).**  For uniform random trees the number of `k`-subtrees is
`≈ N k^{−3/2}`, so the halving fraction decays like `N^{−1/2}` and the step bound holds with
`K = 3/2`.  The mechanism therefore does not prove anything false there, and it shows that a
*constant* halving fraction is model-dependent (`HalvingFractionConst` is false for trees).
-/

namespace LeanFormalizations.Polyomino

/-- `s` splits along one edge into a `k`-cell and an `l`-cell polyomino: the disjoint union
of two polyominoes joined by exactly one grid adjacency. -/
def IsBridgeSplit (k l : ℕ) (s : Finset (ℤ × ℤ)) : Prop :=
  ∃ t u : Finset (ℤ × ℤ), Disjoint t u ∧ t ∪ u = s ∧ t.card = k ∧ u.card = l ∧
    IsPolyomino t ∧ IsPolyomino u ∧
    ∃! e : (ℤ × ℤ) × (ℤ × ℤ), e.1 ∈ t ∧ e.2 ∈ u ∧ gridGraph.Adj e.1 e.2

/-- `G(N, k)`: fixed `N`-cell polyominoes with a bridge cutting off exactly `k` cells. -/
noncomputable def bridgeSplitCount (N k : ℕ) : ℕ :=
  {s : Finset (ℤ × ℤ) | IsBridgeSplit k (N - k) s ∧ IsAnchored s}.ncard

theorem isHalvable_iff_isBridgeSplit (m : ℕ) (s : Finset (ℤ × ℤ)) :
    IsHalvable m s ↔ IsBridgeSplit m m s := Iff.rfl

theorem halvableCount_eq_bridgeSplitCount (m : ℕ) :
    halvableCount m = bridgeSplitCount (2 * m) m := by
  unfold halvableCount bridgeSplitCount
  rw [two_mul, Nat.add_sub_cancel]
  rfl

/-! ## Anchors and data -/

/-- Hand count: all 6 trominoes are paths of 3 cells, and each has a `1 + 2` bridge. -/
theorem bridgeSplitCount_three_one : bridgeSplitCount 3 1 = 6 := by sorry

/-- Hand count: every tetromino except the square O has a leaf cell. -/
theorem bridgeSplitCount_four_one : bridgeSplitCount 4 1 = 18 := by sorry

/-- The `N = 18` column `G(18, 1), …, G(18, 9)` from the enumeration (validated against
OEIS A001168 and the hand anchors).  Confidence 97%. -/
theorem bridgeSplitCount_eighteen :
    (List.range 9).map (fun k => bridgeSplitCount 18 (k + 1)) =
      [1540509728, 1475090026, 1383554696, 1296993764, 1228902084, 1172734362, 1139117794,
        1072893252, 719106076] := by sorry

/-- The `N = 20` column `G(20, 1), …, G(20, 10)`; its last entry is `halvableCount_ten`.
Confidence 97%. -/
theorem bridgeSplitCount_twenty :
    (List.range 10).map (fun k => bridgeSplitCount 20 (k + 1)) =
      [22962163113, 22141723665, 20848582643, 19558090380, 18501518736, 17664467900,
        17038985604, 16567649714, 15592154426, 10429014774] := by sorry

/-! ## The nodes -/

/-- **A constant fraction of polyominoes have a leaf cell** (a bridge cutting off one cell).
Believed (confidence 90%): a leaf is a local pattern, and Madras's pattern theorem (1999)
makes polyominoes without it exponentially rare, so `G(N,1)/A(N) → 1`.  Data: `≥ 0.996` for
every `N ≥ 8`. -/
def PendantFraction : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * count N ≤ bridgeSplitCount N 1

/-- Open, new: **the bridge profile decays at most polynomially from both ends.**
Data: holds with `K = 0.504` for every step at even `N ≤ 20`; mechanism proposed
(switching, see the module docstring), missing input a rate in the pattern theorem.
Confidence 65%. -/
def ProfileStep : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N k : ℕ, 1 ≤ k → 2 * k < N →
    ((k : ℝ) / (k + 1) * ((N - 2 * k : ℝ) / (N - 2 * k + 2))) ^ K * bridgeSplitCount N k
      ≤ bridgeSplitCount N (k + 1)

/-- The chain's new link.  English proof: telescope `ProfileStep` over `k = 1, …, m − 1` at
`N = 2m`; the products are `1/m` and `2/N`, so `H(2m) = G(2m, m) ≥ (1/m²)^K G(2m, 1)
≥ c m^{−2K} A(2m)` by `PendantFraction`.  Confidence 95%. -/
theorem halvingFractionPoly_of_profileStep (hp : PendantFraction) (hs : ProfileStep) :
    HalvingFractionPoly := by sorry

theorem polyLower_of_profileStep (hp : PendantFraction) (hs : ProfileStep) :
    PolyLowerCorrection :=
  polyLower_of_halvingFractionPoly (halvingFractionPoly_of_profileStep hp hs)

/-! ## Single-contact gluing pins `H(2m)` to `A(m)²` (2026-10-06)

`A(m)² ≤ H(2m) ≤ 4m² A(m)²`.  Consequence: `HalvingFractionPoly ↔ PolyLowerCorrection`, so the
halving fraction is no weaker a premise than exact halving.  Of the polyomino nodes, only
`ProfileStep` is not known to be equivalent to the conclusion. -/

/-- **Single-contact gluing**: `A(m)² ≤ H(2m)`.  English proof: for polyominoes `P`, `Q` with
`m` cells, let `p` be the top cell of `P`'s rightmost column (column `c`) and `q` the bottom
cell of `Q`'s leftmost column; translate `Q` so `q = p + (1, 0)`.  `P` lies in columns `≤ c`,
`Q` in columns `≥ c + 1`, and a contact needs a `P`-cell in column `c` and a `Q`-cell in column
`c + 1` in the same row; `P`'s are at rows `≤ row p` and `Q`'s at rows `≥ row p`, so `p–q` is
the only contact.  The union halves along that edge, its halving split is unique
(`isHalvable_unique`), and the left half is `P`, so `(P, Q) ↦ P ∪ Q` is injective.  This is
the video's gluing argument made single-contact.  Confidence 95%. -/
theorem sq_count_le_halvableCount (m : ℕ) : count m ^ 2 ≤ halvableCount m := by sorry

/-- English proof: `A(2m) ≤ C m^K A(m)² ≤ C m^K H(2m)` by `sq_count_le_halvableCount`.
Confidence 98%. -/
theorem halvingFractionPoly_of_doublingReverse (h : DoublingReverse) : HalvingFractionPoly := by
  sorry

/-- **The halving fraction is equivalent to the polynomial correction.** -/
theorem halvingFractionPoly_iff_polyLower : HalvingFractionPoly ↔ PolyLowerCorrection :=
  ⟨polyLower_of_halvingFractionPoly,
    fun h => halvingFractionPoly_of_doublingReverse (doublingReverse_of_polyLower h)⟩

/-! ## The flat gluing count: a generalised Kramers relation -/

/-- `B(N, k)`: pairs (anchored `N`-cell polyomino `s`, side `t`) where `t` is one side of a
bridge of `s` and has `k` cells.  For `2k < N` this counts bridges whose smaller side has `k`
cells; at `2k = N` each halving bridge is counted twice, once per side. -/
noncomputable def bridgeCount (N k : ℕ) : ℕ :=
  {p : Finset (ℤ × ℤ) × Finset (ℤ × ℤ) | IsAnchored p.1 ∧ p.1.card = N ∧ p.2 ⊆ p.1 ∧
    p.2.card = k ∧ IsPolyomino p.2 ∧ IsPolyomino (p.1 \ p.2) ∧
    ∃! e : (ℤ × ℤ) × (ℤ × ℤ), e.1 ∈ p.2 ∧ e.2 ∈ p.1 \ p.2 ∧ gridGraph.Adj e.1 e.2}.ncard

/-- Open: **the single-contact gluing count `κ(N, k) = B(N,k)/(A(k)A(N−k))` is flat in `k`**
(up to a constant, for `3 ≤ k < N/2`).  Evidence: at `N = 20`, `κ` = 15.74, 15.56, 15.56,
15.60, 15.64, 15.67, 15.70 for `k = 3..9`; at `N = 18`, 14.53–14.68 for `k = 3..8`.  This is
the polyomino form of the **generalised Kramers relation** that Rosa–Everaers (arXiv:1610.05230)
observe numerically for interacting lattice trees; for ideal trees the Kramers theorem makes
the branch-weight law exactly `Z_n Z_{N−1−n}`-proportional.  So this observation is prior art
in genre; it is recorded because it is the polyomino instance.  Confidence 75%. -/
def KramersFlat : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N k k' : ℕ, 3 ≤ k → 3 ≤ k' → 2 * k < N → 2 * k' < N →
    c * ((bridgeCount N k : ℝ) / (count k * count (N - k))) ≤
      (bridgeCount N k' : ℝ) / (count k' * count (N - k'))

end LeanFormalizations.Polyomino
