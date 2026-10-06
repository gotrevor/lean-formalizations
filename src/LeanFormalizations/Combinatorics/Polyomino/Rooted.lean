/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Combinatorics.Polyomino.BridgeProfile

/-!
# Rooted log-concavity: `θ ≤ 1` as a monotonicity, and the polycube wall

`a(n) = n·A(n)` counts **rooted** fixed polyominoes (a polyomino with a marked cell).  If
`a` is log-concave from `n = 2` on, its ratios fall to their limit `λ`, so `a(n) ≥ a(2)λ^{n−2}`
and `A(n) ≥ cλⁿ/n`: the polynomial correction with exponent 1, and no bridges needed
(`polyLower_of_rootedLogConcave`).

## Relation to `BridgeMonotone`

`k(N−k)·B(N,k) = κ(N,k) · a(k) · a(N−k)`, with `κ` the Kramers gluing ratio of `KramersFlat`.
So `BridgeMonotone` is "rooted log-concavity, corrected by the drift of `κ`".  Pure rooted
log-concavity makes `a(k)a(N−k)` nondecreasing toward `N/2`; `κ` is nearly flat but not
monotone (it dips at `k = 4, 5` for `N = 20`).  `RootedLogConcave` is the Kramers-free core.

## Data (2026-10-06)

* 2D: the rooted ratios `a(n+1)/a(n)` fall at every step `2 ≤ n ≤ 69`, from 4.5 to 4.06322
  against `λ ≈ 4.06257`.  Source: OEIS A001168 b-file (Jensen's enumeration, extended by
  Barequet–Ben-Shachar 2024); our own enumerator agrees for `n ≤ 20`.  The plain ratios
  `A(n+1)/A(n)` rise on the same range (`BuiRatioMonotone`).  Together the two give the
  sandwich `λ·n/(n+1) ≤ A(n+1)/A(n) ≤ λ`.
* 3D, the known-false sibling: for fixed polycubes (OEIS A001931) the rooted ratios **rise**
  at every `n ≥ 2` up to 22 (7.5, 7.64, 7.76, …, 8.17).  This is what the believed exponent
  `θ₃ = 3/2` (Parisi–Sourlas dimensional reduction) predicts: `n·A₃(n) ≈ λ₃ⁿ n^{−1/2}`.  It
  already fails at `n = 3` (`not_polycubeRootedLogConcave`).

## What the sibling kills

Any **dimension-free** mechanism for `RootedLogConcave`, `BridgeMonotone` or
`MoveDensityDominance` proves a false statement about polycubes.  That covers a
cell-transfer injection `(k−1, k+1) → (k, k)` that does not use planarity, and local
leaf/spot density estimates fed into the switching identity, which holds verbatim in 3D.
A proof must use the plane (Maze row "Dimension-free mechanisms for θ ≤ 1").  The only known
planar handle on `θ = 1` is Brydges–Imbrie's dimensional reduction (Ann. Math. 2003), for
continuum branched polymers, not lattice animals.
-/

namespace LeanFormalizations.Polyomino

/-- **Rooted log-concavity**: `a(n) = n·A(n)` satisfies `a(n−1)·a(n+1) ≤ a(n)²` for `n ≥ 3`.
Open, new as a stated node (as far as we know).  Evidence: `rootedLogConcave_upTo_seventy`,
separated from the 3D sibling, which fails at every size.  Confidence 75%: asymptotically it
says `θ = 1` with a negative first correction, which the 70-term trend supports. -/
def RootedLogConcave : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ((n - 1) * count (n - 1)) * ((n + 1) * count (n + 1)) ≤ (n * count n) ^ 2

/-- Data: the inequality for every `3 ≤ n ≤ 69`, from the OEIS A001168 b-file (independent
enumerations to `n = 70`; ours agrees to `n = 20`).  Confidence 97%. -/
theorem rootedLogConcave_upTo_seventy (n : ℕ) (h3 : 3 ≤ n) (h : n ≤ 69) :
    ((n - 1) * count (n - 1)) * ((n + 1) * count (n + 1)) ≤ (n * count n) ^ 2 := by sorry

/-- English proof: for `n ≥ 2` the ratios `s(n) = a(n+1)/a(n)` are nonincreasing, so they
converge to `s = inf s(n)`, and `a(n)^{1/n} → s` as well.  Since `n^{1/n} → 1`,
`tendsto_klarner` gives `s = λ`.  Each `s(n) ≥ λ`, so for every `n ≥ 2`,
`n·A(n) ≥ 2·A(2)·λ^{n−2}`, i.e. `A(n) ≥ (4/λ²)·λⁿ/n`; `n = 1` is checked directly.  Exponent
`K = 1`.  Confidence 97%. -/
theorem polyLower_of_rootedLogConcave (h : RootedLogConcave) : PolyLowerCorrection := by sorry

/-- The ratio sandwich.  English proof: the lower bound is `s(n) ≥ λ` from the previous
proof, rewritten as `A(n+1)/A(n) ≥ λ·n/(n+1)`.  The upper bound comes from
`BuiRatioMonotone`, whose ratios increase to their limit `λ`.  Confidence 95%. -/
theorem ratio_sandwich (h : RootedLogConcave) (hb : BuiRatioMonotone) (n : ℕ) (hn : 2 ≤ n) :
    klarner * n / (n + 1) ≤ (count (n + 1) : ℝ) / count n ∧
      (count (n + 1) : ℝ) / count n ≤ klarner := by sorry

/-! ## The known-false sibling: polycubes -/

/-- The cubic grid: cells of `ℤ³` are adjacent when they share a face. -/
def cubeGraph : SimpleGraph (ℤ × ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2.1 - q.2.1| + |p.2.2 - q.2.2| = 1
  symm := ⟨fun p q h => by rwa [abs_sub_comm q.1, abs_sub_comm q.2.1, abs_sub_comm q.2.2]⟩
  loopless := ⟨fun p h => by simp at h⟩

/-- `A₃(n)`: fixed polycubes with `n` cells (OEIS A001931), each translation class
represented by its member whose lexicographically least cell is the origin. -/
noncomputable def polycubeCount (n : ℕ) : ℕ :=
  {s : Finset (ℤ × ℤ × ℤ) | s.card = n ∧
    (SimpleGraph.induce (s : Set (ℤ × ℤ × ℤ)) cubeGraph).Connected ∧ ((0, 0, 0)) ∈ s ∧
    ∀ p ∈ s, toLex ((0 : ℤ), toLex ((0 : ℤ), (0 : ℤ))) ≤ toLex (p.1, toLex p.2)}.ncard

/-- Hand count: a dicube points along one of three axes. -/
theorem polycubeCount_two : polycubeCount 2 = 3 := by sorry

/-- Hand count: three straight tricubes, and an L-tricube in each of the 3 coordinate planes
in 4 orientations. -/
theorem polycubeCount_three : polycubeCount 3 = 15 := by sorry

/-- OEIS A001931.  Confidence 99%. -/
theorem polycubeCount_four : polycubeCount 4 = 86 := by sorry

/-- `RootedLogConcave` for polycubes. -/
def PolycubeRootedLogConcave : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ((n - 1) * polycubeCount (n - 1)) * ((n + 1) * polycubeCount (n + 1)) ≤
      (n * polycubeCount n) ^ 2

/-- **The 3D sibling is not rooted log-concave**: `6 · 344 = 2064 > 2025 = 45²` at `n = 3`.
The rooted ratios keep rising through `n = 22` (OEIS A001931), as `θ₃ = 3/2` predicts. -/
theorem not_polycubeRootedLogConcave : ¬ PolycubeRootedLogConcave := by
  intro h
  have := h 3 le_rfl
  rw [show 3 - 1 = 2 from rfl, polycubeCount_two, polycubeCount_three, polycubeCount_four]
    at this
  norm_num at this

end LeanFormalizations.Polyomino
