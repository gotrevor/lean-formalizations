/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Erdos385
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385: the conjecture graph's open nodes and obstruction edges

Every conclusion of `PROBE-`, `LIT-` and `DOOR-*-ERDOS-385.md` that is not an elementary
theorem lives here as a `def … : Prop` node (a claim about a *statement*, never a truth value) or
as a wiring edge between nodes.  `ROADMAP-ERDOS-385.md` draws the graph.

## Nodes

* `NoCarrier n h`: every composite in `[n − h, n)` has least prime factor `≤ h`.  Bad `n` has
  `NoCarrier n h` at every scale (`noCarrier_of_bad`).
* `CrossScaleRepulsion`: Tao's "repulsion" loophole.  An empty scale `h ∈ [log n, √n]` forces a
  carrier at a larger scale.  Door 3; the data (`DOOR-EXCEPTIONAL` Part B) show no signal (85%):
  the joint failure across scales is 23× the product of the marginals, the conspiracy direction.
* `SieveOnlySibling`: the known-false sibling.  One class per prime `≤ h` covers an *arbitrary*
  interval of length `h`.  This is TRUE given FGKMT (`sieveOnlySibling_of_FGKMT`), so an argument
  for #385 that uses only sieve axioms (arbitrary location, arbitrary classes) would refute a true
  statement: it must use that the classes are `0 mod p` at the specific location `n`.
* `BadCountExpBound`: `DOOR-EXCEPTIONAL` A2, `#{bad n ≤ X} ≪_ε X exp(−(log X)^{1/2−ε})`.  Paper
  outline only (75% that it closes); no Lean route planned (needs the large sieve and McDiarmid).
* `AlmostAllF385`: `DOOR-ALMOSTALL`'s headline, `F(n) ≥ n + (1 − δ)√n` for almost all `n`.  The
  phase-E3 target, from four literature Props (to be stated when E3 is planted; see the roadmap).

## Frozen edges (prove them)

* `noCarrier_of_bad`, `eventually_not_bad_of_crossScaleRepulsion`, `sieveOnlySibling_of_FGKMT`.

The Siegel-zero obstruction is `Literature.Granville2022Cor1` (hypothesis
`Literature.SiegelZerosInfinitelyOften`, conclusion `Literature.OneScaleSieveEnemy`); it has no
edge into #385, which is the point (`LIT-ERDOS-385.md` §3: one scale at a time).
-/

namespace LeanFormalizations.Erdos385

open Filter Real LeanFormalizations.Literature

/-- No composite in `[n − h, n)` has least prime factor `> h`. -/
def NoCarrier (n h : ℕ) : Prop :=
  ∀ m, n - h ≤ m → m < n → Composite m → m.minFac ≤ h

/-- **Tao's repulsion loophole** (door 3, open, no signal in the data). -/
def CrossScaleRepulsion : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ h : ℕ, Real.log n ≤ h → h * h ≤ n → NoCarrier n h →
    ∃ h', h < h' ∧ h' * h' ≤ n ∧ ¬ NoCarrier n h'

/-- **The known-false sibling, which is true.**  For every large `h`, one residue class per
prime `p ≤ h` covers `{1, …, h}`. -/
def SieveOnlySibling : Prop :=
  ∀ᶠ h : ℕ in atTop, ∃ a : ℕ → ℤ, ∀ t : ℕ, 1 ≤ t → t ≤ h →
    ∃ p, p.Prime ∧ p ≤ h ∧ (t : ℤ) ≡ a p [ZMOD p]

/-- `DOOR-EXCEPTIONAL` A2 (paper only, 75%). -/
def BadCountExpBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, ∀ X : ℕ, 3 ≤ X →
    ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
      ≤ C * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε))

/-- `DOOR-ALMOSTALL` headline (phase E3): for each `δ ∈ (0, 1/4)`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} = o(X)`. -/
def AlmostAllF385 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
    Tendsto (fun X : ℕ => ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) / X)
      atTop (nhds 0)

theorem noCarrier_of_bad {n : ℕ} (hn : 5 ≤ n) (h : Bad n) (k : ℕ) : NoCarrier n k := by
  sorry

/-- **Edge: repulsion ⇒ #385(i).** -/
theorem eventually_not_bad_of_crossScaleRepulsion (h : CrossScaleRepulsion) :
    ∀ᶠ n : ℕ in atTop, ¬ Bad n := by
  sorry

/-- **Edge: FGKMT ⇒ the sieve-only sibling.**  `Y(x) ≫ x log x log₃ x / log₂ x ≥ x` eventually. -/
theorem sieveOnlySibling_of_FGKMT (h : FGKMT2018Eq12) : SieveOnlySibling := by
  sorry

end LeanFormalizations.Erdos385
