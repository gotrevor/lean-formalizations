/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving
import LeanFormalizations.NumberTheory.Erdos385.Hyperbola
import LeanFormalizations.NumberTheory.Erdos385.Erdos463

/-!
# Erdős #385 / #463: what is left, stated (phase E10)

After E7–E9 the open parts of #385, #430 and #463 are all-`n` statements.  This file records the
remainder in two forms.

* `almost_all_erdos463_powerSaving`: #463 off a set of size `≪ X^{1−c}` (E9's power saving with
  E6's shifted witness window).  Route: copy `almost_all_erdos463` (E6, `card_shift_le`,
  `coeffA_ne_zero_witness`, coefficient `δ = 1/8`) onto the E9 pipeline
  (`almost_all_of_badWindowPowerSaving`, `badWindowPowerSaving_of_lit`): the shifted window moves
  the `x`-range by `≍ δ√Z`, inside the slack of the far/near split.  85%.
* **One conjecture for all four all-`n` statements.**  `PrimePairsDownMargin f` (prime pairs
  `pq < n < pq + p − f(n)`) gives #385(ii) (`erdos385_ii_of_downMargin`), and with `f = 0` it is
  `HyperbolaPrimePairs` (so #385(i), #430).  `PrimePairsUpMargin f` (prime pairs
  `n + f(n) < pq < n + p`) gives #463 (`erdos463_of_upMargin`).  Both conjectures are binary
  problems near `p ≈ √n` (Maze rows anchored at `HyperbolaPrimePairs` and
  `good_iff_exists_prime_floor`).  The edges are elementary.

* **One conjecture behind Goldbach and all of the above: `GoldbachWindow`.**  Every large even
  `N` is `p + q` with the gap `q − p` in any prescribed window `[a√N, b√N]`, `0 ≤ a < b ≤ 3`
  (expected count `≍ (b − a)√N/log² N`).  It gives Goldbach for large `N`
  (`goldbach_of_goldbachWindow`) and, because near `p ≈ √n` the strip `pq ≈ n` is the line
  `p + q = N` with `(q − p)² ≈ N² − 4n`, every all-`n` statement here:
  `hyperbolaPrimePairs_of_goldbachWindow` (#385(i), #430), `ees_of_goldbachWindow` (the all-`n`
  Erdős–Eggleton–Selfridge form for each `e > 0`, hence `F(n) − n → ∞`), and
  `erdos463_of_goldbachWindow`.  Route for the three: given `n`, take the least even
  `N = 2√n + 2t` with `t` in a fixed range; then `pq = N²/4 − (q−p)²/4`, so the condition on
  `n − pq` is a window for `q − p` of length `≍ √N` at position `≍ √(t)√N` (higher-order terms are
  `O(n^{−1/4})`).  75% each.  The shared obstruction is the binary barrier: the main term and the
  Parseval mass of the error have the same size, so a proof needs phase cancellation in a
  two-prime sum (Maze rows anchored at `HyperbolaPrimePairs` and `good_iff_exists_prime_floor`).
  `GoldbachWindow` is stronger than Goldbach (one `N`, one window), so it is a convenient single
  hypothesis, not the weakest one; the conceptual unifier is "prime pairs equidistribute in every
  strip of width `≥ 1` around a smooth curve of length `≍ N`" (the line `p + q = N` for Goldbach,
  the hyperbola `pq = n` for #385).  Evidence (`scripts/goldbach-window-probe.py`, `N ≤ 2·10^6`):
  the window `[0, 3]` last fails at `N = 362534` (heuristic count `≈ 15` at the top); windows of
  width `1` still fail occasionally (heuristic count `≈ 5`), as a Poisson model predicts at this
  height.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Filter LeanFormalizations.Literature

/-- **#463 with a power saving**: off `≪ X^{1−c}` exceptions, a composite `m` with
`n + δ√n < m < n + p(m)` exists. -/
theorem almost_all_erdos463_powerSaving (h1 : RichertZetaGrowth) (h2 : NearOneZeroDensity)
    (h3 : ShortIntervalPrimesLower) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c C : ℝ, 0 < c ∧ ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ ¬ ∃ m : ℕ, Composite m ∧
        (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac}.ncard : ℝ) ≤ C * (X : ℝ) ^ (1 - c) := by
  sorry

/-- Prime pairs below `n` reaching past `n + f(n)`: `pq < n` and `n + f(n) < pq + p`. -/
def PrimePairsDownMargin (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧
    p * q < n ∧ (n : ℝ) + f n < ((p * q + p : ℕ) : ℝ)

/-- Prime pairs just above `n`: `n + f(n) < pq < n + p`. -/
def PrimePairsUpMargin (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧
    (n : ℝ) + f n < ((p * q : ℕ) : ℝ) ∧ p * q < n + p

/-- The least prime factor of a product of primes `p < q` is `p`. -/
theorem minFac_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).minFac = p := by
  have hne : p * q ≠ 1 := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have hle : (p * q).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  have hpr := Nat.minFac_prime hne
  rcases (Nat.Prime.dvd_mul hpr).1 (Nat.minFac_dvd _) with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hpr hp).1 h
  · have := (Nat.prime_dvd_prime_iff_eq hpr hq).1 h; omega

/-- A product of primes `p < q` is composite. -/
theorem composite_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Composite (p * q) := by
  refine ⟨by have := hp.two_le; have := hq.two_le; nlinarith, fun h => ?_⟩
  exact Nat.not_prime_mul hp.ne_one hq.ne_one h

/-- Edge: a down-margin tending to infinity gives #385(ii), `F(n) − n → ∞`. -/
theorem erdos385_ii_of_downMargin {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    (h : PrimePairsDownMargin f) : Tendsto (fun n : ℕ => (F n : ℝ) - n) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ hf
  filter_upwards [h] with n ⟨p, q, hp, hq, hpq, h1, h2⟩
  have hF := add_minFac_le_F h1 (composite_mul_primes hp hq)
  rw [minFac_mul_primes hp hq hpq] at hF
  have : ((p * q + p : ℕ) : ℝ) ≤ F n := by exact_mod_cast hF
  linarith

/-- Edge: an up-margin tending to infinity gives #463 (formal-conjectures shape, real `f`). -/
theorem erdos463_of_upMargin {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    (h : PrimePairsUpMargin f) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, Composite m ∧ (n : ℝ) + f n < m ∧ m < n + m.minFac := by
  filter_upwards [h] with n ⟨p, q, hp, hq, hpq, h1, h2⟩
  exact ⟨p * q, composite_mul_primes hp hq, h1, by rw [minFac_mul_primes hp hq hpq]; exact h2⟩

/-- Edge: the zero margin is `HyperbolaPrimePairs`. -/
theorem hyperbolaPrimePairs_of_downMargin_zero (h : PrimePairsDownMargin 0) :
    HyperbolaPrimePairs := by
  filter_upwards [h] with n ⟨p, q, hp, hq, hpq, h1, h2⟩
  refine ⟨p, q, hp, hq, hpq, h1, ?_⟩
  have : (n : ℝ) < ((p * q + p : ℕ) : ℝ) := by simpa using h2
  exact_mod_cast this

/-- **Goldbach in a gap window** (open; implies binary Goldbach for large `N`): for fixed
`0 ≤ a < b ≤ 3`, every large even `N` is `p + q` with `a√N ≤ q − p ≤ b√N`. -/
def GoldbachWindow : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 3 → ∀ᶠ N : ℕ in atTop, Even N →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N ∧ p ≤ q ∧
      a * Real.sqrt N ≤ (q : ℝ) - p ∧ (q : ℝ) - p ≤ b * Real.sqrt N

/-- Edge: `GoldbachWindow` gives Goldbach for all large even `N`. -/
theorem goldbach_of_goldbachWindow (h : GoldbachWindow) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  filter_upwards [h 0 1 le_rfl one_pos (by norm_num)] with N hN hev
  obtain ⟨p, q, hp, hq, hs, -⟩ := hN hev
  exact ⟨p, q, hp, hq, hs⟩

/-- Edge: `GoldbachWindow` gives prime pairs on the hyperbolic strip (#385(i), #430). -/
theorem hyperbolaPrimePairs_of_goldbachWindow (h : GoldbachWindow) : HyperbolaPrimePairs := by
  sorry

/-- Edge: `GoldbachWindow` gives the all-`n` Erdős–Eggleton–Selfridge bound for each `e > 0`
(formal-conjectures `erdos_385.variants.lb`, eventually). -/
theorem ees_of_goldbachWindow (h : GoldbachWindow) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + (1 - e) * Real.sqrt n ≤ F n := by
  sorry

/-- Edge: `GoldbachWindow` gives #463. -/
theorem erdos463_of_goldbachWindow (h : GoldbachWindow) :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, Composite m ∧ (n : ℝ) + f n < m ∧ m < n + m.minFac := by
  sorry

end LeanFormalizations.Erdos385
