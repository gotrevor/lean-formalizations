/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving
import LeanFormalizations.NumberTheory.Erdos385.Hyperbola
import LeanFormalizations.NumberTheory.Erdos385.Erdos463
import LeanFormalizations.NumberTheory.Erdos385.Remainder.Erdos463Power

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
        (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac}.ncard : ℝ) ≤ C * (X : ℝ) ^ (1 - c) :=
  almost_all_of_windowPowerSaving (δ := 1 / 16) (by norm_num) (by norm_num) (NoWitness463 δ)
    (erdos463_windowPowerSaving (longAveragePower_of_lit h3 (by norm_num) (by norm_num))
      (differenceSplit_of_lit h1 h2 (by norm_num) (by norm_num)) hδ hδ')

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

/-- Integer core of the window reduction: with `N = 2p + d`, the conditions `N² < 4n + d²` and
`4n + d² < N² + 4p` put `p(p+d)` on the strip below `n`. -/
theorem strip_of_gap {n p d : ℕ} (h1 : (2 * p + d) ^ 2 < 4 * n + d ^ 2)
    (h2 : 4 * n + d ^ 2 < (2 * p + d) ^ 2 + 4 * p) :
    p * (p + d) < n ∧ n < p * (p + d) + p := by
  constructor <;> nlinarith

/-- Squaring a lower window bound `√a·√N ≤ x`. -/
theorem sq_le_of_sqrt_mul_le {a N x : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N)
    (h : Real.sqrt a * Real.sqrt N ≤ x) : a * N ≤ x ^ 2 := by
  have h0 : 0 ≤ Real.sqrt a * Real.sqrt N := by positivity
  have := mul_self_le_mul_self h0 h
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hN]

/-- Squaring an upper window bound `0 ≤ x ≤ √b·√N`. -/
theorem sq_le_of_le_sqrt_mul {b N x : ℝ} (hb : 0 ≤ b) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (h : x ≤ Real.sqrt b * Real.sqrt N) : x ^ 2 ≤ b * N := by
  have := mul_self_le_mul_self hx h
  nlinarith [Real.sq_sqrt hb, Real.sq_sqrt hN]

/-- One window, in integers: `GoldbachWindow` at `a² = (j+5)/2`, `b² = (j+7)/2` gives, for each
large `m`, primes `p ≤ q`, `p + q = 2m`, with `(j+5)m ≤ (q−p)² ≤ (j+7)m`. -/
theorem goldbachWindow_int (h : GoldbachWindow) (j : ℕ) (hj : j < 8) :
    ∀ᶠ m : ℕ in atTop, ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ 2 * p + d = 2 * m ∧
      (j + 5) * m ≤ d ^ 2 ∧ d ^ 2 ≤ (j + 7) * m := by
  have hjR : (j : ℝ) ≤ 7 := by exact_mod_cast (by omega : j ≤ 7)
  have hab : Real.sqrt (((j : ℝ) + 5) / 2) < Real.sqrt (((j : ℝ) + 7) / 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hb3 : Real.sqrt (((j : ℝ) + 7) / 2) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hW := h _ _ (Real.sqrt_nonneg _) hab hb3
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  filter_upwards [h2.eventually hW] with m hm
  obtain ⟨p, q, hp, hq, hs, hpq, hlo, hhi⟩ := hm (even_two_mul m)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  refine ⟨p, d, hp, hq, by omega, ?_, ?_⟩
  · have hc : ((p + d : ℕ) : ℝ) - p = d := by push_cast; ring
    rw [hc] at hlo
    have := sq_le_of_sqrt_mul_le (by positivity) (by positivity) hlo
    push_cast at this
    have : (((j + 5) * m : ℕ) : ℝ) ≤ ((d ^ 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have hc : ((p + d : ℕ) : ℝ) - p = d := by push_cast; ring
    rw [hc] at hhi
    have := sq_le_of_le_sqrt_mul (by positivity) (by positivity) (by positivity) hhi
    push_cast at this
    have : ((d ^ 2 : ℕ) : ℝ) ≤ (((j + 7) * m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- Edge: `GoldbachWindow` gives prime pairs on the hyperbolic strip (#385(i), #430). -/
theorem hyperbolaPrimePairs_of_goldbachWindow (h : GoldbachWindow) : HyperbolaPrimePairs := by
  have hall : ∀ᶠ m : ℕ in atTop, ∀ j : Fin 8, ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧
      2 * p + d = 2 * m ∧ (j + 5) * m ≤ d ^ 2 ∧ d ^ 2 ≤ (j + 7) * m :=
    eventually_all.2 fun j => goldbachWindow_int h j j.2
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hall
  refine eventually_atTop.2 ⟨(M0 + 57) ^ 2, fun n hn => ?_⟩
  have hex : ∃ m, n + m ≤ m ^ 2 := ⟨n + 1, by nlinarith⟩
  set m := Nat.find hex with hmdef
  have hm : n + m ≤ m ^ 2 := Nat.find_spec hex
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; have : 0 < (M0 + 57) ^ 2 := by positivity
      simp at hm; omega
    · exact h0
  have hmin : ¬ n + (m - 1) ≤ (m - 1) ^ 2 := Nat.find_min hex (by omega)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hm'] at hmin; simp only [Nat.add_sub_cancel] at hmin
  have hmbig : M0 + 57 ≤ m := by
    by_contra hc; push Not at hc
    have : m ^ 2 < (M0 + 57) ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
    omega
  obtain ⟨e, he⟩ : ∃ e, e = m ^ 2 - n := ⟨_, rfl⟩
  have he1 : m ≤ e := by omega
  have he2 : e + 2 < 3 * m := by
    have : m ^ 2 = m' ^ 2 + 2 * m' + 1 := by rw [hm']; ring
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = 4 * e / m := ⟨_, rfl⟩
  have ht1 : t * m ≤ 4 * e := by rw [ht]; exact Nat.div_mul_le_self _ _
  have ht2 : 4 * e < (t + 1) * m := by
    have := Nat.lt_div_mul_add (a := 4 * e) hm0; rw [← ht] at this; linarith
  have ht4 : 4 ≤ t := ht ▸ (Nat.le_div_iff_mul_le hm0).2 (by linarith)
  have ht11 : t < 12 := ht ▸ (Nat.div_lt_iff_lt_mul hm0).2 (by linarith)
  obtain ⟨p, d, hp, hq, hs, hlo, hhi⟩ := hM0 m (by omega) ⟨t - 4, by omega⟩
  have hj5 : (t - 4 + 5) * m = t * m + m := by
    rw [show t - 4 + 5 = t + 1 by omega]; ring
  have hj7 : (t - 4 + 7) * m = t * m + 3 * m := by
    rw [show t - 4 + 7 = t + 3 by omega]; ring
  have hd : 2 * d < m := by
    by_contra hc; push Not at hc
    have h1 : m * m ≤ 4 * d ^ 2 := by
      have := Nat.mul_le_mul hc hc; rw [show 2 * d * (2 * d) = 4 * d ^ 2 by ring] at this; exact this
    have h2 : t * m ≤ 11 * m := Nat.mul_le_mul_right _ (by omega)
    have h3 : 57 * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
    rw [hj7] at hhi
    linarith
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0] at hlo; nlinarith
    · exact h0
  have hN : (2 * p + d) ^ 2 = 4 * n + 4 * e := by rw [hs, show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
  obtain ⟨h1, h2⟩ := strip_of_gap (n := n) (p := p) (d := d) (by rw [hN]; rw [hj5] at hlo; linarith)
    (by rw [hN]; rw [hj7] at hhi; linarith)
  exact ⟨p, p + d, hp, hq, by omega, h1, h2⟩

/-- Window `i` of mesh `1/K`, in integers: `GoldbachWindow` at `a² = i/(2K)`, `b² = (i+1)/(2K)`
gives, for each large `m`, primes `p, p + d` with `2p + d = 2m` and `im ≤ Kd² ≤ (i+1)m`. -/
theorem goldbachWindow_mesh (h : GoldbachWindow) {K i : ℕ} (hK : 0 < K) (hi : i + 1 ≤ 18 * K) :
    ∀ᶠ m : ℕ in atTop, ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ 2 * p + d = 2 * m ∧
      i * m ≤ K * d ^ 2 ∧ K * d ^ 2 ≤ (i + 1) * m := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hiR : ((i : ℝ) + 1) ≤ 18 * K := by exact_mod_cast hi
  have hab : Real.sqrt ((i : ℝ) / (2 * K)) < Real.sqrt (((i : ℝ) + 1) / (2 * K)) :=
    Real.sqrt_lt_sqrt (by positivity) (by gcongr; linarith)
  have hb3 : Real.sqrt (((i : ℝ) + 1) / (2 * K)) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]; linarith
  have hW := h _ _ (Real.sqrt_nonneg _) hab hb3
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  filter_upwards [h2.eventually hW] with m hm
  obtain ⟨p, q, hp, hq, hs, hpq, hlo, hhi⟩ := hm (even_two_mul m)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  have hc : ((p + d : ℕ) : ℝ) - p = d := by push_cast; ring
  refine ⟨p, d, hp, hq, by omega, ?_, ?_⟩
  · rw [hc] at hlo
    have := sq_le_of_sqrt_mul_le (by positivity) (by positivity) hlo
    push_cast at this
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    have : (((i * m : ℕ)) : ℝ) ≤ ((K * d ^ 2 : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  · rw [hc] at hhi
    have := sq_le_of_le_sqrt_mul (by positivity) (by positivity) (by positivity) hhi
    push_cast at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    have : ((K * d ^ 2 : ℕ) : ℝ) ≤ (((i + 1) * m : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this

/-- The square parameter: every `n ≥ 1` has `m² = n + e` with `m ≤ e < 3m − 2`. -/
theorem exists_sq_param {n : ℕ} (hn : 1 ≤ n) :
    ∃ m e : ℕ, m ^ 2 = n + e ∧ m ≤ e ∧ e + 2 < 3 * m := by
  have hex : ∃ m, n + m ≤ m ^ 2 := ⟨n + 1, by nlinarith⟩
  have hm : n + Nat.find hex ≤ (Nat.find hex) ^ 2 := Nat.find_spec hex
  have hm0 : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0] at hm; simp at hm; omega
    · exact h0
  have hmin : ¬ n + (Nat.find hex - 1) ≤ (Nat.find hex - 1) ^ 2 := Nat.find_min hex (by omega)
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hex = m' + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hm'] at hmin hm; simp only [Nat.add_sub_cancel] at hmin
  refine ⟨m' + 1, (m' + 1) ^ 2 - n, by omega, by omega, ?_⟩
  have : (m' + 1) ^ 2 = m' ^ 2 + 2 * m' + 1 := by ring
  omega

/-- All mesh-`K` windows at once, for large `n`, at the square parameter of `n`. -/
theorem eventually_mesh_windows (h : GoldbachWindow) {K : ℕ} (hK : 0 < K) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ m e : ℕ, m ^ 2 = n + e ∧ m ≤ e ∧ e + 2 < 3 * m ∧ M ≤ m ∧
      ∀ i, i + 1 ≤ 18 * K → ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ 2 * p + d = 2 * m ∧
        i * m ≤ K * d ^ 2 ∧ K * d ^ 2 ≤ (i + 1) * m := by
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i : Fin (18 * K), ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧
      2 * p + d = 2 * m ∧ i * m ≤ K * d ^ 2 ∧ K * d ^ 2 ≤ (i + 1) * m :=
    eventually_all.2 fun i => goldbachWindow_mesh h hK i.2
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hall
  refine eventually_atTop.2 ⟨(M0 + M + 1) ^ 2, fun n hn => ?_⟩
  have : 0 < (M0 + M + 1) ^ 2 := by positivity
  obtain ⟨m, e, hme, h1, h2⟩ := exists_sq_param (n := n) (by omega)
  have hmbig : M0 + M + 1 ≤ m := by
    by_contra hc; push Not at hc
    have : m ^ 2 < (M0 + M + 1) ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
    omega
  exact ⟨m, e, hme, h1, h2, by omega, fun i hi => hM0 m (by omega) ⟨i, by omega⟩⟩

set_option maxHeartbeats 800000 in
/-- `ees_of_goldbachWindow` for `ε ≤ 1` (mesh `K ≈ 2/ε`). -/
theorem ees_of_goldbachWindow_le_one (h : GoldbachWindow) {ε : ℝ} (he : 0 < ε) (he1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + (1 - ε) * Real.sqrt n ≤ F n := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by omega
  have hKε : 2 ≤ (K : ℝ) * ε := by
    have : 2 / ε ≤ (K : ℝ) := by
      rw [hK]; push_cast; linarith [Nat.le_ceil (2 / ε)]
    rwa [div_le_iff₀ he] at this
  filter_upwards [eventually_mesh_windows h hK0 (⌈52 / ε ^ 2⌉₊ + 1)]
    with n ⟨m, e, hme, h1, h2, hM, hw⟩
  have hm0 : 0 < m := by omega
  obtain ⟨t, ht⟩ : ∃ t, t = 4 * K * e / m := ⟨_, rfl⟩
  have ht1 : t * m ≤ 4 * K * e := by rw [ht]; exact Nat.div_mul_le_self _ _
  have ht2 : 4 * K * e < (t + 1) * m := by
    have := Nat.lt_div_mul_add (a := 4 * K * e) hm0; rw [← ht] at this; linarith
  have ht12 : t < 12 * K := ht ▸ (Nat.div_lt_iff_lt_mul hm0).2 (by nlinarith)
  obtain ⟨p, d, hp, hq, hs, hlo, hhi⟩ := hw (t + 1) (by omega)
  have hKd : K * (4 * e) < K * d ^ 2 := by linarith
  have hd4 : 4 * e < d ^ 2 := Nat.lt_of_mul_lt_mul_left hKd
  have hd13 : d ^ 2 ≤ 13 * m := by
    have : K * d ^ 2 ≤ K * (13 * m) := by
      have : (t + 1 + 1) * m ≤ (12 * K + 1) * m := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    exact Nat.le_of_mul_le_mul_left this hK0
  have hN : 4 * (p * (p + d)) + d ^ 2 = 4 * n + 4 * e := by
    have : (2 * p + d) ^ 2 = 4 * (p * (p + d)) + d ^ 2 := by ring
    rw [← this, hs, show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
  have hlt : p * (p + d) < n := by linarith
  have hF := add_minFac_le_F hlt (composite_mul_primes hp hq)
  have hd0 : 0 < d := by nlinarith
  rw [minFac_mul_primes hp hq (by omega)] at hF
  -- real arithmetic
  have hFR : ((p * (p + d) : ℕ) : ℝ) + p ≤ F n := by exact_mod_cast hF
  have hNR : 4 * ((p * (p + d) : ℕ) : ℝ) + (d : ℝ) ^ 2 = 4 * n + 4 * e := by exact_mod_cast hN
  have hsR : 2 * (p : ℝ) + d = 2 * m := by exact_mod_cast hs
  have hhiR : (K : ℝ) * (d : ℝ) ^ 2 ≤ ((t : ℝ) + 2) * m := by
    have : K * d ^ 2 ≤ (t + 2) * m := hhi
    exact_mod_cast this
  have ht1R : (t : ℝ) * m ≤ 4 * K * e := by exact_mod_cast ht1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  -- d² − 4e ≤ ε m
  have hgap : (d : ℝ) ^ 2 - 4 * e ≤ ε * m := by
    have h1 : (K : ℝ) * ((d : ℝ) ^ 2 - 4 * e) ≤ 2 * m := by nlinarith
    have h2 : (K : ℝ) * ((d : ℝ) ^ 2 - 4 * e) ≤ K * (ε * m) := by nlinarith
    exact le_of_mul_le_mul_left h2 hKR
  -- 2d ≤ ε m
  have hMR : 52 / ε ^ 2 ≤ (m : ℝ) := by
    have := Nat.le_ceil (52 / ε ^ 2)
    have : ((⌈52 / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hM
    push_cast at this; linarith
  have h52 : 52 ≤ ε ^ 2 * m := by
    rw [div_le_iff₀ (by positivity)] at hMR; linarith
  have hd13R : (d : ℝ) ^ 2 ≤ 13 * m := by exact_mod_cast hd13
  have h2d : 2 * (d : ℝ) ≤ ε * m := by
    have : (2 * (d : ℝ)) ^ 2 ≤ (ε * m) ^ 2 :=
      calc (2 * (d : ℝ)) ^ 2 = 4 * (d : ℝ) ^ 2 := by ring
        _ ≤ 52 * (m : ℝ) := by linarith
        _ ≤ ε ^ 2 * (m : ℝ) * m := mul_le_mul_of_nonneg_right h52 hmR.le
        _ = (ε * m) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
  have hsq : Real.sqrt n ≤ m := by
    rw [Real.sqrt_le_left (by positivity)]; exact_mod_cast (by omega : n ≤ m ^ 2)
  have hprod : (1 - ε) * Real.sqrt n ≤ (1 - ε) * m := mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith

/-- Edge: `GoldbachWindow` gives the all-`n` Erdős–Eggleton–Selfridge bound for each `e > 0`
(formal-conjectures `erdos_385.variants.lb`, eventually). -/
theorem ees_of_goldbachWindow (h : GoldbachWindow) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + (1 - e) * Real.sqrt n ≤ F n := by
  filter_upwards [ees_of_goldbachWindow_le_one h (lt_min he one_pos) (min_le_right e 1)] with n hn
  have : (1 - e) * Real.sqrt n ≤ (1 - min e 1) * Real.sqrt n :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_left e 1]) (Real.sqrt_nonneg _)
  linarith

/-- Edge: `GoldbachWindow` gives #463. -/
theorem erdos463_of_goldbachWindow (h : GoldbachWindow) :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, Composite m ∧ (n : ℝ) + f n < m ∧ m < n + m.minFac := by
  refine ⟨fun n => Real.sqrt n / 4, ?_, ?_⟩
  · exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  filter_upwards [eventually_mesh_windows h (K := 1) one_pos 45] with n ⟨m, e, hme, h1, h2, hM, hw⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 4 * e / m := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have ht1 : t * m ≤ 4 * e := by rw [ht]; exact Nat.div_mul_le_self _ _
  have ht2 : 4 * e < (t + 1) * m := by
    have := Nat.lt_div_mul_add (a := 4 * e) hm0; rw [← ht] at this; linarith
  have ht4 : 4 ≤ t := ht ▸ (Nat.le_div_iff_mul_le hm0).2 (by linarith)
  have ht11 : t < 12 := ht ▸ (Nat.div_lt_iff_lt_mul hm0).2 (by linarith)
  obtain ⟨p, d, hp, hq, hs, hlo, hhi⟩ := hw (t - 2) (by omega)
  rw [one_mul] at hlo hhi
  have hj1 : (t - 2) * m + 2 * m = t * m := by
    rw [← add_mul, show t - 2 + 2 = t by omega]
  have hj2 : (t - 2 + 1) * m + m = t * m := by
    rw [← add_one_mul, show t - 2 + 1 + 1 = t by omega]
  have hd : 2 * d < m := by
    by_contra hc; push Not at hc
    have h1 : m * m ≤ 4 * d ^ 2 := by
      have := Nat.mul_le_mul hc hc; rw [show 2 * d * (2 * d) = 4 * d ^ 2 by ring] at this
      exact this
    have h2 : t * m ≤ 11 * m := Nat.mul_le_mul_right _ (by omega)
    have h3 : 45 * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
    linarith
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0] at hlo; have : 2 * m ≤ (t - 2) * m := Nat.mul_le_mul_right _ (by omega)
      simp at hlo; omega
    · exact h0
  have hN : 4 * (p * (p + d)) + d ^ 2 = 4 * n + 4 * e := by
    have : (2 * p + d) ^ 2 = 4 * (p * (p + d)) + d ^ 2 := by ring
    rw [← this, hs, show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
  have hlow : 4 * n + m ≤ 4 * (p * (p + d)) := by linarith
  have hup : p * (p + d) < n + p := by linarith
  refine ⟨p * (p + d), composite_mul_primes hp hq, ?_, by
    rw [minFac_mul_primes hp hq (by omega)]; exact hup⟩
  have hsq : Real.sqrt n < m := by
    rw [Real.sqrt_lt' (by exact_mod_cast hm0)]; exact_mod_cast (by nlinarith : n < m ^ 2)
  have : (4 * n + m : ℝ) ≤ 4 * ((p * (p + d) : ℕ) : ℝ) := by exact_mod_cast hlow
  linarith

end LeanFormalizations.Erdos385

#print axioms LeanFormalizations.Erdos385.almost_all_erdos463_powerSaving
#print axioms LeanFormalizations.Erdos385.ees_of_goldbachWindow
#print axioms LeanFormalizations.Erdos385.erdos463_of_goldbachWindow
#print axioms LeanFormalizations.Erdos385.hyperbolaPrimePairs_of_goldbachWindow
#print axioms LeanFormalizations.Erdos385.erdos385_ii_of_downMargin
