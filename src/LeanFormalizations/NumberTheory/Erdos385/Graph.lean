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
  intro m hm hmn hc
  have := add_minFac_le_F hmn hc
  unfold Bad at h
  omega

/-- `(k + 1)² ≤ 2^k` for `k ≥ 6`. -/
theorem sq_succ_le_two_pow {k : ℕ} (hk : 6 ≤ k) : (k + 1) * (k + 1) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; nlinarith

/-- **Edge: repulsion ⇒ #385(i).** -/
theorem eventually_not_bad_of_crossScaleRepulsion (h : CrossScaleRepulsion) :
    ∀ᶠ n : ℕ in atTop, ¬ Bad n := by
  filter_upwards [h, eventually_ge_atTop (2 ^ 6)] with n hn hn64 hbad
  set k := Nat.log 2 n with hk
  have hk6 : 6 ≤ k := Nat.le_log_of_pow_le (by norm_num) hn64
  have hkn : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hlog : Real.log n ≤ (k + 1 : ℕ) := by
    have h1 : Real.log n < Real.log (2 ^ (k + 1) : ℕ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast hlt)
    have h2 : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) = (k + 1 : ℕ) * Real.log 2 := by
      push_cast; rw [Real.log_pow]; push_cast; ring
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h4 : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
    nlinarith
  have hsq : (k + 1) * (k + 1) ≤ n := (sq_succ_le_two_pow hk6).trans hkn
  obtain ⟨h', -, -, hnc⟩ := hn (k + 1) hlog hsq (noCarrier_of_bad (by omega) hbad _)
  exact hnc (noCarrier_of_bad (by omega) hbad _)

/-- **Edge: FGKMT ⇒ the sieve-only sibling.**  `Y(x) ≫ x log x log₃ x / log₂ x ≥ x` eventually. -/
theorem sieveOnlySibling_of_FGKMT (h : FGKMT2018Eq12) : SieveOnlySibling := by
  obtain ⟨c, hc, x₀, hx⟩ := h
  have hlo := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < c by exact hc)
  have hL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hLL : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have key : ∀ᶠ x : ℝ in atTop, x₀ ≤ x ∧ x ≤ c * x * Real.log x * Real.log (Real.log (Real.log x))
      / Real.log (Real.log x) := by
    filter_upwards [eventually_ge_atTop x₀, eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually hlo, hL.eventually_gt_atTop 0,
      hLL.eventually_ge_atTop 1] with x hx0 hx1 hb hpos h3
    refine ⟨hx0, ?_⟩
    have hb' : Real.log (Real.log x) ≤ c * Real.log x := by
      have := hb; simp only [id, Real.norm_eq_abs] at this
      have hlx : 0 < Real.log x := by
        rcases (Real.log_nonneg hx1).lt_or_eq with h | h
        · exact h
        · rw [← h, Real.log_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      rw [abs_of_pos hlx] at this
      exact (le_abs_self _).trans this
    rw [le_div_iff₀ hpos]
    have hx0' : 0 ≤ x := by linarith
    calc x * Real.log (Real.log x) ≤ x * (c * Real.log x) := mul_le_mul_of_nonneg_left hb' hx0'
      _ = c * x * Real.log x * 1 := by ring
      _ ≤ c * x * Real.log x * Real.log (Real.log (Real.log x)) := by
        apply mul_le_mul_of_nonneg_left h3
        have : 0 ≤ Real.log x := Real.log_nonneg hx1
        positivity
  filter_upwards [tendsto_natCast_atTop_atTop.eventually key] with x ⟨hx0, hxc⟩
  obtain ⟨a, ha⟩ := hx x hx0
  exact ⟨a, fun t ht1 htx => ha t ht1 (by
    have : (t : ℝ) ≤ x := by exact_mod_cast htx
    linarith)⟩

end LeanFormalizations.Erdos385
