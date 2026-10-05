/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Practical.Basic

/-!
# Practical numbers in short intervals (2026-10-05)

`PracticalShortInterval θ`: for all large `x`, `[x − x^θ, x]` holds `≫ x^θ (log x)^{−μ}` practical
numbers.  The prime analogue is `BHPTests.PrimesShortInterval` (`θ = 21/40` from BHP).

* Elementary `θ = 1/2`: `practical_near_sqrt` (multiples `2^a k`, `k ≤ σ(2^a)`).
* Weingartner (2021), Theorem 2: from any exponent pair `(k, l)`, every
  `β > β(k, l) = (5k + l + 2)/(6(k + 1))`.  With `A(13/84, 55/84) = (13/194, 76/97)` (Bourgain) he
  got `605/1242 = 0.48711…` (Cor. 4).
* **New (plug-in):** Tao–Trudgian–Yang (2025, Theorem 20) prove `(652397/9713986,
  7599781/9713986)` is an exponent pair, giving `β(k, l) = 15144869/31099149 = 0.486987…`
  (`practicalShortInterval_tty`).  This is the minimum of `β` over the vertices of the known
  hull (Trudgian–Yang 2023's `(k_n, l_n)` plus TTY's four new pairs, closed under the A and B
  processes); a linear-fractional objective is minimized at a vertex.  Trudgian–Yang's own
  vertex `(715/10238, 7955/10238)` already gives `0.487020…`.  Script: `scripts/practical-exponent-opt.py`.
  The gain is in the fourth decimal.  The exponent-pairs conjecture would give `5/12`
  (Weingartner, Cor. 4).

Exponent pairs are not defined in mathlib.  The cited theorems therefore take the notion as a
parameter `EP`: the composition theorem holds for *any* `EP` satisfying both cited statements,
in particular the true one.
-/

namespace LeanFormalizations.Practical

open Real Finset

/-- Practical numbers in the real interval `[a, b]`. -/
noncomputable def practicalIn (a b : ℝ) : ℕ := ((Icc ⌈a⌉₊ ⌊b⌋₊).filter IsPractical).card

/-- `[x − x^θ, x]` holds `≫ x^θ (log x)^{−μ}` practical numbers for all large `x`. -/
def PracticalShortInterval (θ : ℝ) : Prop :=
  ∃ μ d₀ : ℝ, 0 < d₀ ∧ ∃ X : ℝ, ∀ x ≥ X,
    d₀ * x ^ θ / (log x) ^ μ ≤ (practicalIn (x - x ^ θ) x : ℝ)

/-- **Elementary `θ = 1/2`**: pick `a` with `2^{2a−1} ≤ x < 2^{2a+1}`; the largest multiple
`2^a k ≤ x` has `k < 2^{a+1} = σ(2^a) + 1`, so it is practical (`isPractical_mul_of_le_sigma`)
and `≥ x − 2^a ≥ x − √(2x)`.  The analogue of Hausman–Shapiro's `[x², (x+1)²]`.  Believed 97%. -/
theorem practical_near_sqrt (x : ℝ) (hx : 2 ≤ x) :
    ∃ n : ℕ, IsPractical n ∧ x - Real.sqrt (2 * x) ≤ n ∧ (n : ℝ) ≤ x := by
  sorry

/-- The exponent `β(k, l) = (5k + l + 2)/(6(k + 1))` of Weingartner (2021), Theorem 2. -/
noncomputable def weingartnerBeta (k l : ℝ) : ℝ := (5 * k + l + 2) / (6 * (k + 1))

/-- **Weingartner (2021), Theorem 2**, specialized from his set `A` to its superset, the practical
numbers (his §3 remark): for every exponent pair `(k, l)` and `β > β(k, l)`, `[x − z, x]` with
`z ≥ K x^β` holds `≫ z (log x)^{−μ}` members.  Stated at `z = x^β` (weaker).
A. Weingartner, *Somewhat smooth numbers in short intervals*, arXiv:2105.13568, Thm 2. -/
def Literature.Weingartner2021Thm2 (EP : ℝ → ℝ → Prop) : Prop :=
  ∀ k l : ℝ, EP k l → ∀ β > weingartnerBeta k l, PracticalShortInterval β

/-- **Tao–Trudgian–Yang (2025), Theorem 20** (one of four new pairs).
T. Tao, T. Trudgian, A. Yang, *New exponent pairs, zero density estimates, and zero additive
energy estimates: a systematic approach*, arXiv:2501.16779, Thm 20. -/
def Literature.TaoTrudgianYang2025Pair (EP : ℝ → ℝ → Prop) : Prop :=
  EP (652397 / 9713986) (7599781 / 9713986)

/-- Weingartner's own corollary (Cor. 4, Bourgain's pair processed by A): `β = 605/1242`.  A
known-answer check on `weingartnerBeta`. -/
theorem weingartnerBeta_bourgain : weingartnerBeta (13 / 194) (76 / 97) = 605 / 1242 := by
  unfold weingartnerBeta; norm_num

/-- **Practical numbers in `[x − x^β, x]` for every `β > 0.486987…`** (`15144869/31099149`),
improving Weingartner's `0.4871…` by plugging the TTY 2025 exponent pair into his Theorem 2. -/
theorem practicalShortInterval_tty (EP : ℝ → ℝ → Prop)
    (hW : Literature.Weingartner2021Thm2 EP) (hT : Literature.TaoTrudgianYang2025Pair EP) :
    ∀ β > (15144869 / 31099149 : ℝ), PracticalShortInterval β := by
  intro β hβ
  refine hW _ _ hT β ?_
  have : weingartnerBeta (652397 / 9713986) (7599781 / 9713986) = 15144869 / 31099149 := by
    unfold weingartnerBeta; norm_num
  rw [this]; exact hβ

/-- **Open:** the count form for every `ε > 0`.  (Granville's smooth-number conjecture would give
at least one practical number in every `[x − x^ε, x]`, per Pomerance; Weingartner 2021 §3.) -/
def PracticalShortIntervalAll : Prop := ∀ ε > (0 : ℝ), PracticalShortInterval ε

end LeanFormalizations.Practical
