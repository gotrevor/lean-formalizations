/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Practical numbers: definitions, sanity tests, elementary bedrock (phase Pr1)

A positive integer `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`
(Srinivasan 1948).  This file is the elementary layer the analytic results in
`Literature/Practical.lean` are stated against.

* `IsPractical` (decidable, so small cases are `decide`), hand-checked tests below.
* `InB θ n`: the Pomerance–Weingartner / Tenenbaum family `B_θ` (each prime factor bounded by
  `θ` of the part of `n` below it).  `isPractical_iff_inB` is the Stewart–Sierpiński
  characterization `θ = σ + 1`.
* `isPractical_mul_of_le_sigma`: `n` practical, `1 ≤ m ≤ σ(n) + 1` ⇒ `n m` practical.
* `primePlusPractical_window`: Pomerance–Weingartner (2021) Lemma 9, the computational
  bootstrap for Margenstern's conjecture (`PrimePlusPracticalOdd`).

Agreement with formal-conjectures' `Nat.IsPractical` (`FormalConjecturesForMathlib/NumberTheory/
PracticalNumbers.lean`, no positivity clause, `subsetSums`): ours is theirs plus `0 < n`, the form
used by `OeisA5153.A`.  This repo does not depend on formal-conjectures, so the agreement is
recorded here rather than proved.
-/

namespace LeanFormalizations.Practical

open Finset

/-- `σ(n)`, the sum of the positive divisors (kept elementary and decidable). -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` is a sum of distinct positive divisors of `n`. -/
def IsDivisorSubsetSum (n m : ℕ) : Prop := ∃ s ∈ n.divisors.powerset, ∑ d ∈ s, d = m

instance (n m : ℕ) : Decidable (IsDivisorSubsetSum n m) := by
  unfold IsDivisorSubsetSum; infer_instance

/-- **Practical numbers** (Srinivasan 1948): `n ≥ 1` and every `m ≤ n` is a sum of distinct
divisors of `n`.  OEIS A005153. -/
def IsPractical (n : ℕ) : Prop := 0 < n ∧ ∀ m ≤ n, IsDivisorSubsetSum n m

instance : DecidablePred IsPractical := fun n => by unfold IsPractical; infer_instance

/-! ## Sanity tests (hand-checked) -/

/-- Divisor sums: `σ(6) = 12`, `σ(12) = 28`, `σ(2⁴) = 31`. -/
theorem sigma1_6 : sigma1 6 = 12 := by decide
theorem sigma1_12 : sigma1 12 = 28 := by decide
theorem sigma1_16 : sigma1 16 = 31 := by decide

/-- The practical numbers below 31 are `1 2 4 6 8 12 16 18 20 24 28 30` (A005153).  Each
non-listed `n` fails at a named `m`: `3` (`m = 2`), `10` (`m = 4`: divisors `1 2 5 10`),
`14` (`m = 4`), `22` (`m = 4`), `26` (`m = 4`). -/
theorem practical_below_31 :
    (Finset.range 31).filter IsPractical = {1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30} := by
  decide +kernel

theorem not_isPractical_zero : ¬ IsPractical 0 := by decide
theorem not_isPractical_10 : ¬ IsPractical 10 := by decide
/-- `4` is not a sum of distinct divisors of `10` (`1 2 5 10`). -/
theorem not_divisorSubsetSum_10_4 : ¬ IsDivisorSubsetSum 10 4 := by decide
/-- `78 = 6 · 13` with `13 = σ(6) + 1`: the multiplication lemma at its boundary. -/
theorem isPractical_78 : IsPractical 78 := by decide +kernel

/-! ## Elementary bedrock (statements frozen; proofs are phase Pr1) -/

/-- Practical numbers other than `1` are even: `2` must be a sum of distinct divisors, and an odd
`n > 1` has `1` as its only divisor below `3`.  Believed 100%. -/
theorem IsPractical.even_of_one_lt {n : ℕ} (hn : IsPractical n) (h1 : 1 < n) : Even n := by
  sorry

/-- `n!` is practical (formal-conjectures `Erdos18.factorial_isPractical`, proved there for its
`Nat.IsPractical`).  Believed 100%. -/
theorem isPractical_factorial (n : ℕ) : IsPractical n.factorial := by
  sorry

/-- The part of `n` built from its prime factors below `p`: `∏_{q ∣ n, q < p} q^{v_q(n)}`. -/
def partBelow (n p : ℕ) : ℕ := ∏ q ∈ n.primeFactors with q < p, q ^ n.factorization q

/-- The family `B_θ` (Tenenbaum; Weingartner 2015; Pomerance–Weingartner 2021 eq. (1)): `n ≥ 1`
and every prime factor `p` of `n` satisfies `p ≤ θ(partBelow n p)`. -/
def InB (θ : ℕ → ℝ) (n : ℕ) : Prop := 0 < n ∧ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ θ (partBelow n p)

/-- **Stewart (1954), Sierpiński (1955)**: practical numbers are exactly `B_θ` with
`θ(n) = σ(n) + 1`, i.e. `n = p₁^{a₁} ⋯ p_k^{a_k}` (`p₁ < ⋯ < p_k`) is practical iff
`p_j ≤ σ(p₁^{a₁} ⋯ p_{j−1}^{a_{j−1}}) + 1` for all `j`.  As quoted in Pomerance–Weingartner
(2021) §1.  Believed 99% (statement transcription; the theorem is classical). -/
theorem isPractical_iff_inB (n : ℕ) :
    IsPractical n ↔ InB (fun m => (sigma1 m : ℝ) + 1) n := by
  sorry

/-- **Multiplication lemma**: if `n` is practical and `1 ≤ m ≤ σ(n) + 1`, then `n m` is practical.
Pomerance–Weingartner (2021) use it for `n = 2^a` in the proof of Lemma 9.  Route: write
`k ≤ nm` as `k = n·j + r` with `j ≤ σ(n)`, `r < n`; `j` is a subset sum `Σ dᵢ` of divisors of
`n`, so `n j = Σ n dᵢ`... needs care (`n dᵢ` is not a divisor of `nm`); the clean route is via
`isPractical_iff_inB` (each prime of `m` is `≤ m ≤ σ(n) + 1 ≤ σ(partBelow) + 1`).
Believed 95%. -/
theorem isPractical_mul_of_le_sigma {n m : ℕ} (hn : IsPractical n) (hm1 : 1 ≤ m)
    (hm : m ≤ sigma1 n + 1) : IsPractical (n * m) := by
  sorry

/-- **Margenstern's conjecture, odd case** (Margenstern 1991, Conjecture 7, in the stronger
prime + practical form of Pomerance–Weingartner 2021 Corollary 2 and OEIS A005153 (Switkay)):
every odd `n > 1` is a prime plus a practical number.  OPEN: known for `n > x₀` (ineffective,
`Literature.PomeranceWeingartner2021`) and for `n < 2^71` (their §5.1 computation). -/
def PrimePlusPracticalOdd : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ∃ p q : ℕ, p.Prime ∧ IsPractical q ∧ n = p + q

/-- **Pomerance–Weingartner (2021) Lemma 9** (the window): if every odd residue class mod `2^a`
contains a prime `≤ B` (their `M(2^a) ≤ B`), then every odd `n` with `B < n < 2^{2a+1}` is a
prime plus a practical number.  Proof: `q = n − p(n, 2^a)` is a multiple of `2^a` below
`2^{2a+1}`, so `q = 2^a·k` with `k < 2^{a+1} = σ(2^a) + 1`; `isPractical_mul_of_le_sigma`.
(`k ≥ 1` since `p ≤ B < n`.)  Believed 97%. -/
theorem primePlusPractical_window (a B : ℕ)
    (hM : ∀ u : ℕ, Odd u → u < 2 ^ a → ∃ p, p.Prime ∧ p ≤ B ∧ p % 2 ^ a = u)
    (n : ℕ) (hodd : Odd n) (hlo : B < n) (hhi : n < 2 ^ (2 * a + 1)) :
    ∃ p q : ℕ, p.Prime ∧ IsPractical q ∧ n = p + q := by
  sorry

/-- The window at `a = 3` (`M(8) = 17`: primes `17, 3, 5, 7` for `1, 3, 5, 7` mod 8) covers
odd `n ∈ (17, 128)` — Pomerance–Weingartner's worked example.  A test of the window's
hypothesis shape. -/
theorem window_hyp_8 :
    ∀ u : ℕ, Odd u → u < 2 ^ 3 → ∃ p, p.Prime ∧ p ≤ 17 ∧ p % 2 ^ 3 = u := by
  intro u hu hlt
  have : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := by rcases hu with ⟨k, rfl⟩; omega
  rcases this with rfl | rfl | rfl | rfl
  · exact ⟨17, by norm_num, le_rfl, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num⟩

/-- `PrimePlusPracticalOdd` up to `17`, by computation (`3 = 2 + 1`, ..., `17 = 11 + 6`).  With
the `a = 3` window this covers every odd `n < 128`. -/
theorem primePlusPractical_le_17 :
    ∀ n < 18, Odd n → 1 < n → ∃ p ∈ Finset.range n, p.Prime ∧ IsPractical (n - p) := by
  decide +kernel

end LeanFormalizations.Practical
