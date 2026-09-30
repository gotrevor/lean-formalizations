/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 39: `⌊α^(c^n)⌋ + h` is composite i.o. for quadratic Pisot units of norm `−1`

Saito's Problem 1.1 asks whether `⌊β^(3^n)⌋` is composite infinitely often for cubic Pisot `β`.
The quadratic analogue with any shift follows from phase 35.  Let `α = (P + √(P² + 4))/2`
(`P ≥ 1`) be the Pisot unit of norm `−1`.  For odd `N`, `⌊α^N⌋ = V_N(P, −1)`, because the conjugate
`β = −1/α` satisfies `−1 < β^N < 0`.  Checked numerically for `P ≤ 7`, `N ≤ 81`.  So for every odd prime
`c ∤ P` and every `h`, `⌊α^(c^n)⌋ + h` is composite infinitely often.  The golden ratio `φ`
(`P = 1`) is covered at every odd prime `c`.

For `c = 2`: `⌊φ^(2^n)⌋ = L(2^n) − 1`, and the only open shift is `h = 1` (Fermat-type, `L(2^n)`);
this is not claimed here.

## Route
1. `floor_pow_odd`: `⌊α^N⌋ = lucasV P (−1) N` for odd `N`.  `α^N + β^N = V_N` (induction on
   the recurrence, or `α, β` roots of `X² − PX − 1`), `β = −1/α`, `0 < α⁻¹ < 1` since `α > 1`,
   so `β^N ∈ (−1, 0)` for odd `N ≥ 1`.  Use `Int.floor_eq_iff`.
2. Main: rewrite with step 1 (`c^n` is odd) and apply
   `LucasPrimePow.lucasV_prime_pow_add_not_prime`.
3. `golden_floor_prime_pow_add_not_prime`: `P = 1`; `c ∤ 1` for every prime.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.QuadraticPisotFloor

open LeanFormalizations.Mills.LucasPrimePow Filter

/-- The Pisot unit of norm `−1` with trace `P`. -/
noncomputable def pisotNegUnit (P : ℤ) : ℝ := (P + Real.sqrt (P ^ 2 + 4)) / 2

/-- The conjugate root `β = (P − √(P²+4))/2`. -/
noncomputable def pisotConj (P : ℤ) : ℝ := (P - Real.sqrt (P ^ 2 + 4)) / 2

theorem sq_sqrt_disc (P : ℤ) :
    Real.sqrt ((P : ℝ) ^ 2 + 4) ^ 2 = (P : ℝ) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

theorem sqrt_disc_pos (P : ℤ) : 0 < Real.sqrt ((P : ℝ) ^ 2 + 4) :=
  Real.sqrt_pos.2 (by positivity)

/-- `α` and `β` are the two roots of `X² − PX − 1`. -/
theorem pisot_sq (P : ℤ) :
    pisotNegUnit P ^ 2 = (P : ℝ) * pisotNegUnit P + 1 := by
  have h := sq_sqrt_disc P
  simp only [pisotNegUnit]
  push_cast
  nlinarith [h]

theorem pisotConj_sq (P : ℤ) :
    pisotConj P ^ 2 = (P : ℝ) * pisotConj P + 1 := by
  have h := sq_sqrt_disc P
  simp only [pisotConj]
  push_cast
  nlinarith [h]

/-- Binet: `α^N + β^N = V_N(P, −1)`. -/
theorem pow_add_pow_eq_lucasV (P : ℤ) (N : ℕ) :
    pisotNegUnit P ^ N + pisotConj P ^ N = ((lucasV P (-1) N : ℤ) : ℝ) := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num [lucasV_zero]
  | one => simp only [pow_one, lucasV_one, pisotNegUnit, pisotConj]; ring
  | more N ih1 ih2 =>
      have ea : pisotNegUnit P ^ (N + 2)
          = (P : ℝ) * pisotNegUnit P ^ (N + 1) + pisotNegUnit P ^ N := by
        have e : pisotNegUnit P ^ (N + 2) = pisotNegUnit P ^ N * pisotNegUnit P ^ 2 := by ring
        rw [e, pisot_sq]; ring
      have eb : pisotConj P ^ (N + 2)
          = (P : ℝ) * pisotConj P ^ (N + 1) + pisotConj P ^ N := by
        have e : pisotConj P ^ (N + 2) = pisotConj P ^ N * pisotConj P ^ 2 := by ring
        rw [e, pisotConj_sq]; ring
      rw [ea, eb, lucasV_succ_succ]
      push_cast
      push_cast at ih1 ih2
      linear_combination (P : ℝ) * ih2 + ih1

theorem pisotConj_mem {P : ℤ} (hP : 1 ≤ P) : -1 < pisotConj P ∧ pisotConj P < 0 := by
  have hP' : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have h := sq_sqrt_disc P
  have hpos := sqrt_disc_pos P
  constructor
  · simp only [pisotConj]
    nlinarith [h, hpos]
  · simp only [pisotConj]
    nlinarith [h, hpos]

theorem floor_pow_odd {P : ℤ} (hP : 1 ≤ P) {N : ℕ} (hN : Odd N) :
    ⌊pisotNegUnit P ^ N⌋ = lucasV P (-1) N := by
  obtain ⟨hlo, hhi⟩ := pisotConj_mem hP
  have hbn : -1 < pisotConj P ^ N ∧ pisotConj P ^ N < 0 := by
    constructor
    · have : |pisotConj P ^ N| < 1 := by
        rw [abs_pow]
        exact pow_lt_one₀ (abs_nonneg _) (by rw [abs_lt]; exact ⟨hlo, hhi.trans one_pos⟩) hN.pos.ne'
      have := abs_lt.1 this
      exact this.1
    · exact hN.pow_neg hhi
  have hsum := pow_add_pow_eq_lucasV P N
  rw [Int.floor_eq_iff]
  constructor
  · push_cast; linarith [hbn.2, hsum]
  · push_cast; linarith [hbn.1, hsum]

/-- **`⌊α^(c^n)⌋ + h` is composite infinitely often** for the norm `−1` quadratic Pisot unit
`α` of trace `P ≥ 1`, every odd prime `c ∤ P`, and every integer `h`. -/
theorem floor_pisotNegUnit_prime_pow_add_not_prime {P : ℤ} (hP : 1 ≤ P) {c : ℕ}
    (hc : c.Prime) (hc2 : c ≠ 2) (hcP : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (⌊pisotNegUnit P ^ (c ^ n)⌋ + h) := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  refine (lucasV_prime_pow_add_not_prime hc hc2 hcP h).mono ?_
  intro n hn
  rwa [floor_pow_odd hP (hcodd.pow (n := n))]

/-- The golden ratio: `⌊φ^(c^n)⌋ + h` is composite i.o. for every odd prime `c` and every `h`. -/
theorem golden_floor_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (⌊((1 + Real.sqrt 5) / 2) ^ (c ^ n)⌋ + h) := by
  have hP : ¬ ((c : ℤ) ∣ (1 : ℤ)) := by
    intro hd
    have := Int.le_of_dvd one_pos hd
    have h2 : 2 ≤ (c : ℤ) := by exact_mod_cast hc.two_le
    omega
  have heq : pisotNegUnit 1 = (1 + Real.sqrt 5) / 2 := by
    simp only [pisotNegUnit]
    norm_num
  have := floor_pisotNegUnit_prime_pow_add_not_prime (P := 1) le_rfl hc hc2 hP h
  rwa [heq] at this

end LeanFormalizations.Mills.QuadraticPisotFloor
