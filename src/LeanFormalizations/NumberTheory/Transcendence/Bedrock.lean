/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Bedrock: the unconditional classics (phase 21)

Trevor, 2026-09-27: *"the more bedrock we have, the better."*  After the Schanuel phases this file
collects consequences of the **theorems**: Lindemann–Weierstrass (mathlib PR #28013, in
`Literature/Lindemann.lean`), Gelfond–Schneider (`Literature/GelfondSchneider.lean`, real form)
and Nesterenko (`Literature/Nesterenko.lean`).  Nothing here rests on a conjecture.

* Hermite–Lindemann: `e^a` for nonzero algebraic `a`; `log α` for algebraic `α > 0`, `α ≠ 1`;
  `sin a`, `cos a` for nonzero algebraic real `a`.  (For `cos`, use `2cos a = e^{ia} + e^{-ia}`
  with the two exponentials algebraically independent, or LW's linear form with `u = ±ia, 0`.)
* Gelfond–Schneider (real form): `2^√2`; `log 3 / log 2` is transcendental (if it were algebraic
  it would be irrational by unique factorization, and then `2^{log 3/log 2} = 3` contradicts GS).
* Nesterenko: `e^π`, `π + e^π`, `π·e^π`, `Γ(1/4)` transcendental; `e^{-π/2}` (`= i^i`).

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Lindemann
import LeanFormalizations.Literature.GelfondSchneider
import LeanFormalizations.Literature.Nesterenko
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.Bedrock

open LeanFormalizations.Literature LeanFormalizations

/-! ## Lindemann–Weierstrass -/

theorem transcendental_cexp_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℂ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Complex.exp a) := by
  sorry

theorem transcendental_log_of_algebraic (hL : LindemannWeierstrassAlgIndep) {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hpos : 0 < α) (h1 : α ≠ 1) : Transcendental ℚ (Real.log α) := by
  sorry

theorem transcendental_sin_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.sin a) := by
  sorry

theorem transcendental_cos_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.cos a) := by
  sorry

/-! ## Gelfond–Schneider -/

theorem transcendental_two_rpow_sqrt_two (hGS : GelfondSchneider1934) :
    Transcendental ℚ ((2 : ℝ) ^ Real.sqrt 2) := by
  refine hGS 2 (Real.sqrt 2) (by norm_num) (by norm_num) ?_ ?_ irrational_sqrt_two
  · exact isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 2
  · refine (isAlgebraic_iff_isIntegral).2 ?_
    refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
    · monicity!
    · simp [Real.sq_sqrt]

/-- `log 2` and `log 3` are `ℚ`-linearly independent (unique factorization), so their ratio is
irrational. -/
theorem irrational_log_three_div_log_two : Irrational (Real.log 3 / Real.log 2) := by
  have hp : Function.Injective (![(⟨2, Nat.prime_two⟩ : Nat.Primes), ⟨3, Nat.prime_three⟩]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact absurd hij (by decide))
  have hli := Schanuel.linearIndependent_log_primes _ hp
  have hli2 : LinearIndependent ℚ ![Real.log 2, Real.log 3] := by
    convert hli using 1
    funext i
    fin_cases i <;> norm_num
  rw [LinearIndependent.pair_iff] at hli2
  have hne2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  rintro ⟨q, hq⟩
  have hrel : (q : ℝ) * Real.log 2 + (-1 : ℚ) • Real.log 3 = 0 := by
    have : Real.log 3 = (q : ℝ) * Real.log 2 := by
      field_simp at hq; linarith [hq]
    simp [this]
  have := hli2 q (-1) (by simpa [Rat.smul_def] using hrel)
  exact absurd this.2 (by norm_num)

/-- `log 3 / log 2` is transcendental: it is irrational, so if it were algebraic then
Gelfond–Schneider would make `2 ^ (log 3 / log 2) = 3` transcendental. -/
theorem transcendental_log_three_div_log_two (hGS : GelfondSchneider1934) :
    Transcendental ℚ (Real.log 3 / Real.log 2) := by
  intro halg
  have hpow : (2 : ℝ) ^ (Real.log 3 / Real.log 2) = 3 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [mul_div_assoc']
    rw [mul_comm, mul_div_assoc, div_self (by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); intro h; linarith), mul_one]
    exact Real.exp_log (by norm_num)
  have := hGS 2 (Real.log 3 / Real.log 2) (by norm_num) (by norm_num)
    (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 2) halg irrational_log_three_div_log_two
  rw [hpow] at this
  exact this (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 3)

/-! ## Nesterenko -/

/-! ### Leaves -/

open Complex in
/-- `π` and `e^π`, as complex numbers, are algebraically independent (from Nesterenko). -/
theorem algebraicIndependent_pi_exp_pi_complex_of_nesterenko (hN : Nesterenko1996) :
    AlgebraicIndependent ℚ ![(Real.pi : ℂ), ((Real.exp Real.pi : ℝ) : ℂ)] := by
  have hinj : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by decide
  have h2 := hN.comp _ hinj
  have h3 := h2.map' (f := IsScalarTower.toAlgHom ℚ ℝ ℂ)
    (IsScalarTower.toAlgHom ℚ ℝ ℂ).injective
  convert h3 using 1
  funext i
  fin_cases i <;> rfl

theorem transcendental_exp_pi (hN : Nesterenko1996) : Transcendental ℚ (Real.exp Real.pi) := by
  simpa using hN.transcendental 1

theorem transcendental_pi_add_exp_pi (hN : Nesterenko1996) :
    Transcendental ℚ (Real.pi + Real.exp Real.pi) := by
  intro h
  refine Schanuel.not_isAlgebraic_of_algebraicIndependent_pair
    (algebraicIndependent_pi_exp_pi_complex_of_nesterenko hN) ?_
  have hC : IsAlgebraic ℚ ((Real.pi : ℂ) + ((Real.exp Real.pi : ℝ) : ℂ)) := by
    simpa using Schanuel.isAlgebraic_complex_of_real h
  have hrw : ((Real.exp Real.pi : ℝ) : ℂ)
      = ((Real.pi : ℂ) + ((Real.exp Real.pi : ℝ) : ℂ)) - (Real.pi : ℂ) := by ring
  rw [hrw]
  exact Schanuel.isAlgebraic_sub_rat hC
    (isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ ({(Real.pi : ℂ)} : Set ℂ))
      (A := ℂ) ⟨_, IntermediateField.subset_adjoin _ _ rfl⟩)

theorem transcendental_pi_mul_exp_pi (hN : Nesterenko1996) :
    Transcendental ℚ (Real.pi * Real.exp Real.pi) := by
  intro h
  refine Schanuel.not_isAlgebraic_of_algebraicIndependent_pair
    (algebraicIndependent_pi_exp_pi_complex_of_nesterenko hN) ?_
  have hC : IsAlgebraic ℚ ((Real.pi : ℂ) * ((Real.exp Real.pi : ℝ) : ℂ)) := by
    simpa using Schanuel.isAlgebraic_complex_of_real h
  have hne : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hrw : ((Real.exp Real.pi : ℝ) : ℂ)
      = ((Real.pi : ℂ) * ((Real.exp Real.pi : ℝ) : ℂ)) / (Real.pi : ℂ) := by
    field_simp
  rw [hrw]
  exact Schanuel.isAlgebraic_div_rat hC
    (isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ ({(Real.pi : ℂ)} : Set ℂ))
      (A := ℂ) ⟨_, IntermediateField.subset_adjoin _ _ rfl⟩)

theorem transcendental_gamma_quarter (hN : Nesterenko1996) :
    Transcendental ℚ (Real.Gamma (1 / 4)) := by
  simpa using hN.transcendental 2

/-- `i^i = e^{-π/2}` is transcendental: its square is `1/e^π`, so if it were algebraic then
`e^π` would be too. -/
theorem transcendental_exp_neg_pi_div_two (hN : Nesterenko1996) :
    Transcendental ℚ (Real.exp (-(Real.pi / 2))) := by
  intro h
  refine transcendental_exp_pi hN ?_
  have hsq : Real.exp (-(Real.pi / 2)) ^ 2 = (Real.exp Real.pi)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    ring_nf
  have h2 : IsAlgebraic ℚ (Real.exp (-(Real.pi / 2)) ^ 2) := h.pow 2
  rw [hsq] at h2
  simpa using h2.inv

end LeanFormalizations.Bedrock
