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

## Result (phase 21, 2026-09-29): all eleven are PROVED and `#print axioms`-clean.

Routes actually taken, and the gotchas:

* **Hermite–Lindemann.**  The key move is to keep the conclusion *over the algebraic numbers*:
  `transcendental_algClosure_cexp` gives `Transcendental (integralClosure ℚ ℂ) (exp a)`, and
  `transcendental_cexp_of_algebraic` is its `Transcendental.restrictScalars`.  The strong form is
  what makes `sin`/`cos` one-liners: `e^{ia}` is a root of `X² − 2(cos a)X + 1` resp.
  `X² − 2i(sin a)X − 1`, whose coefficients are algebraic but *not* rational, so a
  `Transcendental ℚ` statement would not contradict them.  Feeding LW needs
  `LinearIndependent ℕ` of a one-element family; `linearIndependent_unique_iff` is stated for
  domains-with-subtraction, so `linearIndependent_nat_single` does it by hand (cancel `a`, then
  `CharZero`).
* `log α`: if `log α` were algebraic and nonzero, `e^{log α} = α` would be transcendental.
* **Gelfond–Schneider.**  `2^√2` is a direct instance.  For `log 3 / log 2` the irrationality
  input is *not* re-derived: `Schanuel.linearIndependent_log_primes` at `![2,3]` gives it, and
  then `2^{log 3/log 2} = 3` contradicts GS.
* **Nesterenko.**  `π, e^π` are extracted from the triple by `.comp ![0,1]` and pushed to `ℂ`
  with `AlgebraicIndependent.map'` (note: `map'` takes the injectivity of an `AlgHom` directly,
  unlike `LinearIndependent.map'`, which takes a `ker = ⊥` proof).  Sum and product then reuse
  `Schanuel.not_isAlgebraic_of_algebraicIndependent_pair` verbatim from the `e + π` proofs;
  `Γ(1/4)` and `e^π` are single coordinates; `e^{−π/2}` squares to `(e^π)⁻¹`.
-/
import LeanFormalizations.Literature.Lindemann
import LeanFormalizations.Literature.GelfondSchneider
import LeanFormalizations.Literature.Nesterenko
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.Bedrock

open LeanFormalizations.Literature LeanFormalizations

/-! ## Lindemann–Weierstrass -/

/-! ### Leaves -/

/-- A single nonzero element of the algebraic numbers is `ℕ`-linearly independent.  (`ℕ` is not
a domain-with-subtraction, so `linearIndependent_unique_iff` does not apply; injectivity of
`n ↦ n • a` is proved by hand from `CharZero`.) -/
theorem linearIndependent_nat_single {a : integralClosure ℚ ℂ} (ha : a ≠ 0) :
    LinearIndependent ℕ (fun _ : Unit => a) := by
  intro l m h
  simp only [Finsupp.linearCombination_unique] at h
  have hc : ((l default : ℕ) : integralClosure ℚ ℂ) * a
      = ((m default : ℕ) : integralClosure ℚ ℂ) * a := by
    simpa [nsmul_eq_mul] using h
  have hcast := mul_right_cancel₀ ha hc
  have hn : (l default : ℕ) = m default := by exact_mod_cast hcast
  refine Finsupp.ext fun i => ?_
  obtain rfl : i = default := Subsingleton.elim _ _
  exact hn

/-- A root of a monic quadratic with algebraic-number coefficients is algebraic over them. -/
theorem isAlgebraic_of_quad {K : Type} [CommRing K] [Nontrivial K] [Algebra K ℂ] {z : ℂ}
    (b d : K) (h : z ^ 2 + (algebraMap K ℂ b) * z + (algebraMap K ℂ d) = 0) :
    IsAlgebraic K z := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C d, ?_, by simpa using h⟩
  intro hzero
  have hco := congrArg (fun q => Polynomial.coeff q 2) hzero
  simp at hco

/-- The algebraic closure of `ℚ` in `ℂ`, as an algebra, has injective structure map from `ℚ`. -/
theorem algebraMap_rat_integralClosure_injective :
    Function.Injective (algebraMap ℚ (integralClosure ℚ ℂ)) :=
  (algebraMap ℚ (integralClosure ℚ ℂ)).injective

/-- **Hermite–Lindemann, strong form.**  For algebraic `a ≠ 0`, `e^a` is transcendental *over the
algebraic numbers* — this is the form the `sin`/`cos` arguments need, because there the witness
polynomial has algebraic (not rational) coefficients. -/
theorem transcendental_algClosure_cexp (hL : LindemannWeierstrassAlgIndep) {a : ℂ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) :
    Transcendental (integralClosure ℚ ℂ) (Complex.exp a) := by
  have hmem : IsIntegral ℚ a := ha.isIntegral
  have hne : (⟨a, hmem⟩ : integralClosure ℚ ℂ) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff]
    simpa using h0
  exact (hL (fun _ : Unit => (⟨a, hmem⟩ : integralClosure ℚ ℂ))
    (linearIndependent_nat_single hne)).transcendental default

/-! ### The four statements -/

theorem transcendental_cexp_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℂ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Complex.exp a) :=
  (transcendental_algClosure_cexp hL ha h0).restrictScalars
    algebraMap_rat_integralClosure_injective

theorem transcendental_log_of_algebraic (hL : LindemannWeierstrassAlgIndep) {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hpos : 0 < α) (h1 : α ≠ 1) : Transcendental ℚ (Real.log α) := by
  intro h
  have hlog0 : Real.log α ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos h1
  have hC : IsAlgebraic ℚ ((Real.log α : ℝ) : ℂ) := Schanuel.isAlgebraic_complex_of_real h
  have h0 : ((Real.log α : ℝ) : ℂ) ≠ 0 := by
    simpa using hlog0
  refine transcendental_cexp_of_algebraic hL hC h0 ?_
  rw [← Complex.ofReal_exp, Real.exp_log hpos]
  exact Schanuel.isAlgebraic_complex_of_real hα

open Complex in
/-- The common core of `sin` and `cos`: `e^{ia}` is transcendental over the algebraic numbers,
so it cannot satisfy a monic quadratic with algebraic coefficients. -/
theorem not_quad_cexp_I_mul (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) (b d : integralClosure ℚ ℂ)
    (h : Complex.exp ((a : ℂ) * I) ^ 2
      + (algebraMap (integralClosure ℚ ℂ) ℂ b) * Complex.exp ((a : ℂ) * I)
      + (algebraMap (integralClosure ℚ ℂ) ℂ d) = 0) : False := by
  have haI : IsAlgebraic ℚ ((a : ℂ) * I) :=
    (((Schanuel.isAlgebraic_complex_of_real ha).isIntegral).mul
      (Schanuel.isAlgebraic_I.isIntegral)).isAlgebraic
  have hne : ((a : ℂ) * I) ≠ 0 := by
    simp [Complex.ext_iff, h0]
  exact transcendental_algClosure_cexp hL haI hne (isAlgebraic_of_quad b d h)

open Complex in
theorem transcendental_sin_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.sin a) := by
  intro h
  set z := Complex.exp ((a : ℂ) * I) with hzdef
  have hsmem : ((Real.sin a : ℝ) : ℂ) ∈ integralClosure ℚ ℂ :=
    (Schanuel.isAlgebraic_complex_of_real h).isIntegral
  have hImem : (I : ℂ) ∈ integralClosure ℚ ℂ := Schanuel.isAlgebraic_I.isIntegral
  refine not_quad_cexp_I_mul hL ha h0
    (-(2 * (⟨_, hsmem⟩ : integralClosure ℚ ℂ) * ⟨I, hImem⟩)) (-1) ?_
  have hb : (algebraMap (integralClosure ℚ ℂ) ℂ)
      (-(2 * (⟨_, hsmem⟩ : integralClosure ℚ ℂ) * ⟨I, hImem⟩))
      = -(2 * ((Real.sin a : ℝ) : ℂ) * I) := by
    simp only [map_neg, map_mul, map_ofNat]; rfl
  have hd : (algebraMap (integralClosure ℚ ℂ) ℂ) (-1 : integralClosure ℚ ℂ) = -1 := by simp
  rw [hb, hd]
  have hz : z * Complex.exp (-(a : ℂ) * I) = 1 := by
    rw [hzdef, ← Complex.exp_add]
    ring_nf
    simp
  have hs : 2 * ((Real.sin a : ℝ) : ℂ)
      = (Complex.exp (-(a : ℂ) * I) - Complex.exp ((a : ℂ) * I)) * I := by
    rw [Complex.ofReal_sin]
    exact Complex.two_sin _
  rw [← hzdef] at hs
  linear_combination (-I * z) * hs + hz
    + (z ^ 2 - z * Complex.exp (-(a : ℂ) * I)) * Complex.I_sq

open Complex in
theorem transcendental_cos_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.cos a) := by
  intro h
  set z := Complex.exp ((a : ℂ) * I) with hzdef
  have hcmem : ((Real.cos a : ℝ) : ℂ) ∈ integralClosure ℚ ℂ :=
    (Schanuel.isAlgebraic_complex_of_real h).isIntegral
  refine not_quad_cexp_I_mul hL ha h0
    (-(2 * (⟨_, hcmem⟩ : integralClosure ℚ ℂ))) 1 ?_
  have hb : (algebraMap (integralClosure ℚ ℂ) ℂ) (-(2 * (⟨_, hcmem⟩ : integralClosure ℚ ℂ)))
      = -(2 * ((Real.cos a : ℝ) : ℂ)) := by
    simp only [map_neg, map_mul, map_ofNat]; rfl
  have hd : (algebraMap (integralClosure ℚ ℂ) ℂ) (1 : integralClosure ℚ ℂ) = 1 := by simp
  rw [hb, hd]
  have hz : z * Complex.exp (-(a : ℂ) * I) = 1 := by
    rw [hzdef, ← Complex.exp_add]
    ring_nf
    simp
  have hc : 2 * ((Real.cos a : ℝ) : ℂ)
      = Complex.exp ((a : ℂ) * I) + Complex.exp (-(a : ℂ) * I) := by
    rw [Complex.ofReal_cos]
    exact Complex.two_cos _
  rw [← hzdef] at hc
  linear_combination (-z) * hc - hz

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
