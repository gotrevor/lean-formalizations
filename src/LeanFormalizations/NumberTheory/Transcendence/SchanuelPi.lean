/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Schanuel ⇒ `log π`, `π^e`, `π^π` (phase 23)

Conditional on `SchanuelConjecture`.  None of these is known unconditionally; even the
irrationality of `π^e` is open.  Pattern: bootstrap Schanuel twice.

1. `z = (1, iπ, log π)`, with exponentials `e, −1, π`.  Here `1, iπ, log π` are `ℚ`-linearly
   independent (`log π` is real and irrational, since `π` is transcendental, and `iπ` is purely
   imaginary), so `trdeg ℚ(π, log π, e) ≥ 3`: **`e, π, log π` are algebraically independent.**
2. `z = (1, iπ, log π, e·log π)`, with exponentials `e, −1, π, π^e`.  Linear independence of the `z` over
   `ℚ` follows from step 1 (a relation would put `log π ∈ ℚ(e)`).  Hence `trdeg ℚ(e, π, log π, π^e) ≥ 4`,
   and **`π^e` is transcendental**, indeed algebraically independent from `e, π, log π`.
3. The same with `π·log π`: **`π^π` is transcendental.**

Frozen: the statements below, every earlier name, all of `Literature/`.

## What the proof actually needed (phase 23, done)

* **Step 0 is the only real obstruction.**  `ℚ`-linear independence of `(1, iπ, log π)` needs
  `log π` *irrational*, which is open unconditionally.  `irrational_log_pi` gets it from
  Schanuel's own `e, π` independence (phase 15): if `log π = q = n/d` then `π^d = e^n`, so `π` is
  a root of `X^d − C (e^n)` over `ℚ(e)` — use `Polynomial.monic_X_pow_sub_C` for `≠ 0` and
  `map_zpow₀` to push the coefficient through `algebraMap ℚ⟮e⟯ ℂ`.
* **Step 2's linear independence is where step 1 gets spent.**  A relation
  `a + b·iπ + c·log π + d·c₀·log π = 0` has `b = 0` (imaginary part), and then either
  `c + d·c₀ ≠ 0`, which puts `log π = −a/(c + d·c₀) ∈ ℚ(c₀)` and contradicts the *pair*
  `(c₀, log π)` from step 1, or `c + d·c₀ = 0`, which forces `d = c = 0` by irrationality of
  `c₀`.  So `linearIndependent_quad` is uniform in `c₀ ∈ {e, π}`; only the membership
  `c₀ ∈ ℚ(e, π, log π, π^{c₀})` needs the case split (`hc2`).
* `algebraicIndependent_pi_rpow` is the shared second bootstrap: `z = (1, iπ, log π, c₀ log π)`,
  exponentials `e, −1, π, π^{c₀}`, via `Real.rpow_def_of_pos`.

Gotchas: `Fintype.linearIndependent_iff` + `Fin.sum_univ_three/four` + `Rat.smul_def`, then
`simp at him hre` already *solves* the imaginary part to `g 1 = 0` (no disjunction to `rcases`);
`algebraMap_mem` is ambiguous under `open IntermediateField`, spell
`IntermediateField.algebraMap_mem`; `field_simp` on the `log π = −a/(…)` goal produces a
doubled-up target, so `rw [eq_div_iff]` + `linear_combination` instead.
-/
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.Schanuel

open LeanFormalizations.Literature
open Complex IntermediateField Algebra Set

/-! ## Step 0: `log π` is irrational (conditionally) -/

/-- If `log π` were rational, `π` would be algebraic over `ℚ(e)`, contradicting Schanuel's
`e, π` independence.  (Irrationality of `log π` is open unconditionally.) -/
theorem irrational_log_pi (hS : SchanuelConjecture) : Irrational (Real.log Real.pi) := by
  rintro ⟨q, hq⟩
  refine not_isAlgebraic_of_algebraicIndependent_pair
    (algebraicIndependent_exp_one_pi_complex hS) ?_
  set K := IntermediateField.adjoin ℚ ({Complex.exp 1} : Set ℂ) with hK
  have hmem : Complex.exp 1 ∈ K := subset_adjoin _ _ rfl
  -- `π = exp q` in `ℂ`
  have hpi : ((Real.pi : ℝ) : ℂ) = Complex.exp ((q : ℝ) : ℂ) := by
    rw [hq, ← Complex.ofReal_exp, Real.exp_log Real.pi_pos]
  have hd : (q.den : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    rw [Rat.cast_def]
    field_simp
  have hpow : ((Real.pi : ℝ) : ℂ) ^ (q.den) = Complex.exp 1 ^ (q.num : ℤ) := by
    rw [hpi, ← Complex.exp_nat_mul]
    push_cast at hd ⊢
    rw [hd, ← Complex.exp_int_mul]
    ring_nf
  set a : K := (⟨Complex.exp 1, hmem⟩ : K) ^ (q.num : ℤ) with ha
  refine ⟨Polynomial.X ^ q.den - Polynomial.C a, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C a q.pos.ne').ne_zero
  · have hav : (algebraMap K ℂ) a = Complex.exp 1 ^ (q.num : ℤ) := by
      rw [ha, map_zpow₀]; rfl
    simp [Polynomial.aeval_def, hav, hpow]

/-! ## Step 1: `e, π, log π` are algebraically independent -/

/-- `1, iπ, log π` are `ℚ`-linearly independent. -/
theorem linearIndependent_one_I_mul_pi_log_pi (hS : SchanuelConjecture) :
    LinearIndependent ℚ ![(1 : ℂ), Complex.I * (Real.pi : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def] at hg
  have him := congrArg Complex.im hg
  have hre := congrArg Complex.re hg
  simp at him hre
  have h1 : g 1 = 0 := him
  have h2 : g 2 = 0 := by
    by_contra hne
    apply (irrational_log_pi hS).ne_rat (-(g 0) / g 2)
    push_cast
    field_simp
    linarith [hre]
  have h0 : g 0 = 0 := by rw [h2] at hre; simpa using hre
  intro i; fin_cases i <;> assumption

/-- Auxiliary: `exp (log π) = π` over `ℂ`. -/
theorem cexp_ofReal_log_pi : Complex.exp ((Real.log Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log Real.pi_pos]

/-- Schanuel ⇒ `e`, `π`, `log π` are algebraically independent, complex form.
Apply Schanuel to `z = (1, iπ, log π)`, whose exponentials are `e`, `−1`, `π`. -/
theorem algebraicIndependent_exp_one_pi_log_pi_complex (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] := by
  set y : Fin 3 → ℂ :=
    ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] with hy
  refine algebraicIndependent_of_schanuel hS _ (linearIndependent_one_I_mul_pi_log_pi hS) y ?_
  set L := IntermediateField.adjoin ℚ (Set.range y) with hL
  have m0 : ((Real.exp 1 : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨0, rfl⟩
  have m1 : ((Real.pi : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨1, rfl⟩
  have m2 : ((Real.log Real.pi : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨2, rfl⟩
  rintro w (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · fin_cases i
    · exact isAlgebraic_one
    · exact isAlgebraic_mul_rat isAlgebraic_I
        (isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m1⟩)
    · exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m2⟩
  · fin_cases i
    · show IsAlgebraic _ (Complex.exp 1)
      rw [show Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) by simp]
      exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m0⟩
    · show IsAlgebraic _ (Complex.exp (Complex.I * (Real.pi : ℂ)))
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_mul_I]
      simpa using (isAlgebraic_algebraMap (R := L) (A := ℂ) (-1))
    · show IsAlgebraic _ (Complex.exp ((Real.log Real.pi : ℝ) : ℂ))
      rw [cexp_ofReal_log_pi]
      exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m1⟩

theorem algebraicIndependent_exp_one_pi_log_pi_real (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.exp 1, Real.pi, Real.log Real.pi] := by
  refine algebraicIndependent_real_of_complex ?_
  have h := algebraicIndependent_exp_one_pi_log_pi_complex hS
  have hcomp : (fun i => ((![Real.exp 1, Real.pi, Real.log Real.pi] i : ℝ) : ℂ))
      = ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hcomp]; exact h

theorem transcendental_log_pi_real (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.log Real.pi) :=
  (algebraicIndependent_exp_one_pi_log_pi_real hS).transcendental 2

/-! ## Step 2: the second bootstrap, `π^c` for `c ∈ {e, π}` -/

/-- The pair `(e, log π)` extracted from the step-1 triple. -/
theorem algebraicIndependent_pair_exp_one_log_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![((Real.exp 1 : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] := by
  have h := (algebraicIndependent_exp_one_pi_log_pi_complex hS).comp
    (![0, 2] : Fin 2 → Fin 3) (by decide)
  convert h using 1
  funext j; fin_cases j <;> rfl

/-- The pair `(π, log π)` extracted from the step-1 triple. -/
theorem algebraicIndependent_pair_pi_log_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)] := by
  have h := (algebraicIndependent_exp_one_pi_log_pi_complex hS).comp
    (![1, 2] : Fin 2 → Fin 3) (by decide)
  convert h using 1
  funext j; fin_cases j <;> rfl

/-- `1, iπ, log π, c·log π` are `ℚ`-linearly independent, for `c` an irrational real with
`(c, log π)` algebraically independent. -/
theorem linearIndependent_quad (_hS : SchanuelConjecture) {c : ℝ} (hc : Irrational c)
    (hpair : AlgebraicIndependent ℚ ![((c : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ)]) :
    LinearIndependent ℚ ![(1 : ℂ), Complex.I * (Real.pi : ℂ), ((Real.log Real.pi : ℝ) : ℂ),
      ((c : ℝ) : ℂ) * ((Real.log Real.pi : ℝ) : ℂ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Rat.smul_def] at hg
  have him := congrArg Complex.im hg
  have hre := congrArg Complex.re hg
  simp at him hre
  have h1 : g 1 = 0 := him
  -- real part: `g0 + (g2 + g3 c) · log π = 0`
  have hkey : (g 0 : ℝ) + ((g 2 : ℝ) + (g 3 : ℝ) * c) * Real.log Real.pi = 0 := by
    ring_nf; ring_nf at hre; linarith [hre]
  have hcoef : (g 2 : ℝ) + (g 3 : ℝ) * c = 0 := by
    by_contra hne
    refine not_isAlgebraic_of_algebraicIndependent_pair hpair ?_
    set K := IntermediateField.adjoin ℚ ({((c : ℝ) : ℂ)} : Set ℂ) with hK
    have hmem : ((c : ℝ) : ℂ) ∈ K := subset_adjoin _ _ rfl
    have hden : ((g 2 : ℂ) + (g 3 : ℂ) * ((c : ℝ) : ℂ)) ∈ K := by
      exact add_mem (IntermediateField.algebraMap_mem K _)
        (mul_mem (IntermediateField.algebraMap_mem K _) hmem)
    have heq : ((Real.log Real.pi : ℝ) : ℂ)
        = (-(g 0 : ℂ)) / ((g 2 : ℂ) + (g 3 : ℂ) * ((c : ℝ) : ℂ)) := by
      have hne' : ((g 2 : ℂ) + (g 3 : ℂ) * ((c : ℝ) : ℂ)) ≠ 0 := by
        intro h0
        apply hne
        have := congrArg Complex.re h0
        simpa using this
      have hC : ((g 0 : ℂ)) + ((g 2 : ℂ) + (g 3 : ℂ) * ((c : ℝ) : ℂ))
          * ((Real.log Real.pi : ℝ) : ℂ) = 0 := by
        have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hkey
        push_cast at this
        linear_combination this
      rw [eq_div_iff hne']
      linear_combination hC
    rw [heq]
    exact isAlgebraic_div_rat
      (by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-(g 0)))
      (isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, hden⟩)
  have h3 : g 3 = 0 := by
    by_contra hne
    apply hc.ne_rat (-(g 2) / g 3)
    push_cast
    field_simp
    linarith [hcoef]
  have h2 : g 2 = 0 := by
    rw [h3] at hcoef; simpa using hcoef
  have h0 : g 0 = 0 := by
    rw [h2, h3] at hkey; simpa using hkey
  intro i; fin_cases i <;> assumption

/-- The second Schanuel bootstrap: `z = (1, iπ, log π, c log π)`, exponentials
`e, −1, π, π^c`. -/
theorem algebraicIndependent_pi_rpow (hS : SchanuelConjecture) {c : ℝ}
    (hc2 : c = Real.exp 1 ∨ c = Real.pi)
    (hlin : LinearIndependent ℚ ![(1 : ℂ), Complex.I * (Real.pi : ℂ),
      ((Real.log Real.pi : ℝ) : ℂ), ((c : ℝ) : ℂ) * ((Real.log Real.pi : ℝ) : ℂ)]) :
    AlgebraicIndependent ℚ
      ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ),
        ((Real.pi ^ c : ℝ) : ℂ)] := by
  set y : Fin 4 → ℂ :=
    ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ),
      ((Real.pi ^ c : ℝ) : ℂ)] with hy
  refine algebraicIndependent_of_schanuel hS _ hlin y ?_
  set L := IntermediateField.adjoin ℚ (Set.range y) with hL
  have m0 : ((Real.exp 1 : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨0, rfl⟩
  have m1 : ((Real.pi : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨1, rfl⟩
  have m2 : ((Real.log Real.pi : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨2, rfl⟩
  have m3 : ((Real.pi ^ c : ℝ) : ℂ) ∈ L := subset_adjoin _ _ ⟨3, rfl⟩
  have mc : ((c : ℝ) : ℂ) ∈ L := by
    rcases hc2 with h | h <;> subst h <;> assumption
  have hrpow : Complex.exp (((c : ℝ) : ℂ) * ((Real.log Real.pi : ℝ) : ℂ))
      = ((Real.pi ^ c : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Real.rpow_def_of_pos Real.pi_pos, mul_comm]
  rintro w (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · fin_cases i
    · exact isAlgebraic_one
    · exact isAlgebraic_mul_rat isAlgebraic_I
        (isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m1⟩)
    · exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m2⟩
    · exact isAlgebraic_algebraMap (R := L) (A := ℂ)
        ⟨_, mul_mem mc m2⟩
  · fin_cases i
    · show IsAlgebraic _ (Complex.exp 1)
      rw [show Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) by simp]
      exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m0⟩
    · show IsAlgebraic _ (Complex.exp (Complex.I * (Real.pi : ℂ)))
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_mul_I]
      simpa using (isAlgebraic_algebraMap (R := L) (A := ℂ) (-1))
    · show IsAlgebraic _ (Complex.exp ((Real.log Real.pi : ℝ) : ℂ))
      rw [cexp_ofReal_log_pi]
      exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m1⟩
    · show IsAlgebraic _ (Complex.exp (((c : ℝ) : ℂ) * ((Real.log Real.pi : ℝ) : ℂ)))
      rw [hrpow]
      exact isAlgebraic_algebraMap (R := L) (A := ℂ) ⟨_, m3⟩


/-! ## The five frozen statements -/

theorem algebraicIndependent_exp_one_pi_log_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.exp 1, Real.pi, Real.log Real.pi] :=
  algebraicIndependent_exp_one_pi_log_pi_real hS

theorem transcendental_log_pi (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.log Real.pi) :=
  transcendental_log_pi_real hS

theorem algebraicIndependent_pi_rpow_exp_one (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![Real.exp 1, Real.pi, Real.log Real.pi, Real.pi ^ Real.exp 1] := by
  refine algebraicIndependent_real_of_complex ?_
  have h := algebraicIndependent_pi_rpow hS (c := Real.exp 1) (Or.inl rfl)
    (linearIndependent_quad hS
      LeanFormalizations.Transcendence.e_transcendental.irrational
      (algebraicIndependent_pair_exp_one_log_pi hS))
  have hcomp : (fun i =>
      ((![Real.exp 1, Real.pi, Real.log Real.pi, Real.pi ^ Real.exp 1] i : ℝ) : ℂ))
      = ![((Real.exp 1 : ℝ) : ℂ), ((Real.pi : ℝ) : ℂ), ((Real.log Real.pi : ℝ) : ℂ),
          ((Real.pi ^ Real.exp 1 : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hcomp]; exact h

theorem transcendental_pi_rpow_exp_one (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.pi ^ Real.exp 1) :=
  (algebraicIndependent_pi_rpow_exp_one hS).transcendental 3

theorem transcendental_pi_rpow_pi (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.pi ^ Real.pi) := by
  have h := algebraicIndependent_pi_rpow hS (c := Real.pi) (Or.inr rfl)
    (linearIndependent_quad hS irrational_pi (algebraicIndependent_pair_pi_log_pi hS))
  have := h.transcendental 3
  simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
  intro hcon
  exact this ((isAlgebraic_complex_of_real hcon))

end LeanFormalizations.Schanuel
