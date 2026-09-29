/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# More bedrock: Lindemann–Weierstrass odds and ends, and Baker (phase 22)

Unconditional, like `Bedrock.lean`.  Inputs: `LindemannWeierstrassAlgIndep`, `BakerHomogeneous`
(`Literature/Waldschmidt2023.lean`, `ℚ̄`-linear independence of `1, λ₁, …, λₙ`, checked against
the rendered survey page 4) and `Baker1966` (inhomogeneous).

* LW: `tan a`, `sinh a`, `cosh a` for nonzero algebraic real `a`.
* Baker, the survey's own example (p. 4): `λ₁ = log 2` and `λ₂ = log 2 + 2πi` are `ℚ`-linearly
  independent logarithms of `2`, so `1, log 2, πi` are `ℚ̄`-linearly independent.  Hence
  **`π + log 2` is transcendental**: if it equalled an algebraic `β`, then `β = log 2 + (λ₂−λ₁)/(2i)`
  would be a nontrivial `ℚ̄`-relation among `1, λ₁, λ₂`.
* Baker: **`2^{√2}·3^{√3}` is transcendental**.  If it equalled an algebraic `γ`, then
  `√2 log 2 + √3 log 3 − log γ = 0`; take a `ℚ`-basis of `log 2, log 3, log γ` and apply
  `BakerHomogeneous` (the coefficients `√2, √3` are algebraic and `1, √2, √3` are `ℚ`-independent).

Frozen: the statements below, every earlier name, all of `Literature/`.

## Result (phase 22, 2026-09-29): all five are PROVED and `#print axioms`-clean.

Routes actually taken, and the gotchas:

* **`sinh`/`cosh`.**  Exactly the `sin`/`cos` pattern of `Bedrock.lean`, with the real-exponential
  leaf `not_quad_cexp_real`: `z = e^a` satisfies `z² − 2(sinh a)z − 1 = 0` resp.
  `z² − 2(cosh a)z + 1 = 0`, whose coefficients are algebraic, so the *strong* Hermite–Lindemann
  (`transcendental_algClosure_cexp`, transcendence over `ℚ̄`) is what contradicts.
* **`tan`.**  Not a quadratic in `e^{ia}` — it is a *linear* relation in `z² = e^{2ia}`:
  `z²(t + i) = i − t`, so `z² = (i−t)/(t+i)` is algebraic **over `ℚ`**, and the weak form
  `transcendental_cexp_of_algebraic` at `2ai` suffices.  `t + i ≠ 0` because `t` is real.
  Note `Real.tan a = sin a / cos a` is `0` when `cos a = 0`, so `cos a ≠ 0` has to be established
  first — it follows from `transcendental_cos_of_algebraic` (`0` is algebraic).
* **Baker leaf.**  `baker_relation` repackages `BakerHomogeneous` through
  `Fintype.linearIndependent_iff` + `Algebra.smul_def`, so applications only have to exhibit
  coefficients in `integralClosure ℚ ℂ` and a `∑ (cᵢ : ℂ) * (Fin.cons 1 ℓ) i = 0`.
* **`π + log 2`.**  With `λ₀ = log 2`, `λ₁ = log 2 + 2πi` (`logTwoPair`, both exponentials `= 2`,
  `ℚ`-independent by imaginary parts), the relation is `−2β·1 + (2+i)λ₀ + (−i)λ₁ = 0`; scaling by
  `2` avoids ever dividing inside the subalgebra.  `i ≠ 0` kills it.  Gotcha: `simp` rewrites
  `((Real.log 2 : ℝ) : ℂ)` to `Complex.log 2`, which destroys `Complex.ofReal_im`; the fix is to
  write the `2πi` term as `((2 * Real.pi : ℝ) : ℂ) * I` and use `simp only` with
  `Complex.mul_I_im`/`Complex.mul_I_re` rather than plain `simp`.
* **`2^√2·3^√3`.**  The third logarithm is `μ = √2 log 2 + √3 log 3` itself (`e^μ` is the number
  assumed algebraic), so no separate `log γ` is needed.  Case split on
  `LinearIndependent ℚ ![log 2, log 3, μ]`:
  - independent: Baker at `n = 3` and the relation `√2 log2 + √3 log3 − μ = 0` (coefficient `−1`);
  - dependent: the dependency must have `g₂ ≠ 0` (else it contradicts independence of
    `log 2, log 3`), so `μ ∈ ℚ-span`, giving `(g₀ + g₂√2)log2 + (g₁ + g₂√3)log3 = 0`; Baker at
    `n = 2` forces `g₁ + g₂√3 = 0`, i.e. `√3 ∈ ℚ`, contradiction.
-/
import LeanFormalizations.NumberTheory.Transcendence.Bedrock
import LeanFormalizations.Literature.Waldschmidt2023

namespace LeanFormalizations.Bedrock

open LeanFormalizations.Literature

/-! ### Leaves -/

open Complex in
/-- Real-exponential analogue of `not_quad_cexp_I_mul`: `e^a` for nonzero algebraic real `a` is
transcendental over the algebraic numbers, so it satisfies no monic quadratic over them. -/
theorem not_quad_cexp_real (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) (b d : integralClosure ℚ ℂ)
    (h : Complex.exp (a : ℂ) ^ 2
      + (algebraMap (integralClosure ℚ ℂ) ℂ b) * Complex.exp (a : ℂ)
      + (algebraMap (integralClosure ℚ ℂ) ℂ d) = 0) : False := by
  have haC : IsAlgebraic ℚ ((a : ℝ) : ℂ) := Schanuel.isAlgebraic_complex_of_real ha
  have hne : ((a : ℝ) : ℂ) ≠ 0 := by simpa using h0
  exact transcendental_algClosure_cexp hL haC hne (isAlgebraic_of_quad b d h)

/-! ### The statements -/

theorem transcendental_sinh_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.sinh a) := by
  intro h
  set z := Complex.exp (a : ℂ) with hzdef
  have hsmem : ((Real.sinh a : ℝ) : ℂ) ∈ integralClosure ℚ ℂ :=
    (Schanuel.isAlgebraic_complex_of_real h).isIntegral
  refine not_quad_cexp_real hL ha h0 (-(2 * (⟨_, hsmem⟩ : integralClosure ℚ ℂ))) (-1) ?_
  have hb : (algebraMap (integralClosure ℚ ℂ) ℂ) (-(2 * (⟨_, hsmem⟩ : integralClosure ℚ ℂ)))
      = -(2 * ((Real.sinh a : ℝ) : ℂ)) := by
    simp only [map_neg, map_mul, map_ofNat]; rfl
  have hd : (algebraMap (integralClosure ℚ ℂ) ℂ) (-1 : integralClosure ℚ ℂ) = -1 := by simp
  rw [hb, hd]
  have hz : z * Complex.exp (-(a : ℂ)) = 1 := by
    rw [hzdef, ← Complex.exp_add]; ring_nf; simp
  have hs : 2 * ((Real.sinh a : ℝ) : ℂ) = Complex.exp (a : ℂ) - Complex.exp (-(a : ℂ)) := by
    rw [Complex.ofReal_sinh]; exact Complex.two_sinh _
  rw [← hzdef] at hs
  linear_combination (-z) * hs + hz

theorem transcendental_cosh_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.cosh a) := by
  intro h
  set z := Complex.exp (a : ℂ) with hzdef
  have hcmem : ((Real.cosh a : ℝ) : ℂ) ∈ integralClosure ℚ ℂ :=
    (Schanuel.isAlgebraic_complex_of_real h).isIntegral
  refine not_quad_cexp_real hL ha h0 (-(2 * (⟨_, hcmem⟩ : integralClosure ℚ ℂ))) 1 ?_
  have hb : (algebraMap (integralClosure ℚ ℂ) ℂ) (-(2 * (⟨_, hcmem⟩ : integralClosure ℚ ℂ)))
      = -(2 * ((Real.cosh a : ℝ) : ℂ)) := by
    simp only [map_neg, map_mul, map_ofNat]; rfl
  have hd : (algebraMap (integralClosure ℚ ℂ) ℂ) (1 : integralClosure ℚ ℂ) = 1 := by simp
  rw [hb, hd]
  have hz : z * Complex.exp (-(a : ℂ)) = 1 := by
    rw [hzdef, ← Complex.exp_add]; ring_nf; simp
  have hc : 2 * ((Real.cosh a : ℝ) : ℂ) = Complex.exp (a : ℂ) + Complex.exp (-(a : ℂ)) := by
    rw [Complex.ofReal_cosh]; exact Complex.two_cosh _
  rw [← hzdef] at hc
  linear_combination (-z) * hc - hz

open Complex in
theorem transcendental_tan_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.tan a) := by
  intro h
  -- `cos a ≠ 0`, since `cos a` is transcendental.
  have hcos : Real.cos a ≠ 0 := by
    intro hc
    exact transcendental_cos_of_algebraic hL ha h0 (hc ▸ isAlgebraic_zero)
  have hst : Real.sin a = Real.tan a * Real.cos a := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  set t : ℂ := ((Real.tan a : ℝ) : ℂ) with htdef
  set z : ℂ := Complex.exp ((a : ℂ) * I) with hzdef
  set w : ℂ := Complex.exp (-(a : ℂ) * I) with hwdef
  have hzw : z * w = 1 := by
    rw [hzdef, hwdef, ← Complex.exp_add]; ring_nf; simp
  have hs : 2 * ((Real.sin a : ℝ) : ℂ) = (w - z) * I := by
    rw [Complex.ofReal_sin, hzdef, hwdef]; exact Complex.two_sin _
  have hc : 2 * ((Real.cos a : ℝ) : ℂ) = z + w := by
    rw [Complex.ofReal_cos, hzdef, hwdef]; exact Complex.two_cos _
  have hstC : ((Real.sin a : ℝ) : ℂ) = t * ((Real.cos a : ℝ) : ℂ) := by
    rw [htdef]; exact_mod_cast congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hst
  -- the key identity `z²(t + i) = i − t`
  have hkey : z ^ 2 * (t + I) = I - t := by
    linear_combination (-2 * z) * hstC + z * hs + (-t * z) * hc + (I - t) * hzw
  have htI : t + I ≠ 0 := by
    intro hcon
    have := congrArg Complex.im hcon
    simp [htdef] at this
  have hz2 : z ^ 2 = (I - t) / (t + I) := by
    field_simp [htI]; linear_combination hkey
  -- but `z² = e^{2ai}` is transcendental
  have hualg : IsAlgebraic ℚ ((2 * (a : ℂ)) * I) :=
    (((isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2).isIntegral.mul
      (Schanuel.isAlgebraic_complex_of_real ha).isIntegral).mul
        Schanuel.isAlgebraic_I.isIntegral).isAlgebraic
  have hune : ((2 * (a : ℂ)) * I) ≠ 0 := by
    simp [Complex.ext_iff, h0]
  refine transcendental_cexp_of_algebraic hL hualg hune ?_
  have hexp : Complex.exp ((2 * (a : ℂ)) * I) = z ^ 2 := by
    rw [hzdef, ← Complex.exp_nat_mul]; ring_nf
  rw [hexp, hz2]
  have htalg : IsAlgebraic ℚ t := Schanuel.isAlgebraic_complex_of_real h
  refine IsAlgebraic.mul ?_ (IsAlgebraic.inv ?_)
  · exact (Schanuel.isAlgebraic_I.isIntegral.sub htalg.isIntegral).isAlgebraic
  · exact (htalg.isIntegral.add Schanuel.isAlgebraic_I.isIntegral).isAlgebraic

/-! ## Baker -/

/-! ### Leaves -/

/-- Repackaged `BakerHomogeneous`: any `ℚ̄`-linear relation `c₀·1 + c₁λ₁ + ⋯ + cₙλₙ = 0` among
`1` and `ℚ`-independent logarithms of algebraic numbers is trivial. -/
theorem baker_relation (hB : BakerHomogeneous) {n : ℕ} (ℓ : Fin n → ℂ)
    (hli : LinearIndependent ℚ ℓ) (halg : ∀ i, IsAlgebraic ℚ (Complex.exp (ℓ i)))
    (c : Fin (n + 1) → integralClosure ℚ ℂ)
    (hsum : ∑ i, (c i : ℂ) * (Fin.cons (1 : ℂ) ℓ : Fin (n + 1) → ℂ) i = 0) :
    ∀ i, c i = 0 := by
  refine Fintype.linearIndependent_iff.1 (hB n ℓ hli halg) c ?_
  simpa [Algebra.smul_def] using hsum

/-- The two logarithms of `2` used by the survey's own Baker example: `log 2` and `log 2 + 2πi`. -/
noncomputable def logTwoPair : Fin 2 → ℂ :=
  ![((Real.log 2 : ℝ) : ℂ), ((Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I]

theorem exp_logTwoPair (i : Fin 2) : Complex.exp (logTwoPair i) = 2 := by
  have h2 : Complex.exp ((Real.log 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  fin_cases i
  · exact h2
  · show Complex.exp (((Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 2
    rw [Complex.exp_add, h2, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_two_pi_mul_I, mul_one]

theorem linearIndependent_logTwoPair : LinearIndependent ℚ logTwoPair := by
  have hlog2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by
    have := Real.pi_pos; positivity
  rw [linearIndependent_fin2]
  constructor
  · show ((Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0
    intro hcon
    have h := congrArg Complex.im hcon
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
      zero_add, Complex.zero_im] at h
    exact hpi h
  · rintro q hq
    have hq' : q • (((Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = ((Real.log 2 : ℝ) : ℂ) := hq
    have him := congrArg Complex.im hq'
    simp only [Rat.smul_def, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re,
      Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_I_im,
      Complex.mul_I_re, Complex.I_im, Complex.I_re, neg_zero, zero_add, add_zero, zero_mul,
      mul_zero, mul_one, sub_zero] at him
    have hq0 : (q : ℝ) = 0 := by
      rcases mul_eq_zero.1 him with h | h
      · exact h
      · exact absurd h hpi
    have hre := congrArg Complex.re hq'
    simp only [Rat.smul_def, Complex.mul_re, Complex.ratCast_im, Complex.ratCast_re,
      Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_I_im,
      Complex.mul_I_re, Complex.I_im, Complex.I_re, neg_zero, zero_add, add_zero, zero_mul,
      mul_zero, mul_one, sub_zero, hq0] at hre
    exact hlog2 hre.symm

/-! ### The statements -/

theorem transcendental_pi_add_log_two (hB : BakerHomogeneous) :
    Transcendental ℚ (Real.pi + Real.log 2) := by
  intro h
  have hβalg : IsAlgebraic ℚ ((Real.pi + Real.log 2 : ℝ) : ℂ) :=
    Schanuel.isAlgebraic_complex_of_real h
  have hI : IsAlgebraic ℚ Complex.I := Schanuel.isAlgebraic_I
  have h2mem : (2 : ℂ) ∈ integralClosure ℚ ℂ := by
    exact_mod_cast Subalgebra.natCast_mem (integralClosure ℚ ℂ) 2
  -- `-2β·1 + (2+i)·log 2 + (-i)·(log 2 + 2πi) = 0`
  have hc0 : (-2 * ((Real.pi + Real.log 2 : ℝ) : ℂ)) ∈ integralClosure ℚ ℂ :=
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (h2mem)) hβalg.isIntegral
  have hc1 : ((2 : ℂ) + Complex.I) ∈ integralClosure ℚ ℂ :=
    Subalgebra.add_mem _ (h2mem) hI.isIntegral
  have hc2 : (-Complex.I) ∈ integralClosure ℚ ℂ := Subalgebra.neg_mem _ hI.isIntegral
  have hzero := baker_relation hB logTwoPair linearIndependent_logTwoPair
    (fun i => by rw [exp_logTwoPair]; exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2)
    ![⟨_, hc0⟩, ⟨_, hc1⟩, ⟨_, hc2⟩] ?_ 2
  · have hI0 : (-Complex.I) = 0 := congrArg Subtype.val hzero
    simp [Complex.I_ne_zero] at hI0
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.cons_zero, Fin.cons_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, logTwoPair, Matrix.cons_val_one,
      Matrix.head_cons, mul_one]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ)) * Complex.I_sq

/-! ### Leaves for `2^√2·3^√3` -/

/-- `√n` is algebraic (root of `X² − n`). -/
theorem isAlgebraic_sqrt_nat (n : ℕ) : IsAlgebraic ℚ (Real.sqrt n) := by
  refine (isAlgebraic_iff_isIntegral).2 ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), ?_, ?_⟩
  · monicity!
  · simp [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]

/-- `log 2, log 3` as complex numbers are `ℚ`-linearly independent. -/
theorem linearIndependent_logTwoThree :
    LinearIndependent ℚ ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)] := by
  have hp : Function.Injective (![(⟨2, Nat.prime_two⟩ : Nat.Primes), ⟨3, Nat.prime_three⟩]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact absurd hij (by decide))
  have hli := Schanuel.linearIndependent_log_primes _ hp
  have hli2 : LinearIndependent ℚ ![Real.log 2, Real.log 3] := by
    convert hli using 1
    funext i
    fin_cases i <;> norm_num
  rw [linearIndependent_fin2] at hli2 ⊢
  constructor
  · intro hcon
    have hC : ((Real.log 3 : ℝ) : ℂ) = 0 := hcon
    exact hli2.1 (by exact_mod_cast hC)
  · intro q hq
    have hC : (q : ℂ) * ((Real.log 3 : ℝ) : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      simpa [Rat.smul_def] using hq
    refine hli2.2 q ?_
    have : ((q : ℝ) * Real.log 3 : ℝ) = Real.log 2 := by exact_mod_cast hC
    show (q : ℝ) • Real.log 3 = Real.log 2
    simpa [Rat.smul_def] using this

theorem transcendental_two_rpow_sqrt_two_mul_three_rpow_sqrt_three (hB : BakerHomogeneous) :
    Transcendental ℚ ((2 : ℝ) ^ Real.sqrt 2 * (3 : ℝ) ^ Real.sqrt 3) := by
  intro halg
  set L2 : ℂ := ((Real.log 2 : ℝ) : ℂ) with hL2
  set L3 : ℂ := ((Real.log 3 : ℝ) : ℂ) with hL3
  set s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hs2
  set s3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ) with hs3
  set μ : ℂ := s2 * L2 + s3 * L3 with hμ
  have hli23 : LinearIndependent ℚ ![L2, L3] := linearIndependent_logTwoThree
  have hexp2 : Complex.exp L2 = 2 := by
    rw [hL2, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  have hexp3 : Complex.exp L3 = 3 := by
    rw [hL3, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  have hexpμ : Complex.exp μ = (((2 : ℝ) ^ Real.sqrt 2 * (3 : ℝ) ^ Real.sqrt 3 : ℝ) : ℂ) := by
    rw [hμ, Complex.exp_add, hs2, hs3, hL2, hL3, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
    ring_nf
  have hexpμalg : IsAlgebraic ℚ (Complex.exp μ) := by
    rw [hexpμ]; exact Schanuel.isAlgebraic_complex_of_real halg
  have hs2mem : s2 ∈ integralClosure ℚ ℂ := by
    have := Schanuel.isAlgebraic_complex_of_real (isAlgebraic_sqrt_nat 2)
    rw [hs2]; exact (by exact_mod_cast this : IsAlgebraic ℚ ((Real.sqrt 2 : ℝ) : ℂ)).isIntegral
  have hs3mem : s3 ∈ integralClosure ℚ ℂ := by
    have := Schanuel.isAlgebraic_complex_of_real (isAlgebraic_sqrt_nat 3)
    rw [hs3]; exact (by exact_mod_cast this : IsAlgebraic ℚ ((Real.sqrt 3 : ℝ) : ℂ)).isIntegral
  by_cases hind : LinearIndependent ℚ ![L2, L3, μ]
  · -- `√2·log2 + √3·log3 − μ = 0` is a nontrivial `ℚ̄`-relation
    have hzero := baker_relation hB ![L2, L3, μ] hind
      (fun i => by
        fin_cases i
        · show IsAlgebraic ℚ (Complex.exp L2)
          rw [hexp2]; exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2
        · show IsAlgebraic ℚ (Complex.exp L3)
          rw [hexp3]; exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 3
        · exact hexpμalg)
      ![0, ⟨s2, hs2mem⟩, ⟨s3, hs3mem⟩, -1] ?_ 3
    · have : (-1 : ℂ) = 0 := congrArg Subtype.val hzero
      norm_num at this
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.cons_zero, Fin.cons_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      show ((0 : integralClosure ℚ ℂ) : ℂ) * 1
        + (s2 * L2 + (s3 * L3 + ((-1 : integralClosure ℚ ℂ) : ℂ) * μ)) = 0
      push_cast [hμ]
      ring
  · -- `μ` is a `ℚ`-combination of `log2, log3`, and then `√3` would be rational
    rw [Fintype.not_linearIndependent_iff] at hind
    obtain ⟨g, hg, i0, hi0⟩ := hind
    have hgsum : (g 0 : ℂ) * L2 + (g 1 : ℂ) * L3 + (g 2 : ℂ) * μ = 0 := by
      simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def] using hg
    have hg2 : g 2 ≠ 0 := by
      intro h2
      have hrel : (g 0 : ℂ) * L2 + (g 1 : ℂ) * L3 = 0 := by
        rw [h2] at hgsum; simpa using hgsum
      have := Fintype.linearIndependent_iff.1 hli23 ![g 0, g 1] (by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Rat.smul_def]
        exact hrel)
      refine hi0 ?_
      fin_cases i0
      · simpa using this 0
      · simpa using this 1
      · simpa using h2
    -- rewrite as a `ℚ̄`-relation among `1, log2, log3`
    have hc1mem : ((g 0 : ℂ) + (g 2 : ℂ) * s2) ∈ integralClosure ℚ ℂ :=
      Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ (g 0)) (Subalgebra.mul_mem _
        (Subalgebra.algebraMap_mem _ (g 2)) hs2mem)
    have hc2mem : ((g 1 : ℂ) + (g 2 : ℂ) * s3) ∈ integralClosure ℚ ℂ :=
      Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ (g 1)) (Subalgebra.mul_mem _
        (Subalgebra.algebraMap_mem _ (g 2)) hs3mem)
    have hzero := baker_relation hB ![L2, L3] hli23
      (fun i => by
        fin_cases i
        · show IsAlgebraic ℚ (Complex.exp L2)
          rw [hexp2]; exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2
        · show IsAlgebraic ℚ (Complex.exp L3)
          rw [hexp3]; exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 3)
      ![0, ⟨_, hc1mem⟩, ⟨_, hc2mem⟩] ?_ 2
    · -- `g 1 + g 2 · √3 = 0` forces `√3` rational
      have hc : (g 1 : ℂ) + (g 2 : ℂ) * s3 = 0 := congrArg Subtype.val hzero
      have hreal : (g 1 : ℝ) + (g 2 : ℝ) * Real.sqrt 3 = 0 := by
        have := congrArg Complex.re hc
        simpa [hs3] using this
      have : Real.sqrt 3 = ((-g 1 / g 2 : ℚ) : ℝ) := by
        have hg2' : (g 2 : ℝ) ≠ 0 := by exact_mod_cast hg2
        push_cast
        field_simp at hreal ⊢
        linarith [hreal]
      have h3 : Irrational (Real.sqrt 3) := by
        simpa using Nat.prime_three.irrational_sqrt
      exact h3 ⟨_, this.symm⟩
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.cons_zero, Fin.cons_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      show ((0 : integralClosure ℚ ℂ) : ℂ) * 1
        + (((g 0 : ℂ) + (g 2 : ℂ) * s2) * L2 + ((g 1 : ℂ) + (g 2 : ℂ) * s3) * L3) = 0
      rw [hμ] at hgsum
      push_cast
      linear_combination hgsum

end LeanFormalizations.Bedrock
