/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The implications in Waldschmidt's 2023 survey (phase 19)

Phases 15–17 covered Conjecture 2, Theorems 3–5 and Conjecture 6 (`Schanuel.lean`,
`Exponentials.lean`, `ExponentialsKnown.lean`).  This file adds Conjecture 1 and the survey's own
derivations around it.  The coverage map is `WALDSCHMIDT-2023.md`.

* Schanuel ⇒ Conjecture 1 (survey §7: "Conjecture 1 is the special case of Conjecture 6 where the
  `e^{xᵢ}` are algebraic").
* Conjecture 1 ⇒ four exponentials: the survey's own route (§4; Waldschmidt 2000 Ex. 1.8,
  Roy's reformulation).  Independent of phase 16's route from full Schanuel.
* Conjecture 1 ⇒ Baker's homogeneous conclusion (algebraic independence over `ℚ` gives it over
  `ℚ̄`, since `ℚ̄/ℚ` is algebraic, and a `ℚ̄`-linear relation is a polynomial relation).
* Conjecture 1 ⇒ `log 2` and `π` are algebraically independent (survey p. 4: take `λ₁ = log 2`,
  `λ₂ = log 2 + 2πi`).
* Conjecture 1 for `n = 1` is **known**, by Hermite–Lindemann: from `LindemannWeierstrassAlgIndep`
  (a nonzero logarithm of an algebraic number is transcendental).

**Result (2026-09-29, one lap): all five are proved and `#print axioms`-clean; this file is
sorry-free.**  Nothing turned out to be underivable.  Notes:

* Conjecture 1 ⇒ four exponentials reuses phase 16's *shape* but not its lemma: the phase-16
  heart `Exponentials.false_of_exp_algebraic_of_quad` is stated with `hS : SchanuelConjecture`
  and only ever uses it through `algebraicIndependent_of_exp_isAlgebraic`, i.e. through
  Conjecture 1 exactly.  `false_of_exp_algebraic_of_quad'` below is that proof with the
  hypothesis weakened to `AlgIndepLogsConjecture`, which is the honest content of the survey's
  claim that Conjecture 1 (not full Schanuel) already gives Conjecture 2.
* Baker homogeneous needs `AlgebraicIndependent.extendScalars` (mathlib) to move algebraic
  independence from `ℚ` to `ℚ̄` — legitimate because `ℚ̄/ℚ` is algebraic — and then the
  phase-15 leaf `eq_zero_of_algebraicIndependent_linear` at base `ℚ̄` to kill the affine
  relation.  So Conjecture 1 gives Baker for free, with no analytic input at all.
* `log 2, π`: the trade of `ℚ(log 2, log 2 + 2πi)` for `ℚ(log 2, π)` is the phase-15 master
  step `algebraicIndependent_of_le_trdeg_of_isAlgebraic` (`i` is algebraic, so the two fields
  are algebraic over each other).
* `n = 1`: `LinearIndependent ℕ` on a singleton has no `linearIndependent_unique_iff` (that one
  needs a `Ring`), so it goes through `linearIndependent_iff'ₛ`.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.ExponentialsKnown

namespace LeanFormalizations.Waldschmidt2023

open LeanFormalizations.Literature

open LeanFormalizations.Schanuel LeanFormalizations.Exponentials
open Complex IntermediateField Algebra Cardinal Set

/-! ## Toolkit -/

/-- Sums of numbers algebraic over an intermediate field are algebraic over it. -/
theorem isAlgebraic_add' {L : IntermediateField ℚ ℂ} {a b : ℂ}
    (ha : IsAlgebraic L a) (hb : IsAlgebraic L b) : IsAlgebraic L (a + b) :=
  mem_algebraicClosure_iff.1
    (add_mem (mem_algebraicClosure_iff.2 ha) (mem_algebraicClosure_iff.2 hb))

/-! ## Schanuel ⇒ Conjecture 1 -/

/-- **Schanuel ⇒ Conjecture 1** (survey §7): Conjecture 1 is the special case of Schanuel's
conjecture in which all the `e^{xᵢ}` are algebraic, so the transcendence degree of
`ℚ(x, e^x)` is carried entirely by `x`. -/
theorem algIndepLogs_of_schanuel (hS : SchanuelConjecture) : AlgIndepLogsConjecture :=
  fun _ ℓ hl he => algebraicIndependent_of_exp_isAlgebraic hS ℓ hl he

/-! ## Conjecture 1 ⇒ four exponentials (the survey's own route) -/

/-- **The heart of "Conjecture 1 ⇒ four exponentials"**, the analogue of
`Exponentials.false_of_exp_algebraic_of_quad` with the weaker hypothesis: four numbers
`a, b, c, d` with `a·d = b·c`, with `a, b` and `a, c` each `ℚ`-linearly independent, cannot all
have algebraic exponentials.  Only algebraic independence of logarithms is used, never the full
transcendence-degree statement. -/
theorem false_of_exp_algebraic_of_quad' (H : AlgIndepLogsConjecture) {a b c d : ℂ}
    (hab : LinearIndependent ℚ ![a, b]) (hac : LinearIndependent ℚ ![a, c])
    (hrel : a * d = b * c)
    (hea : IsAlgebraic ℚ (Complex.exp a)) (heb : IsAlgebraic ℚ (Complex.exp b))
    (hec : IsAlgebraic ℚ (Complex.exp c)) (hed : IsAlgebraic ℚ (Complex.exp d)) : False := by
  have key : ∀ {n : ℕ} (z : Fin n → ℂ), LinearIndependent ℚ z →
      (∀ i, IsAlgebraic ℚ (Complex.exp (z i))) → AlgebraicIndependent ℚ z :=
    fun z hz he => H _ z hz he
  have ha0 : a ≠ 0 := by simpa using hab.ne_zero 0
  have hABind : AlgebraicIndependent ℚ ![a, b] :=
    key _ hab (by intro i; fin_cases i <;> assumption)
  by_cases h3 : LinearIndependent ℚ ![a, b, c]
  · have hABCind : AlgebraicIndependent ℚ ![a, b, c] :=
      key _ h3 (by intro i; fin_cases i <;> assumption)
    by_cases h4 : LinearIndependent ℚ ![a, b, c, d]
    · have hABCDind : AlgebraicIndependent ℚ ![a, b, c, d] :=
        key _ h4 (by intro i; fin_cases i <;> assumption)
      refine false_of_algebraicIndependent_mem hABCDind (w := ![a, b, c, c]) ?_ ?_
      · intro h
        have : (2 : Fin 4) = 3 := h rfl
        simp at this
      · set L := IntermediateField.adjoin ℚ (Set.range ![a, b, c, c]) with hL
        have hma : a ∈ L := subset_adjoin _ _ ⟨0, rfl⟩
        have hmb : b ∈ L := subset_adjoin _ _ ⟨1, rfl⟩
        have hmc : c ∈ L := subset_adjoin _ _ ⟨2, rfl⟩
        have hd : d = b * c / a := by
          rw [eq_div_iff ha0]; linear_combination hrel
        intro i; fin_cases i
        · exact hma
        · exact hmb
        · exact hmc
        · show d ∈ L
          rw [hd]
          exact div_mem (mul_mem hmb hmc) hma
    · rw [← snoc4, linearIndependent_finSnoc] at h4
      have hdspan : d ∈ Submodule.span ℚ (Set.range ![a, b, c]) := by
        by_contra hn; exact h4 ⟨h3, hn⟩
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hdspan
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def] at hg
      have hden : (g 2 : ℂ) * a - b ≠ 0 := by
        intro h
        have := (LinearIndependent.pair_iff.1 hab) (g 2) (-1) (by
          simp only [Rat.smul_def]; push_cast; linear_combination h)
        simpa using this.2
      have hc : c = -((g 0 : ℂ) * a * a + (g 1 : ℂ) * a * b) / ((g 2 : ℂ) * a - b) := by
        rw [eq_div_iff hden]
        linear_combination hrel + a * hg
      refine false_of_algebraicIndependent_mem hABCind (w := ![a, b, b]) ?_ ?_
      · intro h
        have : (1 : Fin 3) = 2 := h rfl
        simp at this
      · set L := IntermediateField.adjoin ℚ (Set.range ![a, b, b]) with hL
        have hma : a ∈ L := subset_adjoin _ _ ⟨0, rfl⟩
        have hmb : b ∈ L := subset_adjoin _ _ ⟨1, rfl⟩
        intro i; fin_cases i
        · exact hma
        · exact hmb
        · show c ∈ L
          rw [hc]
          exact div_mem
            (neg_mem (add_mem (mul_mem (mul_mem (ratCast_mem_adjoin L (g 0)) hma) hma)
              (mul_mem (mul_mem (ratCast_mem_adjoin L (g 1)) hma) hmb)))
            (sub_mem (mul_mem (ratCast_mem_adjoin L (g 2)) hma) hmb)
  · rw [← snoc3, linearIndependent_finSnoc] at h3
    have hcspan : c ∈ Submodule.span ℚ (Set.range ![a, b]) := by
      by_contra hn; exact h3 ⟨hab, hn⟩
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hcspan
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Rat.smul_def] at hg
    have hq : (g 1 : ℚ) ≠ 0 := by
      intro h
      have := (LinearIndependent.pair_iff.1 hac) (g 0) (-1) (by
        simp only [Rat.smul_def]; push_cast; rw [h] at hg; push_cast at hg; linear_combination hg)
      simpa using this.2
    by_cases h3' : LinearIndependent ℚ ![a, b, d]
    · have hABDind : AlgebraicIndependent ℚ ![a, b, d] :=
        key _ h3' (by intro i; fin_cases i <;> assumption)
      refine false_of_algebraicIndependent_mem hABDind (w := ![a, b, b]) ?_ ?_
      · intro h
        have : (1 : Fin 3) = 2 := h rfl
        simp at this
      · set L := IntermediateField.adjoin ℚ (Set.range ![a, b, b]) with hL
        have hma : a ∈ L := subset_adjoin _ _ ⟨0, rfl⟩
        have hmb : b ∈ L := subset_adjoin _ _ ⟨1, rfl⟩
        have hd : d = ((g 0 : ℂ) * a * b + (g 1 : ℂ) * b * b) / a := by
          rw [eq_div_iff ha0]; linear_combination hrel - b * hg
        intro i; fin_cases i
        · exact hma
        · exact hmb
        · show d ∈ L
          rw [hd]
          exact div_mem (add_mem (mul_mem (mul_mem (ratCast_mem_adjoin L (g 0)) hma) hmb)
            (mul_mem (mul_mem (ratCast_mem_adjoin L (g 1)) hmb) hmb)) hma
    · rw [← snoc3, linearIndependent_finSnoc] at h3'
      have hdspan : d ∈ Submodule.span ℚ (Set.range ![a, b]) := by
        by_contra hn; exact h3' ⟨hab, hn⟩
      obtain ⟨h, hh⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hdspan
      rw [Fin.sum_univ_two] at hh
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Rat.smul_def] at hh
      set L := IntermediateField.adjoin ℚ ({a} : Set ℂ) with hL
      have hma : a ∈ L := subset_adjoin _ _ rfl
      have hqC : ((g 1 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hq
      have hquad : b * b = ((h 0 : ℂ) / (g 1 : ℂ)) * (a * a)
          + (((h 1 : ℂ) - (g 0 : ℂ)) / (g 1 : ℂ)) * (a * b) := by
        field_simp
        linear_combination b * hg - a * hh - hrel
      refine not_isAlgebraic_of_algebraicIndependent_pair hABind ?_
      set A : L := ⟨((h 1 : ℂ) - (g 0 : ℂ)) / (g 1 : ℂ) * a,
        mul_mem (div_mem (sub_mem (ratCast_mem_adjoin L (h 1)) (ratCast_mem_adjoin L (g 0)))
          (ratCast_mem_adjoin L (g 1))) hma⟩ with hA
      set B : L := ⟨(h 0 : ℂ) / (g 1 : ℂ) * (a * a),
        mul_mem (div_mem (ratCast_mem_adjoin L (h 0)) (ratCast_mem_adjoin L (g 1)))
          (mul_mem hma hma)⟩ with hB
      refine ⟨Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X - Polynomial.C B, ?_, ?_⟩
      · have hm : (Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X - Polynomial.C B :
            Polynomial L).Monic := by monicity!
        exact hm.ne_zero
      · simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        show b ^ 2 - (A : ℂ) * b - (B : ℂ) = 0
        simp only [hA, hB]
        linear_combination hquad

theorem fourExponentials_of_algIndepLogs (h : AlgIndepLogsConjecture) :
    FourExponentialsConjecture := by
  intro x y hx hy
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  have hab : LinearIndependent ℚ ![x 0 * y 0, x 0 * y 1] := by
    have h := linearIndependent_const_mul hy (c := x 0) (hx.ne_zero 0)
    have he : (fun i => x 0 * y i) = ![x 0 * y 0, x 0 * y 1] := by
      funext i; fin_cases i <;> rfl
    rwa [he] at h
  have hac : LinearIndependent ℚ ![x 0 * y 0, x 1 * y 0] := by
    have h := linearIndependent_const_mul hx (c := y 0) (hy.ne_zero 0)
    have he : (fun i => y 0 * x i) = ![x 0 * y 0, x 1 * y 0] := by
      funext i; fin_cases i <;> simp [mul_comm]
    rwa [he] at h
  exact false_of_exp_algebraic_of_quad' h hab hac (by ring)
    (hcon 0 0) (hcon 0 1) (hcon 1 0) (hcon 1 1)

/-! ## Conjecture 1 ⇒ Baker's homogeneous theorem -/

theorem bakerHomogeneous_of_algIndepLogs (h : AlgIndepLogsConjecture) : BakerHomogeneous := by
  intro n ℓ hl he
  have hind : AlgebraicIndependent ℚ ℓ := h n ℓ hl he
  have hbar : AlgebraicIndependent (integralClosure ℚ ℂ) ℓ :=
    hind.extendScalars _
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  have hrel : algebraMap (integralClosure ℚ ℂ) ℂ (g 0) +
      ∑ i : Fin n, algebraMap (integralClosure ℚ ℂ) ℂ (g i.succ) * ℓ i = 0 := by
    simpa [Fin.cons_zero, Fin.cons_succ, Algebra.smul_def] using hg
  obtain ⟨h0, hrest⟩ :=
    eq_zero_of_algebraicIndependent_linear hbar (g 0) (fun i => g i.succ) hrel
  intro i
  refine Fin.cases ?_ (fun j => hrest j) i
  exact h0

/-! ## Conjecture 1 ⇒ `log 2` and `π` are algebraically independent -/

theorem linearIndependent_log_two_log_two_add_two_pi_I :
    LinearIndependent ℚ ![((Real.log 2 : ℝ) : ℂ), ((Real.log 2 : ℝ) : ℂ) + 2 * ((Real.pi : ℝ) : ℂ) * I] := by
  have hlog : Real.log 2 ≠ 0 := by
    have : (1:ℝ) < 2 := by norm_num
    exact ne_of_gt (Real.log_pos this)
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Rat.smul_def] at hst
  have him : (t : ℂ).im = 0 := by exact_mod_cast Complex.ofReal_im (t : ℝ)
  have h2 : (t : ℝ) * (2 * Real.pi) = 0 := by
    have hc := congrArg Complex.im hst
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im, Complex.ratCast_im,
      Complex.ratCast_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] at hc
    norm_num at hc ⊢
    tauto
  have ht : t = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact_mod_cast h
    · exact absurd h (by positivity)
  subst ht
  refine ⟨?_, rfl⟩
  simp only [Rat.cast_zero, zero_mul, add_zero] at hst
  have : (s : ℂ) = 0 := by
    rcases mul_eq_zero.1 hst with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hlog
  exact_mod_cast this

/-- Conjecture 1 ⇒ `log 2` and `π` are algebraically independent (survey p. 4): take
`λ₁ = log 2`, `λ₂ = log 2 + 2πi`, both logarithms of `2`. -/
theorem algebraicIndependent_log_two_pi (h : AlgIndepLogsConjecture) :
    AlgebraicIndependent ℚ ![Real.log 2, Real.pi] := by
  set L : ℂ := ((Real.log 2 : ℝ) : ℂ) with hLdef
  have hexp2 : Complex.exp L = 2 := by
    rw [hLdef, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  have hind : AlgebraicIndependent ℚ ![L, L + 2 * ((Real.pi : ℝ) : ℂ) * I] := by
    refine h 2 _ linearIndependent_log_two_log_two_add_two_pi_I ?_
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (Complex.exp L); rw [hexp2]
      exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2
    · show IsAlgebraic ℚ (Complex.exp (L + 2 * ((Real.pi : ℝ) : ℂ) * I))
      rw [Complex.exp_add, hexp2, Complex.exp_two_pi_mul_I]
      simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2
  refine algebraicIndependent_real_of_complex ?_
  have hy : (fun i => ((![Real.log 2, Real.pi] i : ℝ) : ℂ)) = ![L, ((Real.pi : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> rfl
  rw [hy]
  refine algebraicIndependent_of_le_trdeg_of_isAlgebraic (F := ℚ) (E := ℂ)
    ![L, ((Real.pi : ℝ) : ℂ)] (IntermediateField.adjoin ℚ (Set.range ![L, L + 2 * ((Real.pi : ℝ) : ℂ) * I]))
    (by simpa using hind.le_trdeg_adjoin) (forall_isAlgebraic_adjoin ?_)
  set K := IntermediateField.adjoin ℚ (Set.range ![L, ((Real.pi : ℝ) : ℂ)]) with hK
  have hmL : L ∈ K := subset_adjoin _ _ ⟨0, rfl⟩
  have hmpi : ((Real.pi : ℝ) : ℂ) ∈ K := subset_adjoin _ _ ⟨1, rfl⟩
  have hLalg : IsAlgebraic K L := isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, hmL⟩
  have hpialg : IsAlgebraic K ((Real.pi : ℝ) : ℂ) :=
    isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, hmpi⟩
  rintro w ⟨i, rfl⟩
  fin_cases i
  · exact hLalg
  · show IsAlgebraic K (L + 2 * ((Real.pi : ℝ) : ℂ) * I)
    refine isAlgebraic_add' hLalg ?_
    have hrw : 2 * ((Real.pi : ℝ) : ℂ) * I = (2 * I) * ((Real.pi : ℝ) : ℂ) := by ring
    rw [hrw]
    exact isAlgebraic_mul_rat
      (by simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2).mul isAlgebraic_I) hpialg

/-! ## Conjecture 1 at `n = 1` is known -/

/-- Conjecture 1 for `n = 1` is known: a nonzero logarithm of an algebraic number is
transcendental (Hermite–Lindemann). -/
theorem transcendental_log_of_lindemann (hL : LindemannWeierstrassAlgIndep) {ℓ : ℂ}
    (hℓ : ℓ ≠ 0) (he : IsAlgebraic ℚ (Complex.exp ℓ)) : Transcendental ℚ ℓ := by
  intro hal
  set u : Fin 1 → integralClosure ℚ ℂ := ![⟨ℓ, by
    rw [mem_integralClosure_iff]
    exact hal.isIntegral⟩] with hu
  have hli : LinearIndependent ℕ u := by
    rw [linearIndependent_iff'ₛ]
    intro t f g hfg i hi
    have hs : t = {i} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j _ => Subsingleton.elim j i⟩
    subst hs
    rw [Finset.sum_singleton, Finset.sum_singleton] at hfg
    have hval : (f i : ℂ) * ℓ = (g i : ℂ) * ℓ := by
      have := congrArg Subtype.val hfg
      simpa [hu, Subsingleton.elim i 0, nsmul_eq_mul] using this
    have := mul_right_cancel₀ hℓ hval
    exact_mod_cast this
  have hAI := hL u hli
  have htr : Transcendental (integralClosure ℚ ℂ) (Complex.exp ℓ) := by
    have := hAI.transcendental 0
    simpa [hu] using this
  exact htr (he.extendScalars (S := integralClosure ℚ ℂ) (algebraMap ℚ _).injective)

end LeanFormalizations.Waldschmidt2023
