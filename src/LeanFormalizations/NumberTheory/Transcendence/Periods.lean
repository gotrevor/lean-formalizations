/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Periods and zeta values; the sharp-six repair (phase 25)

Inputs are `Literature/Periods.lean`, `Literature/Zeta5.lean` and the phase 15–24 toolkits.

* **Sharp six repairs the refuted edges.**  With `βᵢⱼ = 0`: sharp six ⇒ six exponentials.  With
  `x₃ = γ/x₁` plus Baker (Wikipedia, *Six exponentials theorem*, §Sharp, citing Waldschmidt
  2005): sharp six + `Baker1966` ⇒ five exponentials.  Our `x` has 2 entries and `y` has 3, so
  transpose the roles as needed.
* **Zeta values conjecture ⇒ the known theorems** (consistency): Apéry, Ball–Rivoal, and Fauzan's
  ζ(5) (proved in Lean elsewhere; `Literature/Zeta5.lean`).  Each value is real
  (`(riemannZeta s).im = 0` for real `s > 1`), so irrationality of `.re` is what `∃ x, Irrational x ∧
  riemannZeta s = x` needs.
* **Open consequences**: `ζ(3)/π³` transcendental; `ζ(3)` and `ζ(5)` algebraically independent.
* **Catalan**: the conjecture gives `G` transcendental and `G/π²` irrational.  The anchor
  `catalanG_eq` ties `Literature.catalanG` to the repo's `Catalan.catalanConst` (the salvage work in
  `NumberTheory/Catalan/`).

## Outcome (phase 25, 2026-09-29): all ten are PROVED and `#print axioms`-clean

Nothing turned out false or underivable.  Design points:

* **Sharp six ⇒ six** is a one-liner with `β = 0`: the sharp conclusion `xᵢyⱼ = βᵢⱼ` gives
  `x₀y₀ = 0`, which `LinearIndependent.ne_zero` already forbids.  This is exactly what the
  refuted `SixExponentialsShifted` could not do.
* **Sharp six + Baker ⇒ five** reuses the reduction of
  `ExponentialsKnown.fiveExponentials_of_shifted_of_baker` verbatim (`y₃ = γ/x₁`, shift the
  `(1,3)` entry by `γ` so the sixth exponential is `e⁰ = 1`, Baker in the `ℚ`-dependent case).
  Only the endgame changes: instead of an existential transcendental we get `x₀y₀ = 0`.
  So the sharp form really does "cover both" theorems, and the Baker input is unavoidable —
  see the recorded non-derivability note in `ExponentialsKnown.lean`.
* **Realness of `ζ`** comes from mathlib's `riemannZeta_im_eq_zero_of_one_lt`; the shape
  `∃ x : ℝ, Irrational x ∧ riemannZeta s = x` then needs only `Transcendental.irrational`.
  `zeta_odd_real` is the shared bridge and is uniform in `k`, so Apéry, ζ(5) and Ball–Rivoal
  are one lemma `irrational_zeta_odd` applied at `k = 0`, `k = 1`, and all `k`.
* **`b/πⁿ`** (both `ζ(3)/π³` and `G/π²`) is a *single* lemma `transcendental_div_pi_pow`:
  algebraic `b/πⁿ` would put `b` in the algebraic closure of `ℚ(π)`, contradicting
  `Schanuel.not_isAlgebraic_of_algebraicIndependent_pair`.  Irrationality of `G/π²` is then the
  weaker `Transcendental.irrational`.
* **Gotchas.**  `AlgebraicIndependent` has no `.congr`; transport along a family equality with
  `rw`.  Indexing a `Fin.cons` family at a *numeral* (`(2 : Fin 3)`) fights the dependent
  motive — compose with `Fin.succ` instead (`h2.comp Fin.succ (Fin.succ_injective 2)`), and use
  the `fin_cons_two` helper for the `Fin 2` case.  `set_option ... in` must precede the
  docstring, not sit between it and the declaration.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Periods
import LeanFormalizations.Literature.Zeta5
import LeanFormalizations.NumberTheory.Transcendence.ExponentialsKnown
import LeanFormalizations.NumberTheory.Catalan.Tails

namespace LeanFormalizations.Periods

open LeanFormalizations.Literature LeanFormalizations.Schanuel
open LeanFormalizations.ExponentialsKnown
open Complex IntermediateField Algebra Set

/-! ## Leaf 1: the sharp six exponentials theorem contains the six exponentials theorem -/

theorem sixExponentials_of_sharp (h : SixExponentialsSharp) : SixExponentials := by
  intro x y hx hy
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  have hconc := h x y (fun _ _ => 0) hx hy (fun _ _ => isAlgebraic_zero)
    (by intro i j; simpa using hcon i j)
  have h00 : x 0 * y 0 = 0 := hconc 0 0
  rcases mul_eq_zero.1 h00 with h0 | h0
  · exact hx.ne_zero 0 h0
  · exact hy.ne_zero 0 h0

/-! ## Leaf 2: sharp six + Baker ⇒ five exponentials

Same reduction as `ExponentialsKnown.fiveExponentials_of_shifted_of_baker`: put
`y₃ = γ/x₁`, shift the `(1,3)` entry by `γ` so the sixth exponential is `e⁰ = 1`, and use
Baker in the degenerate case where `y₀, y₁, γ/x₁` are `ℚ`-linearly dependent.  The only
change is the conclusion: the sharp theorem returns `xᵢyⱼ = βᵢⱼ`, and `x₀y₀ = 0` already
contradicts linear independence. -/
theorem fiveExponentials_of_sharp (h : SixExponentialsSharp) (hB : Baker1966) :
    FiveExponentials := by
  have hB2 : BakerTwoLogs := bakerTwoLogs_of_baker1966 hB
  intro x y γ hx hy hγ hγ0
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h4, h5⟩ := hcon
  simp only [Transcendental, not_exists, not_not] at h4
  rw [Transcendental, not_not] at h5
  have hx1 : x 1 ≠ 0 := hx.ne_zero 1
  set y₃ : ℂ := γ / x 1 with hy₃
  have hcol1 : x 0 * y₃ = γ * x 0 / x 1 := by rw [hy₃]; field_simp
  have hcol2 : x 1 * y₃ - γ = 0 := by rw [hy₃]; field_simp; ring
  by_cases hdep : y₃ ∈ Submodule.span ℚ (Set.range y)
  · obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hdep
    rw [Fin.sum_univ_two] at hr
    simp only [Rat.smul_def] at hr
    refine hB2 ![x 1 * y 0, x 1 * y 1] r γ ?_ hγ hγ0 ?_
    · intro i; fin_cases i
      · exact h4 1 0
      · exact h4 1 1
    · have hγeq : γ = x 1 * y₃ := by rw [hy₃]; field_simp
      rw [hγeq, ← hr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
  · have hyy : LinearIndependent ℚ (Fin.snoc y y₃ : Fin 3 → ℂ) :=
      linearIndependent_finSnoc.2 ⟨hy, hdep⟩
    have hconc := h x (Fin.snoc y y₃)
      (fun i j => if j = 2 ∧ i = 1 then γ else 0) hx hyy
      (by intro i j; split; exacts [hγ, isAlgebraic_zero]) ?_
    · have h00 : x 0 * y 0 = 0 := by
        have := hconc 0 0
        rw [if_neg (by simp)] at this
        exact this
      rcases mul_eq_zero.1 h00 with h0 | h0
      · exact hx.ne_zero 0 h0
      · exact hy.ne_zero 0 h0
    · intro i j
      fin_cases j
      · show IsAlgebraic ℚ (Complex.exp (x i * y 0 - _))
        rw [if_neg (by simp)]
        simpa using h4 i 0
      · show IsAlgebraic ℚ (Complex.exp (x i * y 1 - _))
        rw [if_neg (by simp)]
        simpa using h4 i 1
      · show IsAlgebraic ℚ (Complex.exp (x i * y₃ - _))
        fin_cases i
        · rw [if_neg (by simp)]
          show IsAlgebraic ℚ (Complex.exp (x 0 * y₃ - 0))
          rw [sub_zero, hcol1]
          exact h5
        · rw [if_pos (by simp)]
          show IsAlgebraic ℚ (Complex.exp (x 1 * y₃ - γ))
          rw [hcol2, Complex.exp_zero]
          exact isAlgebraic_one

/-! ## Toolkit for the zeta-values conjecture -/

/-- `ζ` is real on the real axis above `1`. -/
theorem zeta_odd_real (k : ℕ) :
    riemannZeta (2 * (k : ℂ) + 3) = (((riemannZeta (2 * (k : ℂ) + 3)).re : ℝ) : ℂ) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx : (1 : ℝ) < 2 * (k : ℝ) + 3 := by linarith
  have hcast : (((2 * (k : ℝ) + 3 : ℝ) : ℝ) : ℂ) = 2 * (k : ℂ) + 3 := by push_cast; ring
  have him := riemannZeta_im_eq_zero_of_one_lt hx
  rw [hcast] at him
  exact Complex.ext (by simp) (by simp [him])

/-- Under the zeta-values conjecture each odd zeta value `ζ(2k+3)` is transcendental. -/
theorem transcendental_zeta_odd (h : ZetaValuesAlgIndepConjecture) (k : ℕ) :
    Transcendental ℚ (riemannZeta (2 * (k : ℂ) + 3)).re := by
  have hk := (h (k + 1)).transcendental (Fin.last k).succ
  rw [Fin.cons_succ] at hk
  simpa using hk

/-- Under the zeta-values conjecture each odd zeta value is irrational, in the
`∃ x : ℝ, Irrational x ∧ riemannZeta _ = x` shape the literature statements use. -/
theorem irrational_zeta_odd (h : ZetaValuesAlgIndepConjecture) (k : ℕ) :
    ∃ x : ℝ, Irrational x ∧ riemannZeta (2 * (k : ℂ) + 3) = x :=
  ⟨_, (transcendental_zeta_odd h k).irrational, zeta_odd_real k⟩

theorem apery_of_zetaValues (h : ZetaValuesAlgIndepConjecture) : Apery1979 := by
  have := irrational_zeta_odd h 0
  norm_num at this
  exact this

theorem zeta5_of_zetaValues (h : ZetaValuesAlgIndepConjecture) : Fauzan2026Zeta5 := by
  have := irrational_zeta_odd h 1
  norm_num at this
  exact this

theorem ballRivoal_of_zetaValues (h : ZetaValuesAlgIndepConjecture) : BallRivoal2001 := by
  have hsub : (Set.univ : Set ℕ) ⊆
      {k : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta (2 * k + 3) = x} := by
    intro k _
    have := irrational_zeta_odd h k
    push_cast at this ⊢
    exact this
  exact Set.Infinite.mono hsub Set.infinite_univ

/-! ## Toolkit: algebraic independence from `π` -/

theorem algIndepPair_complex {a b : ℝ} (h : AlgebraicIndependent ℚ ![a, b]) :
    AlgebraicIndependent ℚ ![(a : ℂ), (b : ℂ)] := by
  have hmap := h.map' (f := IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective
  have heq : (⇑(IsScalarTower.toAlgHom ℚ ℝ ℂ) ∘ ![a, b]) = ![(a : ℂ), (b : ℂ)] := by
    funext i; fin_cases i <;> rfl
  rwa [heq] at hmap

set_option maxHeartbeats 1000000 in
/-- If `π` and `b` are algebraically independent then `b/π^n` is transcendental: otherwise `b`
would be algebraic over `ℚ(π)`. -/
theorem transcendental_div_pi_pow {b : ℝ} (h : AlgebraicIndependent ℚ ![Real.pi, b]) (n : ℕ) :
    Transcendental ℚ (b / Real.pi ^ n) := by
  intro halg
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  refine not_isAlgebraic_of_algebraicIndependent_pair (algIndepPair_complex h) ?_
  have hbR : b = (b / Real.pi ^ n) * Real.pi ^ n := by field_simp
  have hbC : ((b : ℝ) : ℂ) = (((b / Real.pi ^ n : ℝ) : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ n := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← hbR]
  set K := IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ) with hK
  have hmem : ((Real.pi : ℝ) : ℂ) ∈ K := IntermediateField.subset_adjoin _ _ rfl
  have hpow : ((Real.pi : ℝ) : ℂ) ^ n ∈ K := pow_mem hmem n
  rw [hbC]
  exact isAlgebraic_mul_rat (isAlgebraic_complex_of_real halg)
    (isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, hpow⟩)

/-- Evaluating a `Fin 2` family built with `Fin.cons`. -/
theorem fin_cons_two {α : Type} (a : α) (f : Fin 1 → α) :
    (Fin.cons a f : Fin 2 → α) = ![a, f 0] := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rw [Fin.cons_succ]
    fin_cases j
    rfl

/-! ## The open consequences -/

theorem algIndepPair_pi_zeta_three (h : ZetaValuesAlgIndepConjecture) :
    AlgebraicIndependent ℚ ![Real.pi, (riemannZeta 3).re] := by
  have h1 := h 1
  rw [fin_cons_two] at h1
  have heq : (riemannZeta (2 * ((0 : Fin 1) : ℕ) + 3)).re = (riemannZeta 3).re := by norm_num
  rwa [heq] at h1

theorem transcendental_zeta_three_div_pi_cube (h : ZetaValuesAlgIndepConjecture) :
    Transcendental ℚ ((riemannZeta 3).re / Real.pi ^ 3) :=
  transcendental_div_pi_pow (algIndepPair_pi_zeta_three h) 3

theorem algebraicIndependent_zeta_three_zeta_five (h : ZetaValuesAlgIndepConjecture) :
    AlgebraicIndependent ℚ ![(riemannZeta 3).re, (riemannZeta 5).re] := by
  have h2 := h 2
  have hcomp := h2.comp (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)
  have heq : ((Fin.cons Real.pi fun k : Fin 2 ↦ (riemannZeta (2 * (k : ℕ) + 3)).re :
      Fin 3 → ℝ) ∘ (Fin.succ : Fin 2 → Fin 3)) =
      ![(riemannZeta 3).re, (riemannZeta 5).re] := by
    funext i
    have hc : (Fin.cons Real.pi fun k : Fin 2 ↦ (riemannZeta (2 * (k : ℕ) + 3)).re :
        Fin 3 → ℝ) i.succ = (riemannZeta (2 * (i : ℕ) + 3)).re := Fin.cons_succ _ _ _
    simp only [Function.comp_apply, hc]
    fin_cases i <;> norm_num
  rwa [heq] at hcomp

/-! ## Catalan -/

theorem catalanG_eq : catalanG = Catalan.catalanConst := by
  unfold catalanG Catalan.catalanConst Catalan.tail
  norm_num

theorem algIndepPair_pi_catalan (h : CatalanPiAlgIndepConjecture) :
    AlgebraicIndependent ℚ ![Real.pi, Catalan.catalanConst] := by
  rw [← catalanG_eq]; exact h

theorem transcendental_catalan (h : CatalanPiAlgIndepConjecture) :
    Transcendental ℚ Catalan.catalanConst := by
  have := (algIndepPair_pi_catalan h).transcendental 1
  simpa using this

theorem irrational_catalan_div_pi_sq (h : CatalanPiAlgIndepConjecture) :
    Irrational (Catalan.catalanConst / Real.pi ^ 2) :=
  (transcendental_div_pi_pow (algIndepPair_pi_catalan h) 2).irrational

end LeanFormalizations.Periods
