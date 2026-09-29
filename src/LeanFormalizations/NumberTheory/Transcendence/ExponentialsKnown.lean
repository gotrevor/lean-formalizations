/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Consequences of the known exponentials theorems (phase 17, queued)

The six exponentials theorem is **unconditional**, so everything here is a real theorem, modulo
cited literature.

* **`2^t, 3^t, 5^t`** (Trevor, 2026-09-29): for irrational `t`, one of them is transcendental.
  Take `x = (1, t)` and `y = (log 2, log 3, log 5)`, with independence from
  `linearIndependent_log_primes`; the exponentials are `2, 3, 5, 2^t, 3^t, 5^t`.  Any three
  distinct primes work.  `4` does not help, since `log 4 = 2 log 2`.  This is the unconditional
  cousin of phase 16's `two_rpow_or_three_rpow_transcendental`, which needs four exponentials.
* **Consistency edges**: `SixExponentialsShifted ⇒ SixExponentials` and
  `SixExponentialsShifted ⇒ FiveExponentials` (Waldschmidt says it covers both), and
  `StrongSixExponentialsOverQ ⇒ SixExponentials` (if every `e^{xᵢyⱼ}` were algebraic, every `xᵢyⱼ`
  would be a logarithm, hence in `LogAlgSpan`).
* **Five exponentials ⇒** `e^{π²}` or `2^{√2}`-style corollaries: left to the lap to choose one
  (Waldschmidt 2023 §6 lists them); add as a new theorem.

⚠️ **FAITHFULNESS BUG FOUND (2026-09-29): `Literature.StrongSixExponentialsOverQ` is FALSE as
stated**, and `not_strongSixExponentialsOverQ` below is a machine-checked refutation.  Roy's theorem
asks for `x` and `y` linearly independent over the field of *algebraic* numbers; the frozen
`Prop` asks only for `ℚ`-linear independence, which is far too weak.  Witness:
`x = (1, log 2)` and `y = (1, √2, i)` are `ℚ`-linearly independent, yet all six products
`1, √2, i, log 2, √2·log 2, i·log 2` lie in `𝓛̃` — the first three because `𝓛̃ ⊇ ℚ̄`, the last
three because they are `β·log 2` with `β` algebraic.  Over `ℚ̄` the triple `1, √2, i` is
dependent, which is exactly what the real hypothesis rules out.  `Literature/` is frozen, so
fixing the `Prop` (`LinearIndependent ℚ` ⟶ independence over `integralClosure ℚ ℂ`) is an
operator decision; `sixExponentials_of_strong` above stays a valid implication, it just now has
a hypothesis known to be unsatisfiable.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.ExponentialsKnown
import LeanFormalizations.Literature.Exponentials
import LeanFormalizations.NumberTheory.Transcendence.Schanuel
import LeanFormalizations.NumberTheory.Transcendence.Exponentials

namespace LeanFormalizations.ExponentialsKnown

open LeanFormalizations.Literature LeanFormalizations.Schanuel LeanFormalizations.Exponentials
open Complex IntermediateField Algebra Set

/-- `e^{log q}` is algebraic for a positive rational `q` (used to discard the `x = 1` row). -/
theorem exp_ofReal_log_isAlgebraic {q : ℚ} (hq : (0 : ℝ) < (q : ℝ)) (_hq : (0 : ℚ) < q) :
    IsAlgebraic ℚ (Complex.exp (((Real.log (q : ℝ)) : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log hq]
  exact isAlgebraic_complex_of_real
    (by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q)

theorem linearIndependent_log_two_three_five :
    LinearIndependent ℚ
      ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ), ((Real.log 5 : ℝ) : ℂ)] := by
  have hp : Function.Injective (![(⟨2, Nat.prime_two⟩ : Nat.Primes), ⟨3, Nat.prime_three⟩,
      ⟨5, by norm_num⟩]) := by decide
  have h := (linearIndependent_log_primes _ hp).map'
    ((IsScalarTower.toAlgHom ℚ ℝ ℂ).toLinearMap)
    (by rw [LinearMap.ker_eq_bot]; exact (IsScalarTower.toAlgHom ℚ ℝ ℂ).injective)
  simp only [Function.comp_def] at h
  have he : (fun i => ((IsScalarTower.toAlgHom ℚ ℝ ℂ).toLinearMap)
      (Real.log ((((![(⟨2, Nat.prime_two⟩ : Nat.Primes), ⟨3, Nat.prime_three⟩,
        ⟨5, by norm_num⟩] i) : Nat.Primes) : ℕ) : ℝ)))
      = ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ), ((Real.log 5 : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> norm_num
  rwa [he] at h

/-- **Unconditional** (six exponentials): for irrational `t`, one of `2^t, 3^t, 5^t` is
transcendental. -/
theorem two_three_five_rpow_transcendental (h6 : SixExponentials) {t : ℝ} (ht : Irrational t) :
    Transcendental ℚ ((2 : ℝ) ^ t) ∨ Transcendental ℚ ((3 : ℝ) ^ t) ∨
      Transcendental ℚ ((5 : ℝ) ^ t) := by
  obtain ⟨i, j, htr⟩ := h6 ![(1 : ℂ), ((t : ℝ) : ℂ)]
    ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ), ((Real.log 5 : ℝ) : ℂ)]
    (linearIndependent_one_ofReal ht) linearIndependent_log_two_three_five
  have hrow : ∀ q : ℚ, (0:ℚ) < q →
      IsAlgebraic ℚ (Complex.exp ((1 : ℂ) * (((Real.log (q : ℝ)) : ℝ) : ℂ))) := by
    intro q hq
    rw [one_mul]
    exact exp_ofReal_log_isAlgebraic (by exact_mod_cast hq) hq
  have hrow2 : ∀ q : ℝ, 0 < q →
      Complex.exp (((t : ℝ) : ℂ) * (((Real.log q) : ℝ) : ℂ)) = ((q ^ t : ℝ) : ℂ) :=
    fun q hq => cexp_mul_ofReal_log hq
  fin_cases i <;> fin_cases j
  · exact absurd (hrow 2 (by norm_num)) htr
  · exact absurd (hrow 3 (by norm_num)) htr
  · exact absurd (hrow 5 (by norm_num)) htr
  · refine Or.inl (transcendental_real_of_complex ?_)
    have h2 : Transcendental ℚ
        (Complex.exp (((t : ℝ) : ℂ) * (((Real.log (2 : ℝ)) : ℝ) : ℂ))) := htr
    rwa [hrow2 2 (by norm_num)] at h2
  · refine Or.inr (Or.inl (transcendental_real_of_complex ?_))
    have h2 : Transcendental ℚ
        (Complex.exp (((t : ℝ) : ℂ) * (((Real.log (3 : ℝ)) : ℝ) : ℂ))) := htr
    rwa [hrow2 3 (by norm_num)] at h2
  · refine Or.inr (Or.inr (transcendental_real_of_complex ?_))
    have h2 : Transcendental ℚ
        (Complex.exp (((t : ℝ) : ℂ) * (((Real.log (5 : ℝ)) : ℝ) : ℂ))) := htr
    rwa [hrow2 5 (by norm_num)] at h2

theorem sixExponentials_of_shifted (h : SixExponentialsShifted) : SixExponentials := by
  intro x y hx hy
  obtain ⟨i, j, htr⟩ := h x y (fun _ _ => 0) hx hy (fun _ _ => isAlgebraic_zero)
  exact ⟨i, j, by simpa using htr⟩


/-- **Baker's theorem for two logarithms, inhomogeneous form.**  A nonzero algebraic number is
not a `ℚ`-linear combination of two logarithms of algebraic numbers.  (A. Baker, *Linear forms
in the logarithms of algebraic numbers I*, Mathematika **13** (1966); the case `r = 0` or
`s = 0` is already Hermite–Lindemann.)  It is **not** a consequence of
`SixExponentialsShifted`: see `fiveExponentials_of_shifted`. -/
def BakerTwoLogs : Prop :=
  ∀ (ℓ : Fin 2 → ℂ) (r : Fin 2 → ℚ) (γ : ℂ), (∀ i, IsAlgebraic ℚ (exp (ℓ i))) →
    IsAlgebraic ℚ γ → γ ≠ 0 → γ ≠ (r 0 : ℂ) * ℓ 0 + (r 1 : ℂ) * ℓ 1

/-- **The five exponentials theorem, from the shifted six exponentials theorem plus Baker.**
Take `y₃ = γ/x₂`, so that `x₁y₃ = γx₁/x₂` is the fifth number and `x₂y₃ − γ = 0` makes the
sixth exponential `e⁰ = 1`.  The one thing the shifted six exponentials theorem cannot supply is
the `ℚ`-linear independence of `y₁, y₂, γ/x₂`; in the degenerate case `γ` becomes a nonzero
`ℚ`-linear combination of the two logarithms `x₂y₁, x₂y₂`, which is exactly what Baker's
theorem forbids. -/
theorem fiveExponentials_of_shifted_of_baker (h : SixExponentialsShifted) (hB : BakerTwoLogs) :
    FiveExponentials := by
  intro x y γ hx hy hγ hγ0
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h4, h5⟩ := hcon
  simp only [Transcendental, not_exists, not_not] at h4
  rw [Transcendental, not_not] at h5
  have hx1 : x 1 ≠ 0 := hx.ne_zero 1
  set y₃ : ℂ := γ / x 1 with hy₃
  -- the two exponentials in the third column
  have hcol1 : x 0 * y₃ = γ * x 0 / x 1 := by rw [hy₃]; field_simp
  have hcol2 : x 1 * y₃ - γ = 0 := by rw [hy₃]; field_simp; ring
  by_cases hdep : y₃ ∈ Submodule.span ℚ (Set.range y)
  · -- degenerate: `γ = r₀ (x₁y₀) + r₁ (x₁y₁)`, a Baker relation
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hdep
    rw [Fin.sum_univ_two] at hr
    simp only [Rat.smul_def] at hr
    refine hB ![x 1 * y 0, x 1 * y 1] r γ ?_ hγ hγ0 ?_
    · intro i; fin_cases i
      · exact h4 1 0
      · exact h4 1 1
    · have : γ = x 1 * y₃ := by rw [hy₃]; field_simp
      rw [this, ← hr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
  · -- generic: apply the shifted six exponentials theorem
    have hyy : LinearIndependent ℚ (Fin.snoc y y₃ : Fin 3 → ℂ) :=
      linearIndependent_finSnoc.2 ⟨hy, hdep⟩
    obtain ⟨i, j, htr⟩ := h x (Fin.snoc y y₃)
      (fun i j => if j = 2 ∧ i = 1 then γ else 0) hx hyy
      (by intro i j; split; exacts [hγ, isAlgebraic_zero])
    refine htr ?_
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

/-
**`fiveExponentials_of_shifted` is NOT derivable from `SixExponentialsShifted` alone**
(2026-09-29).  The natural — and, as `fiveExponentials_of_shifted_of_baker` above shows, the
only — route applies the shifted six exponentials theorem to `y = (y₀, y₁, γ/x₁)`, with the
shift `β₁₂ = γ` turning the sixth exponential into `e⁰ = 1`.  The frozen
`SixExponentialsShifted` demands that those three `y` be `ℚ`-linearly independent, and nothing
in the hypotheses of `FiveExponentials` supplies that: `γ/x₁ ∈ span_ℚ{y₀, y₁}` is a consistent
configuration.

In that degenerate case the statement collapses to exactly `BakerTwoLogs`: writing
`γ/x₁ = r₀y₀ + r₁y₁` gives `γ = r₀(x₁y₀) + r₁(x₁y₁)`, a nonzero algebraic number as a
`ℚ`-linear combination of the two logarithms `x₁y₀`, `x₁y₁` (logarithms because `e^{x₁y_j}` is
among the five assumed-algebraic numbers).  With `r₀ = 0` or `r₁ = 0` that is already
Hermite–Lindemann; with both nonzero it is Baker's theorem on linear forms in two logarithms,
which is strictly deeper than the six exponentials theorem and is not among this repo's
`Literature/` inputs (adding it there is an operator decision — `Literature/` is frozen).

So the honest content of Waldschmidt's remark that Cor. 2.1 "covers both" theorems is that his
Cor. 2.1 is applied alongside Baker, or is stated with a weaker independence hypothesis than
the one frozen here.  The reduction is fully proved above; only `BakerTwoLogs` is missing.  **Under Schanuel it is
not missing**: `bakerTwoLogs_of_schanuel` below proves `BakerTwoLogs`, so
`fiveExponentials_of_shifted_of_schanuel` closes the five exponentials theorem from the shifted
six exponentials theorem plus Schanuel.  What stays open is only the *unconditional* form.
-/
/-- `Baker1966` (the inhomogeneous linear forms theorem) specialises to `BakerTwoLogs`: take
`n = 2`, `β = (γ, -r₀, -r₁)`. -/
theorem bakerTwoLogs_of_baker1966 (hB : Baker1966) : BakerTwoLogs := by
  intro ℓ r γ hexp hγ hγ0 heq
  refine hB 2 ![γ, -((r 0 : ℚ) : ℂ), -((r 1 : ℚ) : ℂ)] ℓ ?_ hexp (by simpa using hγ0) ?_
  · intro i; fin_cases i
    · exact hγ
    · exact (isAlgebraic_ratCast (r 0)).neg
    · exact (isAlgebraic_ratCast (r 1)).neg
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons]
    rw [heq]; ring

theorem fiveExponentials_of_shifted (h : SixExponentialsShifted) (hB : Baker1966) :
    FiveExponentials :=
  fiveExponentials_of_shifted_of_baker h (bakerTwoLogs_of_baker1966 hB)

theorem sixExponentials_of_strongOverQ (h : StrongSixExponentialsOverQ) : SixExponentials := by
  intro x y hx hy
  obtain ⟨i, j, hmem⟩ := h x y hx hy
  refine ⟨i, j, fun halg => hmem ?_⟩
  exact ⟨1, ![0, 1], ![x i * y j],
    by intro k; fin_cases k; exacts [isAlgebraic_zero, isAlgebraic_one],
    by intro k; fin_cases k; simpa using halg, by simp⟩


/-- Schanuel ⇒ **Baker's theorem for two logarithms** (inhomogeneous, rational coefficients).
If `ℓ₀, ℓ₁` are `ℚ`-linearly independent, Schanuel makes them algebraically independent, and
`γ = r₀ℓ₀ + r₁ℓ₁` with `γ` algebraic then makes `ℓ₁` algebraic over `ℚ(ℓ₀)` — or, when
`r₁ = 0`, makes `ℓ₀` algebraic over `ℚ(ℓ₁)`.  If they are `ℚ`-linearly dependent, the relation
collapses to a rational multiple of a single logarithm, which is Hermite–Lindemann
(`false_of_ratCast_smul_log`). -/
theorem bakerTwoLogs_of_schanuel (hS : SchanuelConjecture) : BakerTwoLogs := by
  intro ℓ r γ hexp hγ hγ0 heq
  by_cases hli : LinearIndependent ℚ ![ℓ 0, ℓ 1]
  · by_cases hr1 : r 1 = 0
    · -- `γ = r₀ℓ₀`: make `ℓ₀` algebraic over `ℚ(ℓ₁)`
      have hli' : LinearIndependent ℚ ![ℓ 1, ℓ 0] := by
        have he : ![ℓ 1, ℓ 0] = ![ℓ 0, ℓ 1] ∘ ⇑(Equiv.swap (0 : Fin 2) 1) := by
          funext i; fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
        rw [he]
        exact hli.comp _ (Equiv.swap (0 : Fin 2) 1).injective
      have hind : AlgebraicIndependent ℚ ![ℓ 1, ℓ 0] :=
        algebraicIndependent_of_exp_isAlgebraic hS _ hli'
          (by intro i; fin_cases i; exacts [hexp 1, hexp 0])
      refine not_isAlgebraic_of_algebraicIndependent_pair hind ?_
      have hr0 : ((r 0 : ℚ) : ℂ) ≠ 0 := by
        intro h0
        refine hγ0 ?_
        rw [heq, h0, hr1]; push_cast; ring
      have hval : ℓ 0 = γ / ((r 0 : ℚ) : ℂ) := by
        rw [eq_div_iff hr0, heq, hr1]; push_cast; ring
      rw [hval]
      exact isAlgebraic_div_left (hγ.tower_top _)
        ((isAlgebraic_ratCast (r 0)).tower_top _)
    · -- `ℓ₁ = (γ − r₀ℓ₀)/r₁` is algebraic over `ℚ(ℓ₀)`
      have hind : AlgebraicIndependent ℚ ![ℓ 0, ℓ 1] :=
        algebraicIndependent_of_exp_isAlgebraic hS _ hli
          (by intro i; fin_cases i; exacts [hexp 0, hexp 1])
      refine not_isAlgebraic_of_algebraicIndependent_pair hind ?_
      have hr1' : ((r 1 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hr1
      have hm0 : ℓ 0 ∈ IntermediateField.adjoin ℚ ({ℓ 0} : Set ℂ) := subset_adjoin _ _ rfl
      have hval : ℓ 1 = (γ - ((r 0 : ℚ) : ℂ) * ℓ 0) / ((r 1 : ℚ) : ℂ) := by
        rw [eq_div_iff hr1']; linear_combination -heq
      rw [hval]
      refine isAlgebraic_div_left (isAlgebraic_sub_left (hγ.tower_top _) ?_)
        ((isAlgebraic_ratCast (r 1)).tower_top _)
      exact isAlgebraic_mul_rat (isAlgebraic_ratCast (r 0))
        (isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ ({ℓ 0} : Set ℂ)) (A := ℂ)
          ⟨_, hm0⟩)
  · -- dependent: the relation collapses to a rational multiple of one logarithm
    rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨a, b, hab, hne⟩ := hli
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Rat.smul_def] at hab
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by
        by_contra ha; exact (hne ha) rfl
      have hℓ0 : ℓ 0 = 0 := by
        have ha' : ((a : ℚ) : ℂ) ≠ 0 := by exact_mod_cast ha
        have : ((a : ℚ) : ℂ) * ℓ 0 = 0 := by push_cast at hab ⊢; linear_combination hab
        exact (mul_eq_zero.1 this).resolve_left ha'
      exact false_of_ratCast_smul_log hS (c := r 1) (hexp 1) hγ hγ0
        (by rw [heq, hℓ0]; ring)
    · have hb' : ((b : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hb
      have hval : ℓ 1 = -((a : ℚ) : ℂ) / ((b : ℚ) : ℂ) * ℓ 0 := by
        field_simp
        linear_combination hab
      exact false_of_ratCast_smul_log hS (c := r 0 - r 1 * a / b) (hexp 0) hγ hγ0
        (by rw [heq, hval]; push_cast; field_simp; ring)

/-- Schanuel ⇒ the five exponentials theorem from the shifted six exponentials theorem: the one
missing ingredient of `fiveExponentials_of_shifted_of_baker` is Baker's theorem for two
logarithms, and Schanuel supplies it. -/
theorem fiveExponentials_of_shifted_of_schanuel (h : SixExponentialsShifted)
    (hS : SchanuelConjecture) : FiveExponentials :=
  fiveExponentials_of_shifted_of_baker h (bakerTwoLogs_of_schanuel hS)



/-- `iπ` and `1` are `ℚ`-linearly independent. -/
theorem linearIndependent_I_mul_pi_one :
    LinearIndependent ℚ ![Complex.I * (Real.pi : ℂ), (1 : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Rat.smul_def] at hst
  have him := congrArg Complex.im hst
  have hre := congrArg Complex.re hst
  simp [Real.pi_ne_zero] at him hre
  exact ⟨him, hre⟩

/-- **Unconditional, from the five exponentials theorem: a special case of the four
exponentials conjecture.**  For any `ℚ`-linearly independent `y₀, y₁`, one of the four numbers
`e^{iπy₀}, e^{iπy₁}, e^{y₀}, e^{y₁}` is transcendental.  The five exponentials theorem is
applied with `x = (iπ, 1)` and `γ = 1`, so that its fifth number is
`e^{γx₀/x₁} = e^{iπ} = −1`, which is algebraic and therefore cannot be the transcendental
one. -/
theorem exists_transcendental_I_pi_row (h5 : FiveExponentials) {y : Fin 2 → ℂ}
    (hy : LinearIndependent ℚ y) :
    ∃ i j : Fin 2,
      Transcendental ℚ (Complex.exp (![Complex.I * (Real.pi : ℂ), (1 : ℂ)] i * y j)) := by
  rcases h5 ![Complex.I * (Real.pi : ℂ), (1 : ℂ)] y 1 linearIndependent_I_mul_pi_one hy
    isAlgebraic_one one_ne_zero with hcase | hcase
  · exact hcase
  · exfalso
    refine hcase ?_
    have hval : (1 : ℂ) * (![Complex.I * (Real.pi : ℂ), (1 : ℂ)] 0)
        / (![Complex.I * (Real.pi : ℂ), (1 : ℂ)] 1) = Complex.I * (Real.pi : ℂ) := by
      simp
    rw [hval, show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_mul_I]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-1))

/-- **Unconditional**: one of `2^{iπ}`, `3^{iπ}` is transcendental.  Apply the previous theorem
to `y = (log 2, log 3)`: its other two numbers are `e^{log 2} = 2` and `e^{log 3} = 3`, both
algebraic. -/
theorem two_or_three_cpow_I_pi (h5 : FiveExponentials) :
    Transcendental ℚ (Complex.exp (Complex.I * (Real.pi : ℂ) * ((Real.log 2 : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * (Real.pi : ℂ) * ((Real.log 3 : ℝ) : ℂ))) := by
  obtain ⟨i, j, htr⟩ := exists_transcendental_I_pi_row h5 linearIndependent_log_two_three
  fin_cases i <;> fin_cases j
  · exact Or.inl (by simpa [mul_assoc] using htr)
  · exact Or.inr (by simpa [mul_assoc] using htr)
  · refine absurd ?_ htr
    show IsAlgebraic ℚ (Complex.exp ((1 : ℂ) * ((Real.log 2 : ℝ) : ℂ)))
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2 : ℚ)
  · refine absurd ?_ htr
    show IsAlgebraic ℚ (Complex.exp ((1 : ℂ) * ((Real.log 3 : ℝ) : ℂ)))
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (3 : ℚ)



/-- `log 2` is irrational, unconditionally: `log 2 = num/den` would make `e^num = 2^den`, so
`e` would be a root of `X^num − 2^den`. -/
theorem irrational_log_two : Irrational (Real.log 2) := by
  rintro ⟨q, hq⟩
  have h2 : Real.exp (q : ℝ) = 2 := by
    rw [hq, Real.exp_log (by norm_num)]
  have hqpos : 0 < (q : ℝ) := by
    rw [hq]; exact Real.log_pos (by norm_num)
  have hnum : 0 < q.num := by
    have : 0 < q := by exact_mod_cast hqpos
    exact Rat.num_pos.2 this
  set N : ℕ := q.num.toNat with hN
  have hNpos : 0 < N := by omega
  have hmul : (q : ℝ) * (q.den : ℝ) = (N : ℝ) := by
    have hd : ((q.den : ℝ)) ≠ 0 := by exact_mod_cast q.den_nz
    have := congrArg (fun t : ℚ => (t : ℝ)) (Rat.mul_den_eq_num q)
    push_cast at this ⊢
    rw [this]
    congr 1
    omega
  have hpow : (Real.exp 1) ^ N = (2 : ℝ) ^ (q.den) := by
    have hA : Real.exp ((q.den : ℝ) * (q : ℝ)) = (2 : ℝ) ^ q.den := by
      rw [Real.exp_nat_mul, h2]
    have hB : ((q.den : ℝ) * (q : ℝ)) = (N : ℝ) * 1 := by
      rw [mul_comm, hmul]; ring
    rw [hB, Real.exp_nat_mul] at hA
    exact hA
  refine LeanFormalizations.Transcendence.e_transcendental ?_
  refine ⟨Polynomial.X ^ N - Polynomial.C ((2 : ℚ) ^ (q.den)), ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C _ hNpos.ne').ne_zero
  · simp [hpow]


/-! ### `StrongSixExponentialsOverQ` as frozen is FALSE -/

/-- Every algebraic number lies in `𝓛̃` (take `n = 0`). -/
theorem mem_logAlgSpan_of_isAlgebraic {z : ℂ} (hz : IsAlgebraic ℚ z) : z ∈ LogAlgSpan :=
  ⟨0, ![z], ![], by intro i; fin_cases i; exact hz, fun i => i.elim0, by simp⟩

/-- `β·ℓ` lies in `𝓛̃` for algebraic `β` and a logarithm `ℓ` of an algebraic number. -/
theorem mem_logAlgSpan_mul {β ℓ : ℂ} (hβ : IsAlgebraic ℚ β)
    (hℓ : IsAlgebraic ℚ (Complex.exp ℓ)) : β * ℓ ∈ LogAlgSpan :=
  ⟨1, ![0, β], ![ℓ], by intro i; fin_cases i; exacts [isAlgebraic_zero, hβ],
    by intro i; fin_cases i; exact hℓ, by simp⟩

theorem isAlgebraic_sqrt_two : IsAlgebraic ℚ ((Real.sqrt 2 : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C _ two_ne_zero).ne_zero
  · have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
      norm_cast
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    simp [h]

theorem linearIndependent_one_sqrt_two_I :
    LinearIndependent ℚ ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ), Complex.I] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def] at hg
  have him := congrArg Complex.im hg
  have hre := congrArg Complex.re hg
  simp at him hre
  have hg1 : g 1 = 0 := by
    by_contra h1
    refine irrational_sqrt_two.ne_rat (-(g 0) / g 1) ?_
    have h1' : (g 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    linarith [hre]
  have hg0 : g 0 = 0 := by
    have h1' : ((g 1 : ℚ) : ℝ) = 0 := by exact_mod_cast hg1
    rw [h1'] at hre
    simp at hre
    exact_mod_cast hre
  intro i; fin_cases i
  · exact hg0
  · exact hg1
  · exact him

/-- **The frozen `Literature.StrongSixExponentialsOverQ` is FALSE as stated** (2026-09-29).  Roy's
strong six exponentials theorem requires `x` and `y` to be linearly independent over the field
of *algebraic* numbers; the frozen statement asks only for `ℚ`-linear independence, and that is
far too weak: `x = (1, log 2)` and `y = (1, √2, i)` are `ℚ`-linearly independent while all six
products `1, √2, i, log 2, √2 log 2, i log 2` lie in `𝓛̃`.  (Over `ℚ̄` the triple `1, √2, i` is
of course dependent, which is exactly what the real theorem rules out.) -/
theorem not_strongSixExponentialsOverQ : ¬ StrongSixExponentialsOverQ := by
  intro h
  obtain ⟨i, j, hmem⟩ := h ![(1 : ℂ), ((Real.log 2 : ℝ) : ℂ)]
    ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ), Complex.I]
    (linearIndependent_one_ofReal irrational_log_two) linearIndependent_one_sqrt_two_I
  refine hmem ?_
  have hlog : IsAlgebraic ℚ (Complex.exp ((Real.log 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2 : ℚ)
  fin_cases i <;> fin_cases j
  · exact mem_logAlgSpan_of_isAlgebraic (by simpa using isAlgebraic_one)
  · exact mem_logAlgSpan_of_isAlgebraic (by simpa using isAlgebraic_sqrt_two)
  · exact mem_logAlgSpan_of_isAlgebraic (by simpa using isAlgebraic_I)
  · show ((Real.log 2 : ℝ) : ℂ) * 1 ∈ LogAlgSpan
    rw [mul_comm]; exact mem_logAlgSpan_mul isAlgebraic_one hlog
  · show ((Real.log 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) ∈ LogAlgSpan
    rw [mul_comm]; exact mem_logAlgSpan_mul isAlgebraic_sqrt_two hlog
  · show ((Real.log 2 : ℝ) : ℂ) * Complex.I ∈ LogAlgSpan
    rw [mul_comm]; exact mem_logAlgSpan_mul isAlgebraic_I hlog


/-- Schanuel ⇒ **Roy's strong six exponentials theorem** (with the corrected `ℚ̄`-independence
hypothesis).  A multi-lap target: the phase-16 handoff sketches the basis-of-logarithms
decomposition, and the `OverQ` refutation shows exactly where `ℚ̄`-independence is used. -/
theorem strongSixExponentials_of_schanuel (hS : SchanuelConjecture) : StrongSixExponentials := by
  sorry

end LeanFormalizations.ExponentialsKnown
