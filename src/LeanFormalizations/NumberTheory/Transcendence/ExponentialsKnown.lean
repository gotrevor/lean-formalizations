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
  `StrongSixExponentials ⇒ SixExponentials` (if every `e^{xᵢyⱼ}` were algebraic, every `xᵢyⱼ`
  would be a logarithm, hence in `LogAlgSpan`).
* **Five exponentials ⇒** `e^{π²}` or `2^{√2}`-style corollaries: left to the lap to choose one
  (Waldschmidt 2023 §6 lists them); add as a new theorem.

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
the one frozen here.  The reduction is fully proved above; only `BakerTwoLogs` is missing.
-/
theorem fiveExponentials_of_shifted (h : SixExponentialsShifted) : FiveExponentials := by
  sorry

theorem sixExponentials_of_strong (h : StrongSixExponentials) : SixExponentials := by
  intro x y hx hy
  obtain ⟨i, j, hmem⟩ := h x y hx hy
  refine ⟨i, j, fun halg => hmem ?_⟩
  exact ⟨1, ![0, 1], ![x i * y j],
    by intro k; fin_cases k; exacts [isAlgebraic_zero, isAlgebraic_one],
    by intro k; fin_cases k; simpa using halg, by simp⟩

end LeanFormalizations.ExponentialsKnown
