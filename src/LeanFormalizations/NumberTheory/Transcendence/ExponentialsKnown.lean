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
