/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Edges out of Stephan's machine-checked Ridout theorem

`Literature.Stephan2026Ridout` is `Rat.finite_setOf_ridout` from R. Stephan's
`rwst/Subspace-Theorems` (Lean 4, sorry-free there, 2026), stated verbatim.  Deriving this repo's
paper-sourced Diophantine `Prop`s from it moves their foundation from "cited paper" to "proved in
Lean elsewhere, waiting on a toolchain match" (`PROBE-ROTH.md`).

Notation: `‖β‖_S₁ := ∏_{l ∈ S₁} |β.num|_l`, `‖β‖_S₂ := ∏_{l ∈ S₂} |β.den|_l`,
`H(β) := max(|β.num|, β.den)`.  Stephan: `{β | |ξ − β| ‖β‖_S₁ ‖β‖_S₂ ≤ H(β)^(−2−ε)}` is finite.

## `roth1955_of_stephan`
`S₁ = S₂ = ∅`, `ε = δ/2`.  If `|α − r| < r.den^(−2−δ)` then `|r| ≤ |α| + 1`, so
`H(r) ≤ (|α| + 1) r.den`, and `r.den^(−2−δ) ≤ H(r)^(−2−δ/2)` once `r.den` is large
(`(|α|+1)^(2+δ/2) ≤ r.den^(δ/2)`).  Rationals with bounded denominator near `α` are finitely many.

## `ridoutSUnitDen_of_stephan`
`S₁ = ∅`, `S₂ = S` (as `Nat.Primes`).  A denominator with all prime factors in `S` has
`∏_{l∈S} |q|_l = 1/q`.  So `|α − r| < q^(−1−δ)` gives `|α − r| · (1/q) < q^(−2−δ)`, then the same
`H ≤ (|α|+1) q` comparison with `ε = δ/2`.

## `mahler_mul_of_stephan` (hence `mahler1957_of_stephan`, `q = 1`)
Same statement as `Diophantine.mahler_mul_of_ridout1957`.  `α = u/v` lowest terms, `v ≥ 2`,
`p* = round(q αⁿ)`, `β = p* vⁿ / uⁿ` (reduce by `g = gcd(p* vⁿ, uⁿ) = gcd(p*, uⁿ)`), target
`ξ = q`, `S₁` = primes of `v`, `S₂` = primes of `u`.  Then `vⁿ ∣ β.num` so `‖β‖_S₁ ≤ v^(−n)`;
`β.den = uⁿ/g` is an `S₂`-unit so `‖β‖_S₂ = g/uⁿ`; `H(β) ≤ C uⁿ / g` (as `p* ≤ 2q αⁿ`).
If `|q αⁿ − p*| ≤ e^(−εn)` then `|q − β| = (v/u)ⁿ |q αⁿ − p*| ≤ (v/u)ⁿ e^(−εn)`, so the product is
`≤ g u^(−2n) e^(−εn) ≤ H(β)^(−2−ε')` with `ε' = ε / (2 log u)` for large `n` (`g ≥ 1`).  Distinct
large `n` give distinct `β` (`β.den · g = uⁿ`, and `β ≠ q` exactly as in the Ridout-1957 proof),
so finiteness of Stephan's set bounds `n`.  Check the `C` bookkeeping; `ε'` may need shrinking.

## `Mills.irrational_of_stephan`
`Mills.irrational hB hM (mahler1957_of_stephan hS)`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.Diophantine.Edges
import LeanFormalizations.NumberTheory.Mills.Irrational

namespace LeanFormalizations.Diophantine

open LeanFormalizations.Literature

/-- Stephan's Ridout ⇒ Thue–Siegel–Roth. -/
theorem roth1955_of_stephan (h : Stephan2026Ridout) : Roth1955 := by
  sorry

/-- Stephan's Ridout ⇒ Ridout's `S`-unit-denominator corollary. -/
theorem ridoutSUnitDen_of_stephan (h : Stephan2026Ridout) : Ridout1957SUnitDen := by
  sorry

/-- Stephan's Ridout ⇒ Mahler (1957) with a factor `q`, the form Dubickas uses.  Same statement
as `mahler_mul_of_ridout1957`. -/
theorem mahler_mul_of_stephan (h : Stephan2026Ridout) (q : ℕ) (hq : 0 < q) (α : ℚ)
    (hα1 : 1 < α) (hden : α.den ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * n)) < |(q : ℝ) * (α : ℝ) ^ n - round ((q : ℝ) * (α : ℝ) ^ n)| := by
  sorry

/-- Stephan's Ridout ⇒ Mahler (1957). -/
theorem mahler1957_of_stephan (h : Stephan2026Ridout) : Mahler1957 := by
  sorry

end LeanFormalizations.Diophantine

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **Mills' constant is irrational, on Baker–Harman–Pintz, Matomäki and a machine-checked
Ridout.**  Same statement as `irrational`, with `Mahler1957` replaced by `Stephan2026Ridout`. -/
theorem irrational_of_stephan (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hS : Stephan2026Ridout) {A : ℝ} (hA : IsMinMills A) : Irrational A := by
  sorry

end LeanFormalizations.Mills
