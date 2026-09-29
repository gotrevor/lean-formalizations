/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Corvaja–Zannier (2004) from Stephan's Subspace Theorem — closing the phase-9 wall

Phase 9 (`DubickasNoSubspace.lean`, `PROBE-DUBICKAS-NOSUBSPACE.md`) reduced Dubickas's Lemma 6
to Corvaja–Zannier's Main Theorem, which needs the `p`-adic Subspace Theorem, and left two
disclosed `sorry`s: `corvajaZannier_dichotomy` and `corvajaZannier_lemma4`.  R. Stephan has now
machine-checked the Subspace Theorem with several places (`Literature.Stephan2026Subspace`,
verbatim) and Ridout/Roth (`Literature.Stephan2026Ridout`).  This file derives the two phase-9
statements, and then `Dubickas2022`, from those two `Prop`s.  Once the toolchains meet
(`PROBE-ROTH.md`) the whole Dubickas Theorem 1 chain becomes unconditional.

## Source

P. Corvaja, U. Zannier, *On the rational approximations to the powers of an algebraic number:
solution of two problems of Mahler and Mendès France*, Acta Math. **193** (2004), 175–191,
arXiv:math/0403522; local text `papers/corvaja-zannier-2004-powers-algebraic.txt` (gitignored).
12 pages.  They apply the Subspace Theorem "in the form [S, Theorem 1D′]" (Schmidt, LNM 1467):
number field `K`, finite set of places `S`, linearly independent forms per place — which is
exactly `Stephan2026Subspace`.

## Route (CZ's numbering)

Setting: `K` Galois over `ℚ` containing `α`, `S` a Galois-stable finite set of places containing
the archimedean ones with `α` an `S`-unit; places normalised as in CZ §2 (Stephan's `approxProd`
raises archimedean factors to `v.mult`, which is CZ's `d(σ)/[K:ℚ]` normalisation up to the global
`1/[K:ℚ]` power — check the exponent bookkeeping once, early).

* **Lemma 1** (from Subspace): an infinite set of `S`-units `u` with
  `|Σ λ_i σ_i(u)|_w < max_i |σ_i(u)|_w · H(u)^(−ε)` has infinitely many members on one nontrivial
  linear relation `Σ a_i σ_i(u) = 0`.  Proof in CZ p. 3: forms `L_{w,1} = Σ λ_i X_i`, coordinate
  forms elsewhere, product formula for `S`-units.
* **Lemma 2** (unit equation, from Subspace, CZ cite [S, Ch. 4]): infinitely many solutions of
  `Σ a_i σ_i(u) = 0` ⇒ infinitely many on some `a σ_i(u) + b σ_j(u) = 0`.  Induction on `n`
  with Lemma 1-style Subspace applications (every vanishing subsum argument).
* **Lemma 3** (the key, from Subspace + Roth): infinitely many `(q, u) ∈ ℤ × (O_S^× ∩ k)` with
  `|δqu| > 1`, `δqu` not pseudo-Pisot, `0 < ‖δqu‖ < H(u)^(−ε) q^(−d−ε)` ⇒ some `u/δ′` lies in a
  proper subfield `k′ ⊂ k` along an infinite subsequence.
* **Main Theorem**: iterate Lemma 3 down the finite subfield lattice to `ℚ`, where Roth
  (`Stephan2026Ridout` ⇒ `Roth1955`, `StephanEdges.lean`) finishes.
* **Lemma 4** (from Lemma 1): if `Tr(q_n αⁿ) ∈ ℤ ∖ {0}` for infinitely many `n` with
  `log q_n = o(n)`, then `α` is an algebraic integer or an `h`-th root of a rational.

Our application needs only `Γ = ⟨α⟩`, `δ = 1`, `q` fixed, `u = α^(s n)`.  Specialise the Main
Theorem as far as it helps; the frozen targets are only the three theorems at the bottom.  Split
any `sorry` into further named leaves freely, restate a leaf if the proof wants another shape.
A precise obstruction written into `PROBE-DUBICKAS-NOSUBSPACE.md` (which step needs what beyond
the two `Prop`s) also counts as progress.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Pisot
import LeanFormalizations.NumberTheory.Diophantine.StephanEdges
import LeanFormalizations.NumberTheory.Transcendence.DubickasNoSubspace

namespace LeanFormalizations.Transcendence.Dubickas

open LeanFormalizations.Literature

/-- `corvajaZannier_dichotomy` (CZ Main Theorem, Dubickas's Lemma 3), from Stephan's Subspace
Theorem and Ridout.  Same conclusion as the phase-9 statement. -/
theorem corvajaZannier_dichotomy_of_stephan (hSub : Stephan2026Subspace)
    (hR : Stephan2026Ridout) {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ}
    (hq : 0 < q) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 0 < s 0)
    (hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * s n)) < |(q : ℝ) * α ^ s n - round ((q : ℝ) * α ^ s n)| := by
  sorry

/-- `corvajaZannier_lemma4` (CZ Lemma 4), from Stephan's Subspace Theorem.  Same statement as the
phase-9 one. -/
theorem corvajaZannier_lemma4_of_stephan (hSub : Stephan2026Subspace) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q)
    (hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α)
    {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α ∨ ∃ (l : ℕ) (r : ℚ), 0 < l ∧ α ^ l = (r : ℝ) := by
  sorry

/-- **Dubickas (2022), Lemma 6, from Stephan's machine-checked Subspace Theorem and Ridout.**
Discharges the last literature input under Dubickas's Theorem 1 (`Dubickas.lean`) down to
Stephan's two theorems. -/
theorem dubickas2022_of_stephan (hSub : Stephan2026Subspace) (hR : Stephan2026Ridout) :
    Dubickas2022 := by
  sorry

end LeanFormalizations.Transcendence.Dubickas
