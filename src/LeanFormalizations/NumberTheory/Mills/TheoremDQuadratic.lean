/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDGround
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence

/-!
# Phase 55 (multi-phase): Theorem D, quadratic case — Saito's Problem 1.7 for `R(n) = c^n + s`

**Target.**  Let `α > 1 > |β|` be the roots of `X² − aX + b` (`a, b ∈ ℤ`, `a² − 4b` not a square), `c`
a prime with `c ∤ b` and `c ∤ a² − 4b`, and `s ≥ 4`.  Then `⌊α^(c^n + s)⌋` is **not prime for
infinitely many `n`**.  (`PROOF-THEOREM-D.md`, draft 2, specialized to `d = 2`; `s₀(2) = 4` since
`κ^4 > 3`.  The hypotheses `c ∤ b` (both roots are `c`-units) and `c ∤ disc` (unramified) are
simplifications for this first Lean version.)

## Proof on paper (draft 2), and the Lean route WITHOUT `c`-adic completions
Notation: `C` = companion matrix, `p_n = ⌊α^(c^n+s)⌋ = tr C^(c^n+s) + ε_n`, `ε_n ∈ {0, −1}`
(`ε_n = −1` iff `β^(c^n+s) > 0`).
1. **Filter / stuck / window** (`TheoremDGround`, phase 44): if every `p_n` (`n ≥ n₀`) is prime, then
   infinitely many `n` are good, and for good `n`, `p_n ≡ ±1 (mod c^(e_n))`, `e_n → ∞`.  So along a
   residue class `r (mod 2)` and a fixed pair `(ω, ε)`: `tr C^(c^n+s) ≡ t := ω − ε (mod c^(e_n))`,
   `t ∈ {−1, 0, 1, 2}`.
2. **Number field, no completion.**  Let `q = c²` (the residue field of `ℚ(α)` at `c` is `𝔽_c` or
   `𝔽_(c²)`), `K = ℚ(α, ζ)` with `ζ` a primitive `(q−1)`-th root of unity, `𝔓` a prime of `𝒪_K` over
   `c`.  Since `c ∤ q − 1`, the `(q−1)`-th roots of unity reduce **injectively** mod `𝔓`, and the
   residue field contains `𝔽_q`, so each unit `x ∈ 𝒪_K` has a unique **Teichmüller** `ζ_x ∈ μ_(q−1)`
   with `x ≡ ζ_x (mod 𝔓)`.  Then `x^(c^n) ≡ ζ_x^(c^n) (mod 𝔓^(n+1))` (`TeichmullerCongruence`-style
   lifting, in `𝒪_K` instead of matrices).
3. **Spectral form.**  `C^N = α^N E₁ + β^N E₂`, `E₁ = (C − β)/(α − β)`.  `α − β` is a `𝔓`-unit
   (`c ∤ disc`).  So `tr(C^(c^n) C^s) ≡ Λ_r := ζ₁^(c^r) α^s + ζ₂^(c^r) β^s (mod 𝔓^(n+1))` for
   `n ≡ r (mod 2)` (`ζ^(c^n)` depends on `n mod 2`, as `c² ≡ 1 (mod q − 1)`).
4. **Separation:** `Λ_r − t ∈ 𝔓^m` for all `m` ⇒ `Λ_r = t` (`Ideal.iInf_pow_eq_bot_of_isDomain`
   / Krull, or `Algebra.norm` of a nonzero element has bounded `c`-valuation).
5. **Size (draft 2), no rigidity.**  `c ∤ b` makes `α` a unit at `𝔓`, so `ζ₁ ≠ 0` and no automorphism is
   needed.  In the real embedding: `α^s = |ζ₁^(c^r) α^s| ≤ |t| + |β|^s < 2 + 1 = 3`.  But the least
   quadratic Pisot number is the golden ratio `φ`, and `α^s ≥ α^4 ≥ φ^4 ≈ 6.85 > 3`.  (Enough: `α^4 > 3`
   from the integrality of `a, b`: `α + β = a ≥ 2` when `α > 1 > |β|`, unless `a = 1`, where `α ≥ φ`.)

## How to proceed (treadmill)
This is a MULTI-PHASE target.  A lap succeeds by advancing the crux.  **Decomposing the frozen
theorem into named, stated sub-lemmas (each `sorry`) is progress**; so is proving any of them.
Suggested nodes: `teichmuller_exists` (step 2), `pow_c_pow_congr_teich` (step 2), `spectral_trace`
(step 3), `eq_of_mem_pow_all` (step 4), `alpha_pow_four_gt_three` (step 5), and the assembly.  If
mathlib's number-field API makes step 2 painful, an alternative is to work in the explicit ring
`ℤ[X]/(X² − aX + b) ⊗ ℤ[ζ]` modulo powers of `c`, or in `ZMod (c^m)` Galois rings as in phase 51.

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.TheoremDQuadratic

open Filter

/-- **Theorem D, quadratic case.** -/
theorem floor_pow_prime_pow_add_not_prime (a b : ℤ) {α β : ℝ} (hsum : α + β = a)
    (hprod : α * β = b) (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    {s : ℕ} (hs : 4 ≤ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDQuadratic
