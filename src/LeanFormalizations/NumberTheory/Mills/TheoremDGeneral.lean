/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDQuadratic

/-!
# Phase 56 (multi-phase): Theorem D in every degree — Saito's Problem 1.7 for `R(n) = c^n + s`

**Target.**  Let `α > 1` be a Pisot number of degree `d ≥ 2`: a root of a monic irreducible
`f ∈ ℤ[X]` whose other complex roots have modulus `< 1`.  Let `c` be a prime with `c ∤ f(0)`, and
`s` with `α^s > d + 1`.  Then `⌊α^(c^n + s)⌋` is **not prime for infinitely many `n`**.
Corollary (degree 3, Saito's "especially"): the plastic number `ρ` (`ρ³ = ρ + 1`), for every prime `c`,
with `s = 5` (`ρ⁵ ≈ 4.08 > 4`).

Paper proof: `PROOF-THEOREM-D.md` draft 2 (the one-automorphism size argument; with `c ∤ f(0)` every
root is a `c`-unit, so no automorphism is needed).

## Route: generalize phase 55 (read `HANDOFF-2026-09-30-phase55-complete.md` first)
Phase 55 found that the whole `c`-adic → archimedean transfer is **integer polynomial equations +
Nullstellensatz + integrality** (`TheoremDQuadratic.exists_complex_zero_of_all_levels`, which is
already stated for a general finite variable set `σ`).  For degree `d`:
1. **Floor = trace + offset.**  `⌊α^N⌋ = tr C^N + ε_N`, `ε_N ∈ {0, −1}`, for large `N` (`C` the
   companion matrix of `f`; `tr C^N = Σ_k α_k^N`; `δ_N = Σ_(k≥2) α_k^N` is real and `→ 0`; if
   `δ_N = 0` then `α^N ∈ ℤ`, impossible for `d ≥ 2` since its conjugates would have modulus `> 1`).
2. **Filter, stuck alternation, good indices unbounded:** as in phases 44/55, with `GL_d(𝔽_p)`.
3. **Window:** at a good `n`, `p_n^i ≡ 1 (mod c^(e_n))` for some `1 ≤ i ≤ d`, `e_n → ∞`.
4. **Pigeonhole** on (the residue of `n` mod the Teichmüller period `D`, which divides
   `lcm_(f ≤ d)(c^f − 1)`-related data; the pair `(i, ε)`).
5. **Integer system at every level `k`:** variables `x₀, …, x_(d−1)` (for `T = Σ x_j C^j`) and `w`,
   with equations `T^Q = I` (`Q = |GL_d(𝔽_c)|`), `w^(i·m) = 1` for a suitable `m` (or `w^i = 1` after
   the window's lifting), and `tr(T·C^s) = w − ε`.  Integer solutions mod `c^k` for every `k` come
   from `T ≡ C^(c^n)` (phase 47/55 torsion congruence) and `w ≡ p_n`.
6. **Transfer:** `exists_complex_zero_of_all_levels` gives a complex solution.
7. **Size:** over ℂ, `T = P(C)` with `P(X) = Σ x_j X^j`, and `C` is diagonalizable with eigenvalues
   `α_k` (distinct: `f` separable), so `tr(T C^s) = Σ_k u_k α_k^s` with `u_k = P(α_k)`, `u_k^Q = 1`,
   and `|w| = 1`.  So `α^s ≤ |w − ε| + Σ_(k≥2) |α_k|^s < 2 + (d − 1) = d + 1`: contradiction.
   (Avoid diagonalization if easier: `u_k = P(α_k)` satisfies `u_k^Q = 1` because `P(X)^Q − 1` is
   divisible by `f` over ℂ... it vanishes at the matrix `C`, whose minimal polynomial is `f`.)

**Decomposing into named sub-lemmas is progress**; generalize phase-55 lemmas rather than copying
them where it is cheap.  Do not change phase 55's frozen statement.

Frozen: the two statements below; all earlier statements; `Literature/`.  No `private`.
(Window encoding hint: at level `k`, `p_n ≡ ω (mod c^k)` with `ω` a `c`-adic root of unity; use the
integer Teichmüller residue `w`, `w^(c−1) ≡ 1` (`c` odd) or `w² ≡ 1` (`c = 2`), as the extra variable.)
-/

namespace LeanFormalizations.Mills.TheoremDGeneral

open Filter Polynomial

/-- **Theorem D, every degree** (all roots `c`-units). -/
theorem floor_pow_prime_pow_add_not_prime_general (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hroot : aeval α f = 0)
    (hα : 1 < α)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) (hc0 : ¬ (c : ℤ) ∣ f.coeff 0)
    {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  sorry

/-- **Degree 3 (Saito's "especially"):** the plastic number, every prime `c`, shift `5`. -/
theorem plastic_floor_pow_prime_pow_add_not_prime {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ1 : 1 < ρ)
    {c : ℕ} (hc : c.Prime) :
    ∃ᶠ n in atTop, ¬ (⌊ρ ^ (c ^ n + 5)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDGeneral
