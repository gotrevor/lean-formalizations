/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremA

/-!
# Phase 54: Theorem A for every `d` when `h ≠ 0`; Tetranacci `T₄(2^n) + h` composite for every `h`

Phase 52's survivor count only used `d` odd to exclude `h = 0`: from `Σ_(k<d) ε_k = d·h` with
`ε_k ∈ {±1}`, `h ≠ 0` already forces `h = ±1` and every `ε_k = h`, for any `d ≥ 1`.  So:

**Theorem A′.**  Same hypotheses as `TheoremA.entry_prime_pow_add_not_prime`, with `Odd d` replaced by
`Odd d ∨ h ≠ 0`.

**Corollary (Tetranacci, `c = 2`).**  `T₄ 0 = T₄ 1 = T₄ 2 = 0`, `T₄ 3 = 1`, `T₄(n+4) = T₄(n+3) + … + T₄ n`.
`X⁴ − X³ − X² − X − 1 ≡ Φ₅ (mod 2)` is irreducible (`ord₅ 2 = 4`); `μ(ℤ₂) = {±1}`; `T₄(2^2) = T₄ 4 = 1`
is odd.  So `T₄(2^n) + h` is composite i.o. for every `h ≠ 0`.  For `h = 0`: by the period
(`OrbitSum.pow_prime_pow_add_card_congr` at `n = 0`, `d = 4`), `T₄(2^(4k)) ≡ T₄(1) = 0 (mod 2)`, and
`T₄(2^(4k)) > 2` for `k ≥ 1`, so it is even and composite.  Hence **every `h`**.
Hypotheses checked by `scripts/theorem-a-tetranacci-probe.py`.  (At `c = 5` the charpoly is also
irreducible, but `μ₄ ⊂ ℤ₅` breaks the window, so `c = 5` is not claimed.)
`T₄ N = (A^N) 3 0` for `A = !![1,1,1,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]`.

## Route
Copy phase 52's proof of `entry_prime_pow_add_not_prime`, replacing the parity step by the case split.
Ideally refactor phase 52's proof into a public lemma that takes the counting step as input.  Do NOT
change phase 52's frozen statements.

Frozen: the two statements below and the def `tetra`; all earlier statements; `Literature/`.
No `private`.
-/

namespace LeanFormalizations.Mills.TheoremAEven

open Matrix Filter

/-- **Theorem A′** (any `d`, `h ≠ 0`). -/
theorem entry_prime_pow_add_not_prime' {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c))))
    (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) {i j : Fin d} (hij : i ≠ j)
    (hnz : ∃ r < d, ¬ (c : ℤ) ∣ (A ^ (c ^ r)) i j)
    (hgrow : Tendsto (fun n => |(A ^ (c ^ n)) i j|) atTop atTop) (h : ℤ) (hdh : Odd d ∨ h ≠ 0) :
    ∃ᶠ n in atTop, ¬ Prime ((A ^ (c ^ n)) i j + h) := by
  sorry

/-- Tetranacci: `T₄ 0 = T₄ 1 = T₄ 2 = 0`, `T₄ 3 = 1`. -/
def tetra : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => tetra (n + 3) + tetra (n + 2) + tetra (n + 1) + tetra n

/-- **`T₄(2^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem tetra_two_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (tetra (2 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.TheoremAEven
