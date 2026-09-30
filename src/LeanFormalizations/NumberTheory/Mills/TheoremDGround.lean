/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.CoveringEngine

/-!
# Phase 44: groundwork for Theorems D and E (Lemmas 2–4 of `PROOF-THEOREM-D.md`)

The Lean-sized pieces of the Saito-1.7 partial answer (Theorem D) and of the transcendence of
`ξ(3^k + s)` (Theorem E/E+).  Everything here is elementary; the Galois-rigidity step is **not**
in this phase.

## Route
1. `not_stuck_twice` (Lemma 3, pure combinatorics): if `n` is stuck for period `j n` (`ε` flips at
   every `n + k·j n`, `k ≥ 1`) then `n + j n` is not stuck for period `j (n + j n)`.  Proof: take
   `k = j n` at `n′ = n + j n` and `k = 1 + j n′` at `n`.
2. `dvd_trace_sub_of_ord_dvd` (Lemma 2, abstract exponents): if `p` is prime, `p ∤ det C`, and
   `orderOf` of `C` in `GL_d(ZMod p)` divides `a − b` (with `b ≤ a`), then
   `p ∣ tr C^a − tr C^b`.  Reuse the `ZMod p` reduction in
   `SharedConjecture.exists_trace_pow_congr`.
3. `exists_pow_sub_one_of_lt_padicValNat_glCard` (Lemma 4): if `p ≠ c` are primes and
   `n < padicValNat c (glCard d p)`, then there is `1 ≤ i ≤ d` with
   `c ^ (n / d) ∣ p ^ i − 1`.  (`glCard d p = ∏ (p^d − p^i) = p^(…) ∏_(i=1..d) (p^i − 1)`; pigeonhole
   on the `c`-adic valuations.)

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.TheoremDGround

open LeanFormalizations.Mills.ThreeAdic Matrix

/-- **Lemma 3 (stuck indices are isolated).**  `ε` takes two values (`Bool`). -/
theorem not_stuck_twice (ε : ℕ → Bool) (j : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n) (n : ℕ)
    (hstuck : ∀ k, 1 ≤ k → ε (n + k * j n) ≠ ε n) :
    ¬ ∀ k, 1 ≤ k → ε (n + j n + k * j (n + j n)) ≠ ε (n + j n) := by
  sorry

/-- **Lemma 2 (abstract exponents).** -/
theorem dvd_trace_sub_of_orderOf_dvd {d : ℕ} (C : Matrix (Fin d) (Fin d) ℤ) {p : ℕ}
    (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ C.det) {a b : ℕ} (hba : b ≤ a)
    (hord : ∀ D : GL (Fin d) (ZMod p), (D : Matrix (Fin d) (Fin d) (ZMod p)) =
      (Int.castRingHom (ZMod p)).mapMatrix C → orderOf D ∣ a - b) :
    (p : ℤ) ∣ (C ^ a).trace - (C ^ b).trace := by
  sorry

/-- **Lemma 4 (the window).** -/
theorem exists_pow_sub_one_of_lt_padicValNat_glCard {c p d n : ℕ} (hc : c.Prime) (hp : p.Prime)
    (hpc : p ≠ c) (hd : 1 ≤ d) (hn : n < padicValNat c (glCard d p)) :
    ∃ i, 1 ≤ i ∧ i ≤ d ∧ (c : ℤ) ^ (n / d) ∣ (p : ℤ) ^ i - 1 := by
  sorry

end LeanFormalizations.Mills.TheoremDGround
