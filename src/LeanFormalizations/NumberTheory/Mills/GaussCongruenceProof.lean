/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.UnipotentTrace

/-!
# Phase 49: the Gauss (Dold) congruence for matrix traces, proved; phase 29 becomes unconditional in it

Discharges the Literature hypothesis `Literature.GaussCongruenceTrace` (Steinlein, AMM 2017) by the
elementary necklace argument, and restates phase 29's 3-adic Mills results without it.

## Route (necklace counting)
`tr(A^N) = Σ_(w : Fin N → Fin n) ∏_t A (w t) (w (t+1 mod N))` (closed walks).  The cyclic group
`ℤ/N` acts by rotation, and the weight `f(w)` is rotation-invariant.  Take `N = p^(k+1)`.
1. Words **not** fixed by rotation by `p^k` have trivial stabilizer, since stabilizers are subgroups of
   the cyclic `p`-group `ℤ/p^(k+1)`.  So their orbits have size `p^(k+1)` and their total weight is
   `≡ 0 (mod p^(k+1))`.  (Sum over orbits; e.g. `Finset.sum_partition`/`MulAction` orbit–stabilizer; or
   avoid group actions by grouping words `w` with their rotations explicitly.)
2. Words fixed by rotation by `p^k` are exactly `w = u^p` with `u` of length `p^k`, and
   `f(u^p) = f(u)^p`.  So that part equals `Σ_u f(u)^p`.
3. **Lemma:** `Σ_(u : length p^k) f(u)^p ≡ Σ_u f(u) (mod p^(k+1))`.  Induct on `k`, or group `u` by
   minimal period `p^j` (`u = v^(p^(k−j))`, `v` primitive).  An orbit of size `p^j` contributes
   `p^j (f(v)^(p^(k−j+1)) − f(v)^(p^(k−j)))`, and `a^(p^(m+1)) ≡ a^(p^m) (mod p^(m+1))`
   (`Int.ModEq.pow_card_sub_one_eq_one`-style / LTE; this is the classical Euler–Fermat for prime powers).
   **Alternative (often easier in Lean):** strong induction on `k`, using step 2 at level `k` and the
   statement at level `k − 1` applied to the matrix whose "walk weights" are `f(u)`: that is, apply the
   statement to `A^(p^?)` or to Kronecker powers.  Choose whatever closes.
4. Assemble: `tr A^(p^(k+1)) = (≡ 0) + Σ_u f(u)^p ≡ Σ_u f(u) = tr A^(p^k)`.

A known short alternative proof: via `Matrix.charpoly` and Newton's identities over `ZMod (p^(k+1))`
— more Mathlib-heavy.  The necklace route is fully elementary.

Frozen: the statements below; all earlier statements (ThreeAdic's hypothesised theorems stay as they
are); `Literature/` (the def `GaussCongruenceTrace` is frozen; we PROVE it here).  No `private`.
-/

namespace LeanFormalizations.Mills.GaussCongruenceProof

open LeanFormalizations.Literature LeanFormalizations.Mills LeanFormalizations.Mills.ThreeAdic Filter

/-- **The Gauss congruence for traces holds** (discharging the Literature hypothesis). -/
theorem gaussCongruenceTrace_holds : GaussCongruenceTrace := by
  sorry

/-- Phase 29 (`ThreeAdic.mills_threeAdic`) without the Gauss-congruence hypothesis. -/
theorem mills_threeAdic' (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) (halg : IsAlgebraic ℚ A) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨ (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e] := by
  sorry

/-- Phase 29 (`ThreeAdic.transcendental_of_not_pm_one`) without the Gauss-congruence hypothesis. -/
theorem transcendental_of_not_pm_one' (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) {e : ℕ}
    (h : ∃ᶠ k in atTop, ¬ ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e])) :
    Transcendental ℚ A := by
  sorry

end LeanFormalizations.Mills.GaussCongruenceProof
