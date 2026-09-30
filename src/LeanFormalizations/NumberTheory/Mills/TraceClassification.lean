/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.CoveringEngine

/-!
# Phase 42: 2×2 traces at odd primes — `DoubleExpTraceComposite` for `n = 2`, classified

Theorem B of `ROADMAP-PRIME-TOWERS.md`.  Take `C ∈ M₂(ℤ)` and an odd prime `c` with
`det C ≡ ε = ±1 (mod c)`, `c ∤ tr C`, `c ∤ disc C`.  Then `tr C^(c^n) + h` is composite i.o. for
**every** `h`, except when `ε = 1` and `tr C ≡ ±1 (mod c)`, i.e. `χ_C ≡ X² ∓ X + 1 = Φ₆, Φ₃`.  In that
case the `c`-adic limit is exactly `τ = ±1`, and the shifts `h ∈ {0, ∓2}` genuinely survive the
filter (Fermat-type).  Numerics: 1276 cases, 0 mismatches.

## Route
1. `trace_pow_prime_congr`: with `Q = det C` and `t_n = tr C^(c^n)`,
   `t_(n+1) ≡ lucasV t_n ε c (mod c^(n+1))`.  Use `trace_pow_eq_lucasV` (phase 35) on
   `B = C^(c^n)`: `t_(n+1) = lucasV t_n (Q^(c^n)) c` exactly; `Q ≡ ε (mod c)` gives
   `Q^(c^n) ≡ ε (mod c^(n+1))` (lifting the exponent: `(ε + c y)^(c^n)`); then `dvd_lucasV_sub`-style
   congruence in the `q` argument.
2. Filter: `SharedConjecture.exists_trace_pow_congr` (trace version) plus
   `FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat` give `t_n ≡ x_n ∈ {±1 − h}` mod
   `c^(n/2)` for all large `n` if every term is prime.
3. Finite sets ⟹ `x_(n+1) = lucasV x_n ε c` exactly for large `n`.
   - `ε = −1`: `lucasV_neg_one_growth` ⟹ `x_n = 0`, contradicting `c ∤ tr C` (since `t_n ≡ tr C`).
   - `ε = +1`: `lucasV x 1 c` (`= 2T_c(x/2)`): `|x| ≥ 3` grows (prove `|x| + 3 ≤ |lucasV x 1 c|`).
     `x ∈ {0, ±2}` are excluded by `c ∤ tr C · disc C` (`t_n ≡ tr C`, and `x = ±2` means
     `t_n² − 4 ≡ 0`, i.e. `disc ≡ 0`).  `x = ±1` with `tr C ≡ ±1` is the excluded `Φ₆`/`Φ₃`
     class; `x = ±1` otherwise contradicts `t_n ≡ tr C (mod c)`.  Also rule out 2-cycles inside
     `{x, x ± 2}` (check `lucasV x 1 c ∈ {x ± 2}` has no admissible solution).
4. `trace_phi_survivor`: in the exceptional class, `c^(n+1) ∣ tr C^(c^n) − τ` (checked
   numerically: `v_c = n + 1` exactly).  Induction with step 1: `lucasV τ 1 c = τ` for
   `τ = ±1` when `c ≡ ±1 (mod 6)`, and the derivative is `≡ 0 (mod c)`.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.TraceClassification

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasPrimePow Filter

/-- The exact-composition congruence for traces at an odd prime with `det ≡ ε (mod c)`. -/
theorem trace_pow_prime_congr (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hdet : (c : ℤ) ∣ C.det - ε) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (C ^ (c ^ (n + 1))).trace - lucasV (C ^ (c ^ n)).trace ε c := by
  sorry

/-- **Theorem B.**  2×2 traces at odd primes: composite infinitely often for every shift, outside
the `Φ₆`/`Φ₃` classes. -/
theorem trace_prime_pow_add_not_prime (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime)
    (hc2 : c ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hdet : (c : ℤ) ∣ C.det - ε)
    (htr : ¬ (c : ℤ) ∣ C.trace) (hdisc : ¬ (c : ℤ) ∣ C.trace ^ 2 - 4 * C.det)
    (hexc : ¬ (ε = 1 ∧ ((c : ℤ) ∣ C.trace - 1 ∨ (c : ℤ) ∣ C.trace + 1)))
    (hgrow : Tendsto (fun n : ℕ => |(C ^ (c ^ n)).trace|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((C ^ (c ^ n)).trace + h) := by
  sorry

/-- **The exceptional classes really are survivors**: the traces converge to `τ = ±1`
`c`-adically at rate `c^(n+1)`. -/
theorem trace_phi_survivor (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime) (hc5 : 5 ≤ c)
    (hdet : (c : ℤ) ∣ C.det - 1) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) (htr : (c : ℤ) ∣ C.trace - τ)
    (n : ℕ) : (c : ℤ) ^ (n + 1) ∣ (C ^ (c ^ n)).trace - τ := by
  sorry

end LeanFormalizations.Mills.TraceClassification
