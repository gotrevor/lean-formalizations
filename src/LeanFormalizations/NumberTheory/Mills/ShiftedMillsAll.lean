/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMills

/-!
# Phase 61: Theorem E+ — `ξ(3^k + s)` is transcendental for EVERY `s ≠ 0`

New mathematics (ours, `PROOF-THEOREM-E.md`, drafts 2–3e, four referee passes, whole claim ~70%).
Phases 58–59 (`ShiftedMillsLarge`, `ShiftedMillsThreePow`) proved the case "3-free part of even
`s` is `≥ 8`" by a *size* argument.  This phase states the full family, which needs the *arithmetic*
argument of Steps 3–6, and wires it to Saito.

Only literature input: `Literature.Saito2025TypeBTrace` (Saito, arXiv:2508.16068, Theorem 2.3 +
Proposition 3.1(iv)).  No RH, no Siegel.

## The statements

* `shiftC j s k = 3^(k+j) + s` (as `ℕ` via `Int.toNat`; positive for `k ≥ 1` under the start rule).
* `ShiftTraceRigidity s` (open node, **our math**, Steps 3–6 with shift `s`): no cubic Pisot `β`
  has `Tr(β^(3^n + s))` prime for all large `n`.  Claimed for every `s ≠ 0` (~75%).
* `HalfShiftTraceRigidity s` (open node, **our math**, the `g = 2` section): no cubic Pisot `β` has
  `Tr(β^((3^n + s)/2))` prime for all large `n`.  Claimed for every odd `s` (~72%).
* Wiring `xi_shift_transcendental_of_rigidity` (elementary, ~95%), the edge
  `shiftedTraceRigidity_of_shift` onto phase 45's node (trivial), and the two headlines, which are
  proved below from the frozen pieces.

## Route (paper references are to `PROOF-THEOREM-E.md`; do the elementary statements first)

**A. `shiftedTraceRigidity_of_shift`** (do first): `((3:ℤ)^n + (-2)).toNat = 3^n - 2` in `ℕ` for
`n ≥ 1`; unfold both `def`s.

**B. `xi_shift_transcendental_of_rigidity`** (section "Theorem E+", "Reduction via Saito's Type B",
"E+ for even `s` with `3 ∣ s`", "E+ for odd `s`"; phases 45/58/59 are the templates —
`shiftedC_hyps`, `largeC_two_mul_le`, `largeC_ratio_of_le`, `largeC_B5`, `threePowC_B5`,
`dvd_three_pow_of_eventually_dvd`):
1. Saito's hypotheses for `C = shiftC j s`.  `C 1 ≥ 1` is `hj1`.  Doubling: `2(X + s) ≤ 3X + s`
   iff `s ≤ X = 3^(k+j)`, from `hj2`.  Ratio `≥ 29/10` iff `X ≥ 19 s`: eventually (always if
   `s < 0`).  `(B5′)`: write `C_m = 3^a · w` with `3 ∤ w`; the start rule forces `a = v₃(s)`
   and `a ≤ m + j`.  Take `t` a multiple of `ord_w(3)` (for odd `s`, `w` is even: use
   `lcm(ord_(w_odd) 3, ord_(2^b) 3)`, `2^b ∥ w`).  Then `C_(m+t) − C_m = 3^(m+j)(3^t − 1)` is
   divisible by `C_m`; take `t` large for the ratio.
2. Saito gives `ξ` (unique `IsLeast`) transcendental, or `ξ^g` cubic Pisot with `g ∣ C_k` and
   `powTrace (ξ^g) (C_k / g) = ⌊ξ^(C_k)⌋₊` for large `k`.
3. `agcd`: `g ∣ 3C_k − C_(k+1) = 2s`; an odd prime `q ≠ 3` dividing `s` and `3^(k+j) + s` divides
   `3^(k+j)`, impossible.  `v₂(3^m + s) = 1` for one parity of `m` (odd `s`); every `C_k` is odd
   for even `s`.  So `g = 3^b` or `g = 2·3^b`, `b ≤ v₃(s)`.
4. `g = 3^b`: `C_k / g = 3^(k+j−b) + s'`, `s' = s / 3^b ≠ 0`; contradict `hR s'` at `β = ξ^g`,
   `n = k + j − b`.  `g = 2·3^b`: `s'` odd, `C_k / g = (3^(k+j−b) + s')/2`; contradict `hH s'`.

**C. `shiftTraceRigidity_holds`** (Steps 3–6; the heavy node).  Reuse what phases 44–60 built:
the filter / stuck lemma (`TheoremDGround`), the 3-adic window (`ShiftedWindow.window_of_eventually_prime`,
phase 46), Teichmüller periodicity (`TeichmullerCongruence`), the unipotent class
(`UnipotentTrace.three_dvd_trace_pow`, phase 48), Theorem D's spectral machinery
(`TheoremDMixed.exists_mixed_limit`, `not_exists_spectral_mixed`, `exists_algEquiv_of_roots`).
1. Step 3: every large `n` is good (`v₃(ord_(p_n) C) > n`, else `p_n ∣ p_(n+kj)`); window
   `p_n ≡ ω_n ∈ {±1} (mod 3^(e_n))`, `e_n → ∞`; limit identity `Σ_k ζ_k^(3^r) α_k^s = ω` along a
   residue class.
2. Step 4: Galois rigidity over `ℚ(ζ_M)`, `M ∣ 104`, weights `w_k = α_k^s` non-constant (root moduli
   differ, `s ≠ 0`): `S₃` by spanning, `C₃` by the circulant (complex case: `√−3 ∉ ℚ(ζ_M)`).  All
   `ζ_k^(3^r)` equal `z` with `z·T = ω`, `T = tr(β^s) ∈ ℚ`.
3. Step 5: `z = 0` impossible; `z = ±1` forces every `ζ_k = z` (`x ↦ x^(3^r)` bijective on
   prime-to-3 roots of unity), `f ≡ (X − z)³ (mod 3)`, so `3 ∣ T` (denominator `σ₃^|s|` prime to
   3), contradicting `T = ±1`.  Every case from here is the template of phase 58's
   `dvd_traceSeq_of_map_eq_X_pow` in the unit class.
4. Step 6 (E1, `ℚ(β) = ` the conductor-13 cubic field): the rank-3 certificate
   `scripts/theorem-e-e1-certificate.py` (`w ↦ Tr_D(ζ₁₃^b w)` has rank 3, `b = 1..12`); `b = 0`
   falls to Step 5.  A finite linear-algebra computation; `decide`/`native_decide` are fine.

**D. `halfShiftTraceRigidity_holds`** ("E+ for odd `s`", drafts 3–3e): `δ_k² = β_k`, limit identity
`Σ a_k δ_k^s = ω`.  Generic case (`f_β(X²)` irreducible over `E = ℚ(μ_M)`, `M ∣ 208`): summing
over `Gal(E(δ)/E)` gives `0 = |G|·ω`.  Kummer-degenerate case: `√β ∈ ℚ(β)` reduces to node C for
`√β` (`Tr(β^N) = Tr((√β)^(2N))`); `ξ = √d·γ` gives `|tr(γ^s)| = d^(−s/2) ∉ ℚ`.  E1 at `g = 2`:
`H` trivial (distinct moduli), then `q`-divisibility (`q ∣ d` has a unique prime `𝔮` in `K`,
`β ∈ 𝔮`, so `q ∣ tr(β^N)` for every `N`), contradicting primes `→ ∞`.  Numeric checks:
`scripts/theorem-e-e1-g2-qdiv.py`, `scripts/theorem-e-e1-g2-search.py`.

Frozen: every statement and def below, all earlier Mills phase statements (incl. phase 45's
`ShiftedTraceRigidity`, which this phase *closes* via edge A), everything in `Literature/`.  No
`private`.  Decomposing C and D into named sub-lemmas (new files under `Mills/` are welcome) is
progress, and so is a refutation: if a node is false, prove `¬` and record a `Maze.lean` row.
-/

namespace LeanFormalizations.Mills.ShiftedMillsAll

open LeanFormalizations.Literature Filter

/-- The exponent sequence `C_k = 3^(k+j) + s` for an integer shift `s`, as a natural number. -/
def shiftC (j : ℕ) (s : ℤ) (k : ℕ) : ℕ := ((3 : ℤ) ^ (k + j) + s).toNat

/-- **Open node (Theorem E+, Steps 3–6 with shift `s`).**  No cubic Pisot number `β` has
`Tr(β^(3^n + s))` prime for all large `n`.  Claimed for every `s ≠ 0`, ~75%. -/
def ShiftTraceRigidity (s : ℤ) : Prop :=
  ∀ β : ℝ, IsPisot β → (minpoly ℚ β).natDegree = 3 →
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ)

/-- **Open node (Theorem E+, the `g = 2` section).**  No cubic Pisot number `β` has
`Tr(β^((3^n + s)/2))` prime for all large `n`.  Claimed for every odd `s`, ~72%. -/
def HalfShiftTraceRigidity (s : ℤ) : Prop :=
  ∀ β : ℝ, IsPisot β → (minpoly ℚ β).natDegree = 3 →
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat / 2) = (p : ℂ)

/-- **Edge A**: the shift-`(-2)` node is phase 45's `ShiftedTraceRigidity`. -/
theorem shiftedTraceRigidity_of_shift (h : ShiftTraceRigidity (-2)) :
    ShiftedMills.ShiftedTraceRigidity := by
  sorry

/-- **Wiring B** (elementary): Saito + both rigidity families ⇒ `ξ(3^(k+j) + s)` transcendental,
for every `s ≠ 0`, with the start rule `3^(j+1) + s ≥ 1` and `s ≤ 3^(j+1)` (every ratio `≥ 2`). -/
theorem xi_shift_transcendental_of_rigidity (hS : Saito2025TypeBTrace)
    (hR : ∀ s : ℤ, s ≠ 0 → ShiftTraceRigidity s)
    (hH : ∀ s : ℤ, Odd s → HalfShiftTraceRigidity s)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

/-- **Node C (our math, ~75%)**: Steps 3–6 of Theorem E for every shift `s ≠ 0`. -/
theorem shiftTraceRigidity_holds {s : ℤ} (hs : s ≠ 0) : ShiftTraceRigidity s := by
  sorry

/-- **Node D (our math, ~72%)**: the `g = 2` section for every odd shift. -/
theorem halfShiftTraceRigidity_holds {s : ℤ} (hs : Odd s) : HalfShiftTraceRigidity s := by
  sorry

/-- **Theorem E+**: `ξ(3^(k+j) + s)` is transcendental for every integer `s ≠ 0`, conditional
only on Saito 2025 (Type B + Prop 3.1(iv)). -/
theorem xi_shift_transcendental (hS : Saito2025TypeBTrace)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  xi_shift_transcendental_of_rigidity hS (fun _ h => shiftTraceRigidity_holds h)
    (fun _ h => halfShiftTraceRigidity_holds h) hs hj1 hj2 hξ

/-- **Theorem E**: `ξ(3^k − 2)` is transcendental, conditional only on Saito 2025 (closes phase
45's rigidity hypothesis). -/
theorem xi_shifted_transcendental_saito (hS : Saito2025TypeBTrace) {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  ShiftedMills.xi_shifted_transcendental hS
    (shiftedTraceRigidity_of_shift (shiftTraceRigidity_holds (by norm_num))) hξ

end LeanFormalizations.Mills.ShiftedMillsAll
