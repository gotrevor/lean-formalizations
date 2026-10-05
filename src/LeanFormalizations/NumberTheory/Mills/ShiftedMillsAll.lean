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
  intro β hβ hd hev
  refine h β hβ hd ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨p, hp, hpe⟩ := hn
  refine ⟨p, hp, ?_⟩
  have h2 : 2 ≤ 3 ^ n := ShiftedMills.two_le_three_pow hn1
  have : ((3 : ℤ) ^ n + -2).toNat = 3 ^ n - 2 := by
    have hc : ((3 : ℤ) ^ n) = ((3 ^ n : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]; omega
  rw [this]; exact hpe

/-! ### Wiring B helpers: Saito's hypotheses for `shiftC` -/

theorem three_pow_ge_of_le {j k : ℕ} (hk : 1 ≤ k) : (3 : ℤ) ^ (j + 1) ≤ 3 ^ (k + j) :=
  pow_le_pow_right₀ (by norm_num) (by omega)

theorem shiftC_cast {s : ℤ} {j k : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hk : 1 ≤ k) :
    ((shiftC j s k : ℕ) : ℤ) = 3 ^ (k + j) + s := by
  have := three_pow_ge_of_le (j := j) hk
  unfold shiftC
  rw [Int.toNat_of_nonneg (by linarith)]

theorem shiftC_pos {s : ℤ} {j k : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hk : 1 ≤ k) :
    1 ≤ shiftC j s k := by
  have h := shiftC_cast hj1 hk
  have := three_pow_ge_of_le (j := j) hk
  have : (1 : ℤ) ≤ (shiftC j s k : ℤ) := by rw [h]; linarith
  exact_mod_cast this

theorem shiftC_two_mul_le {s : ℤ} {j k : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s)
    (hj2 : s ≤ (3 : ℤ) ^ (j + 1)) (hk : 1 ≤ k) : 2 * shiftC j s k ≤ shiftC j s (k + 1) := by
  have h1 := shiftC_cast hj1 hk
  have h2 := shiftC_cast hj1 (show 1 ≤ k + 1 by omega)
  have h3 := three_pow_ge_of_le (j := j) hk
  have h4 : (3 : ℤ) ^ (k + 1 + j) = 3 * 3 ^ (k + j) := by
    rw [show k + 1 + j = (k + j) + 1 by omega, pow_succ]; ring
  have : (2 * shiftC j s k : ℤ) ≤ (shiftC j s (k + 1) : ℤ) := by
    rw [h1, h2, h4]; linarith
  exact_mod_cast this

theorem shiftC_ratio {s : ℤ} {j k : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hk : 1 ≤ k)
    (hks : 19 * s.natAbs ≤ k) :
    (29 : ℝ) / 10 * shiftC j s k ≤ shiftC j s (k + 1) := by
  have h1 := shiftC_cast hj1 hk
  have h2 := shiftC_cast hj1 (show 1 ≤ k + 1 by omega)
  have h4 : (3 : ℤ) ^ (k + 1 + j) = 3 * 3 ^ (k + j) := by
    rw [show k + 1 + j = (k + j) + 1 by omega, pow_succ]; ring
  have hlt : (k : ℤ) < 3 ^ (k + j) := by
    have : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    have h5 : (3 : ℤ) ^ k ≤ 3 ^ (k + j) := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (k : ℤ) < 3 ^ k := by exact_mod_cast this
    linarith
  have hs : 19 * s ≤ 3 ^ (k + j) := by omega
  have key : (29 : ℤ) * shiftC j s k ≤ 10 * shiftC j s (k + 1) := by
    rw [h1, h2, h4]; linarith
  have key' : (29 : ℝ) * shiftC j s k ≤ 10 * shiftC j s (k + 1) := by exact_mod_cast key
  linarith

/-- The 3-part of `C_m` divides `3^(m+j)`: `3^(m+j+1) ∤ C_m` under the start rule. -/
theorem not_pow_dvd_shiftC {s : ℤ} {j m : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s)
    (hj2 : s ≤ (3 : ℤ) ^ (j + 1)) (hm : 1 ≤ m) : ¬ 3 ^ (m + j + 1) ∣ shiftC j s m := by
  intro h
  have hz : ((3 ^ (m + j + 1) : ℕ) : ℤ) ∣ (shiftC j s m : ℤ) := Int.natCast_dvd_natCast.mpr h
  rw [shiftC_cast hj1 hm] at hz
  push_cast at hz
  obtain ⟨q, hq⟩ := hz
  have h3 := three_pow_ge_of_le (j := j) hm
  set P : ℤ := 3 ^ (m + j) with hP
  have hP3 : (3 : ℤ) ^ (m + j + 1) = 3 * P := by rw [pow_succ]; ring
  rw [hP3] at hq
  have hPpos : 0 < P := by positivity
  rcases le_or_gt 1 q with hq1 | hq1
  · nlinarith
  · have : q ≤ 0 := by omega
    nlinarith

/-- `(B5′)` for `shiftC`. -/
theorem shiftC_B5 {s : ℤ} {j m : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s)
    (hj2 : s ≤ (3 : ℤ) ^ (j + 1)) (hm : 1 ≤ m) :
    ∃ k > m, shiftC j s m ∣ shiftC j s k ∧
      (29 : ℝ) / 10 * shiftC j s k ≤ shiftC j s (k + 1) := by
  set n := shiftC j s m with hn
  have hnpos : 1 ≤ n := shiftC_pos hj1 hm
  have hn0 : n ≠ 0 := by omega
  set w := ordCompl[3] n with hw
  have hwcop : Nat.Coprime 3 w := Nat.coprime_ordCompl (by norm_num) hn0
  have hsplit : 3 ^ n.factorization 3 * w = n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have ha : n.factorization 3 ≤ m + j := by
    by_contra hc
    push_neg at hc
    exact not_pow_dvd_shiftC hj1 hj2 hm
      ((Nat.pow_dvd_pow 3 hc).trans (Nat.ordProj_dvd n 3))
  have hwpos : 0 < w := Nat.pos_of_ne_zero (by rintro h; rw [h] at hsplit; omega)
  have hphi : 1 ≤ w.totient := Nat.totient_pos.mpr hwpos
  set i := 19 * s.natAbs + m + 1 with hi
  set t := w.totient * i with hti
  have hti1 : i ≤ t := Nat.le_mul_of_pos_left i hphi
  have hpow : (3 : ℕ) ^ t ≡ 1 [MOD w] := by
    rw [hti, pow_mul]
    simpa using (Nat.ModEq.pow_totient hwcop).pow i
  have hwd : w ∣ 3 ^ t - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hpow.symm
  have hwdZ : (w : ℤ) ∣ (3 : ℤ) ^ t - 1 := by
    have := Int.natCast_dvd_natCast.mpr hwd
    rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))] at this
    <;> push_cast <;> rfl
  refine ⟨m + t, by omega, ?_, shiftC_ratio hj1 (by omega) (by omega)⟩
  have hnZ : (n : ℤ) = 3 ^ (n.factorization 3) * (w : ℤ) := by exact_mod_cast hsplit.symm
  have hnZ' : (n : ℤ) = 3 ^ (m + j) + s := shiftC_cast hj1 hm
  rw [← Int.natCast_dvd_natCast, shiftC_cast (k := m + t) hj1 (by omega)]
  have hdiff : (3 : ℤ) ^ (m + t + j) + s =
      (n : ℤ) + 3 ^ (n.factorization 3) * (3 ^ (m + j - n.factorization 3) *
        ((3 : ℤ) ^ t - 1)) := by
    have : (3 : ℤ) ^ (m + j) = 3 ^ (n.factorization 3) * 3 ^ (m + j - n.factorization 3) := by
      rw [← pow_add]; congr 1; omega
    rw [hnZ', show m + t + j = (m + j) + t by omega, pow_add, this]; ring
  rw [hdiff]
  refine dvd_add dvd_rfl ?_
  rw [hnZ]
  exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right hwdZ _)

/-- The asymptotic gcd: `g = 3^b · h` with `h = 1`, or `h = 2` and `s` odd, and `3^b ∣ s`. -/
theorem shiftC_gcd {s : ℤ} {j g : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hg0 : 1 ≤ g)
    (hg : ∀ᶠ k in atTop, g ∣ shiftC j s k) :
    (3 : ℤ) ^ g.factorization 3 ∣ s ∧
      (ordCompl[3] g = 1 ∨ (ordCompl[3] g = 2 ∧ Odd s)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  set b := g.factorization 3 with hb
  set h := ordCompl[3] g with hh
  set k := max N 1 + b with hk
  have hk1 : 1 ≤ k := by omega
  have h1 : (g : ℤ) ∣ 3 ^ (k + j) + s := by
    rw [← shiftC_cast hj1 hk1]; exact Int.natCast_dvd_natCast.mpr (hN k (by omega))
  have h2 : (g : ℤ) ∣ 3 * 3 ^ (k + j) + s := by
    have := shiftC_cast hj1 (show 1 ≤ k + 1 by omega)
    rw [show k + 1 + j = (k + j) + 1 by omega, pow_succ] at this
    rw [show (3 : ℤ) * 3 ^ (k + j) = 3 ^ (k + j) * 3 by ring, ← this]
    exact Int.natCast_dvd_natCast.mpr (hN (k + 1) (by omega))
  have hsplit : 3 ^ b * h = g := Nat.ordProj_mul_ordCompl_eq_self g 3
  have hhg : (h : ℤ) ∣ g := Int.natCast_dvd_natCast.mpr ⟨3 ^ b, by rw [← hsplit]; ring⟩
  have h3g : ((3 ^ b : ℕ) : ℤ) ∣ g := Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd g 3)
  have h2s : (g : ℤ) ∣ 2 * s := by
    have := dvd_sub (dvd_mul_of_dvd_right h1 3) h2
    have e : 3 * ((3 : ℤ) ^ (k + j) + s) - (3 * 3 ^ (k + j) + s) = 2 * s := by ring
    rwa [e] at this
  refine ⟨?_, ?_⟩
  · have hb3 : (3 : ℤ) ^ b ∣ 3 ^ (k + j) := pow_dvd_pow 3 (by omega)
    have h3g' : (3 : ℤ) ^ b ∣ g := by exact_mod_cast h3g
    have := dvd_sub (h3g'.trans h1) hb3
    simpa using this
  · have hh2 : h ∣ 2 * 3 ^ (k + j) := by
      have := dvd_sub (dvd_mul_of_dvd_right (hhg.trans h1) 2) (hhg.trans h2s)
      have e : 2 * ((3 : ℤ) ^ (k + j) + s) - 2 * s = ((2 * 3 ^ (k + j) : ℕ) : ℤ) := by
        push_cast; ring
      rw [e] at this
      exact Int.natCast_dvd_natCast.mp this
    have hcop : Nat.Coprime h (3 ^ (k + j)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp
        (Nat.coprime_ordCompl (by norm_num) (by omega)))
    have hd2 : h ∣ 2 := hcop.dvd_of_dvd_mul_right hh2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with e | e
    · exact Or.inl e
    · refine Or.inr ⟨e, ?_⟩
      have h2c : (2 : ℤ) ∣ 3 ^ (k + j) + s := by
        have : ((2 : ℕ) : ℤ) ∣ g := by rw [← e]; exact hhg
        exact (by exact_mod_cast this : (2 : ℤ) ∣ g).trans h1
      obtain ⟨r, hr⟩ : Odd ((3 : ℤ) ^ (k + j)) := Odd.pow (by decide)
      obtain ⟨q, hq⟩ := h2c
      exact ⟨q - r - 1, by omega⟩

/-- Dividing `C_k` by `3^b` when `s = 3^b s'`. -/
theorem shiftC_div_three_pow {s s' : ℤ} {j b k : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s)
    (hs : s = 3 ^ b * s') (hk : 1 ≤ k) (hkb : b ≤ k + j) :
    shiftC j s k / 3 ^ b = ((3 : ℤ) ^ (k + j - b) + s').toNat := by
  have hc := shiftC_cast hj1 hk
  have hpos := shiftC_pos hj1 hk
  have hsplit : (3 : ℤ) ^ (k + j) + s = 3 ^ b * (3 ^ (k + j - b) + s') := by
    rw [hs, mul_add, ← pow_add]; congr 2; omega
  have hb : (0 : ℤ) < 3 ^ b := by positivity
  have hnn : 0 ≤ (3 : ℤ) ^ (k + j - b) + s' := by
    have : (0 : ℤ) < 3 ^ b * (3 ^ (k + j - b) + s') := by
      rw [← hsplit, ← hc]; exact_mod_cast hpos
    exact (pos_of_mul_pos_right this hb.le).le
  have heq : shiftC j s k = 3 ^ b * ((3 : ℤ) ^ (k + j - b) + s').toNat := by
    have : ((shiftC j s k : ℕ) : ℤ) = ((3 ^ b * ((3 : ℤ) ^ (k + j - b) + s').toNat : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hnn, hc, hsplit]
    exact_mod_cast this
  rw [heq, Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num))]

/-- **Wiring B** (elementary): Saito + both rigidity families ⇒ `ξ(3^(k+j) + s)` transcendental,
for every `s ≠ 0`, with the start rule `3^(j+1) + s ≥ 1` and `s ≤ 3^(j+1)` (every ratio `≥ 2`). -/
theorem xi_shift_transcendental_of_rigidity (hS : Saito2025TypeBTrace)
    (hR : ∀ s : ℤ, s ≠ 0 → ShiftTraceRigidity s)
    (hH : ∀ s : ℤ, Odd s → HalfShiftTraceRigidity s)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have hC3 : ∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * shiftC j s k ≤ shiftC j s (k + 1) := fun K =>
    ⟨max K (19 * s.natAbs + 1), le_max_left _ _,
      shiftC_ratio hj1 (by omega) (by omega)⟩
  obtain ⟨ξ₀, hleast, hdisj⟩ := hS (shiftC j s) (shiftC_pos hj1 le_rfl)
    (fun k hk => shiftC_two_mul_le hj1 hj2 hk) hC3 (fun m hm => shiftC_B5 hj1 hj2 hm)
  have hxi : ξ₀ = ξ := hleast.unique hξ
  rw [hxi] at hdisj hleast
  rcases hdisj with htr | ⟨g, hg1, hpisot, hdeg, K, hK⟩
  · exact htr
  exfalso
  have hgev : ∀ᶠ k in atTop, g ∣ shiftC j s k := by
    filter_upwards [eventually_ge_atTop (K + 19 * s.natAbs + 1)] with k hk
    exact (hK k (by omega) (shiftC_ratio hj1 (by omega) (by omega))).1
  obtain ⟨h3s, hcase⟩ := shiftC_gcd hj1 hg1 hgev
  set b := g.factorization 3 with hb
  obtain ⟨s', hs'⟩ := h3s
  have hs'0 : s' ≠ 0 := by rintro rfl; simp at hs'; exact hs hs'
  have hsplit : 3 ^ b * ordCompl[3] g = g := Nat.ordProj_mul_ordCompl_eq_self g 3
  -- for large `n`, the index `k = n + b − j` gives a prime trace
  have key : ∀ n ≥ K + 19 * s.natAbs + j + b + 1, ∃ k, 1 ≤ k ∧ k + j - b = n ∧ b ≤ k + j ∧
      powTrace (ξ ^ g) (shiftC j s k / g) = ((⌊ξ ^ shiftC j s k⌋₊ : ℕ) : ℂ) ∧
      (⌊ξ ^ shiftC j s k⌋₊).Prime := by
    intro n hn
    refine ⟨n + b - j, by omega, by omega, by omega, ?_, hleast.1.2 _ (by omega)⟩
    exact (hK _ (by omega) (shiftC_ratio hj1 (by omega) (by omega))).2
  rcases hcase with h1 | ⟨h2, hodd⟩
  · rw [h1, mul_one] at hsplit
    refine hR s' hs'0 (ξ ^ g) hpisot hdeg ?_
    filter_upwards [eventually_ge_atTop (K + 19 * s.natAbs + j + b + 1)] with n hn
    obtain ⟨k, hk1, hkn, hkb, htr, hp⟩ := key n hn
    refine ⟨_, hp, ?_⟩
    rw [← htr, ← hsplit, shiftC_div_three_pow hj1 hs' hk1 hkb, hkn]
  · rw [h2] at hsplit
    have hodd' : Odd s' := by
      rw [hs'] at hodd; exact (Int.odd_mul.mp hodd).2
    refine hH s' hodd' (ξ ^ g) hpisot hdeg ?_
    filter_upwards [eventually_ge_atTop (K + 19 * s.natAbs + j + b + 1)] with n hn
    obtain ⟨k, hk1, hkn, hkb, htr, hp⟩ := key n hn
    refine ⟨_, hp, ?_⟩
    rw [← htr, ← hsplit, ← Nat.div_div_eq_div_mul, shiftC_div_three_pow hj1 hs' hk1 hkb, hkn]

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
