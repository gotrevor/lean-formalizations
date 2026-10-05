/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsAll
import LeanFormalizations.Literature.Primes

/-!
# Phase 62: Saito's Type B from Baker–Harman–Pintz + Dubickas/Corvaja–Zannier

Theorem E+ (`ShiftedMillsAll.xi_shift_transcendental`) currently rests on the single literature
Prop `Literature.Saito2025TypeBTrace` (Saito, arXiv:2508.16068 = Ramanujan J. 70 (2026) Art. 69,
Theorem 2.3 + Prop 3.1(ii),(iv); faithfulness audit `docs/notes/saito-2025-faithfulness-audit.md`).
This phase PROVES Saito's argument in Lean, so E+ rests instead on two classical, short, cited Props
already in the repo:
* `Literature.BakerHarmanPintz2001` (`Literature/Primes.lean`): `≥ d₀ x^(21/40)/log x` primes in
  `[x, x + x^(21/40)]` — exactly Saito's `(†)` at `θ = 21/40` (his Theorem 1.6).
* `Literature.Dubickas2022` (`Literature/Pisot.lean`): Dubickas 2022 Lemma 6 (from Corvaja–Zannier
  2004) — exactly Saito's Theorem 5.4.

**No existence claim.**  `Saito2025TypeBTrace` also asserts that the least `ξ` exists (Saito Thm 1.3,
via Matomäki).  E+ never needs that: its `ξ` is a hypothesis.  So the target `SaitoTypeBLeast` takes
the least `ξ` as given, and Matomäki drops out.

## Statements
* `SaitoTypeBLeast` — Saito's conclusion for a GIVEN least `ξ` (same hypotheses on `C`, same
  conclusion, as `Saito2025TypeBTrace`).
* `saitoTypeBLeast_of_saito` — edge from the old Prop (proved here).
* `saitoTypeBLeast_holds` — **the work**: from BHP + Dubickas2022.
* `xi_shift_transcendental_of_typeB` — E+ wiring from `SaitoTypeBLeast` (proved here: phase 61's
  proof with the `obtain` swapped).
* `xi_shift_transcendental_classical`, `xi_shifted_transcendental_classical` — the headlines on
  BHP + Dubickas2022 only (the first proved here from the pieces; the second, Theorem E, needs only
  `shiftC 0 (-2) k = shiftedC k` for `k ≥ 1`).

## Route for `saitoTypeBLeast_holds` (paper: `papers/saito-2025-transcendency-variants-mills.txt`)
Specialise everything to `θ = 21/40`, `ε` with `40/19 + ε ≤ 29/10`, `I ⊇ {k : C(k+1) ≥ (29/10) C k}`.
1. **(3.1) `ξ^(C_m) ∉ ℕ`** from `(B5′)` (Section 8, first paragraph): an integer `ξ^(C_m)` makes
   `ξ^(C_k) = (ξ^(C_m))^(C_k/C_m)` a perfect power, not the prime `⌊ξ^(C_k)⌋`.
2. **§5.1 key dichotomy, Lemmas 5.1–5.3** (elementary real analysis + BHP + minimality of `ξ`):
   either way `lim sup ‖ξ^(C_k)‖^(1/C_k) < 1`.  Prop 3.1(i) is the quantitative small-fractional-part
   bound for `k ∈ I` (exponent `(1−θ)c_(k+1) − 1`; take the exact form from the paper, line ~430).
   Reuse `Irrational.lean` / `SaitoDigits.lean` (Saito 2024 Lemmas 3.6/3.8 from BHP are already proved
   there, e.g. `saito_lemma36`, `saito_lemma36C`), adapting from `C_k = c^k` to general `C`.
3. **Lemma 6.1** (Dubickas2022 ⇒ `α^g` Pisot of degree `ℓ ≤ 1 + (lim sup t_k)⁻¹`, `g ∣ s_k`
   eventually) and **Lemma 5.7** (Dub02 Lemma 3: a power of a Pisot number of degree `ℓ` is Pisot of
   degree `ℓ`; elementary).  Lemma 6.2 for (G1)–(G4).
4. **Prop 3.1(ii)**: `ℓ ≤ 1 + 400/151 < 4`; `ℓ ≥ 2` (degree 1 ⇒ `ξ^g ∈ ℕ`, contradicting step 1).
   **(iii)**: `ℓ = 2` ⇒ golden ratio and `C_k/g` an odd prime (Lemma 5.6, elementary quadratic
   algebra); then `(B5′)` contradicts it (Section 8).  So `ℓ = 3`.
5. **Prop 3.1(iv)**: `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` for large `k ∈ I` (Section 6), by minimality of `ξ`
   (`ε = 0`).  `powTrace` matches Saito's `Tr` (audit row (g)).

If the proof genuinely needs a further cited input (e.g. `Dubickas2022PisotGap`), do NOT edit the
frozen statement: add a parallel `saitoTypeBLeast_holds'` with the extra hypothesis, record why in
the header and a `Maze.lean` row, and keep going.  A refutation of a transcription is progress too.

Frozen: every statement and def below; all earlier statements; everything in `Literature/`.
No `private`.  Decomposing into named sub-lemmas (new `Mills/` files welcome) is progress.
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature Filter LeanFormalizations.Mills.ShiftedMillsAll

/-- **Saito (2025) Type B + Prop 3.1(ii),(iv) for a GIVEN least `ξ`** (no existence claim): the
hypotheses and conclusion of `Literature.Saito2025TypeBTrace`, with `ξ` supplied. -/
def SaitoTypeBLeast : Prop :=
  ∀ C : ℕ → ℕ,
    1 ≤ C 1 →
    (∀ k ≥ 1, 2 * C k ≤ C (k + 1)) →
    (∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    (∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    ∀ ξ : ℝ, IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime} ξ →
      (Transcendental ℚ ξ ∨
        ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ (minpoly ℚ (ξ ^ g)).natDegree = 3 ∧
          ∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1) →
            g ∣ C k ∧ powTrace (ξ ^ g) (C k / g) = (⌊ξ ^ C k⌋₊ : ℂ))

/-- Edge: the old literature Prop gives the given-`ξ` form (the least element is unique). -/
theorem saitoTypeBLeast_of_saito (hS : Saito2025TypeBTrace) : SaitoTypeBLeast := by
  intro C h1 h2 h3 h5 ξ hξ
  obtain ⟨ξ₀, hleast, hdisj⟩ := hS C h1 h2 h3 h5
  rwa [hleast.unique hξ] at hdisj

/-- **The work (phase 62)**: Saito's Type B argument from Baker–Harman–Pintz and Dubickas 2022
Lemma 6 (Corvaja–Zannier). -/
theorem saitoTypeBLeast_holds (hB : BakerHarmanPintz2001) (hD : Dubickas2022) :
    SaitoTypeBLeast := by
  sorry

/-- E+ wiring from the given-`ξ` form (phase 61's wiring with the `obtain` swapped). -/
theorem xi_shift_transcendental_of_typeB (hT : SaitoTypeBLeast)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have hR : ∀ s : ℤ, s ≠ 0 → ShiftTraceRigidity s := fun _ h => shiftTraceRigidity_holds h
  have hH : ∀ s : ℤ, Odd s → HalfShiftTraceRigidity s := fun _ h => halfShiftTraceRigidity_holds h
  have hC3 : ∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * shiftC j s k ≤ shiftC j s (k + 1) := fun K =>
    ⟨max K (19 * s.natAbs + 1), le_max_left _ _,
      shiftC_ratio hj1 (by omega) (by omega)⟩
  have hdisj := hT (shiftC j s) (shiftC_pos hj1 le_rfl)
    (fun k hk => shiftC_two_mul_le hj1 hj2 hk) hC3 (fun m hm => shiftC_B5 hj1 hj2 hm) ξ hξ
  have hleast := hξ
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

/-- **Theorem E+ on classical inputs**: `ξ(3^(k+j) + s)` is transcendental for every `s ≠ 0`,
conditional only on Baker–Harman–Pintz 2001 and Dubickas 2022 Lemma 6 (Corvaja–Zannier 2004). -/
theorem xi_shift_transcendental_classical (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  xi_shift_transcendental_of_typeB (saitoTypeBLeast_holds hB hD) hs hj1 hj2 hξ

/-- **Theorem E on classical inputs**: `ξ(3^k − 2)` is transcendental, conditional only on
Baker–Harman–Pintz 2001 and Dubickas 2022 Lemma 6. -/
theorem xi_shifted_transcendental_classical (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

end LeanFormalizations.Mills.SaitoTypeB
