/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsAll
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBParts
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBNoGap
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

## Status (2026-10-05, end of lap 1)
* PROVED: `xi_shifted_transcendental_classical` from `xi_shift_transcendental_classical` (edge).
* PROVED, sorry-free: the parallel `saitoTypeBLeastEv_holds (hB hD hG)` and the E+ headline
  `xi_shift_transcendental_classical' (hB hD hG)`, all of Saito §5–§6, §8 in
  `Mills/SaitoTypeBParts.lean` (competitor chain from BHP alone, Lemma 5.9, Lemma 6.1, a
  divisibility proof of Prop 3.1(iii)).
* OPEN: the frozen `saitoTypeBLeast_holds` (hence `xi_shift_transcendental_classical`).  Saito's
  route needs Dubickas 2022 Lemma 8 (Baker) in two places; see `Mills/SaitoTypeBNoGap.lean`: case
  (II) for E+ drops it (`conjPowSum_lower_of_recurrence`, stated), case (I) needs the reopen node
  `SparseNoCancel` (`Maze.lean` row).  General `C` also needs Matomäki.

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

/-! ### Parallel target (2026-10-05): `Dubickas2022PisotGap` added, ratios eventually `≥ 29/10`

Saito's route needs two inputs beyond `hB`, `hD` (see `Mills/SaitoTypeBParts.lean` header and the
`Maze.lean` row "Saito Type B from BHP + Dubickas2022 alone"): Matomäki (Lemma 4.2, only for
chain steps with ratio `< 40/19`) and Dubickas 2022 Lemma 8 (Baker; the degree bound of Lemma
6.1).  The first is avoided by assuming the ratios are eventually `≥ 29/10`, which E+ satisfies;
the second is taken as the cited hypothesis `hG`.  The frozen `saitoTypeBLeast_holds` stays open. -/

/-- `SaitoTypeBLeast` restricted to exponent sequences whose ratios are eventually `≥ 29/10`. -/
def SaitoTypeBLeastEv : Prop :=
  ∀ C : ℕ → ℕ,
    1 ≤ C 1 →
    (∀ k ≥ 1, 2 * C k ≤ C (k + 1)) →
    (∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    (∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1)) →
    ∀ ξ : ℝ, IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime} ξ →
      (Transcendental ℚ ξ ∨
        ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ (minpoly ℚ (ξ ^ g)).natDegree = 3 ∧
          ∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * C k ≤ C (k + 1) →
            g ∣ C k ∧ powTrace (ξ ^ g) (C k / g) = (⌊ξ ^ C k⌋₊ : ℂ))

/-- **Saito's Type B for ratios eventually `≥ 29/10`**, from BHP, Dubickas 2022 Lemma 6 and
Lemma 8. -/
theorem saitoTypeBLeastEv_holds (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) : SaitoTypeBLeastEv := by
  intro C h1 h2 hEv h5 ξ hξ
  obtain ⟨K₀, hK₀⟩ := hEv
  have hξS : ξ ∈ millsSet C := hξ.1
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  by_cases htr : Transcendental ℚ ξ
  · exact Or.inl htr
  right
  have halg : IsAlgebraic ℚ ξ := not_not.1 htr
  have hnot := not_intCast_pow h1 h2 h5 hξS
  obtain ⟨k₁, hlow⟩ := eventually_low hD hG h1 h2 hK₀ hξS hnot halg
  obtain ⟨k₀, hII⟩ := window_of_least hB h1 h2 hK₀ hξ hnot hlow
  obtain ⟨k₂, hfr⟩ := eventually_fract_le h1 h2 hK₀ hξS hII
  have hCge := C_ge_one h1 h2
  -- the decay along `s k = C (k + k₃)`
  set k₃ := k₂ + 1 with hk₃
  set s : ℕ → ℕ := fun k => C (k + k₃) with hs
  have hsmono : StrictMono s := by
    intro a b hab
    exact C_strictMonoOn h1 h2 (by omega) (by omega)
  have hs0 : 0 < s 0 := hCge _ (by omega)
  have hflo := floor_tendsto h1 h2 hξ1
  have hdecay : ∀ᶠ k in atTop, |ξ ^ s k - (round (ξ ^ s k) : ℝ)| ≤
      4 * ξ ^ (-((151 / 400 : ℝ) * s k)) := by
    filter_upwards [eventually_ge_atTop 0] with k _
    set x := ξ ^ s k with hx
    have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
    have hfl1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      have := Nat.floor_pos.2 hx1; exact_mod_cast this
    have hxfl : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x; linarith
    have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
      have := round_le x ⌊x⌋
      rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
    have hf := hfr (k + k₃) (by omega)
    -- `⌊x⌋^(−t) ≤ 2^t x^(−t) ≤ 2 x^(−t)`
    have hpow : (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ 2 * x ^ (-(151 / 400 : ℝ)) := by
      have hxpos : 0 < x := by linarith
      have h1' : (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ (x / 2) ^ (-(151 / 400 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2' : (x / 2) ^ (-(151 / 400 : ℝ)) = 2 ^ (151 / 400 : ℝ) * x ^ (-(151 / 400 : ℝ)) := by
        rw [Real.div_rpow hxpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
      have h3' : (2 : ℝ) ^ (151 / 400 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (151 / 400 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      rw [h2'] at h1'
      have : 0 ≤ x ^ (-(151 / 400 : ℝ)) := by positivity
      nlinarith
    have hxe : x ^ (-(151 / 400 : ℝ)) = ξ ^ (-((151 / 400 : ℝ) * s k)) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
    calc |x - (round x : ℝ)| ≤ Int.fract x := hround
      _ ≤ 2 * (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) := hf
      _ ≤ 2 * (2 * x ^ (-(151 / 400 : ℝ))) := by linarith
      _ = 4 * ξ ^ (-((151 / 400 : ℝ) * s k)) := by rw [hxe]; ring
  have hnot' : ∀ k, ∀ t : ℤ, ξ ^ s k ≠ (t : ℝ) := fun k t => hnot _ (by omega) t
  obtain ⟨g, hg1, hpis, hgdiv, hdeg2, hcard⟩ :=
    exists_pisot_of_decay_subseq hD hG halg hξ1 hsmono hs0 (by norm_num) (by norm_num)
      hdecay hnot'
  obtain ⟨k₄, hk₄⟩ := eventually_atTop.1 hgdiv
  -- `g ∣ C k` for `k ≥ k₅`
  set k₅ := k₄ + k₃ with hk₅
  have hgC : ∀ k ≥ k₅, g ∣ C k := by
    intro k hk
    have := hk₄ (k - k₃) (by omega)
    simpa [hs, show k - k₃ + k₃ = k by omega] using this
  have hpowg : ∀ k ≥ k₅, (ξ ^ g) ^ (C k / g) = ξ ^ C k := by
    intro k hk
    rw [← pow_mul, Nat.mul_div_cancel' (hgC k hk)]
  -- eventually the fractional part is `< 1/2`
  obtain ⟨k₆, hk₆⟩ := eventually_atTop.1
    (hflo.eventually_ge_atTop ((16 : ℝ) ^ ((400 : ℝ) / 151)))
  have hhalf : ∀ k ≥ max k₆ k₂, Int.fract (ξ ^ C k) < 1 / 2 := by
    intro k hk
    have hf := hfr k (le_trans (le_max_right _ _) hk)
    have hbig := hk₆ k (le_trans (le_max_left _ _) hk)
    have hpos : (0 : ℝ) < (16 : ℝ) ^ ((400 : ℝ) / 151) := by positivity
    have : (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ 1 / 16 := by
      calc (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ))
          ≤ ((16 : ℝ) ^ ((400 : ℝ) / 151)) ^ (-(151 / 400 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hbig (by norm_num)
        _ = 1 / 16 := by
            rw [← Real.rpow_mul (by norm_num)]
            norm_num
    linarith
  -- the degree is `3`
  have hβ := hpis
  have hcardle : Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
    by_contra hc
    push_neg at hc
    have : (3 : ℝ) ≤ (Multiset.card (otherConj (ξ ^ g)) : ℝ) := by exact_mod_cast hc
    nlinarith
  have hcard1 := card_otherConj_add_one (hpis.2.1.tower_top)
  have hdeg3 : (minpoly ℚ (ξ ^ g)).natDegree = 3 := by
    rcases (show (minpoly ℚ (ξ ^ g)).natDegree = 2 ∨ (minpoly ℚ (ξ ^ g)).natDegree = 3 by
      omega) with h | h
    · exfalso
      refine not_natDegree_two hpis h (n := fun k => C k / g) (K := max (max k₅ k₆) (k₂ + 1))
        ?_ ?_ ?_ ?_
      · intro k hk
        show (⌊(ξ ^ g) ^ (C k / g)⌋₊).Prime
        rw [hpowg k (by omega)]
        exact hξS.2 k (by omega)
      · intro k hk
        show Int.fract ((ξ ^ g) ^ (C k / g)) < 1 / 2
        rw [hpowg k (by omega)]
        exact hhalf k (by omega)
      · intro M
        obtain ⟨b, hb, hdvd, -⟩ := h5 (M + k₅ + 1) (by omega)
        refine ⟨M + k₅ + 1, by omega, b, hb, ?_, ?_⟩
        · obtain ⟨e, he⟩ := hdvd
          refine ⟨e, ?_⟩
          have hg := hgC (M + k₅ + 1) (by omega)
          obtain ⟨u, hu⟩ := hg
          rw [he, hu, Nat.mul_div_cancel_left _ (by omega), mul_assoc,
            Nat.mul_div_cancel_left _ (by omega)]
        · have hlt := C_strictMonoOn h1 h2 (a := M + k₅ + 1) (b := b) (by omega) hb
          obtain ⟨u, hu⟩ := hgC (M + k₅ + 1) (by omega)
          obtain ⟨v, hv⟩ := hgC b (by omega)
          rw [hu, hv] at hlt ⊢
          rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
          exact Nat.lt_of_mul_lt_mul_left hlt
      · -- `C k / g → ∞`
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨max k₅ (b * g + 1), fun a ha => ?_⟩
        have hCa : a ≤ C a := le_C h1 h2 a (by omega)
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
    · exact h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (powTrace_eq_floor hpis)
  refine ⟨g, hg1, hpis, hdeg3, max (max k₅ k₆) (max k₂ (N₀ * g + 1)), fun k hk _ => ⟨hgC k
    (by omega), ?_⟩⟩
  have hN : N₀ ≤ C k / g := by
    have := le_C h1 h2 k (by omega)
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have := hN₀ (C k / g) hN (by rw [hpowg k (by omega)]; exact hhalf k (by omega))
  rw [this, hpowg k (by omega)]

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
  have hC : ∀ k ≥ 1, shiftC 0 (-2) k = ShiftedMills.shiftedC k := by
    intro k hk
    unfold shiftC ShiftedMills.shiftedC
    have h3 : (3 : ℕ) ≤ 3 ^ k := by
      calc (3 : ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [add_zero, show ((3 : ℤ) ^ k + -2) = ((3 ^ k - 2 : ℕ) : ℤ) by rw [Nat.cast_sub (by omega)]; push_cast; ring]
    exact Int.toNat_natCast _
  have hset : {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC 0 (-2) k⌋₊).Prime} =
      {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} := by
    ext A
    simp only [Set.mem_setOf_eq]
    exact and_congr_right fun _ => forall₂_congr fun k hk => by rw [hC k hk]
  exact xi_shift_transcendental_classical hB hD (s := -2) (j := 0) (by norm_num) (by norm_num)
    (by norm_num) (hset ▸ hξ)

/-- E+ wiring from `SaitoTypeBLeastEv` (same proof; `shiftC` ratios are `≥ 29/10` from `19|s|+1`). -/
theorem xi_shift_transcendental_of_typeBEv (hT : SaitoTypeBLeastEv)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have hR : ∀ s : ℤ, s ≠ 0 → ShiftTraceRigidity s := fun _ h => shiftTraceRigidity_holds h
  have hH : ∀ s : ℤ, Odd s → HalfShiftTraceRigidity s := fun _ h => halfShiftTraceRigidity_holds h
  have hC3 : ∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * shiftC j s k ≤ shiftC j s (k + 1) := fun K =>
    ⟨max K (19 * s.natAbs + 1), le_max_left _ _,
      shiftC_ratio hj1 (by omega) (by omega)⟩
  have hdisj := hT (shiftC j s) (shiftC_pos hj1 le_rfl)
    (fun k hk => shiftC_two_mul_le hj1 hj2 hk)
    ⟨19 * s.natAbs + 1, fun k hk => shiftC_ratio hj1 (by omega) (by omega)⟩ (fun m hm => shiftC_B5 hj1 hj2 hm) ξ hξ
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


/-- **Theorem E+ on classical inputs plus Dubickas 2022 Lemma 8** (the parallel target):
`ξ(3^(k+j) + s)` is transcendental for every `s ≠ 0`, conditional on Baker–Harman–Pintz 2001 and
Dubickas 2022 Lemmas 6 and 8. -/
theorem xi_shift_transcendental_classical' (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  xi_shift_transcendental_of_typeBEv (saitoTypeBLeastEv_holds hB hD hG) hs hj1 hj2 hξ

end LeanFormalizations.Mills.SaitoTypeB
