/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Theorem E+ from any short-interval exponent `θ < 2/3`

`SaitoTypeB.xi_shift_transcendental_classical` proves `ξ(3^(k+j) + s)` transcendental for every
`s ≠ 0` from `BakerHarmanPintz2001` (`θ = 21/40`) and `Dubickas2022`.  The exponent enters only
through Saito's Lemma 5.3, as `1/(1 − θ) + ε ≤ r` where `r` bounds the exponent ratios
`C(k+1)/C k` from below; for `C = 3^k + s` those ratios tend to `3`, so any `θ < 2/3` should do.

This file restates E+ (and Theorem E, `s = −2`) with the prime input weakened to
`PrimesShortInterval θ` for some `0 < θ < 2/3`, and derives the corollary from Ingham's 1937
exponent `5/8`, which needs no sieve.  The BHP headline and its stress tests stay; this is a
second headline beside them.

Why `2/3` is the natural threshold: Ingham's method turns `ζ(1/2 + it) ≪ t^c` into the exponent
`(1 + 4c)/(2 + 4c) + ε`.  The convexity bound `c = 1/4` gives `2/3 + ε`, which just misses; any
subconvex `c < 1/4` suffices.
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeB
import LeanFormalizations.NumberTheory.PrimeIntervals.BHPTests
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBThetaParts
import LeanFormalizations.NumberTheory.Mills.ShiftRigidityDeg

namespace LeanFormalizations.Mills.SaitoTypeBTheta

open LeanFormalizations.Literature LeanFormalizations.BHPTests Filter
  LeanFormalizations.Mills.ShiftedMillsAll

/-- `shiftC 0 (-2)` is the Theorem E exponent sequence, so the Mills sets agree. -/
theorem shifted_set_eq :
    {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC 0 (-2) k⌋₊).Prime} =
      {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} := by
  have hC : ∀ k ≥ 1, shiftC 0 (-2) k = ShiftedMills.shiftedC k := by
    intro k hk
    unfold shiftC ShiftedMills.shiftedC
    have h3 : (3 : ℕ) ≤ 3 ^ k := by
      calc (3 : ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [add_zero, show ((3 : ℤ) ^ k + -2) = ((3 ^ k - 2 : ℕ) : ℤ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    exact Int.toNat_natCast _
  ext A
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => forall₂_congr fun k hk => by rw [hC k hk]

/-! ## The Ingham input, checked against the family -/

/-- `Ingham1937` is the family statement on `(5/8, 1]`, by definition. -/
theorem ingham_iff :
    Ingham1937 ↔ ∀ θ : ℝ, 5 / 8 < θ → θ ≤ 1 → PrimesShortInterval θ := Iff.rfl

/-- **Sanity**: BHP (`θ = 21/40 < 5/8`) implies Ingham's statement, via monotonicity. -/
theorem ingham_of_bhp (h : BakerHarmanPintz2001) : Ingham1937 := fun θ h1 h2 =>
  PrimesShortInterval.mono (θ := (21 : ℝ) / 40) (by norm_num) (by linarith) h2 (bhp_iff.1 h)

/-! ## Theorem E+ from `θ < 5/9` (the threshold the Baker-free degree bound reaches)

The route of `SaitoTypeB.saitoTypeB_shift` with the prime input as a parameter
(`SaitoTypeB.saitoTypeB_shift_theta`).  Saito's (5.17) gives decay `‖ξ^(C k)‖ ≪ ξ^(−μ C k)` for any
`μ < (1 − θ)·3 − 1 = 2 − 3θ`, and the degree bound is `(ℓ − 1) μ ≤ 1`; the degree-3 endgame
needs `ℓ ≤ 3`, i.e. `μ > 1/3`, i.e. `θ < 5/9`. -/

/-- **Theorem E+ from a short-interval exponent `θ < 5/9`**, conditional on
`PrimesShortInterval θ` and Dubickas 2022 Lemma 6.  Covers BHP (`21/40 < 5/9`). -/
theorem xi_shift_transcendental_of_shortInterval' {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 5 / 9)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have h1θ : 0 < 1 - θ := by linarith
  set a : ℝ := 4 / (3 * (1 - θ)) with ha
  have ha43 : 4 / 3 ≤ a := by
    rw [ha, le_div_iff₀ (by positivity)]; nlinarith
  have ha3 : a < 3 := by
    rw [ha, div_lt_iff₀ (by positivity)]; nlinarith
  have hamul : (1 - θ) * a = 4 / 3 := by rw [ha]; field_simp
  set ρ : ℝ := (3 + a) / 2 with hρ
  have hρμ : 1 / 3 < (1 - θ) * ρ - 1 := by
    have : (1 - θ) * ρ = ((1 - θ) * 3 + (1 - θ) * a) / 2 := by rw [hρ]; ring
    rw [this, hamul]; nlinarith
  set μ : ℝ := min 1 ((1 - θ) * ρ - 1) with hμ
  have hμ3 : 1 / 3 < μ := lt_min (by norm_num) hρμ
  exact SaitoTypeB.xi_shift_transcendental_of_shift_disj hs hj1 hξ
    (SaitoTypeB.saitoTypeB_shift_theta (ρ := ρ) (μ := μ) hP hθ0.le (by linarith) (by linarith)
      (min_le_right _ _) (by rw [hρ]; linarith) (min_le_left _ _) (by rw [hρ]; linarith) hD
      hs hj1 hj2 hξ (Or.inl hμ3))

/-- **Theorem E from `θ < 5/9`**: `ξ(3^k − 2)` is transcendental. -/
theorem xi_shifted_transcendental_of_shortInterval' {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 5 / 9)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  rw [← shifted_set_eq] at hξ
  exact xi_shift_transcendental_of_shortInterval' hθ0 hθ hP hD (s := -2) (j := 0) (by norm_num)
    (by norm_num) (by norm_num) hξ

/-- **Open node (the `5/9` wall).**  For the least E+ constant, algebraic, every Pisot power has
degree `≤ 3`.  For `θ < 5/9` this is what `SaitoTypeB.card_le_two_of_records_theta` and
`SaitoTypeB.card_mul_le_shift_theta` prove from decay `μ > 1/3`; for `θ ∈ [5/9, 2/3)` the decay
`μ < 2 − 3θ ≤ 1/3` only gives `ℓ ≤ 1 + 1/μ`.  With it (and a degree-free record step) the frozen
`xi_shift_transcendental_of_shortInterval` would follow by the same endgame. -/
def ShiftPisotDegreeLeThree (θ : ℝ) : Prop :=
  PrimesShortInterval θ → Dubickas2022 → ∀ (s : ℤ) (j : ℕ), s ≠ 0 →
    1 ≤ (3 : ℤ) ^ (j + 1) + s → s ≤ (3 : ℤ) ^ (j + 1) → ∀ ξ : ℝ,
    IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ → IsAlgebraic ℚ ξ →
    ∀ g : ℕ, 1 ≤ g → IsPisot (ξ ^ g) → (minpoly ℚ (ξ ^ g)).natDegree ≤ 3

/-! ## Phase 65: the `5/9` wall, split into a node and an edge -/

/-- **Edge (phase 65)**: the degree bound is the only missing input.  Given
`ShiftPisotDegreeLeThree θ`, the endgame of `xi_shift_transcendental_of_shortInterval'` runs for
every `θ < 2/3` (the record step must not use `μ > 1/3` except through the degree bound). -/
theorem xi_shift_transcendental_of_degree {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hdeg : ShiftPisotDegreeLeThree θ) (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have h1θ : 0 < 1 - θ := by linarith
  -- `ρ = (3 + ρ₀)/2` with `(1 − θ) ρ₀ = 1`, so `2 < ρ < 3` and `μ := (1 − θ) ρ − 1 > 0`
  set a : ℝ := 1 / (1 - θ) with ha
  have ha1 : 1 < a := by rw [ha, lt_div_iff₀ h1θ]; linarith
  have ha3 : a < 3 := by rw [ha, div_lt_iff₀ h1θ]; linarith
  have hamul : (1 - θ) * a = 1 := by rw [ha]; field_simp
  set ρ : ℝ := (3 + a) / 2 with hρ
  have hρμ : 0 < (1 - θ) * ρ - 1 := by
    have : (1 - θ) * ρ = ((1 - θ) * 3 + (1 - θ) * a) / 2 := by rw [hρ]; ring
    rw [this, hamul]; nlinarith
  set μ : ℝ := min 1 ((1 - θ) * ρ - 1) with hμ
  have hμ0 : 0 < μ := lt_min (by norm_num) hρμ
  exact SaitoTypeB.xi_shift_transcendental_of_shift_disj hs hj1 hξ
    (SaitoTypeB.saitoTypeB_shift_theta (ρ := ρ) (μ := μ) hP hθ0.le (by linarith) hμ0
      (min_le_right _ _) (by rw [hρ]; linarith) (min_le_left _ _) (by rw [hρ]; linarith)
      hD hs hj1 hj2 hξ (Or.inr fun halg => hdeg hP hD s j hs hj1 hj2 ξ hξ halg))

/-- **Node (phase 65)**: the degree bound on `[5/9, 2/3)`.  Needs an input beyond decay
(`DecayDegreeFour.decay_admits_degree_four`); see DIRECTION.md phase 65 for the difficulty check.
Expected route: state a `ξ`-free obstruction for a Pisot `β` of degree `≥ 4` whose traces along
the orbit `n ↦ 3n + d` equal `⌊β^n⌋` and are prime, prove it, and specialise. -/
theorem shiftPisotDegreeLeThree_holds {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) :
    ShiftPisotDegreeLeThree θ := by
  -- vacuous: the degree-free route (`ShiftRigidityDeg`) makes an algebraic `ξ` impossible
  intro hP hD s j hs hj1 hj2 ξ hξ halg g _ _
  exact absurd halg (ShiftRigidityDeg.xi_shift_transcendental_of_nodes hθ0 hθ
    (ShiftRigidityDeg.eventuallyRecordShift_holds hθ0 hθ)
    (fun _ h => ShiftRigidityDeg.shiftTraceRigidityGe3_holds h)
    (fun _ h => ShiftRigidityDeg.halfShiftTraceRigidityGe3_holds h) hP hD hs hj1 hj2 hξ)

/-! ## Theorem E+ from `θ < 2/3` (frozen; open beyond `5/9`) -/

/-- **Theorem E+ from a short-interval exponent `θ < 2/3`**: `ξ(3^(k+j) + s)` is transcendental
for every `s ≠ 0`, conditional on `PrimesShortInterval θ` and Dubickas 2022 Lemma 6. -/
theorem xi_shift_transcendental_of_shortInterval {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  rcases lt_or_ge θ (5 / 9) with h59 | h59
  · exact xi_shift_transcendental_of_shortInterval' hθ0 h59 hP hD hs hj1 hj2 hξ
  -- `θ ∈ [5/9, 2/3)`: the decay exponent `μ < 2 − 3θ ≤ 1/3` leaves the Pisot degree bound
  -- `ℓ ≤ 1 + 1/μ ≥ 4`, and the degree-3 endgame (`e2_zero_of_nonrecord`, `not_natDegree_two`) has
  -- no degree-`ℓ` analogue yet.  Needs a Baker-free exclusion of Pisot degree `≥ 4`.
  exact xi_shift_transcendental_of_degree hθ0 hθ (shiftPisotDegreeLeThree_holds hθ0 hθ) hP hD hs hj1
    hj2 hξ

/-- **Theorem E+ on Ingham 1937**: no sieve input, conditional on Ingham and Dubickas 2022. -/
theorem xi_shift_transcendental_ingham (hI : Ingham1937) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  xi_shift_transcendental_of_shortInterval (θ := 13 / 20) (by norm_num) (by norm_num)
    (hI _ (by norm_num) (by norm_num)) hD hs hj1 hj2 hξ

/-- **Theorem E on Ingham 1937**: `ξ(3^k − 2)` is transcendental. -/
theorem xi_shifted_transcendental_ingham (hI : Ingham1937) (hD : Dubickas2022)
    {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  rw [← shifted_set_eq] at hξ
  exact xi_shift_transcendental_ingham hI hD (s := -2) (j := 0) (by norm_num) (by norm_num)
    (by norm_num) hξ

/-! ## Audit -/

#print axioms xi_shift_transcendental_of_shortInterval'
#print axioms xi_shifted_transcendental_of_shortInterval'
#print axioms ingham_of_bhp

end LeanFormalizations.Mills.SaitoTypeBTheta
