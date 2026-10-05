/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftRigidityUnipotent

/-!
# Phase 65 close: E+ for every `θ < 2/3` from Lemma 8 and a hit prime

Phase 65 reduced the `5/9` wall to one ξ-free question.  Eventual records hold in every degree
given `Dubickas2022PisotGap` (`ShiftRigidityDeg.eventuallyRecordShift_of_pisotGap`), and degree
`3` rigidity is proved (`ShiftedMillsAll`).  In degree `≥ 4` the cubic `3`-adic route and the
`q`-power class are both refuted on controls (`ShiftRigidityUnipotent.f₀`, `f₂`); what closes
the degree-`≥ 4` leaves is a **hit prime**: a fixed prime dividing infinitely many orbit traces
(`ShiftRigidityUnipotent.HitPrime`, open, no mechanism known; the Fermat analogue in degree `1`
fails).

This file records the result as Lean data: the half-shift twin `HalfHitPrime`, the two
degree-`≥ 4` rigidity statements from the hit-prime nodes, and the conditional headline
`xi_shift_transcendental_of_hitPrime`.  All of it is wiring.
-/

namespace LeanFormalizations.Mills.ShiftHitPrime

open Filter Polynomial LeanFormalizations.Mills.ShiftRigidity LeanFormalizations.Literature
  LeanFormalizations.Mills.ShiftedMillsAll LeanFormalizations.Mills.SaitoTypeB LeanFormalizations.Mills
  LeanFormalizations.BHPTests LeanFormalizations.Mills.TheoremDGeneral
  LeanFormalizations.Mills.ShiftRigidityDeg LeanFormalizations.Mills.ShiftRigidityUnipotent

/-- **Open node (half-shift hit prime), any degree `≥ 4`.**  The `g = 2` section of `HitPrime`:
for odd `s`, some prime divides `tr C^((3^n + s)/2)` for infinitely many `n`.  Believed (~85%,
same heuristic as `HitPrime`: the orbit of `(3^n + s)/2` modulo `ord(C mod q)` is eventually
periodic, so a single residue with trace `≡ 0 (mod q)` suffices).  No mechanism known. -/
def HalfHitPrime : Prop :=
  ∀ (f : ℤ[X]) (α : ℝ), PisotDataAny f α → 4 ≤ f.natDegree → ∀ s : ℤ, Odd s →
    ∃ q : ℕ, q.Prime ∧ ∀ N : ℕ, ∃ n ≥ N, (q : ℤ) ∣ traceSeq f (((3 : ℤ) ^ n + s).toNat / 2)

/-- **Wiring (~95%)**: `HitPrime` gives shift rigidity in degree `≥ 4`.  Route: as
`ShiftedMillsAll.shiftTraceRigidity_holds`, take `f = minpoly ℤ β`, build `PisotDataAny f β`
from `ShiftedMillsLarge.minpoly_int_*`, rewrite `powTrace` by `ShiftedMillsLarge.powTrace_eq_traceSeq`,
and apply `ShiftRigidityUnipotent.not_primeTraces_of_hitPrime`. -/
theorem shiftTraceRigidity_ge_four_of_hitPrime (hH : HitPrime) {s : ℤ} (hs : s ≠ 0) {β : ℝ}
    (hβ : IsPisot β) (hdeg : 4 ≤ (minpoly ℚ β).natDegree) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ) := by
  have hint : IsIntegral ℤ β := hβ.2.1
  have hD : PisotDataAny (minpoly ℤ β) β :=
    ⟨ShiftedMillsLarge.minpoly_int_monic hint, ShiftedMillsLarge.minpoly_int_irreducible hint,
      minpoly.aeval ℤ β, hβ.1, ShiftedMillsLarge.minpoly_int_conj_small hβ⟩
  have hdeg' : 4 ≤ (minpoly ℤ β).natDegree := by
    rw [ShiftedMillsLarge.minpoly_int_natDegree hint]; exact hdeg
  intro hev
  refine not_primeTraces_of_hitPrime hH hD hdeg' hs ?_
  filter_upwards [hev] with n ⟨p, hp, h⟩
  refine ⟨p, hp, ?_⟩
  rw [ShiftedMillsLarge.powTrace_eq_traceSeq hint] at h
  exact_mod_cast h

/-- **Wiring (~90%)**: `HalfHitPrime` gives half-shift rigidity in degree `≥ 4`.  Route: the
half-shift analogue of `ShiftRigidityUnipotent.not_primeTraces_of_hit` (the index
`(3^n + s)/2 → ∞`, so `traceSeq_tendsto_any` makes the traces exceed `q`, and a prime divisible
by `q` equals `q`), then the bridge of `ShiftedMillsAll.halfShiftTraceRigidity_holds`. -/
theorem halfShiftTraceRigidity_ge_four_of_halfHitPrime (hH : HalfHitPrime) {s : ℤ} (hs : Odd s)
    {β : ℝ} (hβ : IsPisot β) (hdeg : 4 ≤ (minpoly ℚ β).natDegree) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat / 2) = (p : ℂ) := by
  have hint : IsIntegral ℤ β := hβ.2.1
  have hD : PisotDataAny (minpoly ℤ β) β :=
    ⟨ShiftedMillsLarge.minpoly_int_monic hint, ShiftedMillsLarge.minpoly_int_irreducible hint,
      minpoly.aeval ℤ β, hβ.1, ShiftedMillsLarge.minpoly_int_conj_small hβ⟩
  have hdeg' : 4 ≤ (minpoly ℤ β).natDegree := by
    rw [ShiftedMillsLarge.minpoly_int_natDegree hint]; exact hdeg
  intro hev
  obtain ⟨q, hq, hhit⟩ := hH _ β hD hdeg' s hs
  have hP : ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧
      traceSeq (minpoly ℤ β) (((3 : ℤ) ^ n + s).toNat / 2) = p := by
    filter_upwards [hev] with n ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    rw [ShiftedMillsLarge.powTrace_eq_traceSeq hint] at h
    exact_mod_cast h
  have hgrow := (traceSeq_tendsto_any hD).comp (HalfShiftRigidity.halfExp_tendsto s)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hP.and (hgrow.eventually_ge_atTop ((q : ℤ) + 1)))
  obtain ⟨n, hn, hd⟩ := hhit N
  obtain ⟨⟨p, hp, hpe⟩, hb⟩ := hN n hn
  have hb' : (q : ℤ) + 1 ≤ traceSeq (minpoly ℤ β) (((3 : ℤ) ^ n + s).toNat / 2) := hb
  have hpq : p = q := by
    have : (q : ℤ) ∣ (p : ℤ) := hpe ▸ hd
    have : q ∣ p := by exact_mod_cast this
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  rw [hpe, hpq] at hb'
  omega

/-- **Phase 65 headline (wiring, ~95%)**: E+ for every short-interval exponent `θ < 2/3`, from
Dubickas's Lemma 8 and the two hit-prime nodes.  Route: `ShiftRigidityDeg.xi_shift_transcendental_of_nodes`
with `eventuallyRecordShift_of_pisotGap`, and rigidity in degree `≥ 3` split as
`ShiftRigidityDeg.shiftTraceRigidityGe3_holds` does (degree `3` from `ShiftedMillsAll`, degree
`≥ 4` from the two theorems above). -/
theorem xi_shift_transcendental_of_hitPrime {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hG : Dubickas2022PisotGap) (hH : HitPrime) (hH2 : HalfHitPrime)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  refine xi_shift_transcendental_of_nodes hθ0 hθ (eventuallyRecordShift_of_pisotGap hθ0 hθ hG)
    (fun _ h => ?_) (fun _ h => ?_) hP hD hs hj1 hj2 hξ
  · intro β hβ hdeg
    rcases (show (minpoly ℚ β).natDegree = 3 ∨ 4 ≤ (minpoly ℚ β).natDegree by omega) with h' | h'
    · exact shiftTraceRigidity_holds h β hβ h'
    · exact shiftTraceRigidity_ge_four_of_hitPrime hH h hβ h'
  · intro β hβ hdeg
    rcases (show (minpoly ℚ β).natDegree = 3 ∨ 4 ≤ (minpoly ℚ β).natDegree by omega) with h' | h'
    · exact halfShiftTraceRigidity_holds h β hβ h'
    · exact halfShiftTraceRigidity_ge_four_of_halfHitPrime hH2 h hβ h'

end LeanFormalizations.Mills.ShiftHitPrime
