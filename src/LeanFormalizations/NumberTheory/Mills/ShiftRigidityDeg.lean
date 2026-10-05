/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftRigidity
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBThetaParts

/-!
# Phase 65: the `ξ`-free half of the `5/9` wall

`SaitoTypeBTheta.shiftPisotDegreeLeThree_holds` asks that Pisot degree `≥ 4` never occur for an
algebraic least E+ constant when `θ ∈ [5/9, 2/3)`.  Decay cannot give that
(`DecayDegreeFour.decay_admits_degree_four`).  The input that does more than decay in degree `3`
is arithmetic: `ShiftRigidity.not_primeTraces`, no cubic Pisot number has `tr β^(3^n + s)` prime
for all large `n`.  This file states its degree-`ℓ` form as the open node.

Difficulty check.
* Proved: `ℓ = 3` (`shiftTraceRigidityDeg_three`, from `ShiftRigidity.not_primeTraces`).
* Unproved: `ℓ ≥ 4` (`shiftTraceRigidity_ge_four`, `halfShiftTraceRigidity_ge_four`), and
  eventual records (`eventuallyRecordShift_holds`).  Of the cubic proof, the cube class (`not_primeTraces_of_cube`) and the
  spectral transfer (`exists_spectral_solution_shift`, already degree-general) should carry over;
  `rigidity_generic` (one 3-cycle in the Galois group, circulant Fourier modes) and the E1
  certificate (`f mod 3` irreducible with a root in `ℚ(μ_26)`) are cubic.  For degree `ℓ` the
  Teichmüller orders are `3^f − 1` for the factor degrees `f` of `f mod 3`, and the circulant
  becomes a permutation action of a Galois element on `ℓ` roots.
* Sibling sanity: the heuristic count of primes among `tr β^(3^n + s)` is `Σ 1/(3^n log β) < ∞`,
  so "all large traces prime" is expected false for every Pisot `β` of every degree; the node does
  not prove a believed-false sibling.  It does not use decay, so the control does not bite.
* Still missing for the wiring: in degree `≥ 4` the E+ route does not yet give
  `tr = ⌊ξ^(C k)⌋` at **all** large `k` (that used "all large indices are records",
  `eventually_record_shift_theta`, which needs `card otherConj ≤ 2`).  That is the second half of
  the node, not stated here yet.
-/

namespace LeanFormalizations.Mills.ShiftRigidityDeg

open Filter Polynomial LeanFormalizations.Mills.ShiftRigidity LeanFormalizations.Literature
  LeanFormalizations.Mills.ShiftedMillsAll LeanFormalizations.Mills.SaitoTypeB LeanFormalizations.Mills
  LeanFormalizations.BHPTests

/-- `PisotData` without the degree: a monic irreducible integer polynomial with a real root
`α > 1` whose other complex roots have modulus `< 1`. -/
structure PisotDataAny (f : ℤ[X]) (α : ℝ) : Prop where
  monic : f.Monic
  irr : Irreducible f
  root : aeval α f = 0
  gt_one : 1 < α
  small : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1

/-- **Open node (degree `ℓ` shift trace rigidity).**  No Pisot number of degree `ℓ` has
`tr β^(3^n + s)` prime for all large `n`, `s ≠ 0`. -/
def ShiftTraceRigidityDeg (ℓ : ℕ) : Prop :=
  ∀ (f : ℤ[X]) (α : ℝ), PisotDataAny f α → f.natDegree = ℓ → ∀ s : ℤ, s ≠ 0 → ¬ PrimeTraces f s

/-- The cubic case is `ShiftRigidity.not_primeTraces`. -/
theorem shiftTraceRigidityDeg_three : ShiftTraceRigidityDeg 3 := fun f α hD hdeg _ hs =>
  not_primeTraces ⟨hD.monic, hD.irr, hdeg, hD.root, hD.gt_one, hD.small⟩ hs

/-! ## The wiring: two nodes give E+ for every `θ < 2/3` -/

/-- **Open node (shift rigidity, degree `≥ 3`)**, `powTrace` form, as consumed by the wiring.
Degree `3` is `ShiftedMillsAll.shiftTraceRigidity_holds`. -/
def ShiftTraceRigidityGe3 (s : ℤ) : Prop :=
  ∀ β : ℝ, IsPisot β → 3 ≤ (minpoly ℚ β).natDegree →
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ)

/-- **Open node (half-shift rigidity, degree `≥ 3`)**, the `g = 2` section.  Degree `3` is
`ShiftedMillsAll.halfShiftTraceRigidity_holds`. -/
def HalfShiftTraceRigidityGe3 (s : ℤ) : Prop :=
  ∀ β : ℝ, IsPisot β → 3 ≤ (minpoly ℚ β).natDegree →
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat / 2) = (p : ℂ)

/-- **Open node (eventual records, degree-free).**  For an algebraic least E+ constant, every
large index is a record.  Proved for `θ < 5/9` (`SaitoTypeB.eventually_record_shift_theta`,
through `card otherConj ≤ 2`); in degree `≥ 4` the dominant-pair lower bound has no analogue yet. -/
def EventuallyRecordShift (θ : ℝ) : Prop :=
  PrimesShortInterval θ → Dubickas2022 → ∀ (s : ℤ) (j : ℕ), s ≠ 0 →
    1 ≤ (3 : ℤ) ^ (j + 1) + s → s ≤ (3 : ℤ) ^ (j + 1) → ∀ ξ : ℝ,
    IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ → IsAlgebraic ℚ ξ →
    ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m

/-- **Wiring (phase 65)**: eventual records and degree-`≥ 3` rigidity give E+ for every
`θ < 2/3`, with no degree bound. -/
theorem xi_shift_transcendental_of_nodes {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hrec : EventuallyRecordShift θ)
    (hR : ∀ s : ℤ, s ≠ 0 → ShiftTraceRigidityGe3 s)
    (hH : ∀ s : ℤ, Odd s → HalfShiftTraceRigidityGe3 s)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  have h1θ : 0 < 1 - θ := by linarith
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
  rcases saitoTypeB_shift_theta_gen (ρ := ρ) (μ := μ) hP hθ0.le (by linarith) hμ0
      (min_le_right _ _) (by rw [hρ]; linarith) (min_le_left _ _) (by rw [hρ]; linarith)
      hD hs hj1 hj2 hξ (hrec hP hD s j hs hj1 hj2 ξ hξ) with htr | ⟨g, hg1, hpisot, hdeg, K, hK⟩
  · exact htr
  exfalso
  have hleast := hξ
  have hgev : ∀ᶠ k in atTop, g ∣ shiftC j s k := by
    filter_upwards [eventually_ge_atTop (K + 19 * s.natAbs + 1)] with k hk
    exact (hK k (by omega) (shiftC_ratio hj1 (by omega) (by omega))).1
  obtain ⟨h3s, hcase⟩ := shiftC_gcd hj1 hg1 hgev
  set b := g.factorization 3 with hb
  obtain ⟨s', hs'⟩ := h3s
  have hs'0 : s' ≠ 0 := by rintro rfl; simp at hs'; exact hs hs'
  have hsplit : 3 ^ b * ordCompl[3] g = g := Nat.ordProj_mul_ordCompl_eq_self g 3
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

/-- **Believed (~75%)**: shift rigidity in degree `≥ 4`.  English route: the cubic proof's cube
class and spectral transfer (`exists_spectral_solution_shift` is degree-general), with
`rigidity_generic` replaced by a Galois element acting fixed-point-freely on the roots outside
`ℚ(μ_Q)`; the exceptional cases are the factorization types of `f mod 3` with a root in a
cyclotomic `ℚ(μ_(3^f−1))`.  Evidence: degree 3, and the convergent prime heuristic. -/
theorem shiftTraceRigidity_ge_four {s : ℤ} (hs : s ≠ 0) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 4 ≤ (minpoly ℚ β).natDegree) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ) := by
  sorry

/-- **Believed (~70%)**: the half-shift section in degree `≥ 4` (cubic case:
`HalfShiftRigidity.not_halfPrimeTraces`). -/
theorem halfShiftTraceRigidity_ge_four {s : ℤ} (hs : Odd s) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 4 ≤ (minpoly ℚ β).natDegree) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat / 2) = (p : ℂ) := by
  sorry

theorem shiftTraceRigidityGe3_holds {s : ℤ} (hs : s ≠ 0) : ShiftTraceRigidityGe3 s := by
  intro β hβ hdeg
  rcases (show (minpoly ℚ β).natDegree = 3 ∨ 4 ≤ (minpoly ℚ β).natDegree by omega) with h | h
  · exact shiftTraceRigidity_holds hs β hβ h
  · exact shiftTraceRigidity_ge_four hs hβ h

theorem halfShiftTraceRigidityGe3_holds {s : ℤ} (hs : Odd s) : HalfShiftTraceRigidityGe3 s := by
  intro β hβ hdeg
  rcases (show (minpoly ℚ β).natDegree = 3 ∨ 4 ≤ (minpoly ℚ β).natDegree by omega) with h | h
  · exact halfShiftTraceRigidity_holds hs β hβ h
  · exact halfShiftTraceRigidity_ge_four hs hβ h

/-- **Believed (~55%)**: eventual records for `θ < 2/3`.  For `θ < 5/9` this is
`eventually_record_shift_theta`; beyond, it needs a lower bound for `|Σ γ_i^n|` along the records
with `≥ 3` dominant conjugates (`DominantPair.lower_along_records` is for one real / one pair), or
a record argument that avoids the degree.  The weakest open point of the route. -/
theorem eventuallyRecordShift_holds {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) :
    EventuallyRecordShift θ := by
  sorry

/-- **Proved (phase 65 lap 2)**: eventual records in every degree, from Dubickas's Lemma 8 (Saito
Lemma 2.7).  This is a separate theorem next to `eventuallyRecordShift_holds`; it is not a proof
of it, because the frozen `θ < 2/3` route has avoided `Dubickas2022PisotGap` since 2026-09-28.

English proof.  The proof follows `SaitoTypeBRecords.eventually_record_of_card_le_two`, except
for the last step.
1. `records_pisot_theta` gives `g` and `β = ξ^g` Pisot of degree `L + 1`.  On records,
   `⌊ξ^(C r)⌋ = Tr(β^n)` with `n = C r / g`, so the fractional part is `f = |x_n|`, where
   `x_n = Σ_(i ≥ 2) γ_iⁿ`.  `record_gap_bounded` gives records with bounded gaps.
2. A non-record `M` after a record `r` gives `c f P^(c−1) < 1` with `c ≥ 2` and `P = ⌊β^n⌋`
   (`nonrecord_ineq`), so `f < 1/(2P)` and `f < β^(−n)` for large `n`.
3. `Dubickas2022PisotGap` gives `f ≥ Rⁿ n^(−λ)`.  The product of the other conjugates has
   modulus `|N β| / β ≥ 1/β`, so `R ≥ β^(−1/L)`.  Then `β^(n(1 − 1/L)) < n^λ`, which is false
   for large `n` when `L ≥ 2`; in Lean this is `pisot_degree_bound` at rate `μ = 1`, using
   `‖S(n)‖ ≤ fract(β^n) < 1/P ≤ 2 β^(−n)`.  `L ≤ 2` is already handled by `eventually_record_of_card_le_two`.
4. So past some record `r0`, every index is a record (the `exists_last_record` argument).
Consequence: with this input, the `5/9` wall is only `shiftTraceRigidity_ge_four` and
`halfShiftTraceRigidity_ge_four`.  The decay rate `μ` enters only through `L ≤ 1/μ`. -/
theorem eventuallyRecordShift_of_pisotGap {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hG : Dubickas2022PisotGap) : EventuallyRecordShift θ := by
  intro hP hD s j hs hj1 hj2 ξ hξ halg
  have h1θ : 0 < 1 - θ := by linarith
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
  obtain ⟨g, hg1, hpis, hdeg, K, hK⟩ := records_pisot_theta (ρ := ρ) (μ := μ) hP hθ0.le
    (by linarith) hμ0 (min_le_right _ _) (by rw [hρ]; linarith) (min_le_left _ _)
    (by rw [hρ]; linarith) hD hj1 hj2 hξ halg
  obtain ⟨T, K', hT⟩ := record_gap_bounded hj1 hj2 hξ hg1 hpis hK
  by_cases hc2 : Multiset.card (otherConj (ξ ^ g)) ≤ 2
  · exact eventually_record_of_card_le_two hs hj1 hj2 hξ hg1 hpis hc2 hK hT
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hnot := not_intCast_pow h1 h2 h5 hξS
  set β := ξ ^ g with hβ
  have hβ1 : 1 < β := hpis.1
  have hβ0 : 0 < β := by linarith
  -- not eventually records ⇒ frequently `‖S(n)‖ ≤ 2 β^(−n)`
  by_contra hno
  have hno' : ∀ N, ∃ M ≥ N, ¬ IsRecord C ξ M := by
    intro N; by_contra h; push Not at h; exact hno ⟨N, h⟩
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (norm_conjPowSum_eq_round hpis)
  have hfreq : ∃ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ ≤ 2 * (β ^ (-((1 : ℝ) * n)) : ℝ) := by
    rw [frequently_atTop]
    intro A
    obtain ⟨r0, hr0rec, hr0ge⟩ := ((frequently_record h1 h2 hξ hnot).and_eventually
      (eventually_ge_atTop ((A + N0) * g + K + 1))).exists
    obtain ⟨M, hM, hMn⟩ := hno' (r0 + 1)
    obtain ⟨r, hr0r, hrM, hrrec, hlt⟩ := exists_last_record hr0rec (by omega) hMn
    have hr1 : 1 ≤ r := by omega
    have hgr : g ∣ C r := hK r (by omega) hrrec
    obtain ⟨hA, -, hc⟩ := nonrecord_ineq h1 h2 hξ1 hnot hpis hr1 hrM hgr hlt
    set n := C r / g with hn
    have hrC : r ≤ C r := le_C h1 h2 r hr1
    have hnA : A + N0 ≤ n := by
      rw [hn, Nat.le_div_iff_mul_le (by omega)]; nlinarith
    refine ⟨n, by omega, ?_⟩
    set x := ξ ^ C r with hx
    set P : ℝ := (⌊x⌋₊ : ℝ) with hP
    set f := Int.fract x with hf
    set c : ℝ := (C M : ℝ) / C r with hcdef
    have hβn : β ^ n = x := by rw [hβ, hx, ← pow_mul, Nat.mul_div_cancel' hgr]
    have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
    have hfx : x = P + f := by
      rw [hf, hP, Int.fract, ← Int.natCast_floor_eq_floor (by linarith)]; push_cast; ring
    have hf0 : 0 ≤ f := Int.fract_nonneg x
    have hf1 : f < 1 := Int.fract_lt_one x
    have hP1 : 1 ≤ P := by
      have := Nat.floor_pos.2 hx1; rw [hP]; exact_mod_cast this
    have hc2' : 2 ≤ c := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (M - r) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hpc : P ^ (1 : ℝ) ≤ P ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
    rw [Real.rpow_one] at hpc
    have hfP : f * P < 1 := by
      have e0 : 0 ≤ f * P ^ (c - 1) := mul_nonneg hf0 (by positivity)
      have : c * f * P ^ (c - 1) = c * (f * P ^ (c - 1)) := by ring
      have : f * P ≤ f * P ^ (c - 1) := mul_le_mul_of_nonneg_left hpc hf0
      nlinarith
    have hround : ‖conjPowSum β n‖ ≤ f := by
      rw [hN0 n (by omega), hβn]
      have := round_le x ⌊x⌋
      rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
    have hxe : (β ^ (-((1 : ℝ) * n)) : ℝ) = x⁻¹ := by
      rw [one_mul, Real.rpow_neg hβ0.le, Real.rpow_natCast, hβn]
    rw [hxe]
    have hx0 : 0 < x := by linarith
    have hx2 : x ≤ 2 * P := by linarith
    rw [show (2 : ℝ) * x⁻¹ = 2 / x by ring, le_div_iff₀ hx0]
    nlinarith
  have hb := pisot_degree_bound hG hpis hdeg one_pos two_pos hfreq
  have : (3 : ℝ) ≤ Multiset.card (otherConj β) := by exact_mod_cast (by omega :
    3 ≤ Multiset.card (otherConj β))
  linarith

/-- E+ for every `θ < 2/3`, using `Dubickas2022PisotGap` in place of the open record node.  It
is wiring only: what remains open is the degree-`≥ 4` rigidity. -/
theorem xi_shift_transcendental_of_pisotGap {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hG : Dubickas2022PisotGap) (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ :=
  xi_shift_transcendental_of_nodes hθ0 hθ (eventuallyRecordShift_of_pisotGap hθ0 hθ hG)
    (fun _ h => shiftTraceRigidityGe3_holds h) (fun _ h => halfShiftTraceRigidityGe3_holds h)
    hP hD hs hj1 hj2 hξ

end LeanFormalizations.Mills.ShiftRigidityDeg
