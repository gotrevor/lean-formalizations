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
  LeanFormalizations.BHPTests LeanFormalizations.Mills.TheoremDGeneral
  LeanFormalizations.Mills.TheoremDMixed

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

/-! ## The window in any degree (phase 65 lap 3; first piece of the generic leaf) -/

/-- **Window arithmetic, any degree.**  `3^e ∣ q^i − 1` gives `3^(e−i) ∣ q² − 1` (LTE). -/
theorem dvd_sq_sub_one_of_dvd_pow_sub_one {q e i : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) (hi : 1 ≤ i)
    (h : 3 ^ e ∣ q ^ i - 1) : 3 ^ (e - i) ∣ q ^ 2 - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 := hq.two_le
  have h3 : ¬ 3 ∣ q := fun hd => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd).symm
  have hq2' : 1 < q ^ 2 := by nlinarith
  have hmod : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h' | h' <;> simp [Nat.pow_mod, h']
  have h3sq : 3 ∣ q ^ 2 - 1 := by omega
  have h3x : ¬ 3 ∣ q ^ 2 := fun hd => h3 (Nat.prime_three.dvd_of_dvd_pow hd)
  have hlte := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1) (by norm_num) hq2'
    (by simpa using h3sq) h3x (n := i) (by omega)
  rw [one_pow] at hlte
  have hvi : padicValNat 3 i < i := by
    have hd : 3 ^ padicValNat 3 i ∣ i := pow_padicValNat_dvd
    have := Nat.le_of_dvd (by omega) hd
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) this
  have hdiv : q ^ i - 1 ∣ (q ^ 2) ^ i - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (x := q ^ i) (y := 1) (n := 2)
    rw [one_pow, ← pow_mul, mul_comm, pow_mul] at this
    exact this
  have hpos : (q ^ 2) ^ i - 1 ≠ 0 := by
    have : 1 < (q ^ 2) ^ i := one_lt_pow₀ hq2' (by omega)
    omega
  have he : e ≤ padicValNat 3 ((q ^ 2) ^ i - 1) :=
    (padicValNat_dvd_iff_le hpos).1 (h.trans hdiv)
  exact (padicValNat_dvd_iff_le (by omega)).2 (by omega)

theorem coeff_zero_ne_zero_any {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) : f.coeff 0 ≠ 0 := by
  intro h
  obtain ⟨g, hgeq⟩ : (Polynomial.X : ℤ[X]) ∣ f := Polynomial.X_dvd_iff.2 h
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hgeq; exact hmon.ne_zero hgeq
  rcases hirr.isUnit_or_isUnit hgeq with hu | hu
  · exact Polynomial.not_isUnit_X hu
  · have hgd : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hf1 : f.natDegree = 1 := by
      rw [hgeq, Polynomial.natDegree_mul Polynomial.X_ne_zero hg0, hgd, Polynomial.natDegree_X]
    omega

theorem traceSeq_tendsto_any {f : ℤ[X]} {α : ℝ} (hD : PisotDataAny f α) :
    Tendsto (traceSeq f) atTop atTop := by
  classical
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum f hD.monic hD.irr
  have hαr : (f.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0 := by
    have := congrArg (algebraMap ℝ ℂ) hD.root
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval_map]
    rw [RingHom.ext_int ((algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ)) (Int.castRingHom ℂ)] at this
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hsurj _ hαr
  have hsm : ∀ i, i ≠ i₀ → ‖e i‖ < 1 := by
    intro i hi
    refine hD.small _ ((Polynomial.mem_roots (hD.monic.map _).ne_zero).2 (he i)) ?_
    rw [← hi₀]; exact fun h => hi (hinj h)
  have hfl := eventually_floor_eq_traceSeq f hD.monic e he hinj hi₀ hsm
  have hfloor : Tendsto (fun N : ℕ => ⌊α ^ N⌋) atTop atTop :=
    tendsto_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hD.gt_one)
  refine tendsto_atTop_mono' atTop ?_ hfloor
  filter_upwards [hfl] with N hN
  rcases hN with h | h <;> omega

/-- **Step 3 (window), any degree.** -/
theorem window_shift_any {f : ℤ[X]} {α : ℝ} (hD : PisotDataAny f α) (hdeg : 2 ≤ f.natDegree) {s : ℤ} (hP : PrimeTraces f s)
    (k : ℕ) : ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat - w := by
  classical
  have hd1 : 1 ≤ f.natDegree := by omega
  set C := compM ℤ f with hC
  set E : ℕ → ℕ := fun n => ((3 : ℤ) ^ n + s).toNat with hE
  have hdet : C.det ≠ 0 := compM_det_ne_zero_int f hd1 (coeff_zero_ne_zero_any hD.monic hD.irr hdeg)
  have hgrow : Tendsto (fun n => traceSeq f (E n)) atTop atTop :=
    (traceSeq_tendsto_any hD).comp (shiftExp_tendsto s)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hP
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop (|C.det| + 4))
  have hEn : ∀ n, s.natAbs ≤ n → ((E n : ℕ) : ℤ) = 3 ^ n + s := by
    intro n hn
    have h1 : (n : ℤ) < 3 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
    exact Int.toNat_of_nonneg (by omega)
  set n := max (max N0 N1) (max s.natAbs (f.natDegree * (k + f.natDegree) + 1)) with hn
  have hnN0 : N0 ≤ n := by omega
  have hnN1 : N1 ≤ n := by omega
  have hns : s.natAbs ≤ n := by omega
  have hnk : f.natDegree * (k + f.natDegree) + 1 ≤ n := by omega
  obtain ⟨p, hpp, hpe⟩ := hN0 n hnN0
  have hb : |C.det| + 4 ≤ traceSeq f (E n) := hN1 n hnN1
  have hdnn : (0:ℤ) ≤ |C.det| := abs_nonneg _
  have hp4 : (4:ℤ) ≤ (p : ℤ) := by rw [← hpe]; linarith
  have hp2 : 2 ≤ p := by exact_mod_cast (by linarith : (2:ℤ) ≤ (p:ℤ))
  have hp3 : p ≠ 3 := by intro h; rw [h] at hp4; norm_num at hp4
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro hdvd
    have h2 : (p : ℤ) ∣ |C.det| := (dvd_abs _ _).2 hdvd
    have := Int.le_of_dvd (abs_pos.2 hdet) h2
    linarith
  -- Step 1: the `3`-adic valuation of `|GL₃(𝔽_p)|` exceeds `n`
  have hval : n < padicValNat 3 (ThreeAdic.glCard f.natDegree p) := by
    by_contra hcon
    push Not at hcon
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨j, hj1, hj⟩ := ShiftedWindow.exists_period_orderOf_dvd f.natDegree Nat.prime_three hcon
    obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop ((p : ℤ) + 1))
    set K := max N0 N2 + 1 with hK
    set n' := n + K * j with hn'
    have hKj : K ≤ K * j := Nat.le_mul_of_pos_right _ hj1
    obtain ⟨q, hqp, hqe⟩ := hN0 n' (by omega)
    have hbig' : (p : ℤ) + 1 ≤ traceSeq f (E n') := hN2 n' (by omega)
    have hs1 : (1 : ℕ) ≤ 3 ^ (K * j) := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨M, hM⟩ : ∃ M, M = 3 ^ n * (3 ^ (K * j) - 1) := ⟨_, rfl⟩
    have hMz : (M : ℤ) = 3 ^ n' - 3 ^ n := by
      rw [hM, hn', pow_add]; push_cast [Nat.cast_sub hs1]; ring
    have h1 := hEn n hns
    have h2 := hEn n' (by omega)
    have hle : E n ≤ E n' := by
      have : (3 : ℤ) ^ n ≤ 3 ^ n' := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hdiff : E n' - E n = M := by omega
    have hdv : (p : ℤ) ∣ (C ^ E n').trace - (C ^ E n).trace :=
      TheoremDGround.dvd_trace_sub_of_orderOf_dvd C hpp hdetp hle
        (fun D _ => by rw [hdiff, hM]; exact hj K D)
    have hdvn : (p : ℤ) ∣ (C ^ E n).trace := by
      have : (C ^ E n).trace = traceSeq f (E n) := rfl
      rw [this, hpe]
    have hdvn' : (p : ℤ) ∣ (q : ℤ) := by
      have := dvd_add hdv hdvn
      simp only [sub_add_cancel] at this
      have h' : (C ^ E n').trace = traceSeq f (E n') := rfl
      rwa [h', hqe] at this
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).1 (by exact_mod_cast hdvn')
    rw [hqe, ← hpq] at hbig'
    linarith
  -- Step 2: the window
  obtain ⟨i, hi1, hid, hdvdi⟩ :=
    TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard Nat.prime_three hpp hp3 hd1 hval
  have hone : 1 ≤ p ^ i := Nat.one_le_pow _ _ hpp.pos
  have hdvdN : 3 ^ (n / f.natDegree) ∣ p ^ i - 1 := by
    have hc : ((p ^ i - 1 : ℕ) : ℤ) = (p : ℤ) ^ i - 1 := by
      rw [Nat.cast_sub hone]; push_cast; ring
    have hz : ((3 ^ (n / f.natDegree) : ℕ) : ℤ) ∣ ((p ^ i - 1 : ℕ) : ℤ) := by
      rw [hc]; push_cast; exact hdvdi
    exact_mod_cast hz
  have hwin := dvd_sq_sub_one_of_dvd_pow_sub_one hpp hp3 hi1 hdvdN
  have hkle : k ≤ n / f.natDegree - i := by
    have : k + f.natDegree ≤ n / f.natDegree :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    omega
  have hsq : (3 : ℕ) ^ k ∣ p ^ 2 - 1 := (pow_dvd_pow 3 hkle).trans hwin
  refine ⟨n, by nlinarith, by have := hEn n hns; omega, p, ?_, by rw [hpe, sub_self]; exact dvd_zero _⟩
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpp.pos
  have hc : ((p ^ 2 - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hp1]; push_cast; ring
  rw [← hc]
  exact_mod_cast hsq

/-- **The Teichmüller limit, any degree.**  The Frobenius orbit `k ↦ C̄^(3^k)` in the finite ring
`M_d(𝔽₃)` is eventually periodic, with period `F ≥ 1`; lifting gives `T^(3^F) ≡ T` to growing
precision for `T = C^(3^ν)`.  (Degree 3 pins `F ∈ {1,2,3}` by `cm3_check`; not needed here.) -/
theorem exists_teich_limit_any (f : ℤ[X]) :
    ∃ F : ℕ, 1 ≤ F ∧ ∃ n₀ : ℕ, ∀ ν, n₀ ≤ ν → ∀ i j, (3 : ℤ) ^ (ν - n₀ + 1) ∣
        ((compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) - compM ℤ f ^ (3 ^ ν)) i j := by
  classical
  set g : ℕ → Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod 3) :=
    fun k => compM (ZMod 3) f ^ (3 ^ k) with hg
  obtain ⟨a, b, hab, hgab⟩ := Finite.exists_ne_map_eq_of_infinite g
  wlog hlt : a < b generalizing a b
  · exact this b a (Ne.symm hab) hgab.symm (by omega)
  have htr : ∀ m m' : ℕ, compM (ZMod 3) f ^ m = compM (ZMod 3) f ^ m' →
      ∀ i j, (3 : ℤ) ∣ (compM ℤ f ^ m - compM ℤ f ^ m') i j := by
    intro m m' h2 i j
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 ?_
    rw [← compM_map (Int.castRingHom (ZMod 3)) f, ← map_matrix_pow, ← map_matrix_pow] at h2
    have := congrArg (fun M => M i j) h2
    simp only [Matrix.map_apply] at this
    simp only [eq_intCast] at this
    simp [Matrix.sub_apply, this]
  refine ⟨b - a, by omega, a, fun ν hν i j => ?_⟩
  have hcomm : Commute (compM ℤ f ^ (3 ^ b)) (compM ℤ f ^ (3 ^ a)) := Commute.pow_pow_self _ _ _
  have h := pow_c_pow_congr (c := 3) hcomm (htr _ _ hgab.symm) (ν - a) i j
  push_cast at h
  have e1 : (compM ℤ f ^ (3 ^ ν)) ^ (3 ^ (b - a)) = (compM ℤ f ^ (3 ^ b)) ^ (3 ^ (ν - a)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 2; omega
  have e2 : compM ℤ f ^ (3 ^ ν) = (compM ℤ f ^ (3 ^ a)) ^ (3 ^ (ν - a)) := by
    rw [← pow_mul, ← pow_add]; congr 2; omega
  rw [e1, e2]; exact h

/-- **Non-scalarity mod 3, any degree.**  Outside the classes `f ≡ (X − z)^ℓ`, `C^(3^ν) ∓ 1` has
an entry prime to `3`. -/
theorem exists_entry_ne_any {f : ℤ[X]} (hmon : f.Monic) (hd1 : 1 ≤ f.natDegree)
    (hnc : ∀ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) ≠ (X - C z) ^ f.natDegree) (ν : ℕ) (z : ℤ)
    (hz : z = 1 ∨ z = -1) : ∃ a b, ¬ (3 : ℤ) ∣ (compM ℤ f ^ (3 ^ ν) - z • (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)) a b := by
  classical
  by_contra hcon
  push Not at hcon
  set zb : ZMod 3 := (z : ZMod 3) with hzb
  -- `D^(3^ν) = z` in `ZMod 3`
  have hDz : compM (ZMod 3) f ^ (3 ^ ν) - zb • (1 : Matrix _ _ (ZMod 3)) = 0 := by
    ext a b
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (hcon a b)
    rw [← compM_map (Int.castRingHom (ZMod 3)) f]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply] at h ⊢
    rw [← map_matrix_pow] at *
    push_cast at h
    simpa [Matrix.map_apply] using h
  have haev : Polynomial.aeval (compM (ZMod 3) f) ((X - C zb) ^ (3 ^ ν)) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, ZMod.pow_card_pow, map_sub, map_pow, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one]
    exact hDz
  have hdvd := dvd_of_aeval_compM_eq_zero f hmon hd1 _ haev
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C zb) _).1 hdvd
  have heq := eq_of_monic_of_associated (hmon.map _) ((monic_X_sub_C zb).pow i) hi
  have hdeg : i = f.natDegree := by
    have := congrArg natDegree heq
    rw [hmon.natDegree_map, natDegree_pow, natDegree_X_sub_C, mul_one] at this
    exact this.symm
  exact hnc zb (by rw [heq, hdeg])


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

/-- The minimal polynomial of `β` is `≡ (X − ε)^ℓ (mod 3)` for a unit `ε = ±1` (the class on
which every `3`-adic constraint of the cubic route can hold; `ShiftRigidityUnipotent`). -/
def UnipotentMod3 (β : ℝ) : Prop :=
  ∃ f : ℤ[X], f.Monic ∧ f.map (Int.castRingHom ℚ) = minpoly ℚ β ∧ ∃ ε : ZMod 3, ε ≠ 0 ∧
    f.map (Int.castRingHom (ZMod 3)) = (X - Polynomial.C ε) ^ f.natDegree

/-- **Believed (~75%), leaf (generic class)**: shift rigidity in degree `≥ 4` outside the unipotent
class.  Route: the cubic window + Teichmüller + spectral transfer (degree-general), with the
constant `±1` spectral vector excluded because `C ∓ 1` is not nilpotent mod 3, the `z = 0` cube
class excluded since then traces are `≡ 0 (mod 3)`, and the non-constant case by a Galois element
acting without fixed points on the roots outside `ℚ(μ_Q)`. -/
theorem shiftTraceRigidity_ge_four_generic {s : ℤ} (hs : s ≠ 0) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 4 ≤ (minpoly ℚ β).natDegree) (hU : ¬ UnipotentMod3 β) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ) := by
  sorry

/-- **Believed true (~90%) but no mechanism known, leaf (unipotent class)**.  The `3`-adic route
sees nothing here (`ShiftRigidityUnipotent.unipotent_trace_congr`).  A sharper window shows a prime
`p_n = tr C^(3^n+s)` with `v₃(p_n − 1) = n` exactly forces `3^(n+1) ∣ ord(C mod p_n)`, hence (degree
4) a cubic factor of `f mod p_n` whose roots generate the `3`-Sylow of `𝔽_(p³)^*`: a constraint of
positive density each `n`, not a contradiction.  Reopen via `UnipotentCovering`. -/
theorem shiftTraceRigidity_ge_four_unipotent {s : ℤ} (hs : s ≠ 0) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 4 ≤ (minpoly ℚ β).natDegree) (hU : UnipotentMod3 β) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ) := by
  sorry

/-- **Believed (~75%)**: shift rigidity in degree `≥ 4`.  English route: the cubic proof's cube
class and spectral transfer (`exists_spectral_solution_shift` is degree-general), with
`rigidity_generic` replaced by a Galois element acting fixed-point-freely on the roots outside
`ℚ(μ_Q)`; the exceptional cases are the factorization types of `f mod 3` with a root in a
cyclotomic `ℚ(μ_(3^f−1))`.  Evidence: degree 3, and the convergent prime heuristic.

Phase 65 lap 2: that route is **insufficient** on the unipotent class `f ≡ (X ∓ 1)^ℓ (mod 3)`
with `tr β^s = ±1`, which is nonempty in degree 4
(`ShiftRigidityUnipotent.unipotent_trace_congr`, `f₀ = X⁴ − 4X³ − X + 1`, `s = −1`): every
`3`-adic constraint is satisfied there.  That class needs a non-`3`-adic input
(`ShiftRigidityUnipotent.UnipotentCovering`); confidence that a proof is reachable is lower than
the truth confidence. -/
theorem shiftTraceRigidity_ge_four {s : ℤ} (hs : s ≠ 0) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 4 ≤ (minpoly ℚ β).natDegree) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (((3 : ℤ) ^ n + s).toNat) = (p : ℂ) := by
  by_cases hU : UnipotentMod3 β
  · exact shiftTraceRigidity_ge_four_unipotent hs hβ hdeg hU
  · exact shiftTraceRigidity_ge_four_generic hs hβ hdeg hU

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
