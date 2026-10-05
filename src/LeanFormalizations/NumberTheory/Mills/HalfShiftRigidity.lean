/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftRigidity

/-!
# Phase 61, node D: no cubic Pisot `β` has `Tr(β^((3^n + s)/2))` prime for all large `n` (`s` odd)

Decomposition of `ShiftedMillsAll.halfShiftTraceRigidity_holds` (`PROOF-THEOREM-E.md`, "E+ for odd
`s`").  Same frame as node C (`ShiftRigidity`): a Nullstellensatz transfer of the `3`-adic data to
the algebraic numbers `AlgQ`, then Galois rigidity with single automorphisms.  The new content is the
square root: the exponent `N_n = (3^n + s)/2` satisfies `2 N_n = 3^n + s`, so the transferred trace
matrix `P'` satisfies `P'^2 C^(s⁻) = P C^(s⁺)`, and its eigenvalues `v_k` satisfy `v_k² = u_k α_k^s`.

## The pieces
* `not_prime_of_dvd`, `three_dvd_of_cube`: a prime `q` dividing every trace kills prime traces along
  any exponent sequence tending to `∞`; the cube class `f ≡ (X − z)³ (mod 3)` is the case `q = 3`.
* `window_half` (Step 3 for `N_n`): the filter needs `ord ∣ 3^n (3^t − 1)/2`, so the period is doubled.
* `exists_entry_nonscalar`, `exists_half_solution`, `exists_half_spectral` (the transfer): spectral
  data `v_k² = u_k α_k^s`, `Σ v_k = ω`, `ω² = 1`, `u_k^(Q+1) = u_k`, and `u` **non-constant**
  (outside the cube class `C^(3^ν)` is not scalar mod 3; encoded as `y · Σ r (P − P₀₀ • 1) = 1`).
* `flip_mem` (the Kummer step): every `v_k` lies in any field `M` containing the `v_k²`.  An
  automorphism over `M` flipping one `v_k` flips a set `S`: `|S| = 1` gives `v_k = 0`, `|S| = 3`
  gives `ω = 0`, `|S| = 2` gives `v_l = ω`, so `|α_l| = 1`.
* `circulant_const_mu`: node C's circulant with the `u_k` roots of unity of order prime to `3` in
  place of a rational trace (the equilateral configuration needs a primitive 6th root of unity).
* `half_generic` (no root in `ℚ(μ_(2Q))`): `M = ℚ(μ_(2Q), roots)`; a 3-cycle `σ` over `ℚ(μ_(2Q))`;
  `δ² = α` from some `v_j` with `u_j ≠ 0`; `σ³` fixes `M`; `a_k = v_k / δ_k^s ∈ μ_(2Q) ∪ {0}` is fixed
  by `σ`; the circulant makes `a`, hence `u = a²`, constant.
* `half_e1` (E1 at `g = 2`, a root in `ℚ(μ_26) = ℚ(ζ₁₃)`): `flip_mem` over `ℚ(ζ₁₃)` puts every
  `v_k` in `ℚ(ζ₁₃)`, giving `γ ∈ ℚ(ζ₁₃)` with `γ² = ±α_j`; `τ : ζ ↦ ζ²` 3-cycles the roots, so
  `τ³γ = ±γ`.  `(+)`: `g = Π (X − τ^i γ) ∈ ℤ[X]` is cubic Pisot with `tr g^(2N) = tr f^N`, and node C
  applies to `g` (`half_e1_plus`).  `(−)`: `γ = h(ζ)`, `h ∈ ℤ[X]` (integral closure), `Φ₁₃ ∣ h(X⁸) + h(X)`
  gives `13 ∣ h(1)`, so `13` divides every trace (`half_e1_minus`).
* `not_halfPrimeTraces`: the assembly.
-/

namespace LeanFormalizations.Mills.HalfShiftRigidity

open Filter Polynomial IntermediateField LeanFormalizations.Mills.TheoremDGeneral
  LeanFormalizations.Mills.TheoremDMixed LeanFormalizations.Mills.ShiftRigidity

/-- The half exponent `(3^n + s)/2`. -/
def halfExp (s : ℤ) (n : ℕ) : ℕ := ((3 : ℤ) ^ n + s).toNat / 2

/-- The traces `tr C^((3^n + s)/2)` are primes for all large `n`. -/
def HalfPrimeTraces (f : ℤ[X]) (s : ℤ) : Prop :=
  ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ traceSeq f (halfExp s n) = p

/-! ### Divisibility kills prime traces -/

/-- A prime dividing every trace kills prime traces along any exponent sequence tending to `∞`. -/
theorem not_prime_of_dvd {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {q : ℕ} (hq : q.Prime)
    (hdvd : ∀ N, 1 ≤ N → (q : ℤ) ∣ traceSeq f N) {E : ℕ → ℕ} (hE : Tendsto E atTop atTop) :
    ¬ ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ traceSeq f (E n) = p := by
  classical
  intro hP
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
  have hbig : ∀ᶠ N : ℕ in atTop, ((q : ℝ) + 1) ≤ α ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hD.gt_one).eventually_ge_atTop _
  obtain ⟨n, ⟨p, hp, hpe⟩, hf4, hb4, hE1⟩ :=
    (hP.and ((hE.eventually hfl).and ((hE.eventually hbig).and
      (hE.eventually (eventually_ge_atTop 1))))).exists
  have hpq : p = q := by
    have : (q : ℤ) ∣ (p : ℤ) := hpe ▸ hdvd _ hE1
    have : q ∣ p := by exact_mod_cast this
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  have hfl4 : (q : ℤ) + 1 ≤ ⌊α ^ E n⌋ := Int.le_floor.2 (by exact_mod_cast hb4)
  rw [hpe, hpq] at hf4
  push_cast at hf4
  omega

/-- The cube class: every trace is divisible by `3`. -/
theorem three_dvd_of_cube {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) (z : ZMod 3)
    (hz : f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3) (N : ℕ) : (3 : ℤ) ∣ traceSeq f N := by
  classical
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 ?_
  rw [traceSeq_cast]
  have hnil : (compM (ZMod 3) f - z • (1 : Matrix _ _ (ZMod 3))) ^ 3 = 0 := by
    have h := aeval_compM_self (K := ZMod 3) f hD.monic hd1
    rw [hz] at h
    simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] using h
  have key : ∀ (n : ℕ), n = 3 → ∀ M : Matrix (Fin n) (Fin n) (ZMod 3),
      (M - z • (1 : Matrix _ _ (ZMod 3))) ^ 3 = 0 → (M ^ N).trace = 0 := by
    intro n hn; subst hn; intro M hM
    have := UnipotentTrace.trace_pow_eq_zero z _ hM N
    rwa [add_sub_cancel] at this
  exact key _ hD.deg _ hnil

theorem halfExp_tendsto (s : ℤ) : Tendsto (halfExp s) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 * b + s.natAbs + 2)] with n hn
  have h1 : (n : ℤ) < 3 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
  unfold halfExp
  have : 2 * b ≤ ((3 : ℤ) ^ n + s).toNat := by
    rw [Int.le_toNat] <;> omega
  omega

/-! ### Step 3 and the transfer -/

/-- **Step 3 (window) for the half exponent.** -/
theorem window_half {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s)
    (hP : HalfPrimeTraces f s) (k : ℕ) :
    ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f (halfExp s n) - w := by
  classical
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
  set C := compM ℤ f with hC
  set E : ℕ → ℕ := halfExp s with hE
  have hdet : C.det ≠ 0 := compM_det_ne_zero_int f hd1 (coeff_zero_ne_zero hD.monic hD.irr hD.deg)
  have hgrow : Tendsto (fun n => traceSeq f (E n)) atTop atTop :=
    (traceSeq_tendsto hD).comp (halfExp_tendsto s)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hP
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop (|C.det| + 4))
  have hEn : ∀ n, s.natAbs ≤ n → 2 * ((E n : ℕ) : ℤ) = 3 ^ n + s := by
    intro n hn
    have h1 : (n : ℤ) < 3 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
    have hz : (((3 : ℤ) ^ n + s).toNat : ℤ) = 3 ^ n + s := Int.toNat_of_nonneg (by omega)
    have hev : Even ((3 : ℤ) ^ n + s) := Odd.add_odd (Odd.pow (by decide)) hs
    have h2 : 2 ∣ ((3 : ℤ) ^ n + s).toNat := by
      obtain ⟨r, hr⟩ := hev
      have : (((3 : ℤ) ^ n + s).toNat : ℤ) = 2 * r := by rw [hz, hr]; ring
      exact Int.natCast_dvd_natCast.1 ⟨r, this⟩
    show 2 * (((((3 : ℤ) ^ n + s).toNat / 2 : ℕ)) : ℤ) = _
    rw [← hz]; exact_mod_cast Nat.mul_div_cancel' h2
  set n := max (max N0 N1) (max s.natAbs (3 * k + 6)) with hn
  have hnN0 : N0 ≤ n := by omega
  have hnN1 : N1 ≤ n := by omega
  have hns : s.natAbs ≤ n := by omega
  have hnk : 3 * k + 6 ≤ n := by omega
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
    push_neg at hcon
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨j, hj1, hj⟩ := ShiftedWindow.exists_period_orderOf_dvd f.natDegree Nat.prime_three hcon
    obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop ((p : ℤ) + 1))
    set K := max N0 N2 + 1 with hK
    set n' := n + 2 * (K * j) with hn'
    have hKj : K ≤ K * j := Nat.le_mul_of_pos_right _ hj1
    obtain ⟨q, hqp, hqe⟩ := hN0 n' (by omega)
    have hbig' : (p : ℤ) + 1 ≤ traceSeq f (E n') := hN2 n' (by omega)
    have hs1 : (1 : ℕ) ≤ 3 ^ (K * j) := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨X, hX⟩ : ∃ X, X = 3 ^ (K * j) := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := hX ▸ hs1
    obtain ⟨h, hh⟩ : ∃ h, 2 * h = X + 1 := by
      have : Even (3 ^ (K * j) + 1) := Odd.add_one (Odd.pow (by decide))
      obtain ⟨r, hr⟩ := this; exact ⟨r, by omega⟩
    obtain ⟨M, hM⟩ : ∃ M, M = 3 ^ n * (X - 1) * h := ⟨_, rfl⟩
    have hMz : 2 * (M : ℤ) = 3 ^ n' - 3 ^ n := by
      have hhz : 2 * (h : ℤ) = X + 1 := by exact_mod_cast hh
      have hn'z : (3 : ℤ) ^ n' = 3 ^ n * (X : ℤ) ^ 2 := by
        rw [hn', pow_add, mul_comm 2, pow_mul, hX]; push_cast; ring
      rw [hn'z, hM]; push_cast [Nat.cast_sub hX1]
      linear_combination (3 : ℤ) ^ n * ((X : ℤ) - 1) * hhz
    have h1 := hEn n hns
    have h2 := hEn n' (by omega)
    have hle : E n ≤ E n' := by
      have : (3 : ℤ) ^ n ≤ 3 ^ n' := pow_le_pow_right₀ (by norm_num) (by omega)
      have : ((E n : ℕ) : ℤ) ≤ E n' := by omega
      exact_mod_cast this
    have hdiff : E n' - E n = M := by omega
    have hdv : (p : ℤ) ∣ (C ^ E n').trace - (C ^ E n).trace :=
      TheoremDGround.dvd_trace_sub_of_orderOf_dvd C hpp hdetp hle
        (fun D _ => by rw [hdiff, hM]; rw [hX]; exact Dvd.dvd.mul_right (hj K D) _)
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
  obtain ⟨i, hi1, hi3, hdvdi⟩ :=
    TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard Nat.prime_three hpp hp3 hd1 hval
  rw [hD.deg] at hi3 hdvdi
  have hone : 1 ≤ p ^ i := Nat.one_le_pow _ _ hpp.pos
  have hdvdN : 3 ^ (n / 3) ∣ p ^ i - 1 := by
    have hc : ((p ^ i - 1 : ℕ) : ℤ) = (p : ℤ) ^ i - 1 := by
      rw [Nat.cast_sub hone]; push_cast; ring
    have hz : ((3 ^ (n / 3) : ℕ) : ℤ) ∣ ((p ^ i - 1 : ℕ) : ℤ) := by
      rw [hc]; push_cast; exact hdvdi
    exact_mod_cast hz
  have hwin := ShiftedWindow.dvd_sub_or_add_of_dvd_pow_sub_one hp2 hi1 hi3 hdvdN
  have hkle : k ≤ n / 3 - 1 := by omega
  have hsq : (3 : ℕ) ^ k ∣ (p - 1) * (p + 1) := by
    rcases hwin with hw | hw
    · exact dvd_mul_of_dvd_left ((pow_dvd_pow 3 hkle).trans hw) _
    · exact dvd_mul_of_dvd_right ((pow_dvd_pow 3 hkle).trans hw) _
  refine ⟨n, by omega, by have := hEn n hns; omega, p, ?_, by rw [hpe, sub_self]; exact dvd_zero _⟩
  have hc : (((p - 1) * (p + 1) : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  rw [← hc]
  exact_mod_cast hsq

/-- **Non-scalarity mod 3.**  Outside the cube class, `C^(3^ν) − c` has an entry prime to `3`
for `c` its own `(i₀, i₀)` entry. -/
theorem exists_entry_nonscalar {f : ℤ[X]} {α : ℝ} (hD : PisotData f α)
    (hnc : ∀ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) ≠ (X - C z) ^ 3)
    (i₀ : Fin f.natDegree) (ν : ℕ) :
    ∃ a b, ¬ (3 : ℤ) ∣ (compM ℤ f ^ (3 ^ ν) -
      (compM ℤ f ^ (3 ^ ν)) i₀ i₀ • (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)) a b := by
  sorry

/-- **The transfer** for the half exponent. -/
theorem exists_half_solution (f : ℤ[X]) (hd : 1 ≤ f.natDegree) (i₀ : Fin f.natDegree)
    {F n₀ : ℕ} {s : ℤ} (hs : Odd s)
    (hlim : ∀ ν, n₀ ≤ ν → ∀ i j, (3 : ℤ) ^ (ν - n₀ + 1) ∣
        ((compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) - compM ℤ f ^ (3 ^ ν)) i j)
    (hne : ∀ ν : ℕ, ∃ a b, ¬ (3 : ℤ) ∣ (compM ℤ f ^ (3 ^ ν) -
      (compM ℤ f ^ (3 ^ ν)) i₀ i₀ • (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)) a b)
    (hcong : ∀ k : ℕ, ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f (halfExp s n) - w) :
    ∃ (x x' : Fin f.natDegree → AlgQ) (w : AlgQ),
      polyMat AlgQ f x ^ (3 ^ F) = polyMat AlgQ f x ∧ w ^ 2 = 1 ∧
      polyMat AlgQ f x' ^ 2 * compM AlgQ f ^ (-s).toNat =
        polyMat AlgQ f x * compM AlgQ f ^ s.toNat ∧
      (polyMat AlgQ f x').trace = w ∧
      polyMat AlgQ f x ≠ (polyMat AlgQ f x) i₀ i₀ • 1 := by
  sorry

/-- **Steps 3 + transfer**: the spectral solution in `AlgQ`, with square roots. -/
theorem exists_half_spectral {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s)
    (hP : HalfPrimeTraces f s)
    (hnc : ∀ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) ≠ (X - C z) ^ 3) :
    ∃ (Q : ℕ) (e u v : Fin 3 → AlgQ) (ω : AlgQ),
      (Q = 2 ∨ Q = 8 ∨ (Q = 26 ∧ Irreducible (f.map (Int.castRingHom (ZMod 3))))) ∧
      Function.Injective e ∧ (∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0) ∧
      ((e 0 : ℂ) = α) ∧ (∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1) ∧
      (∀ k, u k ^ (Q + 1) = u k) ∧ ω ^ 2 = 1 ∧ (∀ k, v k ^ 2 = u k * e k ^ s) ∧
      (∑ k, v k = ω) ∧ ¬ (∀ k, u k = u 0) := by
  sorry

/-! ### The Kummer step and the circulant -/

/-- A square root outside `M` of an element of `M` is flipped by some automorphism over `M`. -/
theorem exists_flip (M : IntermediateField ℚ AlgQ) {x : AlgQ} (hx : x ∉ M) (hx2 : x ^ 2 ∈ M) :
    ∃ σ : AlgQ ≃ₐ[M] AlgQ, σ x = -x := by
  haveI : Normal M AlgQ := Normal.tower_top_of_normal ℚ M AlgQ
  set c : M := ⟨x ^ 2, hx2⟩
  set g : M[X] := X ^ 2 - Polynomial.C c with hg
  have hgm : g.Monic := by rw [hg]; exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hgd : g.natDegree = 2 := by rw [hg]; exact Polynomial.natDegree_X_pow_sub_C
  have hbr : ∀ z : AlgQ, aeval z g = z ^ 2 - x ^ 2 := by
    intro z; rw [hg]; simp [c]
  have hgirr : Irreducible g := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hgd]; decide) ?_
    intro r hr
    have h0 : aeval (r : AlgQ) g = 0 := by
      have : aeval (r : AlgQ) g = algebraMap M AlgQ (g.eval r) :=
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := AlgQ) r g
      rw [this, hr.eq_zero, map_zero]
    rw [hbr] at h0
    have : ((r : AlgQ) - x) * ((r : AlgQ) + x) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h | h
    · exact hx (by rw [← sub_eq_zero.1 h]; exact r.2)
    · have : x = -(r : AlgQ) := by linear_combination h
      exact hx (by rw [this]; exact M.neg_mem r.2)
  have hmin : minpoly M x = g :=
    (minpoly.eq_of_irreducible_of_monic hgirr (by rw [hbr]; ring) hgm).symm
  have halg : IsAlgebraic M x := ⟨g, hgm.ne_zero, by rw [hbr]; ring⟩
  exact minpoly.exists_algEquiv_of_root' (x := -x) halg (by rw [hmin, hbr]; ring)

theorem sign_rigid {F : Type*} [Field F] [CharZero F] {v0 v1 v2 w0 w1 w2 ω : F}
    (h0 : w0 = v0 ∨ w0 = -v0) (h1 : w1 = v1 ∨ w1 = -v1) (h2 : w2 = v2 ∨ w2 = -v2)
    (hsum : v0 + v1 + v2 = ω) (hs2 : w0 + w1 + w2 = ω) (hω0 : ω ≠ 0)
    (b0 : v0 = ω → False) (b1 : v1 = ω → False) (b2 : v2 = ω → False) :
    w0 = v0 ∧ w1 = v1 ∧ w2 = v2 := by
  have two : (2 : F) ≠ 0 := two_ne_zero
  have z : ∀ x : F, 2 * x = 0 → x = 0 := fun x h => (mul_eq_zero.1 h).resolve_left two
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hs2 ⊢
  · exact ⟨rfl, rfl, rfl⟩
  · have := z v2 (by linear_combination hsum - hs2); exact ⟨rfl, rfl, by rw [this]; ring⟩
  · have := z v1 (by linear_combination hsum - hs2); exact ⟨rfl, by rw [this]; ring, rfl⟩
  · exact (b0 (by have := z (v0 - ω) (by linear_combination hsum + hs2); linear_combination this)).elim
  · have := z v0 (by linear_combination hsum - hs2); exact ⟨by rw [this]; ring, rfl, rfl⟩
  · exact (b1 (by have := z (v1 - ω) (by linear_combination hsum + hs2); linear_combination this)).elim
  · exact (b2 (by have := z (v2 - ω) (by linear_combination hsum + hs2); linear_combination this)).elim
  · exact (hω0 (z ω (by linear_combination -(hs2 + hsum)))).elim

/-- **The flip lemma.**  Every `v_k` lies in any field containing the `v_k²`. -/
theorem flip_mem (M : IntermediateField ℚ AlgQ) {e u v : Fin 3 → AlgQ} {ω : AlgQ} {s : ℤ}
    (hs : s ≠ 0) (hnorm : ∀ k, ‖(e k : ℂ)‖ ≠ 1) (he0 : ∀ k, e k ≠ 0)
    (hu1 : ∀ k, u k = 0 ∨ ‖(u k : ℂ)‖ = 1) (hω : ω ^ 2 = 1)
    (hv : ∀ k, v k ^ 2 = u k * e k ^ s) (hsum : ∑ k, v k = ω) (hM : ∀ k, v k ^ 2 ∈ M) :
    ∀ k, v k ∈ M := by
  classical
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have hωpm : ω = 1 ∨ ω = -1 := by
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  -- no single `v_m` equals `ω`
  have bad : ∀ m, v m = ω → False := by
    intro m hm
    have h1 : u m * e m ^ s = 1 := by rw [← hv, hm, hω]
    have c1 : ((u m : ℂ)) * ((e m : ℂ)) ^ s = 1 := by
      have := congrArg (fun z : AlgQ => (z : ℂ)) h1; push_cast at this; exact this
    have hn := congrArg norm c1
    rw [norm_mul, norm_zpow, norm_one] at hn
    have hu0 : (u m : ℂ) ≠ 0 := by intro h; rw [h, zero_mul] at c1; exact zero_ne_one c1
    have hun : ‖(u m : ℂ)‖ = 1 := by
      rcases hu1 m with h | h
      · exact absurd (by rw [h]; rfl) hu0
      · exact h
    rw [hun, one_mul] at hn
    have hpos : 0 < ‖(e m : ℂ)‖ := norm_pos_iff.2 (by exact_mod_cast he0 m)
    rcases lt_or_gt_of_ne (hnorm m) with hl | hg
    · rcases lt_or_gt_of_ne hs with hn' | hp
      · have := one_lt_zpow_of_neg₀ hpos hl hn'; linarith
      · have := zpow_lt_one₀ hpos hl hp; linarith
    · rcases lt_or_gt_of_ne hs with hn' | hp
      · have := zpow_lt_one_of_neg₀ hg hn'; linarith
      · have := one_lt_zpow₀ hg hp; linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ := hcon
  have hvj0 : v j ≠ 0 := fun h => hj (by rw [h]; exact M.zero_mem)
  obtain ⟨σ, hσ⟩ := exists_flip M hj (hM j)
  have hsg : ∀ k, σ (v k) = v k ∨ σ (v k) = -v k := by
    intro k
    have h2 : σ (v k) ^ 2 = v k ^ 2 := by
      rw [← map_pow]; exact σ.commutes ⟨v k ^ 2, hM k⟩
    have : (σ (v k) - v k) * (σ (v k) + v k) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hσω : σ ω = ω := by rcases hωpm with rfl | rfl <;> simp
  have hs2 : ∑ k, σ (v k) = ω := by rw [← map_sum, hsum, hσω]
  rw [Fin.sum_univ_three] at hsum hs2
  have b0 := bad 0; have b1 := bad 1; have b2 := bad 2
  have key := sign_rigid (hsg 0) (hsg 1) (hsg 2) hsum hs2 hω0 b0 b1 b2
  have hfix : σ (v j) = v j := by fin_cases j <;> simp [key]
  have : (2 : AlgQ) * v j = 0 := by linear_combination hσ - hfix
  exact hvj0 ((mul_eq_zero.1 this).resolve_left two_ne_zero)

/-- Three unit vectors `1, a, b` summing to `0`: `a³ = 1`. -/
theorem cube_one_of_unit_sum {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (h : 1 + a + b = 0) :
    a ^ 3 = 1 := by
  have hb' : b = -1 - a := by linear_combination h
  have hna : a * (starRingEnd ℂ) a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have hnb : b * (starRingEnd ℂ) b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]; simp
  rw [hb'] at hnb
  simp only [map_sub, map_neg, map_one] at hnb
  have hs : a + (starRingEnd ℂ) a = -1 := by linear_combination hnb - hna
  have h2 : a ^ 2 + a + 1 = 0 := by linear_combination a * hs - hna
  linear_combination (a - 1) * h2

theorem eq_one_of_pow {x : ℂ} {M n : ℕ} (hM : Nat.gcd n M = 1) (hx : x ^ M = 1) (hn : x ^ n = 1) :
    x = 1 := by
  have := pow_gcd_eq_one.2 ⟨hn, hx⟩
  rwa [hM, pow_one] at this

theorem no_sixth {x : ℂ} {M : ℕ} (hM : Nat.gcd 6 M ∣ 2) (hx : x ^ M = 1)
    (h : x ^ 2 - x + 1 = 0) : False := by
  have h6 : x ^ 6 = 1 := by linear_combination (x ^ 4 + x ^ 3 - x - 1) * h
  have hg := pow_gcd_eq_one.2 ⟨h6, hx⟩
  have h2 : x ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hM
    rw [← one_pow k, ← hg, ← pow_mul, ← hk]
  have : x = 2 := by linear_combination h2 - h
  rw [this] at h2; norm_num at h2

/-- The equilateral quadratic form vanishes on roots of unity of order prime to `3` (or `0`) only
on constant triples. -/
theorem quad_const_core {u0 u1 u2 : ℂ} {M : ℕ} (hM : Nat.gcd 6 M ∣ 2) (h0 : u0 ^ M = 1)
    (hu1 : u1 = 0 ∨ u1 ^ M = 1) (hu2 : u2 = 0 ∨ u2 ^ M = 1)
    (hQ : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 - u0 * u1 - u1 * u2 - u2 * u0 = 0) : u1 = u0 ∧ u2 = u0 := by
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; norm_num at hM
    · exact h
  have hu0 : u0 ≠ 0 := by
    rintro rfl; simp [zero_pow hMpos.ne'] at h0
  have h3 : Nat.gcd 3 M = 1 := by
    have : Nat.gcd 3 M ∣ Nat.gcd 6 M := Nat.gcd_dvd_gcd_of_dvd_left _ (by norm_num)
    have h := Nat.dvd_trans this hM
    have h3 : Nat.gcd 3 M ∣ 3 := Nat.gcd_dvd_left _ _
    have : Nat.gcd 3 M ∣ Nat.gcd 3 2 := Nat.dvd_gcd h3 h
    simpa using this
  set t1 := u1 / u0 with ht1
  set t2 := u2 / u0 with ht2
  have e1 : u1 = t1 * u0 := by rw [ht1]; field_simp
  have e2 : u2 = t2 * u0 := by rw [ht2]; field_simp
  have hq : u0 ^ 2 * (1 + t1 ^ 2 + t2 ^ 2 - t1 - t1 * t2 - t2) = 0 := by
    rw [e1, e2] at hQ; linear_combination hQ
  have hq' := (mul_eq_zero.1 hq).resolve_left (pow_ne_zero 2 hu0)
  have hpow : ∀ t u : ℂ, u = t * u0 → (u = 0 ∨ u ^ M = 1) → t = 0 ∨ t ^ M = 1 := by
    intro t u he hu
    rcases hu with hu | hu
    · left; rw [hu] at he; exact (mul_eq_zero.1 he.symm).resolve_right hu0
    · right; rw [he, mul_pow, h0, mul_one] at hu; exact hu
  have p1 := hpow _ _ e1 hu1
  have p2 := hpow _ _ e2 hu2
  suffices t1 = 1 ∧ t2 = 1 by rw [e1, e2, this.1, this.2]; simp
  rcases p1 with z1 | m1
  · rw [z1] at hq'
    rcases p2 with z2 | m2
    · rw [z2] at hq'; norm_num at hq'
    · exact (no_sixth hM m2 (by linear_combination hq')).elim
  rcases p2 with z2 | m2
  · rw [z2] at hq'; exact (no_sixth hM m1 (by linear_combination hq')).elim
  have n1 : ‖t1‖ = 1 := norm_eq_one_of_pow_eq_one hMpos m1
  have n2 : ‖t2‖ = 1 := norm_eq_one_of_pow_eq_one hMpos m2
  -- a primitive cube root of unity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ ^ 2 + ρ + 1 = 0 := by
    obtain ⟨ρ, hρp⟩ : ∃ ρ : ℂ, IsPrimitiveRoot ρ 3 := ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
    refine ⟨ρ, ?_⟩
    have h1 : ρ - 1 ≠ 0 := sub_ne_zero.2 (hρp.ne_one (by norm_num))
    have : (ρ - 1) * (ρ ^ 2 + ρ + 1) = 0 := by linear_combination hρp.pow_eq_one
    exact (mul_eq_zero.1 this).resolve_left h1
  have hρ3 : ρ ^ 3 = 1 := by linear_combination (ρ - 1) * hρ
  have nρ : ‖ρ‖ = 1 := norm_eq_one_of_pow_eq_one (by norm_num) hρ3
  have fac : (1 + ρ * t1 + ρ ^ 2 * t2) * (1 + ρ ^ 2 * t1 + ρ * t2) = 0 := by
    linear_combination hq' + (t1 + t2 + (ρ - 1) * (t1 ^ 2 + t2 ^ 2) + (ρ ^ 2 - ρ + 1) * t1 * t2) * hρ
  have nm : ∀ x y : ℂ, ‖x‖ = 1 → ‖y‖ = 1 → ‖x * y‖ = 1 := fun x y hx hy => by
    rw [norm_mul, hx, hy, one_mul]
  have nρ2 : ‖ρ ^ 2‖ = 1 := by rw [norm_pow, nρ, one_pow]
  have key : t1 ^ 3 = 1 ∧ t2 ^ 3 = 1 := by
    rcases mul_eq_zero.1 fac with hA | hA
    · have c1 := cube_one_of_unit_sum (nm _ _ nρ n1) (nm _ _ nρ2 n2) hA
      have c2 := cube_one_of_unit_sum (nm _ _ nρ2 n2) (nm _ _ nρ n1) (by linear_combination hA)
      constructor
      · linear_combination c1 - t1 ^ 3 * hρ3
      · linear_combination c2 - t2 ^ 3 * (ρ ^ 3 + 1) * hρ3
    · have c1 := cube_one_of_unit_sum (nm _ _ nρ2 n1) (nm _ _ nρ n2) hA
      have c2 := cube_one_of_unit_sum (nm _ _ nρ n2) (nm _ _ nρ2 n1) (by linear_combination hA)
      constructor
      · linear_combination c1 - t1 ^ 3 * (ρ ^ 3 + 1) * hρ3
      · linear_combination c2 - t2 ^ 3 * hρ3
  exact ⟨eq_one_of_pow h3 m1 key.1, eq_one_of_pow h3 m2 key.2⟩

/-- **The circulant with roots of unity** of order prime to `3`. -/
theorem circulant_const_mu {u0 u1 u2 w0 w1 w2 r : ℂ} {M : ℕ} (hM : Nat.gcd 6 M ∣ 2) (hr : r ≠ 0)
    (hw : ¬ (w0 = w2 ∧ w1 = w2))
    (hu0 : u0 = 0 ∨ u0 ^ M = 1) (hu1 : u1 = 0 ∨ u1 ^ M = 1) (hu2 : u2 = 0 ∨ u2 ^ M = 1)
    (E0 : u0 * w0 + u1 * w1 + u2 * w2 = r) (E1 : u0 * w1 + u1 * w2 + u2 * w0 = r)
    (E2 : u0 * w2 + u1 * w0 + u2 * w1 = r) : u0 = u1 ∧ u1 = u2 := by
  have D1 : (u0 - u2) * (w0 - w2) + (u1 - u0) * (w1 - w2) = 0 := by linear_combination E0 - E1
  have D2 : (u2 - u1) * (w0 - w2) + (u0 - u2) * (w1 - w2) = 0 := by linear_combination E1 - E2
  have hQ : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 - u0 * u1 - u1 * u2 - u2 * u0 = 0 := by
    by_cases hx : w0 - w2 = 0
    · have hy : w1 - w2 ≠ 0 := fun hy => hw ⟨sub_eq_zero.1 hx, sub_eq_zero.1 hy⟩
      have : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 - u0 * u1 - u1 * u2 - u2 * u0) * (w1 - w2) = 0 := by
        linear_combination (u0 - u2) * D2 - (u2 - u1) * D1
      exact (mul_eq_zero.1 this).resolve_right hy
    · have : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 - u0 * u1 - u1 * u2 - u2 * u0) * (w0 - w2) = 0 := by
        linear_combination (u0 - u2) * D1 - (u1 - u0) * D2
      exact (mul_eq_zero.1 this).resolve_right hx
  rcases hu0 with z0 | m0
  · rcases hu1 with z1 | m1
    · rcases hu2 with z2 | m2
      · exact ⟨z0.trans z1.symm, z1.trans z2.symm⟩
      · obtain ⟨a, b⟩ := quad_const_core hM m2 (Or.inl z0) (Or.inl z1) (by linear_combination hQ)
        exact ⟨by grind, by grind⟩
    · obtain ⟨a, b⟩ := quad_const_core hM m1 hu2 (Or.inl z0) (by linear_combination hQ)
      exact ⟨by grind, by grind⟩
  · obtain ⟨a, b⟩ := quad_const_core hM m0 hu1 hu2 hQ
    exact ⟨by grind, by grind⟩

/-! ### The generic case -/

/-- **The generic case**: no root of `f` in `ℚ(μ_(2Q))`. -/
theorem half_generic {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s) {Q : ℕ}
    (hQ : Q = 2 ∨ Q = 8 ∨ Q = 26)
    {e u v : Fin 3 → AlgQ} {ω : AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    (hbig : 1 < ‖(e 0 : ℂ)‖) (hsm : ∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1)
    (hu : ∀ k, u k ^ (Q + 1) = u k) (hω : ω ^ 2 = 1) (hv : ∀ k, v k ^ 2 = u k * e k ^ s)
    (hsum : ∑ k, v k = ω) (hnc : ¬ ∀ k, u k = u 0)
    (hL : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ cycField (2 * Q)) :
    False := by
  classical
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hc0 := coeff_zero_ne_zero hD.monic hD.irr hD.deg
  have he0 : ∀ k, e k ≠ 0 := by
    intro k h0; have := he k; rw [h0, eval_cubic hD.monic hD.deg] at this; simp at this
    exact hc0 this
  set L := cycField (2 * Q) with hLdef
  obtain ⟨σ, a, b, ha, hb, hab, h0a, hab', hb0⟩ := exists_three_cycle hD.monic hD.deg L hL hinj he
  have hfix : ∀ x ∈ L, ∀ τ : AlgQ ≃ₐ[L] AlgQ, τ x = x := fun x hx τ => τ.commutes ⟨x, hx⟩
  set τ : AlgQ ≃ₐ[L] AlgQ := σ * σ * σ * σ with hτdef
  have hτ : ∀ x, τ x = σ (σ (σ (σ x))) := fun x => rfl
  have t0 : τ (e 0) = e a := by rw [hτ, h0a, hab', hb0, h0a]
  have ta : τ (e a) = e b := by rw [hτ, hab', hb0, h0a, hab']
  have tb : τ (e b) = e 0 := by rw [hτ, hb0, h0a, hab', hb0]
  obtain ⟨d0, hd0⟩ := IsAlgClosed.exists_pow_nat_eq (e 0) two_pos
  set da := τ d0 with hda
  set db := τ da with hdb
  have hda2 : da ^ 2 = e a := by rw [hda, ← map_pow, hd0, t0]
  have hdb2 : db ^ 2 = e b := by rw [hdb, ← map_pow, hda2, ta]
  have hcyc : τ db = d0 := by
    have g3 : ∀ x, τ (τ (τ x)) = (σ * σ * σ) ((σ * σ * σ) ((σ * σ * σ) ((σ * σ * σ) x))) :=
      fun x => rfl
    set t := (σ * σ * σ) d0 with ht
    have hσ3 : (σ * σ * σ) (e 0) = e 0 := by
      show σ (σ (σ (e 0))) = e 0; rw [h0a, hab', hb0]
    have ht2 : t ^ 2 = d0 ^ 2 := by rw [ht, ← map_pow, hd0, hσ3]
    have : (t - d0) * (t + d0) = 0 := by linear_combination ht2
    rw [hdb, hda, g3, ← ht]
    rcases mul_eq_zero.1 this with h | h
    · have h' : t = d0 := by linear_combination h
      rw [h', ← ht, h', ← ht, h']
      exact h'
    · have h' : t = -d0 := by linear_combination h
      rw [h', map_neg, ← ht, h', neg_neg, ← ht, h', map_neg, ← ht, h', neg_neg]
  have hd0ne : ∀ x : AlgQ, x ^ 2 = e 0 ∨ x ^ 2 = e a ∨ x ^ 2 = e b → x ≠ 0 := by
    rintro x (h | h | h) rfl <;> simp at h <;> exact he0 _ h.symm
  have nd0 := hd0ne d0 (Or.inl hd0)
  have nda := hd0ne da (Or.inr (Or.inl hda2))
  have ndb := hd0ne db (Or.inr (Or.inr hdb2))
  -- the coefficients `a_k = v_k / d_k^s` are in `μ_(2Q) ∪ {0}`
  have coef : ∀ (k : Fin 3) (d : AlgQ), d ≠ 0 → d ^ 2 = e k →
      (v k / d ^ s) ^ 2 = u k := by
    intro k d hd hd2
    rw [div_pow, hv k, ← hd2]
    rw [show (d ^ 2) ^ s = (d ^ s) ^ 2 by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]]
    field_simp
  have mu : ∀ (k : Fin 3) (d : AlgQ), d ≠ 0 → d ^ 2 = e k →
      (v k / d ^ s) = 0 ∨ (v k / d ^ s) ^ (2 * Q) = 1 := by
    intro k d hd hd2
    by_cases h0 : v k / d ^ s = 0
    · exact Or.inl h0
    · right
      have hu0 : u k ≠ 0 := by rw [← coef k d hd hd2]; exact pow_ne_zero 2 h0
      have : u k * (u k ^ Q - 1) = 0 := by rw [mul_sub, ← pow_succ', hu k]; ring
      have hQ1 : u k ^ Q = 1 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hu0)
      rw [pow_mul, coef k d hd hd2, hQ1]
  have memL : ∀ (k : Fin 3) (d : AlgQ), d ≠ 0 → d ^ 2 = e k → v k / d ^ s ∈ L := by
    intro k d hd hd2
    apply mem_cycField
    rcases mu k d hd hd2 with h | h
    · rw [h]; simp
    · rw [pow_succ, h, one_mul]
  set A0 := v 0 / d0 ^ s
  set Aa := v a / da ^ s
  set Ab := v b / db ^ s
  have hcase : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    revert ha hb hab; fin_cases a <;> fin_cases b <;> decide
  have hsum3 : ∀ (F : Fin 3 → AlgQ), ∑ k, F k = F 0 + F a + F b := by
    intro F
    rw [Fin.sum_univ_three]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp only [add_assoc, add_comm (F 1)]
  rw [hsum3] at hsum
  have E0 : A0 * d0 ^ s + Aa * da ^ s + Ab * db ^ s = ω := by
    rw [← hsum]; simp only [A0, Aa, Ab]; field_simp
  have hωpm : ω = 1 ∨ ω = -1 := by
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hτω : τ ω = ω := by rcases hωpm with rfl | rfl <;> simp
  have fA0 := hfix _ (memL 0 d0 nd0 hd0) τ
  have fAa := hfix _ (memL a da nda hda2) τ
  have fAb := hfix _ (memL b db ndb hdb2) τ
  have E1 : A0 * da ^ s + Aa * db ^ s + Ab * d0 ^ s = ω := by
    have := congrArg τ E0
    simp only [map_add, map_mul, map_zpow₀, hτω] at this
    rw [fA0, fAa, fAb, ← hda, ← hdb, hcyc] at this; exact this
  have E2 : A0 * db ^ s + Aa * d0 ^ s + Ab * da ^ s = ω := by
    have := congrArg τ E1
    simp only [map_add, map_mul, map_zpow₀, hτω] at this
    rw [fA0, fAa, fAb, ← hdb, hcyc, ← hda] at this; exact this
  have cast : ∀ x y : AlgQ, x = y → (x : ℂ) = (y : ℂ) := fun x y h => by rw [h]
  have c0 := cast _ _ E0; have c1 := cast _ _ E1; have c2 := cast _ _ E2
  push_cast at c0 c1 c2
  have hωC : (ω : ℂ) ≠ 0 := by
    rcases hωpm with rfl | rfl <;> simp
  have hM : Nat.gcd 6 (2 * Q) ∣ 2 := by rcases hQ with rfl | rfl | rfl <;> decide
  have muC : ∀ (k : Fin 3) (d : AlgQ), d ≠ 0 → d ^ 2 = e k →
      ((v k / d ^ s : AlgQ) : ℂ) = 0 ∨ ((v k / d ^ s : AlgQ) : ℂ) ^ (2 * Q) = 1 := by
    intro k d hd hd2
    rcases mu k d hd hd2 with h | h
    · left; rw [h]; rfl
    · right; have := cast _ _ h; push_cast at this ⊢; exact this
  -- `|d0^s| ≠ |db^s|`
  have hw : ¬ (((d0 : ℂ)) ^ s = ((db : ℂ)) ^ s ∧ ((da : ℂ)) ^ s = ((db : ℂ)) ^ s) := by
    rintro ⟨h, -⟩
    have h2 : ((d0 : ℂ) ^ s) ^ 2 = ((db : ℂ) ^ s) ^ 2 := by rw [h]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm, zpow_mul, zpow_mul,
      zpow_natCast, zpow_natCast] at h2
    have q0 : ((d0 : ℂ)) ^ 2 = (e 0 : ℂ) := by rw [← hd0]; push_cast; rfl
    have qb : ((db : ℂ)) ^ 2 = (e b : ℂ) := by rw [← hdb2]; push_cast; rfl
    rw [q0, qb] at h2
    have hb0' : (e b : ℂ) ≠ 0 := by exact_mod_cast he0 b
    exact zpow_ne_of_norm hbig hb0' (hsm b hb) hs0 h2
  obtain ⟨k01, k12⟩ := circulant_const_mu (r := (ω : ℂ)) hM hωC hw
    (muC 0 d0 nd0 hd0) (muC a da nda hda2) (muC b db ndb hdb2) c0 c1 c2
  have k01' : A0 = Aa := Subtype.ext k01
  have k12' : Aa = Ab := Subtype.ext k12
  apply hnc
  have u0 := coef 0 d0 nd0 hd0
  have ua := coef a da nda hda2
  have ub := coef b db ndb hdb2
  have hua : u a = u 0 := by rw [← ua, ← u0]; show Aa ^ 2 = A0 ^ 2; rw [k01']
  have hub : u b = u 0 := by rw [← ub, ← u0]; show Ab ^ 2 = A0 ^ 2; rw [k01', k12']
  intro k
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases k
  all_goals first | rfl | exact hua | exact hub

/-! ### E1 at `g = 2` -/

/-- `i ∉ ℚ(μ_26)`: a `52`nd root of unity in `ℚ(μ_26)` is a `26`th root of unity. -/
theorem pow26_of_pow52 {a : AlgQ} (ha : a ∈ cycField 26) (h : a ^ 52 = 1) : a ^ 26 = 1 := by
  have hpm : (a ^ 26 - 1) * (a ^ 26 + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hpm with h1 | h1
  · linear_combination h1
  exfalso
  set b := a ^ 13 with hb
  have hbK : b ∈ cycField 26 := pow_mem ha 13
  have hb2 : b ^ 2 = -1 := by rw [hb, ← pow_mul]; linear_combination h1
  have hle : cycField 52 ≤ cycField 26 := by
    refine IntermediateField.adjoin_le_iff.2 fun z hz => ?_
    have hz52 : z ^ 52 = 1 := hz
    have : (z ^ 26 - 1) * (z ^ 26 + 1) = 0 := by linear_combination hz52
    rcases mul_eq_zero.1 this with h | h
    · exact IntermediateField.subset_adjoin ℚ _ (show z ^ 26 = 1 by linear_combination h)
    · have b26 : b ^ 26 = -1 := by rw [show b ^ 26 = (b ^ 2) ^ 13 by ring, hb2]; norm_num
      have hzb : (z * b) ^ 26 = 1 := by rw [mul_pow, b26]; linear_combination (-1 : AlgQ) * h
      have hm : z * b ∈ cycField 26 := IntermediateField.subset_adjoin ℚ _ hzb
      have : z = -(z * b) * b := by linear_combination z * hb2
      show z ∈ cycField 26
      rw [this]; exact mul_mem (neg_mem hm) hbK
  haveI := cycField_isCyclotomic 26
  haveI := cycField_isCyclotomic 52
  haveI : FiniteDimensional ℚ (cycField 26) := IsCyclotomicExtension.finiteDimensional {26} ℚ _
  have h26 : Module.finrank ℚ (cycField 26) = Nat.totient 26 :=
    IsCyclotomicExtension.finrank (cycField 26) (cyclotomic.irreducible_rat (by norm_num))
  have h52 : Module.finrank ℚ (cycField 52) = Nat.totient 52 :=
    IsCyclotomicExtension.finrank (cycField 52) (cyclotomic.irreducible_rat (by norm_num))
  have := IntermediateField.finrank_dvd_of_le_right hle
  rw [h26, h52] at this
  have t1 : Nat.totient 26 = 12 := by decide
  have t2 : Nat.totient 52 = 24 := by decide
  rw [t1, t2] at this
  omega

set_option synthInstance.maxHeartbeats 200000 in
/-- A cubic irrationality in `ℚ(μ_52)` has a conjugate in `ℚ(μ_26)`. -/
theorem exists_root_cycField_26 {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0)
    (hxL : x ∈ cycField 52) :
    ∃ y : AlgQ, (f.map (Int.castRingHom AlgQ)).eval y = 0 ∧ y ∈ cycField 26 := by
  classical
  set K := cycField 26 with hK
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgQ) two_pos
  have hiint : IsIntegral K i := ⟨X ^ 2 + 1, by monicity!, by simp [hi]⟩
  haveI : FiniteDimensional K K⟮i⟯ := IntermediateField.adjoin.finiteDimensional hiint
  have hiK : i ∈ K⟮i⟯ := IntermediateField.mem_adjoin_simple_self K i
  have hKK : ∀ z ∈ K, z ∈ K⟮i⟯ := fun z hz =>
    IntermediateField.algebraMap_mem K⟮i⟯ (⟨z, hz⟩ : K)
  have hle : cycField 52 ≤ (K⟮i⟯).restrictScalars ℚ := by
    refine IntermediateField.adjoin_le_iff.2 fun z hz => ?_
    have hz52 : z ^ 52 = 1 := hz
    have : (z ^ 26 - 1) * (z ^ 26 + 1) = 0 := by linear_combination hz52
    show z ∈ K⟮i⟯
    rcases mul_eq_zero.1 this with h | h
    · exact hKK z (IntermediateField.subset_adjoin ℚ _ (show z ^ 26 = 1 by linear_combination h))
    · have hzi : (z * i) ^ 26 = 1 := by
        have i26 : i ^ 26 = -1 := by rw [show i ^ 26 = (i ^ 2) ^ 13 by ring, hi]; norm_num
        rw [mul_pow, i26]
        linear_combination (-1 : AlgQ) * h
      have hm : z * i ∈ K⟮i⟯ := hKK _ (IntermediateField.subset_adjoin ℚ _ hzi)
      have : z = -(z * i) * i := by linear_combination z * hi
      rw [this]; exact mul_mem (neg_mem hm) hiK
  have hxKi : x ∈ K⟮i⟯ := hle hxL
  set g : K[X] := f.map (Int.castRingHom K) with hg
  have hgm : g.Monic := hmon.map _
  have hgd : g.natDegree = 3 := by rw [hg, hmon.natDegree_map, hdeg]
  have hbr : ∀ z : AlgQ, aeval z g = (f.map (Int.castRingHom AlgQ)).eval z := by
    intro z
    rw [hg, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
    congr 2
  have hxint : IsIntegral K x := ⟨g, hgm, by rw [← Polynomial.aeval_def, hbr]; exact hx⟩
  have hdx : (minpoly K x).natDegree ≤ 2 := by
    rw [← IntermediateField.adjoin.finrank hxint]
    have h1 : K⟮x⟯ ≤ K⟮i⟯ := IntermediateField.adjoin_simple_le_iff.2 hxKi
    refine (IntermediateField.finrank_le_of_le_right h1).trans ?_
    rw [IntermediateField.adjoin.finrank hiint]
    have hd : minpoly K i ∣ X ^ 2 + 1 := minpoly.dvd K i (by rw [map_add, map_pow, Polynomial.aeval_X, map_one, hi]; ring)
    have := Polynomial.natDegree_le_of_dvd hd (by
      intro h0; have := congrArg (Polynomial.eval 0) h0; simp at this)
    refine this.trans ?_
    rw [show (X ^ 2 + 1 : K[X]) = X ^ 2 + C 1 by simp, Polynomial.natDegree_X_pow_add_C]
  by_contra hno
  push_neg at hno
  have hgirr : Irreducible g := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hgd]; decide) ?_
    intro r hr
    apply hno (r : AlgQ) _ r.2
    rw [← hbr]
    have : aeval (r : AlgQ) g = algebraMap K AlgQ (g.eval r) :=
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := AlgQ) r g
    rw [this, hr.eq_zero, map_zero]
  have hmin : minpoly K x = g :=
    (minpoly.eq_of_irreducible_of_monic hgirr (by rw [hbr]; exact hx) hgm).symm
  rw [hmin, hgd] at hdx
  omega

/-- An algebraic integer in `ℚ[ζ₁₃]` is an integer polynomial in `ζ` (`ℤ[ζ]` is integrally closed). -/
theorem exists_int_poly {ζ : AlgQ} (hζ : IsPrimitiveRoot ζ 13) {q : ℚ[X]}
    (hint : IsIntegral ℤ (aeval ζ q)) : ∃ h : ℤ[X], aeval ζ h = aeval ζ q := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI := cycField_isCyclotomic 13
  have hζmem : ζ ∈ cycField 13 :=
    IntermediateField.subset_adjoin ℚ _ (show ζ ^ 13 = 1 from hζ.pow_eq_one)
  set ζ' : cycField 13 := ⟨ζ, hζmem⟩ with hζ'def
  have hζ' : IsPrimitiveRoot ζ' 13 :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycField 13).val) hζ (cycField 13).val.injective
  set γ' : cycField 13 := aeval ζ' q with hγ'
  have hval : ((cycField 13).val γ') = aeval ζ q :=
    (Polynomial.aeval_algHom_apply (cycField 13).val ζ' q).symm
  have hint' : IsIntegral ℤ γ' := by
    rw [← isIntegral_algHom_iff ((cycField 13).val.restrictScalars ℤ)
      (cycField 13).val.injective]
    simpa [hval] using hint
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime hζ'
  obtain ⟨y, hy⟩ := hcl.isIntegral_iff.1 hint'
  have hy2 : (y : cycField 13) ∈ Algebra.adjoin ℤ ({ζ'} : Set (cycField 13)) := y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy2
  obtain ⟨h, hh⟩ := hy2
  refine ⟨h, ?_⟩
  rw [← hval, ← hy]
  have : ((cycField 13).val (aeval ζ' h)) = aeval ζ h :=
    (Polynomial.aeval_algHom_apply ((cycField 13).val.restrictScalars ℤ) ζ' h).symm
  rw [← this]
  simp only [AlgHom.toRingHom_eq_coe] at hh
  rw [show (aeval ζ' h) = (y : cycField 13) from hh]
  rfl

/-- Reading an integer polynomial identity at `ζ₁₃` modulo `1 − ζ`. -/
theorem thirteen_dvd_of_aeval {ζ : AlgQ} (hζ : IsPrimitiveRoot ζ 13) {P : ℤ[X]} {n : ℤ}
    (h : aeval ζ P = (n : AlgQ)) : (13 : ℤ) ∣ P.eval 1 - n := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h0 : aeval ζ (P - Polynomial.C n) = 0 := by simp [h]
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (by norm_num)
  have hdvd : cyclotomic 13 ℤ ∣ P - Polynomial.C n := by
    rw [cyclotomic_eq_minpoly hζ (by norm_num)]
    exact minpoly.isIntegrallyClosed_dvd hint h0
  obtain ⟨Q, hQ⟩ := hdvd
  have := congrArg (Polynomial.eval 1) hQ
  rw [eval_mul, eval_one_cyclotomic_prime] at this
  simp only [eval_sub, eval_C] at this
  exact ⟨Q.eval 1, by rw [this]; push_cast; ring⟩

/-- `τ^m` on a polynomial in `ζ`. -/
theorem tau_pow_aeval {ζ : AlgQ} {τ : AlgQ ≃ₐ[ℚ] AlgQ} (hτ : τ ζ = ζ ^ 2) {R : Type*} [CommRing R]
    [Algebra R ℚ] [Algebra R AlgQ] [IsScalarTower R ℚ AlgQ] (h : R[X]) (m : ℕ) :
    (τ ^ m) (aeval ζ h) = aeval (ζ ^ (2 ^ m)) h := by
  rw [← tau_pow_zeta hτ m]
  exact (Polynomial.aeval_algHom_apply (((τ ^ m : AlgQ ≃ₐ[ℚ] AlgQ) : AlgQ →ₐ[ℚ] AlgQ).restrictScalars R) ζ h).symm

/-- The three roots are the `τ`-orbit of any one of them. -/
theorem tau_pow_root {τ : AlgQ ≃ₐ[ℚ] AlgQ} {e : Fin 3 → AlgQ} {t : Fin 3}
    (hτe : ∀ k, τ (e k) = e (k + t)) (j : Fin 3) (m : ℕ) :
    (τ ^ m) (e j) = e (j + Fin.ofNat 3 m * t) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, hτe]
      congr 1
      rw [show Fin.ofNat 3 (m + 1) = Fin.ofNat 3 m + 1 from by ext; simp [Fin.val_add]]
      rw [add_mul, one_mul, add_assoc]

theorem sum_orbit {β : Type*} [AddCommMonoid β] (F : Fin 3 → β) (j t : Fin 3) (ht : t = 1 ∨ t = 2) :
    ∑ k, F k = ∑ m : Fin 3, F (j + m * t) := by
  have hb : Function.Bijective (fun m : Fin 3 => j + m * t) := by
    revert j t; decide
  exact (Fintype.sum_bijective _ hb _ _ (fun _ => rfl)).symm

theorem orbit_surj : ∀ j t : Fin 3, (t = 1 ∨ t = 2) → ∀ k, ∃ i, k = j + i * t := by decide

/-- **E1 at `g = 2`, the `(−)` case**: `τ³γ = −γ` makes `13` divide every trace. -/
theorem half_e1_minus {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3) {ζ : AlgQ}
    (hζ : IsPrimitiveRoot ζ 13) {τ : AlgQ ≃ₐ[ℚ] AlgQ} (hτ : τ ζ = ζ ^ 2) {e : Fin 3 → AlgQ}
    (hinj : Function.Injective e) (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    {t : Fin 3} (ht : t = 1 ∨ t = 2) (hτe : ∀ k, τ (e k) = e (k + t)) {j : Fin 3} {q : ℚ[X]}
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hγ : (aeval ζ q) ^ 2 = (ε : AlgQ) * e j)
    (hτγ : (τ ^ 3) (aeval ζ q) = - aeval ζ q) (N : ℕ) (hN : 1 ≤ N) :
    (13 : ℤ) ∣ traceSeq f N := by
  classical
  -- `γ` is an algebraic integer, so an integer polynomial in `ζ`
  have hej : IsIntegral ℤ (e j) := by
    refine ⟨f, hmon, ?_⟩
    have := he j
    rwa [Polynomial.eval_map, RingHom.ext_int (Int.castRingHom AlgQ) (algebraMap ℤ AlgQ)] at this
  have hγint : IsIntegral ℤ (aeval ζ q) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have hεi : IsIntegral ℤ ((ε : AlgQ)) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := AlgQ) (x := ε))
    rw [hγ]
    exact hεi.mul hej
  obtain ⟨h, hh⟩ := exists_int_poly hζ hγint
  -- `13 ∣ h(1)`
  have h13 : (13 : ℤ) ∣ h.eval 1 := by
    have hz : aeval ζ (h.comp (X ^ 8) + h) = ((0 : ℤ) : AlgQ) := by
      have h3 := tau_pow_aeval hτ h 3
      rw [hh, hτγ] at h3
      rw [map_add, Polynomial.aeval_comp, map_pow, aeval_X, hh]
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h3
      rw [← h3, ← hh]; simp
    have := thirteen_dvd_of_aeval hζ hz
    simp only [eval_add, eval_comp, eval_pow, eval_X, one_pow, sub_zero] at this
    have h2 : (13 : ℤ) ∣ 2 * h.eval 1 := by rw [two_mul]; exact this
    exact (Int.Prime.dvd_mul' (by norm_num) h2).resolve_left (by norm_num)
  -- the trace as an integer polynomial at `ζ`
  set P : ℤ[X] := ∑ m : Fin 3, Polynomial.C (ε ^ N) * (h.comp (X ^ (2 ^ (m : ℕ)))) ^ (2 * N) with hP
  have hroot : ∀ m : Fin 3, e (j + m * t) = (ε : AlgQ) * (aeval ζ (h.comp (X ^ (2 ^ (m : ℕ))))) ^ 2 := by
    intro m
    have h1 := tau_pow_root hτe j m
    rw [show Fin.ofNat 3 (m : ℕ) = m by fin_cases m <;> rfl] at h1
    have hc : aeval ζ (h.comp (X ^ (2 ^ (m : ℕ)))) = (τ ^ (m : ℕ)) (aeval ζ q) := by
      rw [Polynomial.aeval_comp, map_pow, aeval_X, ← tau_pow_aeval hτ h, hh]
    have hε2 : (ε : AlgQ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [← h1, hc, ← map_pow, hγ, map_mul, map_intCast, ← mul_assoc, hε2, one_mul]
  have htr : ((traceSeq f N : ℤ) : AlgQ) = aeval ζ P := by
    have hs := traceSeq_eq_root_sum (K := AlgQ) f hmon (fun i => e (Fin.cast hdeg i))
      (fun i => he _) (fun a b hab => Fin.cast_injective hdeg (hinj hab)) N
    rw [hs, show (∑ i : Fin f.natDegree, e (Fin.cast hdeg i) ^ N) = ∑ k : Fin 3, e k ^ N from
      Fintype.sum_equiv (finCongr hdeg) _ _ (fun i => rfl), sum_orbit _ j t ht, hP, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hroot m]
    simp only [map_mul, map_pow, aeval_C, eq_intCast, map_intCast]
    ring
  have hd := thirteen_dvd_of_aeval hζ htr.symm
  have hP1 : P.eval 1 = 3 * (ε ^ N * h.eval 1 ^ (2 * N)) := by
    simp [hP, Fin.sum_univ_three, eval_comp]; ring
  have h13P : (13 : ℤ) ∣ P.eval 1 := by
    rw [hP1]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_pow h13 (by omega)) _) _
  have := dvd_sub h13P hd
  simpa using this

/-- **E1 at `g = 2`**: no half spectral solution when the roots lie in `ℚ(μ_26)`. -/
theorem half_e1 {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s)
    (hP : HalfPrimeTraces f s)
    {e u v : Fin 3 → AlgQ} {ω : AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    (hbig : 1 < ‖(e 0 : ℂ)‖) (hsm : ∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1)
    (hu : ∀ k, u k ^ (26 + 1) = u k) (hω : ω ^ 2 = 1) (hv : ∀ k, v k ^ 2 = u k * e k ^ s)
    (hsum : ∑ k, v k = ω) (hnc : ¬ ∀ k, u k = u 0)
    {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) (hxL : x ∈ cycField 26) :
    False := by
  classical
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
  have hc0 := coeff_zero_ne_zero hD.monic hD.irr hD.deg
  have he0 : ∀ k, e k ≠ 0 := by
    intro k h0; have := he k; rw [h0, eval_cubic hD.monic hD.deg] at this; simp at this
    exact hc0 this
  obtain ⟨ζ, hζ⟩ := exists_zeta13
  obtain ⟨τ, hτ⟩ := exists_tau hζ
  obtain ⟨q, hq⟩ := exists_poly_of_mem_cycField hζ hxL
  have hroots : ∀ k, ∃ q' : ℚ[X], aeval ζ q' = e k := fun k =>
    exists_poly_of_conj hD.monic hD.irr hd1 hζ hx (he k) hq
  have hτroot : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (τ (e k)) = 0 := by
    intro k
    have := eval_map_int_hom (τ : AlgQ →+* AlgQ) f (e k)
    rw [he k, map_zero] at this
    exact this.symm
  have himg : ∀ k, ∃ j, e j = τ (e k) := fun k =>
    root_enum_surj hD.monic hD.deg hinj he (hτroot k)
  choose p hp using himg
  have hpinj : Function.Injective p := fun a b h => by
    apply hinj; apply τ.injective; rw [← hp a, ← hp b, h]
  have hpfix : ∀ k, p k ≠ k := by
    intro k hk
    obtain ⟨q', hq'⟩ := hroots k
    have hfix : τ (aeval ζ q') = aeval ζ q' := by rw [hq', ← hp k, hk]
    obtain ⟨r, hr⟩ := rat_of_tau_fixed hζ hτ hfix
    refine not_mem_cycField_two hD.monic hD.irr hD.deg (he k) ?_
    rw [← hq', hr]
    exact (cycField 2).algebraMap_mem r
  have hωpm : ω = 1 ∨ ω = -1 := by
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hω0 : ω ≠ 0 := by rcases hωpm with rfl | rfl <;> norm_num
  have hτω : τ ω = ω := by rcases hωpm with rfl | rfl <;> simp
  obtain ⟨t, ht, hpt⟩ : ∃ t : Fin 3, (t = 1 ∨ t = 2) ∧ ∀ k, p k = k + t := by
    rcases three_cycle_of p hpinj hpfix with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨2, Or.inr rfl, h⟩
  have hτe : ∀ k, τ (e k) = e (k + t) := fun k => by rw [← hp k, hpt k]
  -- everything lives in `K = ℚ(μ_26)`
  set K := cycField 26 with hK
  have hζK : ζ ∈ K := IntermediateField.subset_adjoin ℚ _
    (show ζ ^ 26 = 1 by rw [show 26 = 13 * 2 by rfl, pow_mul, hζ.pow_eq_one, one_pow])
  have aevK : ∀ (r : ℚ[X]) (y : AlgQ), y ∈ K → aeval y r ∈ K := by
    intro r y hy
    have : aeval y r = algebraMap K AlgQ (aeval (⟨y, hy⟩ : K) r) :=
      (Polynomial.aeval_algebraMap_apply AlgQ (⟨y, hy⟩ : K) r)
    rw [this]; exact (aeval (⟨y, hy⟩ : K) r).2
  have heK : ∀ k, e k ∈ K := fun k => by
    obtain ⟨q', hq'⟩ := hroots k; rw [← hq']; exact aevK q' ζ hζK
  have huK : ∀ k, u k ∈ K := fun k => mem_cycField (hu k)
  have hnorm : ∀ k, ‖(e k : ℂ)‖ ≠ 1 := by
    intro k
    by_cases hk : k = 0
    · subst hk; exact hbig.ne'
    · exact (hsm k hk).ne
  have hu1 : ∀ k, u k = 0 ∨ ‖(u k : ℂ)‖ = 1 := fun k => unimod_of_pow_succ (by norm_num) (hu k)
  have hvK : ∀ k, v k ∈ K := flip_mem K hs0 hnorm he0 hu1 hω hv hsum
    (fun k => by rw [hv k]; exact mul_mem (huK k) (zpow_mem (heK k) s))
  -- a nonzero coefficient
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hω0
    rw [← hsum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := hv k; rw [h k, zero_mul] at this; exact pow_eq_zero_iff (by norm_num) |>.1 this
  have hu26 : ∀ k, u k ≠ 0 → u k ^ 26 = 1 := by
    intro k hk
    have : u k * (u k ^ 26 - 1) = 0 := by rw [mul_sub, ← pow_succ']; rw [hu k]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hk)
  obtain ⟨m, hm⟩ := hs
  set ε := u j ^ 13 with hεdef
  have hε2 : ε ^ 2 = 1 := by rw [hεdef, ← pow_mul]; exact hu26 j hj
  have hε : ε = 1 ∨ ε = -1 := by
    have : (ε - 1) * (ε + 1) = 0 := by linear_combination hε2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hεs : ε ^ s = ε := by
    rcases hε with h | h <;> rw [h]
    · simp
    · exact Odd.neg_one_zpow ⟨m, hm⟩
  set c := u j ^ 7 with hcdef
  have hc2 : c ^ 2 = ε * u j := by rw [hcdef, hεdef, ← pow_mul, ← pow_succ]
  have hc0' : c ≠ 0 := pow_ne_zero _ hj
  set γ := v j / (c * e j ^ m) with hγdef
  have hγ2 : γ ^ 2 = ε * e j := by
    have hX : e j ^ s = (e j ^ m) ^ 2 * e j := by
      rw [hm, zpow_add₀ (he0 j), zpow_one, show (2 : ℤ) * m = m * 2 by ring, zpow_mul]; norm_cast
    have hne : c * e j ^ m ≠ 0 := mul_ne_zero hc0' (zpow_ne_zero _ (he0 j))
    have h1 : γ * (c * e j ^ m) = v j := div_mul_cancel₀ _ hne
    have h2 := congrArg (· ^ 2) h1
    rw [hv j, hX] at h2
    have h3 : (u j * (e j ^ m) ^ 2) * (γ ^ 2 * ε - e j) = 0 := by
      linear_combination h2 - γ ^ 2 * (e j ^ m) ^ 2 * hc2
    have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hj (pow_ne_zero _ (zpow_ne_zero _ (he0 j))))
    linear_combination ε * h4 + γ ^ 2 * hε2 - 2 * v j ^ 2 * (u j)⁻¹ ^ 14 * (e j ^ m)⁻¹ ^ 2 * hε2
  have hγK : γ ∈ K := div_mem (hvK j) (mul_mem (pow_mem (huK j) 7) (zpow_mem (heK j) m))
  obtain ⟨qγ, hqγ⟩ := exists_poly_of_mem_cycField hζ hγK
  have hτ3e : (τ ^ 3) (e j) = e j := by
    rw [tau_pow_root hτe j 3]; congr 1
    rw [show Fin.ofNat 3 3 = 0 from rfl, zero_mul, add_zero]
  have hτε : ∀ n : ℕ, (τ ^ n) ε = ε := by
    intro n; rcases hε with h | h <;> rw [h] <;> simp
  have hτ3 : (τ ^ 3) γ = γ ∨ (τ ^ 3) γ = -γ := by
    have h2 : ((τ ^ 3) γ) ^ 2 = γ ^ 2 := by rw [← map_pow, hγ2, map_mul, hτε, hτ3e]
    have : ((τ ^ 3) γ - γ) * ((τ ^ 3) γ + γ) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hτ3 with hp3 | hm3
  swap
  · -- `(−)`: `13` divides every trace
    obtain ⟨εZ, hεZ, hεc⟩ : ∃ εZ : ℤ, (εZ = 1 ∨ εZ = -1) ∧ (εZ : AlgQ) = ε := by
      rcases hε with h | h
      · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
      · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
    have hdvd := half_e1_minus hD.monic hD.deg hζ hτ hinj he ht hτe hεZ
      (by rw [hqγ, hεc]; exact hγ2) (by rw [hqγ]; exact hm3)
    exact not_prime_of_dvd hD (by norm_num : Nat.Prime 13) hdvd (halfExp_tendsto s) hP
  · -- `(+)`: the `τ`-orbit of `γ` is a consistent family of square roots
    have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set δ : Fin 3 → AlgQ := fun i => (τ ^ (i : ℕ)) γ with hδ
    have hstep : ∀ (n : ℕ) (y : AlgQ), τ ((τ ^ n) y) = (τ ^ (n + 1)) y := fun n y => by
      rw [pow_succ', AlgEquiv.mul_apply]
    have hτδ : ∀ i, τ (δ i) = δ (i + 1) := by
      intro i; fin_cases i
      · show τ ((τ ^ 0) γ) = (τ ^ 1) γ; rw [hstep]
      · show τ ((τ ^ 1) γ) = (τ ^ 2) γ; rw [hstep]
      · show τ ((τ ^ 2) γ) = (τ ^ 0) γ; rw [hstep, hp3, pow_zero]; rfl
    have hofn : ∀ i : Fin 3, Fin.ofNat 3 (i : ℕ) = i := by decide
    have hδ2 : ∀ i, δ i ^ 2 = ε * e (j + i * t) := by
      intro i
      show ((τ ^ (i : ℕ)) γ) ^ 2 = _
      rw [← map_pow, hγ2, map_mul, hτε, tau_pow_root hτe j, hofn]
    have hδ0 : ∀ i, δ i ≠ 0 := by
      intro i h0; have := hδ2 i; rw [h0] at this
      exact mul_ne_zero hε0 (he0 _) (by rw [← this]; ring)
    have hδK : ∀ i, δ i ∈ K := by
      intro i
      show (τ ^ (i : ℕ)) γ ∈ K
      rw [← hqγ, tau_pow_aeval hτ]
      exact aevK qγ _ (pow_mem hζK _)
    set W : Fin 3 → AlgQ := fun i => δ i ^ s with hW
    have hW0 : ∀ i, W i ≠ 0 := fun i => zpow_ne_zero _ (hδ0 i)
    have hτW : ∀ i, τ (W i) = W (i + 1) := fun i => by
      show τ (δ i ^ s) = δ (i + 1) ^ s; rw [map_zpow₀, hτδ]
    have hW2 : ∀ i, W i ^ 2 = ε * e (j + i * t) ^ s := by
      intro i
      show (δ i ^ s) ^ 2 = _
      rw [show (δ i ^ s) ^ 2 = (δ i ^ 2) ^ s by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm], hδ2, mul_zpow, hεs]
    set A : Fin 3 → AlgQ := fun i => v (j + i * t) / W i with hA
    have hAW : ∀ i, A i * W i = v (j + i * t) := fun i => div_mul_cancel₀ _ (hW0 i)
    have hA2 : ∀ i, A i ^ 2 = ε * u (j + i * t) := by
      intro i
      have h1 := congrArg (· ^ 2) (hAW i)
      rw [mul_pow, hW2, hv] at h1
      have hes : e (j + i * t) ^ s ≠ 0 := zpow_ne_zero _ (he0 _)
      have h3 : e (j + i * t) ^ s * (A i ^ 2 * ε - u (j + i * t)) = 0 := by
        linear_combination h1
      have h4 := (mul_eq_zero.1 h3).resolve_left hes
      linear_combination ε * h4 - A i ^ 2 * hε2
    have hAK : ∀ i, A i ∈ K := fun i =>
      div_mem (hvK _) (zpow_mem (hδK i) s)
    have hA27 : ∀ i, A i ^ 27 = A i := by
      intro i
      by_cases h0 : A i = 0
      · rw [h0]; ring
      have hu0 : u (j + i * t) ≠ 0 := by
        intro h; apply h0; have := hA2 i; rw [h, mul_zero] at this
        exact pow_eq_zero_iff (by norm_num) |>.1 this
      have h52 : A i ^ 52 = 1 := by
        rw [show A i ^ 52 = (A i ^ 2) ^ 26 by ring, hA2, mul_pow, hu26 _ hu0,
          show ε ^ 26 = (ε ^ 2) ^ 13 by ring, hε2]; ring
      rw [pow_succ, pow26_of_pow52 (hAK i) h52, one_mul]
    have hsumA : ∑ i, A i * W i = ω := by
      simp_rw [hAW]; rw [← sum_orbit v j t ht]; exact hsum
    have hsurj : ∀ k : Fin 3, ∃ i : Fin 3, k = j + i * t := orbit_surj j t ht
    rcases e1_core hζ hτ (t := 1) (Or.inl rfl) hτW hA27 hω0 hτω hsumA with hc | hc
    · apply hnc
      have hu' : ∀ i, u (j + i * t) = u j := by
        intro i
        have e1 : u (j + i * t) = ε * A i ^ 2 := by
          rw [hA2]; linear_combination (-(u (j + i * t))) * hε2
        have e2 : u j = ε * A 0 ^ 2 := by
          have := hA2 0; simp only [zero_mul, add_zero] at this
          rw [this]; linear_combination (-(u j)) * hε2
        rw [e1, e2, hc i]
      have hall : ∀ k, u k = u j := fun k => by
        obtain ⟨i, rfl⟩ := hsurj k; exact hu' i
      intro k; rw [hall k, hall 0]
    · have hes : ∀ k, e k ^ s = e j ^ s := by
        intro k
        obtain ⟨i, rfl⟩ := hsurj k
        have h1 := hW2 i
        have h2 := hW2 0
        rw [hc i] at h1
        simp only [zero_mul, add_zero] at h2
        have : ε * (e (j + i * t) ^ s - e j ^ s) = 0 := by linear_combination h2 - h1
        linear_combination (mul_eq_zero.1 this).resolve_left hε0
      have he1 : e 1 ≠ 0 := he0 1
      apply zpow_ne_of_norm hbig (by exact_mod_cast he1) (hsm 1 (by decide)) hs0
      have := congrArg (algebraicClosure ℚ ℂ).val ((hes 0).trans (hes 1).symm)
      rw [map_zpow₀, map_zpow₀] at this
      exact this

/-! ### Assembly -/

/-- **Node D** in polynomial form. -/
theorem not_halfPrimeTraces {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s) :
    ¬ HalfPrimeTraces f s := by
  intro hP
  by_cases hcube : ∃ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3
  · obtain ⟨z, hz⟩ := hcube
    exact not_prime_of_dvd hD Nat.prime_three (fun N _ => three_dvd_of_cube hD z hz N)
      (halfExp_tendsto s) hP
  push_neg at hcube
  obtain ⟨Q, e, u, v, ω, hQ, hinj, he, he0, hsm, hu, hω, hv, hsum, hnc⟩ :=
    exists_half_spectral hD hs hP hcube
  have hbig : 1 < ‖(e 0 : ℂ)‖ := by
    rw [he0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hD.gt_one])]
    exact hD.gt_one
  have hQ' : Q = 2 ∨ Q = 8 ∨ Q = 26 := by rcases hQ with h | h | ⟨h, _⟩ <;> omega
  have hgen : (∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ cycField (2 * Q)) →
      False := fun hL =>
    half_generic hD hs hQ' hinj he hbig hsm hu hω hv hsum hnc hL
  rcases hQ with rfl | rfl | ⟨rfl, _⟩
  · exact hgen fun x hx hxL => by
      have h := three_dvd_totient hD.monic hD.irr hD.deg hx hxL
      have ht : Nat.totient (2 * 2) = 2 := by decide
      omega
  · exact hgen fun x hx hxL => by
      have h := three_dvd_totient hD.monic hD.irr hD.deg hx hxL
      have ht : Nat.totient (2 * 8) = 8 := by decide
      omega
  · by_cases hE : ∃ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 ∧ x ∈ cycField 52
    · obtain ⟨x, hx, hxL⟩ := hE
      obtain ⟨y, hy, hyL⟩ := exists_root_cycField_26 hD.monic hD.irr hD.deg hx hxL
      exact half_e1 hD hs hP hinj he hbig hsm hu hω hv hsum hnc hy hyL
    · exact hgen fun x hx hxL => hE ⟨x, hx, hxL⟩

end LeanFormalizations.Mills.HalfShiftRigidity
