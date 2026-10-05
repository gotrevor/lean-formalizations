/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsLarge
import LeanFormalizations.NumberTheory.Mills.UnipotentTrace

/-!
# Phase 61, node C: no cubic Pisot number has `Tr(β^(3^n + s))` prime for all large `n` (`s ≠ 0`)

Decomposition of `ShiftedMillsAll.shiftTraceRigidity_holds` (`PROOF-THEOREM-E.md` Steps 3–6).  The
route is Theorem D's (phases 55–57) **Nullstellensatz transfer**, not a `3`-adic limit: every
`3`-adic statement is an integer polynomial congruence at every level `3^k`, so it has a solution in
the algebraic numbers `AlgQ`.  The new content is what the solution is made to carry.

## The pieces
* `not_primeTraces_of_cube` (Step 5, the cube class): if `f ≡ (X − z)³ (mod 3)` (`z = 0` included),
  every trace is divisible by `3`, while the traces are primes tending to `∞`.
* `exists_spectral` (Steps 3 + the transfer): outside the cube class, a solution in `AlgQ` of
  `Σ_k u_k α_k^s = ω`, `ω² = 1`, `u_k^(Q+1) = u_k`, with `Q = 3^f − 1 ∈ {2, 8, 26}` read off the
  factorization type of `f mod 3` (the Teichmüller orders), and `(u_k)` **not** the constant `±1`
  (that is the integer equation `y · (T − z)_(ab) = 1`, true at every level because `C − z` is not
  nilpotent mod 3 outside the cube class).
* `rigidity_generic` (Step 4): if no root of `f` lies in a field `L` containing every `u_k`, then
  `u` is constant.  One automorphism of `AlgQ` over `L` acting on the roots as a 3-cycle gives the
  circulant system; its Fourier modes force `u` constant or an equilateral triangle of points of
  modulus `0` or `1` centred at the rational `ω / tr(β^s)`, and the latter is impossible
  (centroid of three unimodular points with equal distances is `0`; with one zero vertex the
  centre has square `1/3`).  No `√−3` argument, no restriction on `Q`.
* `eq_one_or_neg_one_of_const`: a constant `u = z` has `z · tr(β^s) = ω`, so `z ∈ ℚ` is a root of
  unity: `z = ±1`, contradicting the non-constancy.
* `not_mem_cycField_two`, `not_mem_cycField_eight`: a cubic irrationality is not in `ℚ(μ_2) = ℚ`
  or in `ℚ(μ_8)` (degree `4`).  So the exceptional case is `Q = 26` (`f mod 3` irreducible) with a
  root in `ℚ(μ_26)`: that is E1 (Step 6).
* `e1_empty` (Step 6): E1 is empty.  Needs the Frobenius coherence `u_(σk) = u_k³` (an extra
  integer equation `P(h(C)) = P(C)³`, `h(α) = σ₃(α)`) and the rank-3 certificate
  `scripts/theorem-e-e1-certificate.py`.
-/

namespace LeanFormalizations.Mills.ShiftRigidity

open Filter Polynomial LeanFormalizations.Mills.TheoremDGeneral
  LeanFormalizations.Mills.TheoremDMixed

/-- A monic irreducible integer cubic with a real root `α > 1` whose other roots have modulus `< 1`. -/
structure PisotData (f : ℤ[X]) (α : ℝ) : Prop where
  monic : f.Monic
  irr : Irreducible f
  deg : f.natDegree = 3
  root : aeval α f = 0
  gt_one : 1 < α
  small : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1

/-- The traces `tr C^(3^n + s)` are primes for all large `n`. -/
def PrimeTraces (f : ℤ[X]) (s : ℤ) : Prop :=
  ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ traceSeq f ((3 : ℤ) ^ n + s).toNat = p

/-- `ℚ(μ_Q)` inside the algebraic numbers. -/
noncomputable def cycField (Q : ℕ) : IntermediateField ℚ AlgQ :=
  IntermediateField.adjoin ℚ {z : AlgQ | z ^ Q = 1}

theorem mem_cycField {Q : ℕ} {u : AlgQ} (hu : u ^ (Q + 1) = u) : u ∈ cycField Q := by
  by_cases h0 : u = 0
  · rw [h0]; exact (cycField Q).zero_mem
  · refine IntermediateField.subset_adjoin ℚ _ ?_
    show u ^ Q = 1
    have : u * (u ^ Q - 1) = 0 := by rw [mul_sub, ← pow_succ', hu]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.1 h

/-! ### The pieces (statements; see the module docstring) -/

/-- **Step 5, the cube class.** -/
theorem not_primeTraces_of_cube {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) (s : ℤ) (z : ZMod 3)
    (hz : f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3) : ¬ PrimeTraces f s := by
  sorry

/-- **Steps 3 + transfer**: the spectral solution in `AlgQ`. -/
theorem exists_spectral {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : s ≠ 0)
    (hP : PrimeTraces f s)
    (hnc : ∀ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) ≠ (X - C z) ^ 3) :
    ∃ (Q : ℕ) (e u : Fin 3 → AlgQ) (ω : AlgQ),
      (Q = 2 ∨ Q = 8 ∨ (Q = 26 ∧ Irreducible (f.map (Int.castRingHom (ZMod 3))))) ∧
      Function.Injective e ∧ (∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0) ∧
      ((e 0 : ℂ) = α) ∧ (∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1) ∧
      (∀ k, u k ^ (Q + 1) = u k) ∧ ω ^ 2 = 1 ∧ (∑ k, u k * e k ^ s = ω) ∧
      ¬ (∀ k, u k = 1) ∧ ¬ (∀ k, u k = -1) := by
  sorry

/-- **Step 4, Galois rigidity**: with no root of `f` in a field containing the `u_k`, `u` is
constant. -/
theorem rigidity_generic {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 3)
    {e : Fin 3 → AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    (hbig : 1 < ‖(e 0 : ℂ)‖) (hsmall : ∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1)
    {s : ℤ} (hs : s ≠ 0) (L : IntermediateField ℚ AlgQ) {u : Fin 3 → AlgQ} (hu : ∀ k, u k ∈ L)
    (hL : ∀ k, e k ∉ L) {ω : AlgQ} (hω : ω ^ 2 = 1) (hsum : ∑ k, u k * e k ^ s = ω) :
    ∀ k, u k = u 0 := by
  sorry

/-- A constant spectral vector is `±1`. -/
theorem eq_one_or_neg_one_of_const {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3)
    {e : Fin 3 → AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0) {s : ℤ} {Q : ℕ} (hQ : 1 ≤ Q)
    {z ω : AlgQ} (hz : z ^ (Q + 1) = z) (hω : ω ^ 2 = 1) (hsum : ∑ k, z * e k ^ s = ω) :
    z = 1 ∨ z = -1 := by
  sorry

/-- A root of an irreducible integer cubic is not rational. -/
theorem not_mem_cycField_two {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    x ∉ cycField 2 := by
  sorry

/-- A root of an irreducible integer cubic is not in `ℚ(μ_8)` (degree 4). -/
theorem not_mem_cycField_eight {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    x ∉ cycField 8 := by
  sorry

/-- **Step 6 (E1)**: no prime-trace cubic Pisot number with `f mod 3` irreducible has a root in
`ℚ(μ_26)`. -/
theorem e1_empty {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : s ≠ 0)
    (hP : PrimeTraces f s) (h3 : Irreducible (f.map (Int.castRingHom (ZMod 3))))
    {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) (hxL : x ∈ cycField 26) : False := by
  sorry

/-! ### Assembly -/

/-- **Node C** in polynomial form. -/
theorem not_primeTraces {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : s ≠ 0) :
    ¬ PrimeTraces f s := by
  intro hP
  by_cases hcube : ∃ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3
  · obtain ⟨z, hz⟩ := hcube
    exact not_primeTraces_of_cube hD s z hz hP
  push_neg at hcube
  obtain ⟨Q, e, u, ω, hQ, hinj, he, he0, hsm, hu, hω, hsum, hn1, hn2⟩ :=
    exists_spectral hD hs hP hcube
  have hbig : 1 < ‖(e 0 : ℂ)‖ := by
    rw [he0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hD.gt_one])]
    exact hD.gt_one
  have hQ1 : 1 ≤ Q := by rcases hQ with h | h | ⟨h, _⟩ <;> omega
  -- the generic case: `u` constant, hence `±1`
  have hgen : (∀ k, e k ∉ cycField Q) → False := by
    intro hL
    have hc := rigidity_generic hD.monic hD.irr hD.deg hinj he hbig hsm hs (cycField Q)
      (fun k => mem_cycField (hu k)) hL hω hsum
    have hsum' : ∑ k, u 0 * e k ^ s = ω := by
      rw [← hsum]; exact Finset.sum_congr rfl fun k _ => by rw [hc k]
    rcases eq_one_or_neg_one_of_const hD.monic hD.deg hinj he hQ1 (hu 0) hω hsum' with h | h
    · exact hn1 fun k => (hc k).trans h
    · exact hn2 fun k => (hc k).trans h
  rcases hQ with rfl | rfl | ⟨rfl, h3⟩
  · exact hgen fun k => not_mem_cycField_two hD.monic hD.irr hD.deg (he k)
  · exact hgen fun k => not_mem_cycField_eight hD.monic hD.irr hD.deg (he k)
  · by_cases hE : ∃ k, e k ∈ cycField 26
    · obtain ⟨k, hk⟩ := hE
      exact e1_empty hD hs hP h3 (he k) hk
    · push_neg at hE
      exact hgen hE

end LeanFormalizations.Mills.ShiftRigidity
