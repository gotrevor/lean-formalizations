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
  sorry

/-- The cube class: every trace is divisible by `3`. -/
theorem three_dvd_of_cube {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) (z : ZMod 3)
    (hz : f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3) (N : ℕ) : (3 : ℤ) ∣ traceSeq f N := by
  sorry

theorem halfExp_tendsto (s : ℤ) : Tendsto (halfExp s) atTop atTop := by
  sorry

/-! ### Step 3 and the transfer -/

/-- **Step 3 (window) for the half exponent.** -/
theorem window_half {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s)
    (hP : HalfPrimeTraces f s) (k : ℕ) :
    ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f (halfExp s n) - w := by
  sorry

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

/-- **The flip lemma.**  Every `v_k` lies in any field containing the `v_k²`. -/
theorem flip_mem (M : IntermediateField ℚ AlgQ) {e u v : Fin 3 → AlgQ} {ω : AlgQ} {s : ℤ}
    (hs : s ≠ 0) (hnorm : ∀ k, ‖(e k : ℂ)‖ ≠ 1) (he0 : ∀ k, e k ≠ 0)
    (hu1 : ∀ k, u k = 0 ∨ ‖(u k : ℂ)‖ = 1) (hω : ω ^ 2 = 1)
    (hv : ∀ k, v k ^ 2 = u k * e k ^ s) (hsum : ∑ k, v k = ω) (hM : ∀ k, v k ^ 2 ∈ M) :
    ∀ k, v k ∈ M := by
  sorry

/-- **The circulant with roots of unity** of order prime to `3`. -/
theorem circulant_const_mu {u0 u1 u2 w0 w1 w2 r : ℂ} {M : ℕ} (hM : Nat.gcd 6 M ∣ 2) (hr : r ≠ 0)
    (hw : ¬ (w0 = w2 ∧ w1 = w2))
    (hu0 : u0 = 0 ∨ u0 ^ M = 1) (hu1 : u1 = 0 ∨ u1 ^ M = 1) (hu2 : u2 = 0 ∨ u2 ^ M = 1)
    (E0 : u0 * w0 + u1 * w1 + u2 * w2 = r) (E1 : u0 * w1 + u1 * w2 + u2 * w0 = r)
    (E2 : u0 * w2 + u1 * w0 + u2 * w1 = r) : u0 = u1 ∧ u1 = u2 := by
  sorry

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
  sorry

/-! ### E1 at `g = 2` -/

/-- A cubic irrationality in `ℚ(μ_52)` has a conjugate in `ℚ(μ_26)`. -/
theorem exists_root_cycField_26 {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0)
    (hxL : x ∈ cycField 52) :
    ∃ y : AlgQ, (f.map (Int.castRingHom AlgQ)).eval y = 0 ∧ y ∈ cycField 26 := by
  sorry

/-- **E1 at `g = 2`**: no half spectral solution when the roots lie in `ℚ(μ_26)`. -/
theorem half_e1 {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hs : Odd s)
    (hP : HalfPrimeTraces f s)
    {e u v : Fin 3 → AlgQ} {ω : AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    (hbig : 1 < ‖(e 0 : ℂ)‖) (hsm : ∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1)
    (hu : ∀ k, u k ^ (26 + 1) = u k) (hω : ω ^ 2 = 1) (hv : ∀ k, v k ^ 2 = u k * e k ^ s)
    (hsum : ∑ k, v k = ω)
    {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) (hxL : x ∈ cycField 26) :
    False := by
  sorry

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
      exact half_e1 hD hs hP hinj he hbig hsm hu hω hv hsum hy hyL
    · exact hgen fun x hx hxL => hE ⟨x, hx, hxL⟩

end LeanFormalizations.Mills.HalfShiftRigidity
