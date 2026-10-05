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

open Filter Polynomial IntermediateField LeanFormalizations.Mills.TheoremDGeneral
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

theorem unimod_of_pow_succ {Q : ℕ} (hQ : 1 ≤ Q) {u : AlgQ} (hu : u ^ (Q + 1) = u) :
    u = 0 ∨ ‖(u : ℂ)‖ = 1 := by
  by_cases h0 : u = 0
  · exact Or.inl h0
  · right
    have : u * (u ^ Q - 1) = 0 := by rw [mul_sub, ← pow_succ', hu]; ring
    have hQ1 : u ^ Q = 1 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)
    have hc : ((u : ℂ)) ^ Q = 1 := by
      have := congrArg (fun z : AlgQ => (z : ℂ)) hQ1; simpa using this
    exact norm_eq_one_of_pow_eq_one hQ hc

theorem mem_cycField {Q : ℕ} {u : AlgQ} (hu : u ^ (Q + 1) = u) : u ∈ cycField Q := by
  by_cases h0 : u = 0
  · rw [h0]; exact (cycField Q).zero_mem
  · refine IntermediateField.subset_adjoin ℚ _ ?_
    show u ^ Q = 1
    have : u * (u ^ Q - 1) = 0 := by rw [mul_sub, ← pow_succ', hu]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.1 h

/-! ### Step 4: the circulant and the 3-cycle -/

/-- Three points `c + a_k` (`c` rational, `Σ a = 0`, `e₂(a) = 0`), each `0` or unimodular,
force `a = 0`. -/
theorem norm_eq_of_e2 {a0 a1 a2 : ℂ} (h1 : a0 + a1 + a2 = 0)
    (h2 : a0 * a1 + a1 * a2 + a2 * a0 = 0) : ‖a0‖ = ‖a1‖ ∧ ‖a1‖ = ‖a2‖ := by
  have s0 : a0 ^ 2 = a1 * a2 := by
    have : a0 = -a1 - a2 := by linear_combination h1
    subst this; linear_combination -h2
  have s1 : a1 ^ 2 = a0 * a2 := by
    have : a1 = -a0 - a2 := by linear_combination h1
    subst this; linear_combination -h2
  have s2 : a2 ^ 2 = a0 * a1 := by
    have : a2 = -a0 - a1 := by linear_combination h1
    subst this; linear_combination -h2
  have n0 : ‖a0‖ ^ 2 = ‖a1‖ * ‖a2‖ := by rw [← norm_pow, s0, norm_mul]
  have n1 : ‖a1‖ ^ 2 = ‖a0‖ * ‖a2‖ := by rw [← norm_pow, s1, norm_mul]
  have n2 : ‖a2‖ ^ 2 = ‖a0‖ * ‖a1‖ := by rw [← norm_pow, s2, norm_mul]
  have p0 := norm_nonneg a0; have p1 := norm_nonneg a1; have p2 := norm_nonneg a2
  have c01 : ‖a0‖ ^ 3 = ‖a1‖ ^ 3 := by nlinarith
  have c12 : ‖a1‖ ^ 3 = ‖a2‖ ^ 3 := by nlinarith
  exact ⟨(pow_left_inj₀ p0 p1 (by norm_num)).1 c01, (pow_left_inj₀ p1 p2 (by norm_num)).1 c12⟩

theorem normSq_add_real (c : ℝ) (a : ℂ) : ‖(c : ℂ) + a‖ ^ 2 = c ^ 2 + 2 * c * a.re + ‖a‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp; ring

theorem not_three_sq_eq_one (c : ℚ) : (3 : ℝ) * (c : ℝ) ^ 2 ≠ 1 := by
  intro h
  have hq : (3 : ℚ) * c ^ 2 = 1 := by exact_mod_cast h
  have hirr : Irrational (Real.sqrt 3) := by
    simpa using (Nat.Prime.irrational_sqrt (p := 3) Nat.prime_three)
  apply hirr
  refine ⟨|3 * c|, ?_⟩
  have h9 : ((|3 * c| : ℚ) : ℝ) ^ 2 = 3 := by
    push_cast; rw [sq_abs]; nlinarith
  rw [← Real.sqrt_sq (show (0:ℝ) ≤ ((|3 * c| : ℚ) : ℝ) by positivity), h9]

/-- one-zero case: `a0 = -c` -/
theorem equilateral_one_zero {a0 a1 a2 : ℂ} {c : ℚ} (hc : c ≠ 0) (h1 : a0 + a1 + a2 = 0)
    (h2 : a0 * a1 + a1 * a2 + a2 * a0 = 0) (h0 : (c : ℂ) + a0 = 0)
    (hu1 : (c : ℂ) + a1 = 0 ∨ ‖(c : ℂ) + a1‖ = 1) (hu2 : (c : ℂ) + a2 = 0 ∨ ‖(c : ℂ) + a2‖ = 1) :
    False := by
  obtain ⟨e01, e12⟩ := norm_eq_of_e2 h1 h2
  have ha0 : a0 = -(c : ℂ) := by linear_combination h0
  have hn0 : ‖a0‖ = |(c : ℝ)| := by rw [ha0, norm_neg]; simp
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hre : a1.re + a2.re = c := by
    have := congrArg Complex.re h1; rw [ha0] at this; simp at this; linarith
  have key : ∀ a : ℂ, ‖a‖ = |(c : ℝ)| → (c : ℂ) + a = 0 → a = -(c : ℂ) := by
    intro a _ h; linear_combination h
  rcases hu1 with z1 | n1
  · -- a1 = -c, then a2 = 2c, wrong modulus
    have ha1 : a1 = -(c : ℂ) := by linear_combination z1
    have ha2 : a2 = 2 * (c : ℂ) := by linear_combination h1 - ha0 - ha1
    have : ‖a2‖ = 2 * |(c : ℝ)| := by rw [ha2, norm_mul]; simp
    have hpos : 0 < |(c : ℝ)| := abs_pos.2 hcR
    rw [← e12, ← e01, hn0] at this; linarith
  rcases hu2 with z2 | n2
  · have ha2 : a2 = -(c : ℂ) := by linear_combination z2
    have ha1 : a1 = 2 * (c : ℂ) := by linear_combination h1 - ha0 - ha2
    have : ‖a1‖ = 2 * |(c : ℝ)| := by rw [ha1, norm_mul]; simp
    have hpos : 0 < |(c : ℝ)| := abs_pos.2 hcR
    rw [← e01, hn0] at this; linarith
  have q1 := normSq_add_real c a1
  have q2 := normSq_add_real c a2
  push_cast at q1 q2
  rw [n1, ← e01, hn0, sq_abs] at q1
  rw [n2, ← e12, ← e01, hn0, sq_abs] at q2
  have : (3 : ℝ) * (c : ℝ) ^ 2 = 1 := by
    have : (2 : ℝ) = 4 * c ^ 2 + 2 * c * (a1.re + a2.re) := by linarith
    rw [hre] at this; linarith
  exact not_three_sq_eq_one c this

theorem equilateral_zero {a0 a1 a2 : ℂ} {c : ℚ} (hc : c ≠ 0) (h1 : a0 + a1 + a2 = 0)
    (h2 : a0 * a1 + a1 * a2 + a2 * a0 = 0)
    (hu0 : (c : ℂ) + a0 = 0 ∨ ‖(c : ℂ) + a0‖ = 1)
    (hu1 : (c : ℂ) + a1 = 0 ∨ ‖(c : ℂ) + a1‖ = 1) (hu2 : (c : ℂ) + a2 = 0 ∨ ‖(c : ℂ) + a2‖ = 1) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  rcases hu0 with z0 | n0
  · exact (equilateral_one_zero hc h1 h2 z0 hu1 hu2).elim
  rcases hu1 with z1 | n1
  · exact (equilateral_one_zero (a0 := a1) (a1 := a2) (a2 := a0) hc (by linear_combination h1)
      (by linear_combination h2) z1 hu2 (Or.inr n0)).elim
  rcases hu2 with z2 | n2
  · exact (equilateral_one_zero (a0 := a2) (a1 := a0) (a2 := a1) hc (by linear_combination h1)
      (by linear_combination h2) z2 (Or.inr n0) (Or.inr n1)).elim
  obtain ⟨e01, e12⟩ := norm_eq_of_e2 h1 h2
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have q0 := normSq_add_real c a0
  have q1 := normSq_add_real c a1
  have q2 := normSq_add_real c a2
  push_cast at q0 q1 q2
  rw [n0] at q0; rw [n1, ← e01] at q1; rw [n2, ← e12, ← e01] at q2
  have hre : a0.re + a1.re + a2.re = 0 := by
    have := congrArg Complex.re h1; simpa using this
  have r01 : a0.re = a1.re := mul_left_cancel₀ (mul_ne_zero two_ne_zero hcR) (by linarith)
  have r12 : a1.re = a2.re := mul_left_cancel₀ (mul_ne_zero two_ne_zero hcR) (by linarith)
  have r0 : a0.re = 0 := by linarith
  have r1 : a1.re = 0 := by linarith
  have r2 : a2.re = 0 := by linarith
  -- `Σ a_k² = 0` with purely imaginary `a_k`
  have hsq : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 0 := by linear_combination (a0 + a1 + a2) * h1 - 2 * h2
  have hre2 := congrArg Complex.re hsq
  simp [pow_two, r0, r1, r2] at hre2
  have i0 : a0.im = 0 := by nlinarith [sq_nonneg a0.im, sq_nonneg a1.im, sq_nonneg a2.im]
  have i1 : a1.im = 0 := by nlinarith [sq_nonneg a0.im, sq_nonneg a1.im, sq_nonneg a2.im]
  have i2 : a2.im = 0 := by nlinarith [sq_nonneg a0.im, sq_nonneg a1.im, sq_nonneg a2.im]
  exact ⟨Complex.ext r0 i0, Complex.ext r1 i1, Complex.ext r2 i2⟩

theorem circulant_const {u0 u1 u2 w0 w1 w2 : ℂ} {r q : ℚ} (hr : r ≠ 0)
    (hT : w0 + w1 + w2 = q) (hw : ¬ (w0 = w2 ∧ w1 = w2))
    (hu0 : u0 = 0 ∨ ‖u0‖ = 1) (hu1 : u1 = 0 ∨ ‖u1‖ = 1) (hu2 : u2 = 0 ∨ ‖u2‖ = 1)
    (E0 : u0 * w0 + u1 * w1 + u2 * w2 = r) (E1 : u0 * w1 + u1 * w2 + u2 * w0 = r)
    (E2 : u0 * w2 + u1 * w0 + u2 * w1 = r) : u0 = u1 ∧ u1 = u2 := by
  have hS : (u0 + u1 + u2) * (q : ℂ) = 3 * r := by
    rw [← hT]; linear_combination E0 + E1 + E2
  have hq : q ≠ 0 := by
    rintro rfl; simp at hS; exact hr (by exact_mod_cast hS)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = r / q := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hc]; exact div_ne_zero hr hq
  have hcq : (c : ℂ) * q = r := by rw [hc]; push_cast; field_simp
  have h3 : u0 + u1 + u2 = 3 * c := by
    apply mul_right_cancel₀ hqC; rw [hS, mul_assoc, hcq]
  have h1 : (u0 - c) + (u1 - c) + (u2 - c) = 0 := by linear_combination h3
  have F0 : (u0 - c) * (w0 - w2) + (u1 - c) * (w1 - w2) = 0 := by
    linear_combination E0 - (c : ℂ) * hT - hcq - w2 * h1
  have F1 : (u0 - c) * ((w1 - w2) - (w0 - w2)) - (u1 - c) * (w0 - w2) = 0 := by
    linear_combination E1 - (c : ℂ) * hT - hcq - w0 * h1
  have hall : u0 - c = 0 ∧ u1 - c = 0 ∧ u2 - c = 0 := by
    set a0 := u0 - (c : ℂ) with ha0
    set a1 := u1 - (c : ℂ) with ha1
    set a2 := u2 - (c : ℂ) with ha2
    set x := w0 - w2 with hx
    set y := w1 - w2 with hy
    by_cases hD : x ^ 2 - x * y + y ^ 2 = 0
    · have hx0 : x ≠ 0 := by
        intro h0
        rw [h0] at hD
        have : y = 0 := by simpa using hD
        exact hw ⟨by rw [← sub_eq_zero, ← hx, h0], by rw [← sub_eq_zero, ← hy, this]⟩
      have he : x ^ 2 * (a0 ^ 2 + a0 * a1 + a1 ^ 2) = 0 := by
        linear_combination (a0 * x + a1 * x - a1 * y) * F0 + a1 ^ 2 * hD
      have he' : a0 ^ 2 + a0 * a1 + a1 ^ 2 = 0 :=
        (mul_eq_zero.1 he).resolve_left (pow_ne_zero 2 hx0)
      have h2 : a0 * a1 + a1 * a2 + a2 * a0 = 0 := by
        have : a2 = -a0 - a1 := by linear_combination h1
        rw [this]; linear_combination -he'
      have e := equilateral_zero hc0 h1 h2
        (by rcases hu0 with h | h
            · left; rw [ha0, h]; ring
            · right; rw [ha0]; simpa using h)
        (by rcases hu1 with h | h
            · left; rw [ha1, h]; ring
            · right; rw [ha1]; simpa using h)
        (by rcases hu2 with h | h
            · left; rw [ha2, h]; ring
            · right; rw [ha2]; simpa using h)
      exact e
    · have z0 : a0 * (x ^ 2 - x * y + y ^ 2) = 0 := by linear_combination x * F0 + y * F1
      have z1 : a1 * (x ^ 2 - x * y + y ^ 2) = 0 := by linear_combination (y - x) * F0 - x * F1
      have a00 := (mul_eq_zero.1 z0).resolve_right hD
      have a10 := (mul_eq_zero.1 z1).resolve_right hD
      exact ⟨a00, a10, by linear_combination h1 - a00 - a10⟩
  obtain ⟨k0, k1, k2⟩ := hall
  exact ⟨by linear_combination k0 - k1, by linear_combination k1 - k2⟩


/-- An injective enumeration of three roots of a cubic hits every root. -/
theorem root_enum_surj {K : Type*} [Field K] {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3)
    {e : Fin 3 → K} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom K)).eval (e k) = 0) {z : K}
    (hz : (f.map (Int.castRingHom K)).eval z = 0) : ∃ k, e k = z := by
  classical
  by_contra hcon
  push_neg at hcon
  set g := f.map (Int.castRingHom K) with hg
  have hg0 : g ≠ 0 := (hmon.map _).ne_zero
  have hgd : g.natDegree = 3 := by rw [hg, hmon.natDegree_map, hdeg]
  have hsub : insert z (Finset.univ.image e) ⊆ g.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hz
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx; exact he k
  have hcard : (insert z (Finset.univ.image e)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj]
    · simp
    · intro hm; obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hm; exact hcon k hk
  have h1 := Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le g.roots
  have h3 := Polynomial.card_roots' g
  omega

/-- `Σ_k P(e_k)` is rational for `P ∈ ℚ[X]`. -/
theorem sum_aeval_rat {K : Type*} [Field K] [CharZero K] {f : ℤ[X]} (hmon : f.Monic)
    (hdeg : f.natDegree = 3) {e : Fin 3 → K} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom K)).eval (e k) = 0) (P : ℚ[X]) :
    ∃ q : ℚ, ∑ k, aeval (e k) P = (q : K) := by
  classical
  refine ⟨∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * traceSeq f j, ?_⟩
  have hd : f.natDegree = 3 := hdeg
  have hroot : ∀ N, ((traceSeq f N : ℤ) : K) = ∑ k, e k ^ N := by
    intro N
    have := traceSeq_eq_root_sum (K := K) f hmon (fun i => e (Fin.cast hd i))
      (fun i => he _) (fun i j h => Fin.cast_injective hd (hinj h)) N
    rw [this]
    exact Fintype.sum_equiv (finCongr hd) _ _ (fun i => rfl)
  simp_rw [Polynomial.aeval_eq_sum_range]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hroot j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]; rfl

theorem eval_cubic {K : Type*} [CommRing K] [Nontrivial K] {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3)
    (z : K) : (f.map (Int.castRingHom K)).eval z
      = z ^ 3 + (f.coeff 2 : K) * z ^ 2 + (f.coeff 1 : K) * z + (f.coeff 0 : K) := by
  rw [Polynomial.eval_eq_sum_range, hmon.natDegree_map, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.coeff_map, eq_intCast]
  have h3 : f.coeff 3 = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
  rw [h3]; push_cast; ring

/-- `Σ_k e_k^s` is rational for every integer `s`. -/
theorem sum_zpow_rat {K : Type*} [Field K] [CharZero K] {f : ℤ[X]} (hmon : f.Monic)
    (hdeg : f.natDegree = 3) (hc0 : f.coeff 0 ≠ 0) {e : Fin 3 → K} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom K)).eval (e k) = 0) (s : ℤ) :
    ∃ q : ℚ, ∑ k, e k ^ s = (q : K) := by
  set hinv : ℚ[X] := -C ((f.coeff 0 : ℚ)⁻¹) * (X ^ 2 + C (f.coeff 2 : ℚ) * X + C (f.coeff 1 : ℚ))
  have hc0K : (f.coeff 0 : K) ≠ 0 := by exact_mod_cast hc0
  have hinvK : ∀ k, (e k)⁻¹ = aeval (e k) hinv := by
    intro k
    have h := he k
    rw [eval_cubic hmon hdeg] at h
    have hek : e k ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; exact hc0 h
    simp only [hinv, map_mul, map_neg, map_add, map_pow, aeval_C, aeval_X,
      eq_ratCast, map_inv₀, Rat.cast_intCast]
    field_simp
    linear_combination h
  rcases s.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · obtain ⟨q, hq⟩ := sum_aeval_rat hmon hdeg hinj he (X ^ n)
    exact ⟨q, by simpa using hq⟩
  · obtain ⟨q, hq⟩ := sum_aeval_rat hmon hdeg hinj he (hinv ^ n)
    refine ⟨q, ?_⟩
    rw [← hq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [zpow_neg, zpow_natCast, ← inv_pow, hinvK k, map_pow]

/-- Roots of `f` with no root in `L` are conjugate over `L`. -/
theorem exists_auto_over {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3)
    (L : IntermediateField ℚ AlgQ)
    (hL : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ L) {x y : AlgQ}
    (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0)
    (hy : (f.map (Int.castRingHom AlgQ)).eval y = 0) :
    ∃ σ : AlgQ ≃ₐ[L] AlgQ, σ x = y := by
  haveI : Normal L AlgQ := Normal.tower_top_of_normal ℚ L AlgQ
  set g : L[X] := f.map (Int.castRingHom L) with hg
  have hgm : g.Monic := hmon.map _
  have hgd : g.natDegree = 3 := by rw [hg, hmon.natDegree_map, hdeg]
  have hbr : ∀ z : AlgQ, aeval z g = (f.map (Int.castRingHom AlgQ)).eval z := by
    intro z
    rw [hg, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
    congr 2
  have hgirr : Irreducible g := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hgd]; decide) ?_
    intro r hr
    apply hL (r : AlgQ) _ r.2
    rw [← hbr]
    have : aeval (r : AlgQ) g = algebraMap L AlgQ (g.eval r) := by
      exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := AlgQ) r g
    rw [this, hr.eq_zero, map_zero]
  have hmin : minpoly L y = g :=
    (minpoly.eq_of_irreducible_of_monic hgirr (by rw [hbr]; exact hy) hgm).symm
  have halg : IsAlgebraic L y := ⟨g, hgm.ne_zero, by rw [hbr]; exact hy⟩
  exact minpoly.exists_algEquiv_of_root halg (by rw [hmin, hbr]; exact hx)

theorem root_map_alg {f : ℤ[X]} {L : IntermediateField ℚ AlgQ} (σ : AlgQ ≃ₐ[L] AlgQ) {z : AlgQ}
    (hz : (f.map (Int.castRingHom AlgQ)).eval z = 0) :
    (f.map (Int.castRingHom AlgQ)).eval (σ z) = 0 := by
  have h := Polynomial.hom_eval₂ f (Int.castRingHom AlgQ) (σ : AlgQ →+* AlgQ) z
  rw [Polynomial.eval_map] at hz ⊢
  rw [hz, map_zero] at h
  rw [show (σ : AlgQ →+* AlgQ).comp (Int.castRingHom AlgQ) = Int.castRingHom AlgQ from
    RingHom.ext_int _ _] at h
  exact h.symm

/-- **The 3-cycle**: some automorphism over `L` cycles the three roots. -/
theorem exists_three_cycle {f : ℤ[X]} (hmon : f.Monic) (hdeg : f.natDegree = 3)
    (L : IntermediateField ℚ AlgQ)
    (hL : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ L)
    {e : Fin 3 → AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0) :
    ∃ σ : AlgQ ≃ₐ[L] AlgQ, ∃ a b : Fin 3, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      σ (e 0) = e a ∧ σ (e a) = e b ∧ σ (e b) = e 0 := by
  have img : ∀ (σ : AlgQ ≃ₐ[L] AlgQ) k, ∃ j, σ (e k) = e j := fun σ k =>
    let ⟨j, hj⟩ := root_enum_surj hmon hdeg hinj he (root_map_alg σ (he k)); ⟨j, hj.symm⟩
  have inj : ∀ (σ : AlgQ ≃ₐ[L] AlgQ) k k', σ (e k) = σ (e k') → k = k' := fun σ k k' h =>
    hinj (σ.injective h)
  obtain ⟨σ1, h1⟩ := exists_auto_over hmon hdeg L hL (he 0) (he 1)
  obtain ⟨σ2, h2⟩ := exists_auto_over hmon hdeg L hL (he 0) (he 2)
  obtain ⟨j, hj⟩ := img σ1 1
  obtain ⟨k, hk⟩ := img σ1 2
  fin_cases j
  · -- σ1 swaps e0, e1 and fixes e2
    have hk2 : k = 2 := by
      fin_cases k
      · exact absurd (inj σ1 2 1 (hk.trans hj.symm)) (by decide)
      · exact absurd (inj σ1 2 0 (hk.trans h1.symm)) (by decide)
      · rfl
    subst hk2
    obtain ⟨j', hj'⟩ := img σ2 2
    obtain ⟨k', hk'⟩ := img σ2 1
    fin_cases j'
    · have hk1 : k' = 1 := by
        fin_cases k'
        · exact absurd (inj σ2 1 2 (hk'.trans hj'.symm)) (by decide)
        · rfl
        · exact absurd (inj σ2 1 0 (hk'.trans h2.symm)) (by decide)
      subst hk1
      refine ⟨σ1 * σ2, 2, 1, by decide, by decide, by decide, ?_, ?_, ?_⟩
      · simp only [AlgEquiv.mul_apply, h2]; exact hk
      · simp only [AlgEquiv.mul_apply]; rw [hj']; exact h1
      · simp only [AlgEquiv.mul_apply]; rw [hk']; exact hj
    · have hk0 : k' = 0 := by
        fin_cases k'
        · rfl
        · exact absurd (inj σ2 1 2 (hk'.trans hj'.symm)) (by decide)
        · exact absurd (inj σ2 1 0 (hk'.trans h2.symm)) (by decide)
      subst hk0
      exact ⟨σ2, 2, 1, by decide, by decide, by decide, h2, hj', hk'⟩
    · exact absurd (inj σ2 2 0 (hj'.trans h2.symm)) (by decide)
  · exact absurd (inj σ1 1 0 (hj.trans h1.symm)) (by decide)
  · have hk0 : k = 0 := by
      fin_cases k
      · rfl
      · exact absurd (inj σ1 2 0 (hk.trans h1.symm)) (by decide)
      · exact absurd (inj σ1 2 1 (hk.trans hj.symm)) (by decide)
    subst hk0
    exact ⟨σ1, 1, 2, by decide, by decide, by decide, h1, hj, hk⟩

theorem coeff_zero_ne_zero {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) : f.coeff 0 ≠ 0 := by
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

theorem zpow_ne_of_norm {x y : ℂ} (hx : 1 < ‖x‖) (hy0 : y ≠ 0) (hy : ‖y‖ < 1) {s : ℤ}
    (hs : s ≠ 0) : x ^ s ≠ y ^ s := by
  intro h
  have h' : ‖x‖ ^ s = ‖y‖ ^ s := by rw [← norm_zpow, ← norm_zpow, h]
  have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases lt_or_gt_of_ne hs with hn | hp
  · have h1 : ‖x‖ ^ s < 1 := zpow_lt_one_of_neg₀ hx hn
    have h2 : 1 < ‖y‖ ^ s := one_lt_zpow_of_neg₀ hyp hy hn
    linarith
  · have h1 : 1 < ‖x‖ ^ s := one_lt_zpow₀ hx hp
    have h2 : ‖y‖ ^ s < 1 := zpow_lt_one₀ hyp hy hp
    linarith

theorem rigidity_generic {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 3)
    {e : Fin 3 → AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0)
    (hbig : 1 < ‖(e 0 : ℂ)‖) (hsmall : ∀ k, k ≠ 0 → ‖(e k : ℂ)‖ < 1)
    {s : ℤ} (hs : s ≠ 0) (L : IntermediateField ℚ AlgQ) {u : Fin 3 → AlgQ} (hu : ∀ k, u k ∈ L)
    (hu1 : ∀ k, u k = 0 ∨ ‖(u k : ℂ)‖ = 1)
    (hL : ∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ L)
    {ω : AlgQ} (hω : ω ^ 2 = 1) (hsum : ∑ k, u k * e k ^ s = ω) :
    ∀ k, u k = u 0 := by
  have hc0 := coeff_zero_ne_zero hmon hirr hdeg
  obtain ⟨σ, a, b, ha, hb, hab, h0a, hab', hb0⟩ := exists_three_cycle hmon hdeg L hL hinj he
  have hωpm : ω = 1 ∨ ω = -1 := by
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hσω : σ ω = ω := by rcases hωpm with rfl | rfl <;> simp
  have hσu : ∀ k, σ (u k) = u k := fun k => σ.commutes ⟨u k, hu k⟩
  have happ : ∀ (τ : AlgQ ≃ₐ[L] AlgQ), τ ω = ω → ∑ k, u k * (τ (e k)) ^ s = ω := by
    intro τ hτ
    have := congrArg τ hsum
    rw [map_sum, hτ] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc := τ.commutes ⟨u k, hu k⟩
    simp only [IntermediateField.algebraMap_apply] at hc
    rw [map_mul, map_zpow₀, hc]
  have E1 := happ σ hσω
  have E2 := happ (σ * σ) (by simp [hσω])
  obtain ⟨q, hq⟩ := sum_zpow_rat hmon hdeg hc0 hinj he s
  have he0 : ∀ k, e k ≠ 0 := by
    intro k h0; have := he k; rw [h0, eval_cubic hmon hdeg] at this; simp at this
    exact hc0 this
  -- cast everything to `ℂ`
  have cast : ∀ x y : AlgQ, x = y → (x : ℂ) = (y : ℂ) := fun x y h => by rw [h]
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℚ, r ≠ 0 ∧ (ω : ℂ) = r := by
    rcases hωpm with rfl | rfl
    · exact ⟨1, one_ne_zero, by simp⟩
    · exact ⟨-1, by norm_num, by simp⟩
  have hw : ∀ k, k ≠ 0 → ((e 0 : ℂ)) ^ s ≠ ((e k : ℂ)) ^ s := fun k hk =>
    zpow_ne_of_norm hbig (by exact_mod_cast he0 k) (hsmall k hk) hs
  have hcase : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    revert ha hb hab; fin_cases a <;> fin_cases b <;> decide
  have hsum3 : ∀ (F : Fin 3 → AlgQ), ∑ k, F k = F 0 + F a + F b := by
    intro F
    rw [Fin.sum_univ_three]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp only [add_assoc, add_comm (F 1)]
  rw [hsum3] at hsum E1 E2 hq
  simp only [AlgEquiv.mul_apply, h0a, hab', hb0] at E1 E2
  have c0 := cast _ _ hsum; have c1 := cast _ _ E1; have c2 := cast _ _ E2
  have cq := cast _ _ hq
  push_cast at c0 c1 c2 cq
  rw [hr] at c0 c1 c2
  have hun : ∀ k, (u k : ℂ) = 0 ∨ ‖(u k : ℂ)‖ = 1 := by
    intro k; rcases hu1 k with h | h
    · left; rw [h]; rfl
    · right; exact h
  obtain ⟨k0a, kab⟩ := circulant_const hr0 cq (fun h => hw b hb h.1) (hun 0) (hun a) (hun b)
    c0 (by linear_combination c1) (by linear_combination c2)
  have hu0a : u 0 = u a := Subtype.ext k0a
  have huab : u a = u b := Subtype.ext kab
  intro k
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases k
  all_goals first | rfl | exact hu0a.symm | exact (hu0a.trans huab).symm

/-! ### The pieces (statements; see the module docstring) -/

/-- **Step 5, the cube class.** -/
theorem not_primeTraces_of_cube {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) (s : ℤ) (z : ZMod 3)
    (hz : f.map (Int.castRingHom (ZMod 3)) = (X - C z) ^ 3) : ¬ PrimeTraces f s := by
  classical
  intro hP
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
  -- every trace is `0 mod 3`
  have h3 : ∀ N, (3 : ℤ) ∣ traceSeq f N := by
    intro N
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
  -- the traces tend to `∞`
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
  have hbig : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ α ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hD.gt_one).eventually_ge_atTop 4
  have htN : Tendsto (fun n : ℕ => ((3 : ℤ) ^ n + s).toNat) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b + s.natAbs)] with n hn
    have h1 : (n : ℤ) < 3 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
    rw [Int.le_toNat]
    · omega
    · omega
  obtain ⟨n, ⟨p, hp, hpe⟩, hf4, hb4⟩ :=
    (hP.and ((htN.eventually hfl).and (htN.eventually hbig))).exists
  have hp3 : p = 3 := by
    have : (3 : ℤ) ∣ (p : ℤ) := hpe ▸ h3 _
    have : 3 ∣ p := by exact_mod_cast this
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
  set N := ((3 : ℤ) ^ n + s).toNat
  have hfl4 : (4 : ℤ) ≤ ⌊α ^ N⌋ := Int.le_floor.2 (by exact_mod_cast hb4)
  rw [hpe, hp3] at hf4
  push_cast at hf4
  omega

/-! ### `exists_spectral`, decomposed

The integer data: `C = compM ℤ f`, `T = C^(3^ν)`.
* `window_shift` (Step 3): the traces `p_n = tr C^(3^n + s)` are `≡ ω_n ∈ {±1}` modulo `3^k`
  for arbitrarily large `n`, at every level `k`.
* `exists_teich_limit`: `T^(3^F) ≡ T (mod 3^(ν − n₀ + 1))` with `F = 1, 2, 3` the lcm of the degrees
  of the factors of `f mod 3` (`F = 3` exactly when `f mod 3` is irreducible).
* `exists_entry_ne`: outside the cube class, `T ∓ 1` has an entry prime to `3`.
* `exists_spectral_solution_shift`: the transfer of the resulting integer system to `AlgQ`.
* `readout_trace`, `readout_ne`: the eigenvalues of the solution, read off by Vandermonde. -/

/-- Vandermonde conjugation of `P(C) · C^a`. -/
theorem vandermonde_mul_polyMat_mul_pow {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (x : Fin f.natDegree → K) (a : ℕ) :
    Matrix.vandermonde e * (polyMat K f x * compM K f ^ a)
      = Matrix.diagonal (fun i => polyVal x (e i) * e i ^ a) * Matrix.vandermonde e := by
  calc Matrix.vandermonde e * (polyMat K f x * compM K f ^ a)
      = (Matrix.vandermonde e * polyMat K f x) * compM K f ^ a := by rw [Matrix.mul_assoc]
    _ = Matrix.diagonal (fun i => polyVal x (e i)) * (Matrix.vandermonde e * compM K f ^ a) := by
          rw [vandermonde_mul_polyMat f hmon e he x, Matrix.mul_assoc]
    _ = Matrix.diagonal (fun i => polyVal x (e i))
          * (Matrix.diagonal e ^ a * Matrix.vandermonde e) := by
          rw [conj_pow _ _ _ (vandermonde_mul_compM f hmon e he) a]
    _ = Matrix.diagonal (fun i => polyVal x (e i) * e i ^ a) * Matrix.vandermonde e := by
          rw [← Matrix.mul_assoc, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
          rfl

/-- **Read-out of the shifted trace.**  `P'(C) C^(s⁻) = P(C) C^(s⁺)` makes `tr P'(C)` the
spectral sum `Σ_i P(e_i) e_i^s`. -/
theorem readout_trace {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (he0 : ∀ i, e i ≠ 0) (x x' : Fin f.natDegree → K) {s : ℤ}
    (hrel : polyMat K f x' * compM K f ^ (-s).toNat = polyMat K f x * compM K f ^ s.toNat) :
    (polyMat K f x').trace = ∑ i, polyVal x (e i) * e i ^ s := by
  classical
  have hV := vandermonde_isUnit_det e hinj
  have h1 := vandermonde_mul_polyMat_mul_pow f hmon e he x' (-s).toNat
  have h2 := vandermonde_mul_polyMat_mul_pow f hmon e he x s.toNat
  rw [hrel, h2] at h1
  have hdiag := right_cancel_of_isUnit_det hV h1
  have hi : ∀ i, polyVal x' (e i) * e i ^ (-s).toNat = polyVal x (e i) * e i ^ s.toNat := by
    intro i
    have := congrArg (fun M : Matrix (Fin f.natDegree) (Fin f.natDegree) K => M i i) hdiag
    simpa using this.symm
  have htr := trace_polyMat_mul_compM_pow f hmon e he hinj x' 0
  simp only [pow_zero, Matrix.mul_one] at htr
  rw [htr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : s = (s.toNat : ℤ) - ((-s).toNat : ℤ) := by omega
  have hne : e i ^ (-s).toNat ≠ 0 := pow_ne_zero _ (he0 i)
  rw [hs, zpow_sub₀ (he0 i), zpow_natCast, zpow_natCast, mul_one, ← mul_div_assoc,
    eq_div_iff hne]
  exact hi i

/-- **Read-out of non-scalarity.**  `P(C) ≠ c` forces some `P(e_i) ≠ c`. -/
theorem readout_ne {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (x : Fin f.natDegree → K) (c : K)
    (hP : polyMat K f x ≠ c • 1) : ∃ i, polyVal x (e i) ≠ c := by
  classical
  by_contra hcon
  push_neg at hcon
  apply hP
  have hV := (Matrix.isUnit_iff_isUnit_det _).2 (vandermonde_isUnit_det e hinj)
  have h := vandermonde_mul_polyMat f hmon e he x
  have hd : Matrix.diagonal (fun i => polyVal x (e i)) = c • 1 := by
    ext i j; by_cases hij : i = j <;> simp [hij, hcon, Matrix.one_apply]
  rw [hd, Matrix.smul_mul, Matrix.one_mul, ← Matrix.mul_one (Matrix.vandermonde e),
    Matrix.mul_assoc, Matrix.one_mul, ← Matrix.mul_smul] at h
  exact hV.mul_left_cancel h

/-- **Step 3 (window), shifted.**  For arbitrarily large `n`, the trace `tr C^(3^n + s)` is
`≡ ±1` modulo `3^k`. -/
theorem window_shift {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) {s : ℤ} (hP : PrimeTraces f s)
    (k : ℕ) : ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat - w := by
  sorry

/-- The companion matrix of `X³ + a₂X² + a₁X + a₀` over `ZMod 3`. -/
def cm3 (a : Fin 3 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  Matrix.of fun i j => (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) - (if (j : ℕ) + 1 = 3 then a i else 0)

/-- **Finite check** over the 27 monic cubics mod 3: the Frobenius period of the companion
matrix, with period `27` only for the cubics without a root. -/
theorem cm3_check : ∀ a : Fin 3 → ZMod 3, cm3 a ^ 9 = cm3 a ^ 3 ∨ cm3 a ^ 27 = cm3 a ^ 3 ∨
    (cm3 a ^ 81 = cm3 a ^ 3 ∧ ∀ r : ZMod 3, r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0 ≠ 0) := by
  native_decide

/-- **The Teichmüller limit.**  `T = C^(3^ν)` satisfies `T^(3^F) ≡ T` to growing precision, with
`3^F − 1 ∈ {2, 8, 26}` and `F = 3` only when `f mod 3` is irreducible. -/
theorem exists_teich_limit {f : ℤ[X]} {α : ℝ} (hD : PisotData f α) :
    ∃ F : ℕ, (F = 1 ∨ F = 2 ∨ (F = 3 ∧ Irreducible (f.map (Int.castRingHom (ZMod 3))))) ∧
      ∃ n₀ : ℕ, ∀ ν, n₀ ≤ ν → ∀ i j, (3 : ℤ) ^ (ν - n₀ + 1) ∣
        ((compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) - compM ℤ f ^ (3 ^ ν)) i j := by
  classical
  set a : Fin 3 → ZMod 3 := fun i => ((f.coeff i : ℤ) : ZMod 3) with ha
  set E : Fin 3 ≃ Fin f.natDegree := finCongr hD.deg.symm with hE
  have hcm : compM (ZMod 3) f = Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) E (cm3 a) := by
    ext i j
    simp [compM, cm3, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, hE, ha, hD.deg]
  have htr : ∀ m m' : ℕ, cm3 a ^ m = cm3 a ^ m' →
      ∀ i j, (3 : ℤ) ∣ (compM ℤ f ^ m - compM ℤ f ^ m') i j := by
    intro m m' h i j
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 ?_
    have h2 : compM (ZMod 3) f ^ m = compM (ZMod 3) f ^ m' := by
      rw [hcm, ← map_pow, ← map_pow, h]
    rw [← compM_map (Int.castRingHom (ZMod 3)) f, ← map_matrix_pow, ← map_matrix_pow] at h2
    have := congrArg (fun M => M i j) h2
    simp only [Matrix.map_apply] at this
    simp only [eq_intCast] at this
    simp [Matrix.sub_apply, this]
  have hlift : ∀ F : ℕ, cm3 a ^ (3 ^ (F + 1)) = cm3 a ^ 3 → ∀ ν, 1 ≤ ν → ∀ i j,
      (3 : ℤ) ^ (ν - 1 + 1) ∣ ((compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) - compM ℤ f ^ (3 ^ ν)) i j := by
    intro F hF ν hν i j
    have h := pow_c_pow_congr (c := 3) (Commute.pow_pow_self (compM ℤ f) (3 ^ (F + 1)) 3)
      (htr _ _ hF) (ν - 1) i j
    push_cast at h
    have e1 : (compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) = (compM ℤ f ^ (3 ^ (F + 1))) ^ (3 ^ (ν - 1)) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 2; omega
    have e2 : compM ℤ f ^ (3 ^ ν) = (compM ℤ f ^ 3) ^ (3 ^ (ν - 1)) := by
      rw [← pow_mul, ← pow_succ']; congr 2; omega
    rw [e1, e2]; exact h
  have hroot : (∀ r : ZMod 3, r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0 ≠ 0) →
      Irreducible (f.map (Int.castRingHom (ZMod 3))) := by
    intro hr
    have hmon := hD.monic.map (Int.castRingHom (ZMod 3))
    have hdeg : (f.map (Int.castRingHom (ZMod 3))).natDegree = 3 := by
      rw [hD.monic.natDegree_map, hD.deg]
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro r hr'
    apply hr r
    rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range, hdeg] at hr'
    have h3 : (f.map (Int.castRingHom (ZMod 3))).coeff 3 = 1 := by
      have := hmon.coeff_natDegree; rwa [hdeg] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h3] at hr'
    simp only [Polynomial.coeff_map, eq_intCast, ha] at hr' ⊢
    simp at hr' ⊢
    linear_combination hr'
  rcases cm3_check a with h | h | ⟨h, hr⟩
  · exact ⟨1, Or.inl rfl, 1, hlift 1 h⟩
  · exact ⟨2, Or.inr (Or.inl rfl), 1, hlift 2 h⟩
  · exact ⟨3, Or.inr (Or.inr ⟨rfl, hroot hr⟩), 1, hlift 3 h⟩

/-- **Non-scalarity mod 3.**  Outside the cube class, `C^(3^ν) ∓ 1` has an entry prime to `3`. -/
theorem exists_entry_ne {f : ℤ[X]} {α : ℝ} (hD : PisotData f α)
    (hnc : ∀ z : ZMod 3, f.map (Int.castRingHom (ZMod 3)) ≠ (X - C z) ^ 3) (ν : ℕ) (z : ℤ)
    (hz : z = 1 ∨ z = -1) : ∃ a b, ¬ (3 : ℤ) ∣ (compM ℤ f ^ (3 ^ ν) - z • (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)) a b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
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
  have hdvd := dvd_of_aeval_compM_eq_zero f hD.monic hd1 _ haev
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C zb) _).1 hdvd
  have heq := eq_of_monic_of_associated (hD.monic.map _) ((monic_X_sub_C zb).pow i) hi
  have hdeg : i = 3 := by
    have := congrArg natDegree heq
    rw [hD.monic.natDegree_map, hD.deg, natDegree_pow, natDegree_X_sub_C, mul_one] at this
    exact this.symm
  exact hnc zb (by rw [heq, hdeg])

/-- Variables of the shifted integer system: `x`, `x'`, `(w, y₁, y₂)`, `r₁`, `r₂`. -/
abbrev ShiftVar (d : ℕ) := (Fin d ⊕ Fin d) ⊕ (Fin 3 ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d)))

/-- Equations of the shifted integer system. -/
abbrev ShiftEq (d : ℕ) := (Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ Fin 4)

/-- The shifted integer system, read in any commutative ring:
`P^(3^F) = P`, `P' C^a = P C^b`, `w² = 1`, `tr P' = w`, `y₁ Σ r₁ (P − 1) = 1`,
`y₂ Σ r₂ (P + 1) = 1`. -/
def shiftSys (R : Type*) [CommRing R] (f : ℤ[X]) (F a b : ℕ) (p : ShiftVar f.natDegree → R) :
    ShiftEq f.natDegree → R :=
  let P := polyMat R f (fun j => p (Sum.inl (Sum.inl j)))
  let P' := polyMat R f (fun j => p (Sum.inl (Sum.inr j)))
  let w := p (Sum.inr (Sum.inl 0))
  let y₁ := p (Sum.inr (Sum.inl 1))
  let y₂ := p (Sum.inr (Sum.inl 2))
  Sum.elim (fun ij => (P ^ (3 ^ F) - P) ij.1 ij.2)
    (Sum.elim (fun ij => (P' * compM R f ^ a - P * compM R f ^ b) ij.1 ij.2)
      (fun t => match t with
        | 0 => w ^ 2 - 1
        | 1 => P'.trace - w
        | 2 => y₁ * (∑ ij : Fin f.natDegree × Fin f.natDegree,
            p (Sum.inr (Sum.inr (Sum.inl ij))) * (P - 1) ij.1 ij.2) - 1
        | 3 => y₂ * (∑ ij : Fin f.natDegree × Fin f.natDegree,
            p (Sum.inr (Sum.inr (Sum.inr ij))) * (P + 1) ij.1 ij.2) - 1))

theorem shiftSys_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℤ[X])
    (F a b : ℕ) (p : ShiftVar f.natDegree → R) (i : ShiftEq f.natDegree) :
    φ (shiftSys R f F a b p i) = shiftSys S f F a b (fun v => φ (p v)) i := by
  classical
  have hP : ∀ (g : Fin f.natDegree → R),
      (polyMat R f g).map φ = polyMat S f (fun j => φ (g j)) := fun g => polyMat_map φ f g
  have hent : ∀ (M : Matrix (Fin f.natDegree) (Fin f.natDegree) R) i j, φ (M i j) = M.map φ i j :=
    fun M i j => rfl
  rcases i with ⟨i, j⟩ | ⟨i, j⟩ | t
  · simp only [shiftSys, Sum.elim_inl]
    rw [hent, map_matrix_sub, map_matrix_pow, hP]
  · simp only [shiftSys, Sum.elim_inr, Sum.elim_inl]
    rw [hent, map_matrix_sub, map_matrix_mul, map_matrix_mul, map_matrix_pow, map_matrix_pow,
      hP, hP, compM_map]
  · fin_cases t
    · simp [shiftSys]
    · simp only [shiftSys, Sum.elim_inr]
      simp only [Fin.isValue, map_sub]
      rw [← trace_map_eq, hP]
    · simp only [shiftSys, Sum.elim_inr]
      simp only [map_sub, map_mul, map_sum, map_one]
      congr 2
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [hent (polyMat R f _ - 1), map_matrix_sub, hP, map_matrix_one]
    · simp only [shiftSys, Sum.elim_inr]
      simp only [map_sub, map_mul, map_sum, map_one]
      congr 2
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [hent (polyMat R f _ + 1)]
      have e := map_add (RingHom.mapMatrix φ) (polyMat R f (fun j => p (Sum.inl (Sum.inl j)))) 1
      simp only [RingHom.mapMatrix_apply, map_one] at e
      rw [e, hP]

/-- An entry prime to `3` is invertible modulo `3^k`. -/
theorem exists_inv_mod {e : ℤ} (h : ¬ (3 : ℤ) ∣ e) (k : ℕ) : ∃ y : ℤ, (3 : ℤ) ^ k ∣ y * e - 1 := by
  have hc : IsCoprime ((3 : ℤ) ^ k) e :=
    ((Prime.coprime_iff_not_dvd Int.prime_three).2 h).pow_left
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨v, ⟨-u, by linear_combination huv⟩⟩

/-- **The transfer**, shifted: the integer system at every level has a solution in `AlgQ`. -/
theorem exists_spectral_solution_shift (f : ℤ[X]) (hd : 1 ≤ f.natDegree) {F n₀ : ℕ} {s : ℤ}
    (hlim : ∀ ν, n₀ ≤ ν → ∀ i j, (3 : ℤ) ^ (ν - n₀ + 1) ∣
        ((compM ℤ f ^ (3 ^ ν)) ^ (3 ^ F) - compM ℤ f ^ (3 ^ ν)) i j)
    (hne : ∀ (ν : ℕ) (z : ℤ), (z = 1 ∨ z = -1) →
        ∃ a b, ¬ (3 : ℤ) ∣ (compM ℤ f ^ (3 ^ ν) - z • (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)) a b)
    (hcong : ∀ k : ℕ, ∃ n, k ≤ n ∧ 0 ≤ (3 : ℤ) ^ n + s ∧ ∃ w : ℤ, (3 : ℤ) ^ k ∣ w ^ 2 - 1 ∧
      (3 : ℤ) ^ k ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat - w) :
    ∃ (x x' : Fin f.natDegree → AlgQ) (w : AlgQ),
      polyMat AlgQ f x ^ (3 ^ F) = polyMat AlgQ f x ∧ w ^ 2 = 1 ∧
      polyMat AlgQ f x' * compM AlgQ f ^ (-s).toNat = polyMat AlgQ f x * compM AlgQ f ^ s.toNat ∧
      (polyMat AlgQ f x').trace = w ∧
      polyMat AlgQ f x ≠ (1 : AlgQ) • 1 ∧ polyMat AlgQ f x ≠ (-1 : AlgQ) • 1 := by
  classical
  set d := f.natDegree with hdd
  set a := (-s).toNat with ha
  set b := s.toNat with hb
  set Fsys : ShiftEq d → MvPolynomial (ShiftVar d) ℤ := shiftSys _ f F a b MvPolynomial.X
    with hFsys
  have hevZ : ∀ (p : ShiftVar d → ℤ) i, MvPolynomial.eval p (Fsys i) = shiftSys ℤ f F a b p i := by
    intro p i
    rw [hFsys, shiftSys_map (MvPolynomial.eval p)]
    simp
  have hevA : ∀ (q : ShiftVar d → AlgQ) i,
      MvPolynomial.eval₂ (Int.castRingHom AlgQ) q (Fsys i) = shiftSys AlgQ f F a b q i := by
    intro q i
    rw [← MvPolynomial.coe_eval₂Hom, hFsys, shiftSys_map]
    simp
  have hlev : ∀ k : ℕ, ∃ p : ShiftVar d → ℤ, ∀ i,
      ((3 : ℕ) : ℤ) ^ k ∣ MvPolynomial.eval p (Fsys i) := by
    intro k
    obtain ⟨n, hn, hn0, w, hw, hV⟩ := hcong (k + n₀)
    obtain ⟨x, hx⟩ := exists_coords f hd (3 ^ n)
    obtain ⟨x', hx'⟩ := exists_coords f hd ((3 : ℤ) ^ n + s).toNat
    obtain ⟨a1, b1, h1⟩ := hne n 1 (Or.inl rfl)
    obtain ⟨a2, b2, h2⟩ := hne n (-1) (Or.inr rfl)
    obtain ⟨y1, hy1⟩ := exists_inv_mod h1 k
    obtain ⟨y2, hy2⟩ := exists_inv_mod h2 k
    refine ⟨Sum.elim (Sum.elim x x') (Sum.elim ![w, y1, y2]
      (Sum.elim (fun ij => if ij = (a1, b1) then 1 else 0)
        (fun ij => if ij = (a2, b2) then 1 else 0))), fun i => ?_⟩
    rw [hevZ]
    push_cast
    have hxe : polyMat ℤ f x = compM ℤ f ^ (3 ^ n) := hx.symm
    have hxe' : polyMat ℤ f x' = compM ℤ f ^ ((3 : ℤ) ^ n + s).toNat := hx'.symm
    rcases i with ⟨i, j⟩ | ⟨i, j⟩ | t
    · simp only [shiftSys, Sum.elim_inl]
      rw [hxe]
      exact dvd_trans (pow_dvd_pow 3 (by omega)) (hlim n (by omega) i j)
    · simp only [shiftSys, Sum.elim_inl, Sum.elim_inr]
      rw [hxe, hxe', ← pow_add, ← pow_add]
      have h3 : (((3 ^ n : ℕ) : ℤ)) = (3 : ℤ) ^ n := by push_cast; rfl
      have hexp : ((3 : ℤ) ^ n + s).toNat + a = 3 ^ n + b := by omega
      rw [hexp, sub_self]
      simp
    · fin_cases t
      · simpa [shiftSys] using dvd_trans (pow_dvd_pow 3 (by omega)) hw
      · simpa [shiftSys, hxe', traceSeq] using dvd_trans (pow_dvd_pow 3 (by omega)) hV
      · simp only [shiftSys, Sum.elim_inr, Sum.elim_inl]
        simp [Finset.sum_ite_eq', hxe]
        simpa [one_smul] using hy1
      · simp only [shiftSys, Sum.elim_inr, Sum.elim_inl]
        simp [Finset.sum_ite_eq', hxe]
        simpa [sub_neg_eq_add] using hy2
  obtain ⟨q, hq⟩ := exists_zero_of_family (K := AlgQ) (σ := ShiftVar d) (c := 3) (by norm_num)
    Fsys hlev
  have hq' : ∀ i, shiftSys AlgQ f F a b q i = 0 := fun i => by rw [← hevA]; exact hq i
  refine ⟨fun j => q (Sum.inl (Sum.inl j)), fun j => q (Sum.inl (Sum.inr j)),
    q (Sum.inr (Sum.inl 0)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have := hq' (Sum.inl (i, j))
    simp only [shiftSys, Sum.elim_inl] at this
    exact sub_eq_zero.1 (by simpa [Matrix.sub_apply] using this)
  · have := hq' (Sum.inr (Sum.inr 0))
    simp only [shiftSys, Sum.elim_inr] at this
    exact sub_eq_zero.1 this
  · refine Matrix.ext fun i j => ?_
    have := hq' (Sum.inr (Sum.inl (i, j)))
    simp only [shiftSys, Sum.elim_inl, Sum.elim_inr] at this
    exact sub_eq_zero.1 (by simpa [Matrix.sub_apply] using this)
  · have := hq' (Sum.inr (Sum.inr 1))
    simp only [shiftSys, Sum.elim_inr] at this
    exact sub_eq_zero.1 this
  · intro hP
    have := hq' (Sum.inr (Sum.inr 2))
    simp only [shiftSys, Sum.elim_inr] at this
    rw [hP, one_smul, sub_self] at this
    simp at this
  · intro hP
    have := hq' (Sum.inr (Sum.inr 3))
    simp only [shiftSys, Sum.elim_inr] at this
    rw [hP, neg_one_smul, neg_add_cancel] at this
    simp at this

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
  classical
  have hd1 : 1 ≤ f.natDegree := by rw [hD.deg]; norm_num
  obtain ⟨F, hF, n₀, hlim⟩ := exists_teich_limit hD
  obtain ⟨x, x', w, hT, hw, hrel, htr, hne1, hne2⟩ :=
    exists_spectral_solution_shift f hd1 hlim (fun ν z hz => exists_entry_ne hD hnc ν z hz)
      (window_shift hD hP)
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum_field (K := AlgQ) f hD.monic hD.irr
  set ι : AlgQ →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom with hι
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext hab
  have hrootC : (f.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0 := by
    have := congrArg (algebraMap ℝ ℂ) hD.root
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval_map]
    rw [RingHom.ext_int ((algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ)) (Int.castRingHom ℂ)] at this
    simpa using this
  have halgα : IsAlgebraic ℚ (α : ℂ) := by
    refine ⟨f.map (Int.castRingHom ℚ), (hD.monic.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
        RingHom.ext fun n => by simp]
    exact hrootC
  set α' : AlgQ := ⟨(α : ℂ), (mem_algebraicClosure_iff).2 halgα⟩ with hα'
  have hα'root : (f.map (Int.castRingHom AlgQ)).eval α' = 0 := by
    refine hιinj ?_
    rw [eval_map_int_hom ι f α', map_zero]
    exact hrootC
  obtain ⟨i₀, hi₀⟩ := hsurj α' hα'root
  set σ : Fin 3 ≃ Fin f.natDegree :=
    (finCongr hD.deg.symm).trans (Equiv.swap (finCongr hD.deg.symm 0) i₀) with hσ
  have hσ0 : σ 0 = i₀ := by simp [hσ]
  have he0 : ∀ i, e i ≠ 0 := by
    intro i h0
    have := he i
    rw [h0, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at this
    exact coeff_zero_ne_zero hD.monic hD.irr hD.deg (by simpa using this)
  have hQ1 : 3 ^ F - 1 + 1 = 3 ^ F := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))
  refine ⟨3 ^ F - 1, fun k => e (σ k), fun k => polyVal x (e (σ k)), w, ?_,
    hinj.comp σ.injective, fun k => he _, ?_, ?_, ?_, hw, ?_, ?_, ?_⟩
  · rcases hF with rfl | rfl | ⟨rfl, h3⟩
    · left; norm_num
    · right; left; norm_num
    · right; right; exact ⟨by norm_num, h3⟩
  · show ((e (σ 0) : AlgQ) : ℂ) = α
    rw [hσ0, hi₀]
  · intro k hk
    have hne : e (σ k) ≠ α' := by
      rw [← hi₀, ← hσ0]; exact fun h => hk (σ.injective (hinj h))
    refine hD.small _ ((Polynomial.mem_roots (hD.monic.map _).ne_zero).2 ?_) ?_
    · have := congrArg ι (he (σ k))
      rw [eval_map_int_hom ι f, map_zero] at this
      exact this
    · intro h; apply hne; exact Subtype.ext h
  · intro k
    have := polyVal_pow_succ_eq f hD.monic e he hinj x (Q := 3 ^ F - 1) (by rw [hQ1]; exact hT) (σ k)
    exact this
  · have h := readout_trace f hD.monic e he hinj he0 x x' hrel
    rw [← htr, h]
    exact (Equiv.sum_comp σ (fun i => polyVal x (e i) * e i ^ s))
  · intro hall
    obtain ⟨i, hi⟩ := readout_ne f hD.monic e he hinj x 1 hne1
    exact hi (by simpa using hall (σ.symm i))
  · intro hall
    obtain ⟨i, hi⟩ := readout_ne f hD.monic e he hinj x (-1) hne2
    exact hi (by simpa using hall (σ.symm i))

-- Step 4 (`rigidity_generic`) is proved above.

/-- A constant spectral vector is `±1`. -/
theorem eq_one_or_neg_one_of_const {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3)
    {e : Fin 3 → AlgQ} (hinj : Function.Injective e)
    (he : ∀ k, (f.map (Int.castRingHom AlgQ)).eval (e k) = 0) {s : ℤ} {Q : ℕ} (hQ : 1 ≤ Q)
    {z ω : AlgQ} (hz : z ^ (Q + 1) = z) (hω : ω ^ 2 = 1) (hsum : ∑ k, z * e k ^ s = ω) :
    z = 1 ∨ z = -1 := by
  obtain ⟨q, hq⟩ := sum_zpow_rat hmon hdeg (coeff_zero_ne_zero hmon hirr hdeg) hinj he s
  have hzq : z * (q : AlgQ) = ω := by rw [← hq, Finset.mul_sum]; exact hsum
  have hωpm : ω = 1 ∨ ω = -1 := by
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  obtain ⟨r, hr⟩ : ∃ r : ℚ, ω = r := by
    rcases hωpm with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  have hω0 : ω ≠ 0 := by rcases hωpm with rfl | rfl <;> norm_num
  have hq0 : (q : AlgQ) ≠ 0 := by rintro h; rw [h, mul_zero] at hzq; exact hω0 hzq.symm
  have hzc : z = ((r / q : ℚ) : AlgQ) := by
    push_cast; rw [← hr, ← hzq]; field_simp
  have hz0 : z ≠ 0 := by rintro rfl; rw [zero_mul] at hzq; exact hω0 hzq.symm
  have hzQ : z ^ Q = 1 := by
    have : z * (z ^ Q - 1) = 0 := by rw [mul_sub, ← pow_succ', hz]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz0)
  set c : ℚ := r / q
  have hcQ : c ^ Q = 1 := by
    have : ((c ^ Q : ℚ) : AlgQ) = ((1 : ℚ) : AlgQ) := by push_cast; rw [← hzc]; exact hzQ
    exact_mod_cast this
  have habs : |c| = 1 := by
    have : |c| ^ Q = 1 := by rw [← abs_pow, hcQ, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg c) (by omega)).1 this
  rcases abs_eq (zero_le_one) |>.1 habs with h | h
  · left; rw [hzc, h]; simp
  · right; rw [hzc, h]; simp


theorem cycField_isCyclotomic (Q : ℕ) [NeZero Q] : IsCyclotomicExtension {Q} ℚ (cycField Q) := by
  have hS : {z : AlgQ | z ^ Q = 1} = {b : AlgQ | ∃ n ∈ ({Q} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} := by
    ext z; simp [NeZero.ne Q]
  rw [cycField, hS]
  refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot {Q} ℚ AlgQ ?_
  intro n hn _
  rw [Set.mem_singleton_iff] at hn; subst hn
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (cyclotomic n AlgQ)
    (by rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 (NeZero.pos n)).ne')
  exact ⟨μ, (isRoot_cyclotomic_iff).1 hμ⟩

theorem three_dvd_totient {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {Q : ℕ} [NeZero Q] {x : AlgQ}
    (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) (hxL : x ∈ cycField Q) : 3 ∣ Q.totient := by
  haveI := cycField_isCyclotomic Q
  haveI : FiniteDimensional ℚ (cycField Q) := IsCyclotomicExtension.finiteDimensional {Q} ℚ _
  have hfin : Module.finrank ℚ (cycField Q) = Q.totient :=
    IsCyclotomicExtension.finrank (cycField Q) (cyclotomic.irreducible_rat (NeZero.pos Q))
  set g := f.map (Int.castRingHom ℚ) with hg
  have hgirr : Irreducible g :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).1 hirr
  have hgm : g.Monic := hmon.map _
  have hbr : aeval x g = (f.map (Int.castRingHom AlgQ)).eval x := by
    rw [hg, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]; congr 2
  have hmin : minpoly ℚ x = g :=
    (minpoly.eq_of_irreducible_of_monic hgirr (by rw [hbr]; exact hx) hgm).symm
  have hint : IsIntegral ℚ x := ⟨g, hgm, by rw [← Polynomial.aeval_def, hbr]; exact hx⟩
  have h3 : Module.finrank ℚ ℚ⟮x⟯ = 3 := by
    rw [IntermediateField.adjoin.finrank hint, hmin, hg, hmon.natDegree_map, hdeg]
  have hle : ℚ⟮x⟯ ≤ cycField Q := by
    rw [IntermediateField.adjoin_simple_le_iff]; exact hxL
  have := IntermediateField.finrank_dvd_of_le_right hle
  rwa [h3, hfin] at this

/-- A root of an irreducible integer cubic is not rational. -/
theorem not_mem_cycField_two {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    x ∉ cycField 2 := by
  intro hxL
  have h := three_dvd_totient hmon hirr hdeg hx hxL
  have ht : Nat.totient 2 = 1 := by decide
  omega

/-- A root of an irreducible integer cubic is not in `ℚ(μ_8)` (degree 4). -/
theorem not_mem_cycField_eight {f : ℤ[X]} (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) {x : AlgQ} (hx : (f.map (Int.castRingHom AlgQ)).eval x = 0) :
    x ∉ cycField 8 := by
  intro hxL
  have h := three_dvd_totient hmon hirr hdeg hx hxL
  have ht : Nat.totient 8 = 4 := by decide
  omega

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
  have hgen : (∀ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 → x ∉ cycField Q) →
      False := by
    intro hL
    have hc := rigidity_generic hD.monic hD.irr hD.deg hinj he hbig hsm hs (cycField Q)
      (fun k => mem_cycField (hu k)) (fun k => unimod_of_pow_succ hQ1 (hu k)) hL hω hsum
    have hsum' : ∑ k, u 0 * e k ^ s = ω := by
      rw [← hsum]; exact Finset.sum_congr rfl fun k _ => by rw [hc k]
    rcases eq_one_or_neg_one_of_const hD.monic hD.irr hD.deg hinj he hQ1 (hu 0) hω hsum' with h | h
    · exact hn1 fun k => (hc k).trans h
    · exact hn2 fun k => (hc k).trans h
  rcases hQ with rfl | rfl | ⟨rfl, h3⟩
  · exact hgen fun x hx => not_mem_cycField_two hD.monic hD.irr hD.deg hx
  · exact hgen fun x hx => not_mem_cycField_eight hD.monic hD.irr hD.deg hx
  · by_cases hE : ∃ x : AlgQ, (f.map (Int.castRingHom AlgQ)).eval x = 0 ∧ x ∈ cycField 26
    · obtain ⟨x, hx, hxL⟩ := hE
      exact e1_empty hD hs hP h3 hx hxL
    · exact hgen fun x hx hxL => hE ⟨x, hx, hxL⟩

end LeanFormalizations.Mills.ShiftRigidity
