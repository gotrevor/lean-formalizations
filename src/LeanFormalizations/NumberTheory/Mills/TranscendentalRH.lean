/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Mills' constant is transcendental, assuming RH (Saito 2025, Theorems 1.7–1.8)

K. Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068 (v3, 2025-12-07),
Ramanujan J. (2026); local `papers/saito-2025-transcendency-variants-mills.txt`.  Our route is the
elementary one in `PROBE-MILLS-TRANSCENDENCE.md` (re-derived independently, it lands on Saito's
Theorem 1.7), with RH entering only through `Schoenfeld1976` (already in `RH.lean`).

## Setting

`transcendental_or_pisot` (`Transcendental.lean`, Saito 2024 Thm 1.2): if `A` (least Mills) is
algebraic, some `β = A^(3^m)`, `m ≥ 1`, is a Pisot number of degree 3.  Let `β₂, β₃` be its other
conjugates (`otherConj β`), `N = N_k = 3^(k−m)` (odd), `xᵢ = βᵢ^N`, `s_k = x₂ + x₃ ∈ ℝ`,
`p_k = ⌊A^(3^k)⌋` (the Mills primes; under RH they are `gseq`, `RH.lean`).

## Steps

1. **Traces are the primes** (Saito 2024, Lemma 4.2): `Tr β^N = p_k` for all large `k`.  (Uses
   `ξ^(3^k) − p_k → 0` fast; the degree-2 proof in `SaitoDegreeTwo.lean` may already have it.)
2. **Exact gap identity** (Newton's identities for cubes, pure algebra):
   `p_(k+1) − p_k³ = −3 s_k (x₁² + x₁ s_k + x₂x₃)`.
3. **Sign**: `p_(k+1) > p_k³` (prime, not a cube), and `x₁² + x₁ s + x₂x₃ > 0` for large `k`,
   so `s_k < 0` for all large `k`.
4. **Complex case dies (unconditional).**  If `β₂ = β̄₃ ∉ ℝ`: `s_k = 2|x₂| cos ψ_k`,
   `ψ_(k+1) = 3 ψ_k (mod 2π)`.  Circle lemma (`times_three_orbit`): if `x, 3x, 9x, … (mod 1)`
   all lie in the open interval `(1/4, 3/4)` then `x = 1/2` (by induction `|3ʲx mod 1 − 1/2| =
   3ʲ|x − 1/2| < 1/4`).  So `β₂^N` is real and `β₂^N = β₃^N`; then `β^N ∈ ℚ(β)` has a conjugate of
   multiplicity 2 while its degree is 1 or 3 — impossible (`|β₂| < 1 < β`).
5. **Real case under RH.**  `|β₂| ≠ |β₃|` (else `β₃ = −β₂` and `s_k = 0` for odd `N`); say
   `ρ = |β₂/β₃| > 1`.  Then `|s_k| ≥ |β₂|^N / 2`, `|β₂|² = ρ |β₂β₃| ≥ ρ / β` (norm is a nonzero
   integer), so `p_(k+1) − p_k³ ≥ ρ^(N/2) · √(p_k³)` for large `k`.  Under RH (Schoenfeld) the
   least prime above `x` is `< x + C √x log x`, and `p_(k+1)` is the least prime above `p_k³`
   (greedy chain, `RH.lean`).  `log (p_k³) ≤ 3N log β + O(1)` is linear in `N`, `ρ^(N/2)` is
   exponential: contradiction.

Numbers are Saito's where they match; split into named leaves freely.  Frozen: the two theorems
below (names and statements), every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Mills.Transcendental
import LeanFormalizations.NumberTheory.Mills.RH
import LeanFormalizations.NumberTheory.Mills.SaitoDegreeTwo
import LeanFormalizations.NumberTheory.Transcendence.DubickasNoSubspace

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature Polynomial Filter

/-! ### Leaf 1: elementary complex algebra

`(w³).re` in terms of `w.re` and `‖w‖`: the real-part half of the triple-angle formula, with no
trigonometry.  This is what turns the `×3` map on the circle into a cubic recursion. -/

theorem norm_sq_eq_re_sq_add_im_sq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]; ring

/-- **Triple-angle, real part**: `Re(w³) = 4 (Re w)³ − 3 ‖w‖² (Re w)`. -/
theorem cube_re (w : ℂ) : (w ^ 3).re = 4 * w.re ^ 3 - 3 * ‖w‖ ^ 2 * w.re := by
  have h : ‖w‖ * ‖w‖ = w.re * w.re + w.im * w.im := by
    have := norm_sq_eq_re_sq_add_im_sq w; nlinarith [this]
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  linear_combination (3 * w.re) * h

/-- The complex roots of a rational polynomial are closed under conjugation. -/
theorem conj_mem_aroots {p : ℚ[X]} (hp : p ≠ 0) {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    (starRingEnd ℂ) z ∈ p.aroots ℂ := by
  rw [Polynomial.mem_aroots] at hz ⊢
  refine ⟨hp, ?_⟩
  have h := aeval_algHom_apply ((Complex.conjAe.restrictScalars ℚ) : ℂ →ₐ[ℚ] ℂ) z p
  simpa [hz.2] using h

/-! ### Leaf 2: the `×3` orbit on the circle

If `c j = cos(3ʲ θ)` is negative for every `j`, then `cos θ = −1`.  Stated purely in terms of the
cubic recursion `c_{j+1} = 4c_j³ − 3c_j`, so no trigonometry is needed: negativity forces
`4c² > 3`, and then `c_{j+1} + 1 = (c_j + 1)(2c_j − 1)²` with `(2c_j − 1)² > 4`, so `c_j + 1`
grows like `4ʲ` while staying `≤ 1`. -/
theorem eq_neg_one_of_triple_orbit {c : ℕ → ℝ}
    (hrec : ∀ j, c (j + 1) = 4 * c j ^ 3 - 3 * c j)
    (hlb : ∀ j, -1 ≤ c j) (hneg : ∀ j, c j < 0) : c 0 = -1 := by
  have hsq : ∀ j, 3 < 4 * c j ^ 2 := by
    intro j
    by_contra h
    push Not at h
    have h1 := hneg (j + 1)
    rw [hrec] at h1
    nlinarith [hneg j]
  have hgrow : ∀ j, 4 * (c j + 1) ≤ c (j + 1) + 1 := by
    intro j
    have h1 := hsq j
    have h2 := hneg j
    have h3 := hlb j
    have hfac : (0:ℝ) ≤ (c j + 1) * (4 * c j ^ 2 - 4 * c j - 3) :=
      mul_nonneg (by linarith) (by nlinarith)
    rw [hrec]
    nlinarith [hfac]
  have hpow : ∀ j, (4:ℝ) ^ j * (c 0 + 1) ≤ c j + 1 := by
    intro j
    induction j with
    | zero => simp
    | succ n ih =>
        have := hgrow n
        have h4 : (0:ℝ) < 4 := by norm_num
        calc (4:ℝ) ^ (n + 1) * (c 0 + 1) = 4 * ((4:ℝ) ^ n * (c 0 + 1)) := by ring
          _ ≤ 4 * (c n + 1) := by nlinarith
          _ ≤ c (n + 1) + 1 := this
  by_contra hne
  have hpos : 0 < c 0 + 1 := lt_of_le_of_ne (by linarith [hlb 0]) (by intro h; exact hne (by linarith))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 1 / (c 0 + 1) < (4:ℝ) ^ j := pow_unbounded_of_one_lt _ (by norm_num)
  have h1 : (4:ℝ) ^ j * (c 0 + 1) ≤ 1 := le_trans (hpow j) (by linarith [hneg j])
  have hj' := mul_lt_mul_of_pos_right hj hpos
  rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)] at hj'
  linarith

/-! ### Leaf 3: Newton's identity for cubes

The exact gap identity behind Saito's Theorem 1.7: with `x₁ = βⁿ` and `x₂, x₃` the other
conjugates' `n`-th powers, `Tr(β^{3n}) = Tr(βⁿ)³ − 3 s (x₁² + x₁ s + x₂x₃)` where `s = x₂ + x₃`. -/
theorem newton_cube_gap (x₁ x₂ x₃ : ℂ) :
    (x₁ + x₂ + x₃) ^ 3 - (x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3)
      = 3 * (x₂ + x₃) * (x₁ ^ 2 + x₁ * (x₂ + x₃) + x₂ * x₃) := by ring

/-! ### Leaf 4: an integer within `1/2` of `A^(3ᵏ)` is its floor -/

theorem eq_floor_of_abs_lt_half {A : ℝ} (hA0 : 0 ≤ A) {k : ℕ} {S : ℝ} {t : ℤ}
    (hS : |S| < 1 / 2)
    (hfr : A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2)
    (ht : A ^ ((3:ℕ) ^ k) + S = (t : ℝ)) :
    t = (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) := by
  have hfl : ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℕ) : ℝ) ≤ A ^ ((3:ℕ) ^ k) := Nat.floor_le (by positivity)
  have habs := abs_lt.1 hS
  have hlo : ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℕ) : ℝ) - 1 < (t : ℝ) := by rw [← ht]; linarith
  have hhi : (t : ℝ) < ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℕ) : ℝ) + 1 := by rw [← ht]; linarith
  have h1 : ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℕ) : ℤ) - 1 < t := by exact_mod_cast hlo
  have h2 : t < ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℕ) : ℤ) + 1 := by exact_mod_cast hhi
  omega




/-! ### Steps 1–3: the traces are the Mills primes, and `s_k < 0`

`β = A^(3^m)` is a cubic Pisot number with other conjugates `u, v`.  Write `n = 3ⁱ`,
`x₁ = βⁿ`, `x₂ = uⁿ`, `x₃ = vⁿ`, `s = x₂ + x₃`.  Then `Tr βⁿ = x₁ + s` is a rational integer
within `1/2` of `A^(3^(m+i))`, hence *equal* to the Mills prime `p_{m+i} = ⌊A^(3^(m+i))⌋₊`
(Saito 2024 Lemma 4.2).  Newton's identity for cubes then gives the exact gap

    p_{m+i}³ − p_{m+i+1} = 3 s (x₁² + x₁ s + x₂x₃),

whose left side is negative (`p_{k+1} > p_k³`) while `x₁² + x₁ s + x₂x₃ > 0` for large `i`
(`x₁ → ∞`, `|s| < 1/2`, `|x₂x₃| ≤ 1`).  So `s < 0` for all large `i`. -/

/-- For a Pisot number with exactly two other conjugates, the conjugate power sum is `uⁿ + vⁿ`. -/
theorem conjPowSum_pair {β : ℝ} {u v : ℂ} (huv : otherConj β = {u, v}) (n : ℕ) :
    u ^ n + v ^ n = conjPowSum β n := by
  simp [conjPowSum, huv]

/-- **Step 3**: with `otherConj β = {u, v}`, the real number `s_i = u^(3ⁱ) + v^(3ⁱ)` is
eventually negative. -/
theorem pair_pow_sum_re_neg {A : ℝ} (hA1 : 1 < A) {m : ℕ}
    (hβ : IsPisot (A ^ ((3:ℕ) ^ m))) {u v : ℂ}
    (huv : otherConj (A ^ ((3:ℕ) ^ m)) = {u, v})
    (hcube : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊) ^ 3 < ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊)
    (hfrac : ∀ᶠ k : ℕ in atTop, A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2)
    (hm : 1 ≤ m) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      (u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)).im = 0 ∧
      (u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)).re < 0 := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  set β : ℝ := A ^ ((3:ℕ) ^ m) with hβdef
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0:ℝ) < β := by linarith
  -- the other conjugates are small
  have humem : u ∈ otherConj β := by rw [huv]; simp
  have hvmem : v ∈ otherConj β := by rw [huv]; simp
  have hcM := conjMax_lt_one hβ
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt (norm_le_conjMax humem) hcM
  have hv1 : ‖v‖ < 1 := lt_of_le_of_lt (norm_le_conjMax hvmem) hcM
  have hcard : Multiset.card (otherConj β) = 2 := by rw [huv]; rfl
  -- `βⁿ + uⁿ + vⁿ` is a rational integer
  have hint : ∀ n : ℕ, ∃ t : ℤ, u ^ n + v ^ n = (((t : ℝ) - β ^ n : ℝ) : ℂ) := by
    intro n
    obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ n
    refine ⟨t, ?_⟩
    rw [conjPowSum_pair huv n]
    push_cast
    linear_combination ht
  -- the sum is tiny for large `n`
  have hsmall : ∃ n₁ : ℕ, ∀ n ≥ n₁, ‖u ^ n + v ^ n‖ < 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => (2:ℝ) * conjMax β ^ n) atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (conjMax_nonneg β) hcM).const_mul (2:ℝ)
    obtain ⟨n₁, hn₁⟩ :=
      eventually_atTop.1 (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 2)))
    refine ⟨n₁, fun n hn => ?_⟩
    have h1 := norm_conjPowSum_le β n
    rw [hcard] at h1
    rw [conjPowSum_pair huv n]
    calc ‖conjPowSum β n‖ ≤ ((2:ℕ) : ℝ) * conjMax β ^ n := h1
      _ < 1 / 2 := by push_cast at hn₁ ⊢; exact hn₁ n hn
  obtain ⟨n₁, hn₁⟩ := hsmall
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfrac
  -- `βⁿ ≥ 2` for large `n`
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, ∀ n ≥ n₂, (2:ℝ) ≤ β ^ n := by
    obtain ⟨n₂, hn₂⟩ := pow_unbounded_of_one_lt (2:ℝ) hβ1
    exact ⟨n₂, fun n hn => le_of_lt (lt_of_lt_of_le hn₂ (pow_le_pow_right₀ hβ1.le hn))⟩
  set i₀ : ℕ := max (max n₁ n₂) k₀ with hi₀
  refine ⟨i₀, fun i hi => ?_⟩
  have hipow : ∀ j : ℕ, j ≤ (3:ℕ) ^ j := fun j => (Nat.lt_pow_self (by norm_num)).le
  -- the exponent `n = 3ⁱ` is at least `i`, hence at least all the thresholds
  have hn : n₁ ≤ (3:ℕ) ^ i ∧ n₂ ≤ (3:ℕ) ^ i := by
    have h := le_trans hi (hipow i)
    exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h,
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h⟩
  have hn3 : n₁ ≤ 3 * (3:ℕ) ^ i := le_trans hn.1 (by omega)
  -- `β^(3ⁱ) = A^(3^(m+i))`
  have hpow : ∀ j : ℕ, β ^ ((3:ℕ) ^ j) = A ^ ((3:ℕ) ^ (m + j)) := by
    intro j; rw [hβdef, ← pow_mul, ← pow_add]
  have hpow3 : β ^ (3 * (3:ℕ) ^ i) = A ^ ((3:ℕ) ^ (m + i + 1)) := by
    rw [hβdef, ← pow_mul]
    congr 1
    rw [pow_succ]
    ring
  -- the two traces are the two Mills primes
  obtain ⟨t, ht⟩ := hint ((3:ℕ) ^ i)
  obtain ⟨T, hT⟩ := hint (3 * (3:ℕ) ^ i)
  have htv : t = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ) := by
    refine eq_floor_of_abs_lt_half hA0 (S := ((t : ℝ) - β ^ ((3:ℕ) ^ i)))
      ?_ (hk₀ (m + i) (by omega)) (by rw [← hpow i]; ring)
    have h1 : ‖u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)‖ < 1 / 2 := hn₁ _ hn.1
    rw [ht, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  have hTv : T = (⌊A ^ ((3:ℕ) ^ (m + i + 1))⌋₊ : ℤ) := by
    refine eq_floor_of_abs_lt_half hA0 (S := ((T : ℝ) - β ^ (3 * (3:ℕ) ^ i)))
      ?_ (hk₀ (m + i + 1) (by omega)) (by rw [← hpow3]; ring)
    have h1 : ‖u ^ (3 * (3:ℕ) ^ i) + v ^ (3 * (3:ℕ) ^ i)‖ < 1 / 2 := hn₁ _ hn3
    rw [hT, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  -- abbreviations
  set b : ℝ := β ^ ((3:ℕ) ^ i) with hbdef
  set σ : ℝ := (t : ℝ) - b with hσdef
  have hsu : u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i) = ((σ : ℝ) : ℂ) := ht
  have him : (u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)).im = 0 := by rw [hsu]; simp
  refine ⟨him, ?_⟩
  have hre : (u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)).re = σ := by rw [hsu]; simp
  rw [hre]
  -- the Newton identity, in `ℂ`
  have hx3 : ∀ w : ℂ, w ^ (3 * (3:ℕ) ^ i) = (w ^ ((3:ℕ) ^ i)) ^ 3 := by
    intro w; rw [mul_comm, pow_mul]
  have hkey : ((t : ℝ) : ℂ) ^ 3 - ((T : ℝ) : ℂ)
      = 3 * ((σ : ℝ) : ℂ) * ((((b : ℝ) : ℂ)) ^ 2 + ((b : ℝ) : ℂ) * ((σ : ℝ) : ℂ)
          + u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)) := by
    have hsum : ((b : ℝ) : ℂ) + u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i) = ((t : ℝ) : ℂ) := by
      rw [add_assoc, hsu, hσdef]
      push_cast
      ring
    have hsum3 : ((b : ℝ) : ℂ) ^ 3 + (u ^ ((3:ℕ) ^ i)) ^ 3 + (v ^ ((3:ℕ) ^ i)) ^ 3
        = ((T : ℝ) : ℂ) := by
      have h1 : ((b : ℝ) : ℂ) ^ 3 = ((β ^ (3 * (3:ℕ) ^ i) : ℝ) : ℂ) := by
        rw [hbdef]; push_cast; rw [← pow_mul, mul_comm]
      rw [h1, ← hx3 u, ← hx3 v, add_assoc, hT]
      push_cast
      ring
    have hnc := newton_cube_gap (((b : ℝ) : ℂ)) (u ^ ((3:ℕ) ^ i)) (v ^ ((3:ℕ) ^ i))
    rw [hsum, hsum3, hsu] at hnc
    exact hnc
  -- real part of the identity
  have hreal : (t : ℝ) ^ 3 - (T : ℝ)
      = 3 * σ * (b ^ 2 + b * σ + (u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)).re) := by
    have h := congrArg Complex.re hkey
    simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, pow_succ] using h
  -- the left side is negative
  have hlt : (t : ℝ) ^ 3 - (T : ℝ) < 0 := by
    have h := hcube (m + i) (by omega)
    rw [htv, hTv]
    have : ((⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℕ) : ℝ) ^ 3 < ((⌊A ^ ((3:ℕ) ^ (m + i + 1))⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast
    linarith
  -- the quadratic factor is positive
  have hb2 : (2:ℝ) ≤ b := hn₂ _ hn.2
  have hσabs : |σ| < 1 / 2 := by
    have h1 : ‖u ^ ((3:ℕ) ^ i) + v ^ ((3:ℕ) ^ i)‖ < 1 / 2 := hn₁ _ hn.1
    rw [hsu, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  have hPre : |(u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)).re| ≤ 1 := by
    have h1 : |(u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)).re|
        ≤ ‖u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)‖ := Complex.abs_re_le_norm _
    have h2 : ‖u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)‖ ≤ 1 := by
      rw [norm_mul, norm_pow, norm_pow]
      have := pow_le_one₀ (norm_nonneg u) hu1.le (n := (3:ℕ) ^ i)
      have := pow_le_one₀ (norm_nonneg v) hv1.le (n := (3:ℕ) ^ i)
      nlinarith [pow_nonneg (norm_nonneg u) ((3:ℕ) ^ i), pow_nonneg (norm_nonneg v) ((3:ℕ) ^ i)]
    linarith
  have habs1 := abs_lt.1 hσabs
  have habs2 := abs_le.1 hPre
  have hquad : 0 < b ^ 2 + b * σ + (u ^ ((3:ℕ) ^ i) * v ^ ((3:ℕ) ^ i)).re := by nlinarith
  nlinarith [hreal, hlt, hquad]


/-! ### Step 4: the `×3` orbit kills a complex pair

If the other conjugates are a genuine complex pair `u, ū`, then `s_i = 2 Re(u^(3ⁱ))`, so
`Re(u^(3ⁱ)) < 0` for all large `i`.  Normalising by `‖u‖^(3ⁱ)` turns this into the cubic
orbit of Leaf 2, forcing `u^(3^{i₀})` to be the *negative real* number `−‖u‖^(3^{i₀})`.  Then
`u^N = ū^N` for `N = 3^{i₀}`, the two trace relations at `N` and `2N` give an explicit integer
quadratic killed by `β^N`, and `β^N` collapses to a Pisot number of degree 2 — impossible by
Saito 2024 Lemma 4.3 (`not_pisot_two_of_cube`). -/

/-- **Step 4a**: normalised real parts along the `×3` orbit obey the cubic recursion, so a
conjugate whose powers all have negative real part is eventually a negative real. -/
theorem pow_im_eq_zero_of_re_neg {z : ℂ} (hz : z ≠ 0) {i₀ : ℕ}
    (hneg : ∀ i ≥ i₀, (z ^ ((3:ℕ) ^ i)).re < 0) :
    (z ^ ((3:ℕ) ^ i₀)).im = 0 := by
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hRpos : ∀ j : ℕ, 0 < ‖z‖ ^ ((3:ℕ) ^ (i₀ + j)) := fun j => pow_pos hr0 _
  have hnorm : ∀ j : ℕ, ‖z ^ ((3:ℕ) ^ (i₀ + j))‖ = ‖z‖ ^ ((3:ℕ) ^ (i₀ + j)) := fun j => by
    rw [norm_pow]
  have hstep : ∀ j : ℕ, z ^ ((3:ℕ) ^ (i₀ + (j + 1))) = (z ^ ((3:ℕ) ^ (i₀ + j))) ^ 3 := by
    intro j; rw [← pow_mul, show i₀ + (j + 1) = (i₀ + j) + 1 by ring, pow_succ]
  have hRstep : ∀ j : ℕ,
      ‖z‖ ^ ((3:ℕ) ^ (i₀ + (j + 1))) = (‖z‖ ^ ((3:ℕ) ^ (i₀ + j))) ^ 3 := by
    intro j; rw [← pow_mul, show i₀ + (j + 1) = (i₀ + j) + 1 by ring, pow_succ]
  have key := eq_neg_one_of_triple_orbit
    (c := fun j => (z ^ ((3:ℕ) ^ (i₀ + j))).re / ‖z‖ ^ ((3:ℕ) ^ (i₀ + j)))
    (by
      intro j
      have hcb := cube_re (z ^ ((3:ℕ) ^ (i₀ + j)))
      rw [hnorm j] at hcb
      have hR := (hRpos j).ne'
      show (z ^ ((3:ℕ) ^ (i₀ + (j + 1)))).re / ‖z‖ ^ ((3:ℕ) ^ (i₀ + (j + 1))) = _
      rw [hstep j, hRstep j, hcb]
      field_simp)
    (by
      intro j
      have h1 : |(z ^ ((3:ℕ) ^ (i₀ + j))).re| ≤ ‖z‖ ^ ((3:ℕ) ^ (i₀ + j)) := by
        rw [← hnorm j]; exact Complex.abs_re_le_norm _
      have h2 := (abs_le.1 h1).1
      show -1 ≤ (z ^ ((3:ℕ) ^ (i₀ + j))).re / ‖z‖ ^ ((3:ℕ) ^ (i₀ + j))
      rw [le_div_iff₀ (hRpos j)]
      linarith)
    (by
      intro j
      show (z ^ ((3:ℕ) ^ (i₀ + j))).re / ‖z‖ ^ ((3:ℕ) ^ (i₀ + j)) < 0
      exact div_neg_of_neg_of_pos (hneg (i₀ + j) (by omega)) (hRpos j))
  simp only [Nat.add_zero] at key
  have hR0 : (0:ℝ) < ‖z‖ ^ ((3:ℕ) ^ i₀) := pow_pos hr0 _
  rw [div_eq_iff (ne_of_gt hR0)] at key
  have hsq := norm_sq_eq_re_sq_add_im_sq (z ^ ((3:ℕ) ^ i₀))
  rw [norm_pow] at hsq
  have him2 : (z ^ ((3:ℕ) ^ i₀)).im ^ 2 = 0 := by nlinarith [hsq, key]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 him2

/-- **Step 4b**: if the two other conjugates of a cubic Pisot number `β` have the *same* `N`-th
power, a real number `y`, then the two trace relations at `N` and `2N` exhibit an integer
quadratic killed by `β^N`, so `β^N` is a Pisot number of degree exactly 2. -/
theorem pisot_pow_two_of_pow_eq {β : ℝ} (hβ : IsPisot β) {u v : ℂ}
    (huv : otherConj β = {u, v}) {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hu : u ^ N = (y : ℂ)) (hv : v ^ N = (y : ℂ)) :
    Multiset.card (otherConj (β ^ N)) = 1 ∧ IsPisot (β ^ N) := by
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0:ℝ) < β := by linarith
  have hx1 : 1 < β ^ N := one_lt_pow₀ hβ1 (by omega)
  have humem : u ∈ otherConj β := by rw [huv]; simp
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt (norm_le_conjMax humem) (conjMax_lt_one hβ)
  -- the trace at `N`: `β^N + 2y = t`
  obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ N
  rw [← conjPowSum_pair huv N, hu, hv] at ht
  have htR : β ^ N + 2 * y = (t : ℝ) := by
    have h := congrArg Complex.re ht
    simp [← Complex.ofReal_pow] at h
    linarith
  -- the trace at `2N`: `β^(2N) + 2y² = T`
  obtain ⟨T, hT⟩ := pisot_conjPowSum_add_mem_int hβ (2 * N)
  rw [← conjPowSum_pair huv (2 * N), show (2:ℕ) * N = N * 2 by ring] at hT
  simp only [pow_mul, hu, hv] at hT
  have hTR : (β ^ N) ^ 2 + 2 * y ^ 2 = (T : ℝ) := by
    have h := congrArg Complex.re hT
    simp [← Complex.ofReal_pow] at h
    linarith
  -- the integer quadratic `3x² − 2tx + (t² − 2T) = 0`
  have hquad : 3 * (β ^ N) ^ 2 - 2 * (t : ℝ) * (β ^ N) + ((t : ℝ) ^ 2 - 2 * (T : ℝ)) = 0 := by
    linear_combination (β ^ N - (t : ℝ) - 2 * y) * htR + 2 * hTR
  set q : ℚ[X] := C (3 : ℚ) * X ^ 2 + C (-2 * (t : ℚ)) * X + C ((t : ℚ) ^ 2 - 2 * (T : ℚ))
    with hqdef
  have hqdeg : q.degree = 2 := by
    rw [hqdef]; exact degree_quadratic (by norm_num)
  have hqne : q ≠ 0 := by
    intro h; rw [h] at hqdeg; simp at hqdeg
  have hroot : (aeval (β ^ N) q) = 0 := by
    have hev : (aeval (β ^ N) q)
        = 3 * (β ^ N) ^ 2 - 2 * (t : ℝ) * (β ^ N) + ((t : ℝ) ^ 2 - 2 * (T : ℝ)) := by
      simp only [hqdef, map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
      push_cast
      ring
    rw [hev, hquad]
  have hdegle : (minpoly ℚ (β ^ N)).degree ≤ 2 := by
    rw [← hqdeg]; exact minpoly.degree_le_of_ne_zero ℚ _ hqne hroot
  have hintN : IsIntegral ℚ (β ^ N) := (hβ.2.1.tower_top).pow N
  have hndle : (minpoly ℚ (β ^ N)).natDegree ≤ 2 := natDegree_le_iff_degree_le.2 hdegle
  -- `u^N` is a conjugate of `β^N`, distinct from it
  have hune : u ^ N ≠ (((β ^ N : ℝ)) : ℂ) := by
    intro h
    have h1 : ‖u ^ N‖ = β ^ N := by
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_pow] at h1
    have h2 : ‖u‖ ^ N < 1 := pow_lt_one₀ (norm_nonneg u) hu1 (by omega)
    linarith
  have hmemN : u ^ N ∈ otherConj (β ^ N) := by
    rw [otherConj, Multiset.mem_erase_of_ne hune]
    exact LeanFormalizations.Transcendence.Dubickas.aroots_pow_mem
      (hβ.2.1.tower_top) N (Multiset.mem_of_mem_erase humem)
  have hcard1 : Multiset.card (otherConj (β ^ N)) = 1 := by
    have hc := card_otherConj_add_one hintN
    have hpos : 0 < Multiset.card (otherConj (β ^ N)) :=
      Multiset.card_pos.2 (fun h => by simp [h] at hmemN)
    omega
  refine ⟨hcard1, hx1, hβ.2.1.pow N, ?_⟩
  obtain ⟨w, hw⟩ := Multiset.card_eq_one.1 hcard1
  have hwv : w = u ^ N := by
    rw [hw] at hmemN; exact (Multiset.mem_singleton.1 hmemN).symm
  intro z hz
  have hz' : z ∈ otherConj (β ^ N) := hz
  rw [hw, hwv] at hz'
  have hzu : z = u ^ N := Multiset.mem_singleton.1 hz'
  rw [hzu, norm_pow]
  exact pow_lt_one₀ (norm_nonneg u) hu1 (by omega)

/-- **Saito (2025), Theorem 1.7, first half**: in the Pisot branch of Mills' constant, the two
other conjugates of the cubic Pisot number are real (no complex pair).  Unconditional beyond the
hypotheses of Saito 2024 Thm 1.2. -/
theorem pisot_branch_otherConj_real (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    {A : ℝ} (hA : IsMinMills A) {m : ℕ} (hm : 1 ≤ m) (hP : IsPisot (A ^ (3 ^ m)))
    (h3 : (minpoly ℚ (A ^ (3 ^ m))).natDegree = 3) :
    ∀ z ∈ otherConj (A ^ (3 ^ m)), z.im = 0 := by
  obtain ⟨⟨hA1, hAm⟩, hmin⟩ := hA
  -- the three Mills facts we need about the digits of `A`
  have h36 := saito_lemma36C (c := 3) hB hM (by norm_num) ⟨⟨hA1, hAm⟩, hmin⟩
  have hμ0 : (0:ℝ) < (19 * ((3:ℕ):ℝ)) / 40 - 1 := by norm_num
  have hK0 : (0:ℝ) < (2:ℝ) ^ ((19 * ((3:ℕ):ℝ)) / 40) := Real.rpow_pos_of_pos (by norm_num) _
  have hfrac : ∀ᶠ k : ℕ in atTop, A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2 := by
    filter_upwards [decay_of_lemma36C (c := 3) (by norm_num) hA1 hAm h36,
      eventually_rpow_neg_lt (c := 3) hA1 (by norm_num) hμ0 hK0 (by norm_num : (0:ℝ) < 1 / 2)]
      with k hk hk2
    exact lt_of_le_of_lt hk.2 hk2
  have hprime : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊).Prime :=
    fun k hk => Nat.prime_iff.2 (hAm ⟨k, by omega⟩)
  have hcube : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊) ^ 3 < ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊ := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact mdigitC_pow_lt (c := 3) (by norm_num) hA1 hAm j
  set β : ℝ := A ^ ((3:ℕ) ^ m) with hβdef
  have halg : IsIntegral ℚ β := hP.2.1.tower_top
  intro z hz
  by_contra him
  -- the conjugate pair `z, z̄`
  have hzne : z ≠ (starRingEnd ℂ) z := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact him (by linarith)
  have hne1 : (starRingEnd ℂ) z ≠ ((β : ℝ) : ℂ) := by
    intro h
    have h2 := congrArg Complex.im h
    simp at h2
    exact him (by linarith)
  have hcz : (starRingEnd ℂ) z ∈ otherConj β := by
    rw [otherConj, Multiset.mem_erase_of_ne hne1]
    exact conj_mem_aroots (minpoly.ne_zero halg) (Multiset.mem_of_mem_erase hz)
  have hc2 : Multiset.card (otherConj β) = 2 := by
    have := card_otherConj_add_one halg
    omega
  obtain ⟨M, hM⟩ : ∃ M, otherConj β = z ::ₘ M :=
    ⟨(otherConj β).erase z, (Multiset.cons_erase hz).symm⟩
  have hcardM : Multiset.card M = 1 := by rw [hM] at hc2; simpa using hc2
  have hczM : (starRingEnd ℂ) z ∈ M := by
    rw [hM, Multiset.mem_cons] at hcz
    rcases hcz with h | h
    · exact absurd h.symm hzne
    · exact h
  have hMs : M = {(starRingEnd ℂ) z} := by
    obtain ⟨w, hw⟩ := Multiset.card_eq_one.1 hcardM
    rw [hw] at hczM ⊢
    rw [Multiset.mem_singleton.1 hczM]
  have huv : otherConj β = {z, (starRingEnd ℂ) z} := by rw [hM, hMs]; rfl
  -- the sign step, then the `×3` orbit
  obtain ⟨i₀, hi₀⟩ := pair_pow_sum_re_neg hA1 hP huv hcube hfrac hm
  have hzneg : ∀ i ≥ i₀, (z ^ ((3:ℕ) ^ i)).re < 0 := by
    intro i hi
    have h := (hi₀ i hi).2
    rw [show ((starRingEnd ℂ) z) ^ ((3:ℕ) ^ i) = (starRingEnd ℂ) (z ^ ((3:ℕ) ^ i)) from
      (map_pow _ _ _).symm] at h
    simp only [Complex.add_re, Complex.conj_re] at h
    linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have hzim := pow_im_eq_zero_of_re_neg hz0 hzneg
  set N : ℕ := (3:ℕ) ^ i₀ with hNdef
  have hNpos : 0 < N := Nat.pow_pos (by norm_num)
  set y : ℝ := (z ^ N).re with hydef
  have hu : z ^ N = ((y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hydef, hzim]
  have hv : ((starRingEnd ℂ) z) ^ N = ((y : ℝ) : ℂ) := by
    rw [← map_pow, hu]
    simp
  obtain ⟨hcard1, hPisot⟩ := pisot_pow_two_of_pow_eq hP huv hNpos hu hv
  -- `β^N = A^(3^(m+i₀))` is a Pisot number of degree 2 — impossible
  have hβN : β ^ N = A ^ ((3:ℕ) ^ (m + i₀)) := by rw [hβdef, hNdef, ← pow_mul, ← pow_add]
  obtain ⟨m', hm'⟩ : ∃ m', m + i₀ = m' + 1 := ⟨m + i₀ - 1, by omega⟩
  rw [hβN, hm'] at hcard1 hPisot
  exact not_pisot_two_of_cube hA1 hPisot hcard1 hprime hcube hfrac

/-- **Mills' constant is transcendental, assuming the Riemann Hypothesis** (Saito 2025,
Theorem 1.8; RH via Schoenfeld's explicit prime-counting bound). -/
theorem transcendental_of_RH (hS : Schoenfeld1976) (hRH : RiemannHypothesis)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) : Transcendental ℚ A := by
  sorry

end LeanFormalizations.Mills
