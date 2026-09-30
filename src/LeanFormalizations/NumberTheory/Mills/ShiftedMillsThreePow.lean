/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsLarge

/-!
# Phase 59: `ξ(3^k + s)` is transcendental whenever the 3-free part of even `s` is `≥ 8`

Phase 58 (`ShiftedMillsLarge.xi_shifted_large_transcendental`) needs `3 ∤ s`.  Here
`s = 3^a · s'` with `s'` even, `3 ∤ s'`, `s' ≥ 8`, and the conclusion is the same, conditional only
on `Literature.Saito2025TypeBTrace` and `Literature.Siegel1944SmallestPisot`.

Let `C_k = 3^(k+j) + 3^a s'` with `3^a s' ≤ 3^(j+1)`, and `ξ` the least `A > 1` with `⌊A^(C_k)⌋`
prime for every `k ≥ 1`.

## Route
0. **`a < j`**: `8·3^a ≤ 3^a s' ≤ 3^(j+1)` forces `a + 1 < j + 1`.  So for `k ≥ 1`,
   `C_k = 3^a · D_k` with `D_k = 3^(k+j−a) + s'` and `3 ∤ D_k`.
1. **Saito's hypotheses.**  `C 1 ≥ 1`, doubling and the eventual ratio bound exactly as in
   phase 58 (`largeC_two_mul_le`, `largeC_ratio_of_le` with `s := 3^a s'`).  `(B5′)`: Euler on
   `C_m` is unavailable (`3 ∣ C_m` when `a ≥ 1`), so use `D_m`: with `t = φ(D_m)·i`,
   `3^t ≡ 1 (mod D_m)`, hence `D_m ∣ D_(m+t)` (the phase 58 `largeC_dvd_shift` computation with
   `j − a` in place of `j` and `s'` in place of `s`), hence `C_m = 3^a D_m ∣ 3^a D_(m+t) = C_(m+t)`.
2. **`IsLeast` is unique**, so Saito's `ξ` is ours.  Branch 1: transcendental, done.
3. **Branch 2: `g = 3^b` with `b ≤ a`.**  `g ∣ 3C_k − C_(k+1) = 2·3^a s'`; `C_k` is odd, so `g` is
   odd, so `g ∣ 3^a s'`; then `g ∣ C_k − 3^a s' = 3^(k+j)`, and `gcd(3^a s', 3^(k+j)) = 3^a`
   (`3 ∤ s'`, `k + j ≥ a`), so `g ∣ 3^a`, i.e. `g = 3^b` (`Nat.dvd_prime_pow`).
4. **Pass to `β = ξ^g`**, a cubic Pisot number.  `C_k / g = 3^(k+j−b) + σ` with
   `σ = 3^(a−b) s' ≥ s' ≥ 8`, and `⌊ξ^(C_k)⌋ = ⌊β^(C_k / g)⌋` (`pow_mul`, `g ∣ C_k`).
   - `β^σ > 4 = d + 1` (`ShiftedMillsLarge.four_lt_pisot_pow`).
   - If `minpoly ℤ β ≢ X³ (mod 3)`: `TheoremDMixed.floor_pow_prime_pow_add_not_prime_full` at
     `c = 3`, shift `σ`, gives infinitely many `n` with `⌊β^(3^n + σ)⌋` not prime; take `n ≥ j + 1`,
     write `n = k + j − b` with `k ≥ 1`, and `⌊β^(3^n + σ)⌋ = ⌊ξ^(C_k)⌋` is prime: contradiction.
   - If `minpoly ℤ β ≡ X³ (mod 3)`: `ShiftedMillsLarge.dvd_traceSeq_of_map_eq_X_pow` and Saito's
     trace identity `powTrace β (C_k / g) = ⌊ξ^(C_k)⌋` make the prime `⌊ξ^(C_k)⌋` divisible by 3
     for all large `k`, yet it tends to infinity: contradiction (as in phase 58, with `β`).

Phase 58's statement is the case `a = 0`.  Checked: `scripts/shifted-mills-three-pow-probe.py`
(72 `(a, s')` cases; controls `s' = 4` and Euler-on-`C_m` fail as they should).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.  Decomposing
into named sub-lemmas is progress.
-/

namespace LeanFormalizations.Mills.ShiftedMillsThreePow

open Filter Polynomial LeanFormalizations.Literature
  LeanFormalizations.Mills.TheoremDGeneral LeanFormalizations.Mills.TheoremDMixed
  LeanFormalizations.Mills.ShiftedMillsLarge

/-! ### Step 0: the exponent sequence `C_k = 3^a (3^(k+j) + s)` -/

/-- The exponent sequence `C_k = 3^a · (3^(k+j) + s) = 3^(k+a+j) + 3^a s`. -/
def threePowC (a j s k : ℕ) : ℕ := 3 ^ a * largeC j s k

theorem threePowC_eq (a j s k : ℕ) : threePowC a j s k = 3 ^ (k + (a + j)) + 3 ^ a * s := by
  have h : (3 : ℕ) ^ a * 3 ^ (k + j) = 3 ^ (k + (a + j)) := by
    rw [← pow_add]; congr 1; omega
  simp only [threePowC, largeC, Nat.mul_add, h]

theorem threePowC_pos (a j s k : ℕ) : 0 < threePowC a j s k :=
  Nat.mul_pos (Nat.pow_pos (by norm_num)) (largeC_pos j s k)

/-- `3^a s ≤ C_k`. -/
theorem le_threePowC (a j s k : ℕ) : 3 ^ a * s ≤ threePowC a j s k := by
  rw [threePowC_eq]; exact Nat.le_add_left _ _

/-- `C_k` is odd when `s` is even (both factors are odd). -/
theorem threePowC_odd {s : ℕ} (hs : Even s) (a j k : ℕ) : Odd (threePowC a j s k) :=
  Odd.mul (Odd.pow (by decide)) (largeC_odd hs j k)

/-- Doubling, inherited from `largeC`. -/
theorem threePowC_two_mul_le {s j : ℕ} (hj : s ≤ 3 ^ (j + 1)) (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    2 * threePowC a j s k ≤ threePowC a j s (k + 1) := by
  have h := largeC_two_mul_le hj hk (s := s) (j := j)
  simp only [threePowC]
  calc 2 * (3 ^ a * largeC j s k) = 3 ^ a * (2 * largeC j s k) := by ring
    _ ≤ 3 ^ a * largeC j s (k + 1) := Nat.mul_le_mul le_rfl h

/-- The ratio bound is scale-invariant. -/
theorem threePowC_ratio_of_largeC {s j k : ℕ} (a : ℕ)
    (h : (29 : ℝ) / 10 * largeC j s k ≤ largeC j s (k + 1)) :
    (29 : ℝ) / 10 * threePowC a j s k ≤ threePowC a j s (k + 1) := by
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ a := by positivity
  have hc : ∀ m : ℕ, ((threePowC a j s m : ℕ) : ℝ) = (3 : ℝ) ^ a * ((largeC j s m : ℕ) : ℝ) := by
    intro m; simp only [threePowC]; push_cast; ring
  rw [hc, hc, show (29 : ℝ) / 10 * ((3 : ℝ) ^ a * (largeC j s k : ℕ))
      = (3 : ℝ) ^ a * ((29 : ℝ) / 10 * (largeC j s k : ℕ)) from by ring]
  exact mul_le_mul_of_nonneg_left h hpos

theorem threePowC_ratio_of_le {s j k : ℕ} (a : ℕ) (h : 19 * s ≤ k) :
    (29 : ℝ) / 10 * threePowC a j s k ≤ threePowC a j s (k + 1) :=
  threePowC_ratio_of_largeC a (largeC_ratio_of_le h)

/-- `(B5′)` for `C_k = 3^a (3^(k+j) + s)`: inherited from `largeC_B5` by scaling, which is why
Euler is applied to the 3-free part `D_m` rather than to `C_m` itself. -/
theorem threePowC_B5 {s : ℕ} (hs3 : ¬ 3 ∣ s) (a : ℕ) {j m : ℕ} (hm : 1 ≤ m) :
    ∃ k > m, threePowC a j s m ∣ threePowC a j s k ∧
      (29 : ℝ) / 10 * threePowC a j s k ≤ threePowC a j s (k + 1) := by
  obtain ⟨k, hkm, hdvd, hratio⟩ := largeC_B5 hs3 (j := j) hm
  exact ⟨k, hkm, Nat.mul_dvd_mul_left _ hdvd, threePowC_ratio_of_largeC a hratio⟩

/-! ### Step 3: the Saito period `g` is a power of `3` dividing `3^a` -/

/-- If `g` divides `C_k` for all large `k`, then `g ∣ 3^a`.  `g ∣ 3 C_k − C_(k+1) = 3^a · 2s`,
`C_k` is odd so `g` is odd, hence `g ∣ 3^a s`; also `g ∣ C_k − 3^a s = 3^(k+a+j)`; and
`gcd(3^a s, 3^a 3^(k+j)) = 3^a` because `3 ∤ s`. -/
theorem dvd_three_pow_of_eventually_dvd {s : ℕ} (hs_even : Even s) (hs3 : ¬ 3 ∣ s) {a j g : ℕ}
    (hg : ∀ᶠ k in atTop, g ∣ threePowC a j s k) : g ∣ 3 ^ a := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  set k := max N 1 with hk
  have h1 : g ∣ threePowC a j s k := hN k (le_max_left _ _)
  have h2 : g ∣ threePowC a j s (k + 1) :=
    hN (k + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  have hid : 3 * threePowC a j s k = threePowC a j s (k + 1) + 3 ^ a * (2 * s) := by
    simp only [threePowC, largeC]; ring
  have hgd : g ∣ 3 ^ a * (2 * s) := by
    have h3 : g ∣ 3 * threePowC a j s k := h1.mul_left 3
    rw [hid] at h3
    simpa using Nat.dvd_sub h3 h2
  have hgodd : Odd g := (threePowC_odd hs_even a j k).of_dvd_nat h1
  have hg2 : Nat.Coprime g 2 := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    rw [Nat.odd_iff] at hgodd
    omega
  have hgs : g ∣ 3 ^ a * s := by
    refine Nat.Coprime.dvd_of_dvd_mul_left hg2 ?_
    rwa [show (3 : ℕ) ^ a * (2 * s) = 2 * (3 ^ a * s) from by ring] at hgd
  have hgpow : g ∣ 3 ^ a * 3 ^ (k + j) := by
    have h4 := Nat.dvd_sub h1 hgs
    rw [threePowC_eq] at h4
    have h5 : (3 : ℕ) ^ (k + (a + j)) = 3 ^ a * 3 ^ (k + j) := by
      rw [← pow_add]; congr 1; omega
    rw [h5] at h4
    simpa using h4
  have hcop : Nat.Coprime s (3 ^ (k + j)) :=
    Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hs3))
  have hgg : g ∣ Nat.gcd (3 ^ a * s) (3 ^ a * 3 ^ (k + j)) := Nat.dvd_gcd hgs hgpow
  rwa [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at hgg

/-! ### Step 4: dividing `C_k` by `3^b` -/

theorem threePowC_split {a b : ℕ} (hb : b ≤ a) (j s k : ℕ) :
    threePowC a j s k = 3 ^ b * threePowC (a - b) j s k := by
  simp only [threePowC, ← mul_assoc, ← pow_add]
  congr 2
  omega

theorem threePowC_dvd {a b : ℕ} (hb : b ≤ a) (j s k : ℕ) :
    (3 : ℕ) ^ b ∣ threePowC a j s k :=
  ⟨threePowC (a - b) j s k, threePowC_split hb j s k⟩

theorem threePowC_div {a b : ℕ} (hb : b ≤ a) (j s k : ℕ) :
    threePowC a j s k / 3 ^ b = threePowC (a - b) j s k := by
  rw [threePowC_split hb, Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num))]

/-- **Transcendence of `ξ(3^(k+j) + 3^a s')`** for even `s' ≥ 8` with `3 ∤ s'` and any `a`. -/
theorem xi_shifted_three_pow_transcendental (hS : Saito2025TypeBTrace)
    (hSieg : Siegel1944SmallestPisot) {a s' j : ℕ} (hs_even : Even s') (hs3 : ¬ 3 ∣ s')
    (hs8 : 8 ≤ s') (hj : 3 ^ a * s' ≤ 3 ^ (j + 1)) {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ (3 ^ (k + j) + 3 ^ a * s')⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  classical
  have hpa : 0 < (3 : ℕ) ^ a := Nat.pow_pos (by norm_num)
  -- Step 0: `a < j`
  have haj : a < j := by
    by_contra hcon
    push_neg at hcon
    have h1 : (3 : ℕ) ^ (j + 1) ≤ 3 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (3 : ℕ) ^ (a + 1) = 3 * 3 ^ a := by ring
    have h3 : 8 * 3 ^ a ≤ 3 ^ a * s' := by
      calc 8 * (3 : ℕ) ^ a = 3 ^ a * 8 := by ring
        _ ≤ 3 ^ a * s' := Nat.mul_le_mul le_rfl hs8
    omega
  set j' := j - a with hj'def
  have hjj : a + j' = j := by omega
  have hs'le : s' ≤ 3 ^ (j' + 1) := by
    refine Nat.le_of_mul_le_mul_left ?_ hpa
    calc (3 : ℕ) ^ a * s' ≤ 3 ^ (j + 1) := hj
      _ = 3 ^ (a + (j' + 1)) := by congr 1; omega
      _ = 3 ^ a * 3 ^ (j' + 1) := pow_add 3 a (j' + 1)
  -- recast the frozen statement in terms of `threePowC`
  have hexp : ∀ k, threePowC a j' s' k = 3 ^ (k + j) + 3 ^ a * s' := by
    intro k; rw [threePowC_eq, hjj]
  have hξ' : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ threePowC a j' s' k⌋₊).Prime} ξ := by
    simpa only [hexp] using hξ
  -- Step 1: Saito's hypotheses
  have hC1 : 1 ≤ threePowC a j' s' 1 := threePowC_pos a j' s' 1
  have hC2 : ∀ k ≥ 1, 2 * threePowC a j' s' k ≤ threePowC a j' s' (k + 1) := fun k hk =>
    threePowC_two_mul_le hs'le a hk
  have hC3 : ∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * threePowC a j' s' k
      ≤ threePowC a j' s' (k + 1) := fun K =>
    ⟨max K (19 * s'), le_max_left _ _, threePowC_ratio_of_le a (le_max_right _ _)⟩
  obtain ⟨ξ₀, hleast, hdisj⟩ :=
    hS (threePowC a j' s') hC1 hC2 hC3 (fun m hm => threePowC_B5 hs3 a hm)
  have hxi : ξ₀ = ξ := hleast.unique hξ'
  rw [hxi] at hdisj hleast
  rcases hdisj with htr | ⟨g, hg1, hpisot, hdegQ, K, hK⟩
  · exact htr
  exfalso
  -- Step 3: `g = 3^b` with `b ≤ a`
  have hgdvd : g ∣ 3 ^ a := by
    refine dvd_three_pow_of_eventually_dvd (s := s') hs_even hs3 (a := a) (j := j') (g := g) ?_
    filter_upwards [eventually_ge_atTop (max K (19 * s'))] with k hk
    exact (hK k (le_trans (le_max_left _ _) hk)
      (threePowC_ratio_of_le a (le_trans (le_max_right _ _) hk))).1
  obtain ⟨b, hba, hgb⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hgdvd
  subst hgb
  -- Step 4: pass to `β = ξ^(3^b)`, a cubic Pisot number with shift `σ = 3^(a-b) s'`
  set β : ℝ := ξ ^ (3 : ℕ) ^ b with hβdef
  set σ : ℕ := 3 ^ (a - b) * s' with hσdef
  have hσ8 : 8 ≤ σ := le_trans hs8 (Nat.le_mul_of_pos_left s' (Nat.pow_pos (by norm_num)))
  have hpowβ : ∀ k, β ^ (threePowC (a - b) j' s' k) = ξ ^ (threePowC a j' s' k) := by
    intro k
    rw [hβdef, ← pow_mul, ← threePowC_split hba]
  have hint : IsIntegral ℤ β := hpisot.2.1
  set f : ℤ[X] := minpoly ℤ β with hfdef
  have hmon : f.Monic := minpoly_int_monic hint
  have hirr : Irreducible f := minpoly_int_irreducible hint
  have hdeg3 : f.natDegree = 3 := by rw [hfdef, minpoly_int_natDegree hint, hdegQ]
  have hroot : aeval β f = 0 := minpoly.aeval ℤ β
  have hβ1 : 1 < β := hpisot.1
  have hconj : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (β : ℂ) → ‖z‖ < 1 :=
    minpoly_int_conj_small hpisot
  have hc3 : Nat.Prime 3 := by norm_num
  have hσle : ∀ k, σ ≤ threePowC (a - b) j' s' k := fun k => le_threePowC _ _ _ _
  by_cases hX : f.map (Int.castRingHom (ZMod 3)) = X ^ f.natDegree
  · -- `f ≡ X³ (mod 3)`: the trace, hence the prime floor, is divisible by 3
    obtain ⟨n₀, hn₀⟩ := exists_floor_gt hβ1 (c := 3) (by norm_num) σ 3
    set k := max (max K 1) (max (19 * s') n₀) with hk
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
    have hkK : K ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
    have hks : 19 * s' ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkn : n₀ ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have hratio := threePowC_ratio_of_le (s := s') (j := j') a hks
    have htrace := (hK k hkK hratio).2
    rw [threePowC_div hba] at htrace
    have hprime : (⌊ξ ^ threePowC a j' s' k⌋₊).Prime := hleast.1.2 k hk1
    have hts : ((traceSeq f (threePowC (a - b) j' s' k) : ℤ) : ℂ)
        = ((⌊ξ ^ threePowC a j' s' k⌋₊ : ℕ) : ℂ) := by
      rw [← powTrace_eq_traceSeq hint]; exact htrace
    have htsZ : traceSeq f (threePowC (a - b) j' s' k)
        = ((⌊ξ ^ threePowC a j' s' k⌋₊ : ℕ) : ℤ) := by exact_mod_cast hts
    have hdvd3 : (3 : ℤ) ∣ traceSeq f (threePowC (a - b) j' s' k) := by
      refine dvd_traceSeq_of_map_eq_X_pow f hmon (by omega) hc3 hX ?_
      have h8 := hσle k
      omega
    have hdvdN : (3 : ℕ) ∣ ⌊ξ ^ threePowC a j' s' k⌋₊ := by
      rw [htsZ] at hdvd3
      exact_mod_cast hdvd3
    have heq3 : ⌊ξ ^ threePowC a j' s' k⌋₊ = 3 :=
      ((Nat.Prime.eq_one_or_self_of_dvd hprime 3 hdvdN).resolve_left (by norm_num)).symm
    -- but the floor exceeds 3
    have hnn : k + (a - b + j') = (k + (a - b + j')) := rfl
    have hgt := hn₀ (k + (a - b + j')) (by omega)
    have hrw : (3 : ℕ) ^ (k + (a - b + j')) + σ = threePowC (a - b) j' s' k := by
      rw [threePowC_eq]
    rw [hrw, hpowβ] at hgt
    have hfl : ((⌊ξ ^ threePowC a j' s' k⌋₊ : ℕ) : ℤ) = ⌊ξ ^ threePowC a j' s' k⌋ :=
      Int.natCast_floor_eq_floor (pow_nonneg (by linarith [hleast.1.1]) _)
    rw [heq3] at hfl
    omega
  · -- `f ≢ X³ (mod 3)`: Theorem D produces a non-prime floor
    have hsize : ((f.natDegree : ℝ)) + 1 < β ^ σ := by
      rw [hdeg3]
      have := four_lt_pisot_pow hSieg hpisot hσ8
      push_cast
      linarith
    have hfreq := floor_pow_prime_pow_add_not_prime_full f hmon hirr (by omega) hroot hβ1 hconj
      hc3 hX hsize
    obtain ⟨n, hnp, hnj⟩ :=
      (hfreq.and_eventually (eventually_ge_atTop ((a - b + j') + 1))).exists
    refine hnp ?_
    have hk1 : 1 ≤ n - (a - b + j') := by omega
    have hnn : n = (n - (a - b + j')) + (a - b + j') := by omega
    have hrw : (3 : ℕ) ^ n + σ = threePowC (a - b) j' s' (n - (a - b + j')) := by
      rw [threePowC_eq, ← hnn]
    rw [hrw, hpowβ]
    exact hleast.1.2 _ hk1

end LeanFormalizations.Mills.ShiftedMillsThreePow
