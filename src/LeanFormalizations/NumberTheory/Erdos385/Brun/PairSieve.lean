/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Brun.GLower
import LeanFormalizations.NumberTheory.Erdos385.Brun.Density
import LeanFormalizations.NumberTheory.Erdos385.Brun.Selberg

/-!
# Erdős #385 E2b: the Selberg sieve for prime pairs `n, n + h`

Sift `{n (n + h) : n < N}` by the primes `≤ y`; level `y²` via the optimal Λ² weights on
`L = {d ∣ y# : d ≤ y}`.  Result: `#{n < N : (y#, n(n+h)) = 1} ≤ N/G + y⁶` with
`G ≥ (φ(h)/h) (log t)²/4` whenever `t² ≤ y`.
-/

namespace Erdos385.Brun

open Finset ArithmeticFunction

/-- `ν(p) = ρ(p)/p`. -/
noncomputable def nuP (h p : ℕ) : ℝ := (rho h p : ℝ) / p

lemma two_le_of_prime' {p : ℕ} (hp : p.Prime) : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le

lemma three_le_of_not_dvd {h p : ℕ} (h2 : 2 ∣ h) (hp : p.Prime) (hph : ¬ p ∣ h) : (3 : ℝ) ≤ p := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hph h2
  have := hp.two_le; exact_mod_cast (show 3 ≤ p by omega)

lemma nuP_eq {h p : ℕ} (hp : p.Prime) : nuP h p = if p ∣ h then 1 / (p : ℝ) else 2 / p := by
  unfold nuP; rw [rho_prime h hp]; split_ifs <;> simp

lemma nuP_pos (h : ℕ) {p : ℕ} (hp : p.Prime) : 0 < nuP h p := by
  have := two_le_of_prime' hp
  rw [nuP_eq hp]; split_ifs <;> positivity

lemma nuP_lt_one {h p : ℕ} (h2 : 2 ∣ h) (hp : p.Prime) : nuP h p < 1 := by
  have := two_le_of_prime' hp
  rw [nuP_eq hp]; split_ifs with hph
  · rw [div_lt_one (by linarith)]; linarith
  · have := three_le_of_not_dvd h2 hp hph
    rw [div_lt_one (by linarith)]; linarith

lemma one_sub_nuP_inv_le {h p : ℕ} (h2 : 2 ∣ h) (hp : p.Prime) : (1 - nuP h p)⁻¹ ≤ p := by
  have h2p := two_le_of_prime' hp
  have hlt := nuP_lt_one h2 hp
  rw [inv_le_comm₀ (by linarith) (by linarith)]
  rw [nuP_eq hp]; split_ifs with hph
  · rw [one_div]
    have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2p
    linarith
  · have h3 := three_le_of_not_dvd h2 hp hph
    rw [inv_le_iff_one_le_mul₀ (by linarith), sub_mul, div_mul_cancel₀ _ (by linarith)]
    nlinarith

lemma gS_eq_nuP {h p : ℕ} (h2 : 2 ∣ h) (hp : p.Prime) :
    nuP h p * (1 - nuP h p)⁻¹ = gS h p := by
  have h2p := two_le_of_prime' hp
  unfold gS; rw [nuP_eq hp]; split_ifs with hph
  · have : (1 : ℝ) - 1 / p = (p - 1) / p := by field_simp
    rw [this, inv_div, div_mul_div_cancel₀ (by linarith)]
  · have h3 := three_le_of_not_dvd h2 hp hph
    have : (1 : ℝ) - 2 / p = (p - 2) / p := by field_simp
    rw [this, inv_div, div_mul_div_cancel₀ (by linarith)]

lemma squarefree_primorial (y : ℕ) : Squarefree (primorial y) := by
  unfold primorial
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_) (fun p hp => ?_)
  · simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hp.2 hq.2).mpr hpq)
  · exact (mem_filter.mp hp).2.prime.squarefree

/-- The prime-pair sieve. -/
noncomputable def pairSieve {h : ℕ} (h2 : 2 ∣ h) (y N : ℕ) : BoundingSieve where
  support := (range N).image (fun n => n * (n + h))
  prodPrimes := primorial y
  prodPrimes_squarefree := squarefree_primorial y
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := prodPrimeFactors (nuP h)
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]; exact nuP_pos h hp
  nu_lt_one_of_prime := fun p hp _ => by
    rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]; exact nuP_lt_one h2 hp

section Concrete

variable {h : ℕ} (h2 : 2 ∣ h) (y N : ℕ)

lemma pairSieve_nu_eq {d : ℕ} (hd : d ∣ primorial y) :
    (pairSieve h2 y N).nu d = (rho h d : ℝ) / d := by
  have hsq : Squarefree d := (squarefree_primorial y).squarefree_of_dvd hd
  change prodPrimeFactors (nuP h) d = _
  rw [prodPrimeFactors_apply hsq.ne_zero, rho_eq_prod h hsq]
  have hd' : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [hd']; push_cast; rw [← prod_div_distrib]; rfl

lemma pairSieve_multSum (d : ℕ) :
    (pairSieve h2 y N).multSum d = Nat.count (fun a => d ∣ a * (a + h)) N := by
  unfold BoundingSieve.multSum
  change ∑ m ∈ (range N).image (fun n => n * (n + h)), (if d ∣ m then (1 : ℝ) else 0) = _
  have hinj : Set.InjOn (fun n => n * (n + h)) (range N : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : a * (a + h) < b * (b + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
    · have : b * (b + h) < a * (a + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
  rw [sum_image (f := fun m => if d ∣ m then (1 : ℝ) else 0) hinj, Nat.count_eq_card_filter_range,
    ← sum_boole]

lemma pairSieve_abs_rem_le {d : ℕ} (hd : d ∣ primorial y) :
    |(pairSieve h2 y N).rem d| ≤ d := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (primorial_pos y)
  unfold BoundingSieve.rem
  rw [pairSieve_multSum, pairSieve_nu_eq h2 y N hd]
  change |(Nat.count (fun a => d ∣ a * (a + h)) N : ℝ) - rho h d / d * N| ≤ d
  rw [show (rho h d : ℝ) / d * N = N * rho h d / d by ring]
  exact (abs_count_dvd_sub_le h hd0 N).trans (by exact_mod_cast rho_le h d)

lemma pairSieve_siftedSum :
    (pairSieve h2 y N).siftedSum =
      #{n ∈ range N | Nat.Coprime (primorial y) (n * (n + h))} := by
  unfold BoundingSieve.siftedSum
  change ∑ m ∈ (range N).image (fun n => n * (n + h)),
    (if Nat.Coprime (primorial y) m then (1 : ℝ) else 0) = _
  have hinj : Set.InjOn (fun n => n * (n + h)) (range N : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : a * (a + h) < b * (b + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
    · have : b * (b + h) < a * (a + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
  rw [sum_image (f := fun m => if Nat.Coprime (primorial y) m then (1 : ℝ) else 0) hinj,
    ← sum_boole]

lemma pairSieve_selbergTerms {l : ℕ} (hl : l ∣ primorial y) :
    (pairSieve h2 y N).selbergTerms l = prodPF (gS h) l := by
  have hsq : Squarefree l := (squarefree_primorial y).squarefree_of_dvd hl
  rw [BoundingSieve.selbergTerms_apply]
  change prodPrimeFactors (nuP h) l * ∏ p ∈ l.primeFactors, (1 - prodPrimeFactors (nuP h) p)⁻¹ = _
  rw [prodPrimeFactors_apply hsq.ne_zero, ← prod_mul_distrib]
  unfold prodPF
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors, prod_singleton, gS_eq_nuP h2 hp']

lemma selbergTerms_div_nu_le {d : ℕ} (hd : d ∣ primorial y) :
    (pairSieve h2 y N).selbergTerms d / (pairSieve h2 y N).nu d ≤ d := by
  have hsq : Squarefree d := (squarefree_primorial y).squarefree_of_dvd hd
  have hν : (pairSieve h2 y N).nu d ≠ 0 := BoundingSieve.nu_ne_zero (s := pairSieve h2 y N) hd
  rw [BoundingSieve.selbergTerms_apply, mul_div_cancel_left₀ _ hν]
  have hd' : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [hd']
  refine prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp' := Nat.prime_of_mem_primeFactors hp
    change 0 ≤ (1 - prodPrimeFactors (nuP h) p)⁻¹
    rw [prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors, prod_singleton]
    exact inv_nonneg.mpr (by linarith [nuP_lt_one h2 hp'])
  · have hp' := Nat.prime_of_mem_primeFactors hp
    change (1 - prodPrimeFactors (nuP h) p)⁻¹ ≤ p
    rw [prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors, prod_singleton]
    exact one_sub_nuP_inv_le h2 hp'

/-- The level set `L = {d ∣ y# : d ≤ y}`. -/
def levelSet : Finset ℕ := (primorial y).divisors.filter (· ≤ y)

lemma levelSet_eq : levelSet y = (Icc 1 y).filter Squarefree := by
  ext d
  simp only [levelSet, mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hd, -⟩, hdy⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (primorial_pos y), hdy⟩,
      (squarefree_primorial y).squarefree_of_dvd hd⟩
  · rintro ⟨⟨hd1, hdy⟩, hsq⟩
    refine ⟨⟨?_, (primorial_pos y).ne'⟩, hdy⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    unfold primorial
    refine prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
    simp only [mem_filter, mem_range]
    exact ⟨by have := Nat.le_of_mem_primeFactors hp; omega, Nat.prime_of_mem_primeFactors hp⟩

end Concrete

/-- **Selberg upper bound for prime pairs.**  For even `h ≠ 0`, `2 ≤ t`, `t² ≤ y`:
`#{n < N : (y#, n(n+h)) = 1} ≤ N · 4h/(φ(h) log² t) + y⁶`. -/
theorem card_sifted_le {h : ℕ} (h2 : 2 ∣ h) (hh : h ≠ 0) {y t : ℕ} (hty : t * t ≤ y)
    (ht : 2 ≤ t) (N : ℕ) :
    (#{n ∈ range N | Nat.Coprime (primorial y) (n * (n + h))} : ℝ) ≤
      N * (4 * h / (Nat.totient h * Real.log t ^ 2)) + (y : ℝ) ^ 6 := by
  classical
  set s := pairSieve h2 y N with hs
  set L := levelSet y with hLdef
  have hy : 1 ≤ y := by nlinarith
  have hLP : L ⊆ s.prodPrimes.divisors := filter_subset _ _
  have hL1 : 1 ∈ L := by
    simp only [hLdef, levelSet, mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, (primorial_pos y).ne'⟩, hy⟩
  have hLcl : ∀ m ∈ L, ∀ d, d ∣ m → d ∈ L := by
    intro m hm d hd
    simp only [hLdef, levelSet, mem_filter, Nat.mem_divisors] at hm ⊢
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm.1.1 (primorial_pos y)
    exact ⟨⟨hd.trans hm.1.1, hm.1.2⟩, (Nat.le_of_dvd hm0 hd).trans hm.2⟩
  have hLy : ∀ d ∈ L, d ≤ y := fun d hd => (mem_filter.mp hd).2
  have hLdvd : ∀ d ∈ L, d ∣ primorial y := fun d hd =>
    (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  set w := selbergW s L with hw
  have hupper := s.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w (selbergW_one hLP hL1))
  rw [mainSum_selbergW hLP hL1 hLcl, pairSieve_siftedSum] at hupper
  -- main term
  have hG := selbergG_pos hLP hL1
  have hGlow : (Nat.totient h : ℝ) / h * Real.log t ^ 2 / 4 ≤ selbergG s L := by
    have := G_lower h2 hh hty
    rw [← levelSet_eq] at this
    refine this.trans (le_of_eq ?_)
    unfold selbergG
    exact sum_congr rfl fun l hl => (pairSieve_selbergTerms h2 y N (hLdvd l hl)).symm
  have hφ : (0 : ℝ) < Nat.totient h := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hh)
  have hh' : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hlow0 : 0 < (Nat.totient h : ℝ) / h * Real.log t ^ 2 / 4 := by positivity
  have hmain : s.totalMass * (1 / selbergG s L) ≤
      N * (4 * h / (Nat.totient h * Real.log t ^ 2)) := by
    change (N : ℝ) * (1 / selbergG s L) ≤ _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    calc 1 / selbergG s L ≤ 1 / ((Nat.totient h : ℝ) / h * Real.log t ^ 2 / 4) :=
          one_div_le_one_div_of_le hlow0 hGlow
      _ = _ := by field_simp
  -- error term
  have hw0 : ∀ d, d ∉ L → w d = 0 := fun d hd => by simp [hw, selbergW, hd]
  have hwle : ∀ d ∈ L, |w d| ≤ y := fun d hd =>
    (abs_selbergW_le hLP hLcl hd hL1).trans
      ((selbergTerms_div_nu_le h2 y N (hLdvd d hd)).trans (by exact_mod_cast hLy d hd))
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ (y : ℝ) ^ 6 := by
    refine (errSum_lambdaSquared_le s w).trans ?_
    have hrest : ∀ d1 ∈ s.prodPrimes.divisors, d1 ∉ L →
        ∑ d2 ∈ s.prodPrimes.divisors, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| = 0 :=
      fun d1 _ hd1 => sum_eq_zero fun d2 _ => by simp [hw0 d1 hd1]
    rw [← sum_subset hLP hrest]
    have hrest2 : ∀ d1, ∀ d2 ∈ s.prodPrimes.divisors, d2 ∉ L →
        |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| = 0 :=
      fun d1 d2 _ hd2 => by simp [hw0 d2 hd2]
    simp_rw [← sum_subset hLP (hrest2 _)]
    have hcard : (L.card : ℝ) ≤ y := by
      have : L.card ≤ y := by
        rw [hLdef, levelSet_eq]
        exact (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    calc ∑ d1 ∈ L, ∑ d2 ∈ L, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)|
        ≤ ∑ d1 ∈ L, ∑ d2 ∈ L, (y : ℝ) * y * (y * y) := by
          refine sum_le_sum fun d1 hd1 => sum_le_sum fun d2 hd2 => ?_
          have hl : Nat.lcm d1 d2 ∣ primorial y := Nat.lcm_dvd (hLdvd d1 hd1) (hLdvd d2 hd2)
          have hrem : |s.rem (Nat.lcm d1 d2)| ≤ y * y := by
            refine (pairSieve_abs_rem_le h2 y N hl).trans ?_
            have : Nat.lcm d1 d2 ≤ y * y :=
              (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_dvd_of_pos (hLdvd d1 hd1) (primorial_pos y)) (Nat.pos_of_dvd_of_pos (hLdvd d2 hd2) (primorial_pos y))) (Nat.lcm_dvd_mul d1 d2)).trans (Nat.mul_le_mul (hLy d1 hd1) (hLy d2 hd2))
            exact_mod_cast this
          have := hwle d1 hd1; have := hwle d2 hd2
          gcongr
      _ = (L.card : ℝ) ^ 2 * (y : ℝ) ^ 4 := by simp [sum_const]; ring
      _ ≤ (y : ℝ) ^ 2 * (y : ℝ) ^ 4 := by gcongr
      _ = (y : ℝ) ^ 6 := by ring
  linarith

end Erdos385.Brun
