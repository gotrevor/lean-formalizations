/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Brun.Selberg
import LeanFormalizations.NumberTheory.Erdos385.Brun.PairSieve
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Buchstab

/-!
# Selberg's upper bound for the one-class-per-prime problem (phase E5, step 1)

`siftMax_le_selberg`: `S⁺(N, z) ≤ N / G + E²`, with `L = {d ∣ (z−1)# : d ≤ ξ}`,
`G = Σ_{d ∈ L} ∏_{p ∣ d} 1/(p−1)` and `E = Σ_{d ∈ L} ∏_{p ∣ d} p/(p−1)`.

The excluded classes are glued by CRT into one integer `R` (`exists_crt`), so a problem becomes
the sifted set `{(k − R) : k ∈ [lo, lo+N)}` coprime to `(z−1)#`, a `BoundingSieve` with
`ν(d) = 1/d` and `|r_d| ≤ 1`; the optimal Λ² weights of `Brun/Selberg.lean` do the rest.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset ArithmeticFunction Erdos385.Brun

lemma prime_dvd_primorial_iff {p n : ℕ} (hp : p.Prime) : p ∣ primorial n ↔ p ≤ n := by
  constructor
  · intro h
    unfold primorial at h
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    simp only [mem_filter, mem_range] at hq
    have := (Nat.prime_dvd_prime_iff_eq hp hq.2).mp hpq
    omega
  · intro h
    unfold primorial
    exact dvd_prod_of_mem _ (by simp only [mem_filter, mem_range]; exact ⟨by omega, hp⟩)

/-- **CRT**: one integer in every excluded class. -/
lemma exists_crt (r : ℕ → ℤ) (z : ℕ) : ∃ R : ℤ, ∀ q, q.Prime → q < z → (q : ℤ) ∣ R - r q := by
  induction z with
  | zero => exact ⟨0, fun q _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ z ih =>
    obtain ⟨R, hR⟩ := ih
    by_cases hz : z.Prime
    · have hcop : IsCoprime (primorial (z - 1) : ℤ) (z : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hz).mpr ?_)
        rw [prime_dvd_primorial_iff hz]; have := hz.two_le; omega
      obtain ⟨u, v, huv⟩ := hcop
      refine ⟨R * (v * z) + r z * (u * primorial (z - 1)), fun q hq hqz => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hqz with h | h
      · have hqP : (q : ℤ) ∣ (primorial (z - 1) : ℤ) := by
          exact_mod_cast (prime_dvd_primorial_iff hq).mpr (by omega)
        have : R * (v * z) + r z * (u * primorial (z - 1)) - r q =
            (R - r q) + (r z - R) * (u * primorial (z - 1)) := by linear_combination R * huv
        rw [this]
        exact dvd_add (hR q hq h) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hqP _) _)
      · subst h
        have : R * (v * q) + r q * (u * primorial (q - 1)) - r q =
            (q : ℤ) * (R * v - r q * v) := by linear_combination (r q) * huv
        rw [this]; exact dvd_mul_right _ _
    · exact ⟨R, fun q hq hqz => hR q hq (by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hqz with h | h
        · exact h
        · exact absurd (h ▸ hq) hz)⟩

/-- `ν(p) = 1/p`. -/
noncomputable def nuOne : ArithmeticFunction ℝ := prodPrimeFactors (fun p => 1 / (p : ℝ))

lemma nuOne_prime {p : ℕ} (hp : p.Prime) : nuOne p = 1 / p := by
  unfold nuOne; rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]

lemma nuOne_sqfree {d : ℕ} (hd : Squarefree d) : nuOne d = 1 / d := by
  unfold nuOne
  rw [prodPrimeFactors_apply hd.ne_zero, prod_div_distrib, prod_const_one]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

/-- The problem `[lo, lo+N)`, shifted by the CRT representative `R < lo`, as a bounding sieve. -/
noncomputable def probSieve (lo R : ℤ) (N z : ℕ) : BoundingSieve where
  support := (Ico lo (lo + N)).image (fun k => (k - R).toNat)
  prodPrimes := primorial (z - 1)
  prodPrimes_squarefree := squarefree_primorial _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := nuOne
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [nuOne_prime hp]; have := hp.pos; positivity
  nu_lt_one_of_prime := fun p hp _ => by
    rw [nuOne_prime hp, div_lt_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_lt

section Prob

variable {lo R : ℤ} (hR : R < lo) (N z : ℕ)
include hR

lemma probSieve_injOn : Set.InjOn (fun k : ℤ => (k - R).toNat) (Ico lo (lo + N) : Set ℤ) := by
  intro x hx y hy hxy
  simp only [coe_Ico, Set.mem_Ico] at hx hy
  simp only at hxy
  omega

lemma probSieve_multSum (d : ℕ) :
    (probSieve lo R N z).multSum d = #{k ∈ Ico lo (lo + N) | k ≡ R [ZMOD d]} := by
  classical
  unfold BoundingSieve.multSum
  change ∑ m ∈ (Ico lo (lo + N)).image (fun k => (k - R).toNat), (if d ∣ m then (1 : ℝ) else 0) = _
  rw [sum_image (f := fun m => if d ∣ m then (1 : ℝ) else 0) (probSieve_injOn hR N),
    natCast_card_filter]
  refine sum_congr rfl fun k hk => ?_
  have hk' := (mem_Ico.mp hk).1
  have key : d ∣ (k - R).toNat ↔ k ≡ R [ZMOD d] := by
    rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg (by omega), Int.modEq_comm,
      Int.modEq_iff_dvd]
  by_cases h : k ≡ R [ZMOD d] <;> simp [h, key]

lemma probSieve_abs_rem_le {d : ℕ} (hd : d ∣ primorial (z - 1)) :
    |(probSieve lo R N z).rem d| ≤ 1 := by
  have hsq : Squarefree d := (squarefree_primorial _).squarefree_of_dvd hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  unfold BoundingSieve.rem
  rw [probSieve_multSum hR N z d]
  change |(_ : ℝ) - nuOne d * N| ≤ 1
  rw [nuOne_sqfree hsq]
  have hcard := Int.Ico_filter_modEq_card lo (lo + N) (r := (d : ℤ)) (by exact_mod_cast hd0) R
  set a : ℚ := (lo - R : ℚ) / d
  have hb : ((lo + N : ℤ) - R : ℚ) / (d : ℤ) = a + N / d := by
    simp only [a]; push_cast; ring
  have ha : ((lo : ℤ) - R : ℚ) / (d : ℤ) = a := by simp only [a]; push_cast; ring
  rw [hb, ha] at hcard
  set c : ℤ := ⌈a + (N : ℚ) / d⌉ - ⌈a⌉
  have hc1 : (c : ℚ) < N / d + 1 := by
    have h1 := Int.ceil_lt_add_one (a + (N : ℚ) / d)
    have h2 := Int.le_ceil a
    simp only [c]; push_cast; linarith
  have hc2 : (N : ℚ) / d - 1 < c := by
    have h1 := Int.le_ceil (a + (N : ℚ) / d)
    have h2 := Int.ceil_lt_add_one a
    simp only [c]; push_cast; linarith
  have hc1' : (c : ℝ) < N / d + 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hc1; push_cast at this; exact this
  have hc2' : (N : ℝ) / d - 1 < c := by
    have := (Rat.cast_lt (K := ℝ)).mpr hc2; push_cast at this; exact this
  have hNd : 1 / (d : ℝ) * N = N / d := by ring
  have hcardR : ((#{k ∈ Ico lo (lo + N) | k ≡ R [ZMOD d]} : ℕ) : ℝ) = ((max c 0 : ℤ) : ℝ) := by
    rw [← hcard]; push_cast; rfl
  rw [hcardR, abs_le, hNd]
  have hN : (0 : ℝ) ≤ N / d := by positivity
  rcases le_total c 0 with h | h
  · rw [max_eq_right h]; push_cast
    have : (c : ℝ) ≤ 0 := by exact_mod_cast h
    constructor <;> linarith
  · rw [max_eq_left h]; constructor <;> linarith

lemma probSieve_siftedSum {r : ℕ → ℤ} (hcrt : ∀ q, q.Prime → q < z → (q : ℤ) ∣ R - r q) :
    (probSieve lo R N z).siftedSum = sift lo N r z := by
  classical
  unfold BoundingSieve.siftedSum sift
  change ∑ m ∈ (Ico lo (lo + N)).image (fun k => (k - R).toNat),
    (if Nat.Coprime (primorial (z - 1)) m then (1 : ℝ) else 0) = _
  rw [sum_image (f := fun m => if Nat.Coprime (primorial (z - 1)) m then (1 : ℝ) else 0)
    (probSieve_injOn hR N), natCast_card_filter]
  refine sum_congr rfl fun k hk => ?_
  have hk' := (mem_Ico.mp hk).1
  have key : Nat.Coprime (primorial (z - 1)) (k - R).toNat ↔ Survives r z k := by
    have hdv : ∀ q : ℕ, q.Prime → q < z → ((q ∣ (k - R).toNat) ↔ (q : ℤ) ∣ k - r q) := by
      intro q hq hqz
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg (by omega)]
      have : k - r q = (k - R) + (R - r q) := by ring
      rw [this, dvd_add_left (hcrt q hq hqz)]
    constructor
    · intro hc q hq hqz hdq
      have h1 : q ∣ primorial (z - 1) := (prime_dvd_primorial_iff hq).mpr (by omega)
      have h2 : q ∣ (k - R).toNat := (hdv q hq hqz).mpr hdq
      exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one (hc ▸ Nat.dvd_gcd h1 h2))
    · intro hs
      refine Nat.coprime_of_dvd fun q hq h1 h2 => ?_
      have hqz : q < z := by have := (prime_dvd_primorial_iff hq).mp h1; have := hq.two_le; omega
      exact hs q hq hqz ((hdv q hq hqz).mp h2)
  by_cases h : Survives r z k <;> simp [h, key]

lemma probSieve_selbergTerms {d : ℕ} (hd : d ∣ primorial (z - 1)) :
    (probSieve lo R N z).selbergTerms d = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1) := by
  have hsq : Squarefree d := (squarefree_primorial _).squarefree_of_dvd hd
  rw [BoundingSieve.selbergTerms_apply]
  change nuOne d * ∏ p ∈ d.primeFactors, (1 - nuOne p)⁻¹ = _
  unfold nuOne
  rw [prodPrimeFactors_apply hsq.ne_zero, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  rw [prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors, prod_singleton]
  field_simp

lemma probSieve_selbergTerms_div_nu {d : ℕ} (hd : d ∣ primorial (z - 1)) :
    (probSieve lo R N z).selbergTerms d / (probSieve lo R N z).nu d =
      ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hsq : Squarefree d := (squarefree_primorial _).squarefree_of_dvd hd
  rw [probSieve_selbergTerms hR N z hd]
  change _ / nuOne d = _
  unfold nuOne
  rw [prodPrimeFactors_apply hsq.ne_zero, ← prod_div_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  field_simp

end Prob

/-- The level set `L = {d ∣ (z−1)# : d ≤ ξ}`. -/
def levelL (z ξ : ℕ) : Finset ℕ := (primorial (z - 1)).divisors.filter (· ≤ ξ)

/-- `G = Σ_{d ∈ L} ∏_{p ∣ d} 1/(p−1)`. -/
noncomputable def selG (z ξ : ℕ) : ℝ := ∑ d ∈ levelL z ξ, ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)

/-- `E = Σ_{d ∈ L} ∏_{p ∣ d} p/(p−1)`. -/
noncomputable def selE (z ξ : ℕ) : ℝ :=
  ∑ d ∈ levelL z ξ, ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)

/-- **Selberg's upper bound** for one problem. -/
theorem sift_le_selberg (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) (z ξ : ℕ) (hξ : 1 ≤ ξ) :
    (sift lo N r z : ℝ) ≤ N / selG z ξ + selE z ξ ^ 2 := by
  classical
  obtain ⟨R0, hR0⟩ := exists_crt r z
  have hP1 : (1 : ℤ) ≤ (primorial (z - 1) : ℤ) := by exact_mod_cast primorial_pos (z - 1)
  obtain ⟨P, hPdef⟩ : ∃ P : ℤ, P = (primorial (z - 1) : ℤ) := ⟨_, rfl⟩
  rw [← hPdef] at hP1
  set R := R0 - P * |R0 - lo + 1| with hRdef
  have hR : R < lo := by
    have : |R0 - lo + 1| ≤ P * |R0 - lo + 1| := le_mul_of_one_le_left (abs_nonneg _) hP1
    have := le_abs_self (R0 - lo + 1)
    linarith
  have hcrt : ∀ q, q.Prime → q < z → (q : ℤ) ∣ R - r q := by
    intro q hq hqz
    have hqP : (q : ℤ) ∣ P := by
      rw [hPdef]; exact_mod_cast (prime_dvd_primorial_iff hq).mpr (by omega)
    have : R - r q = (R0 - r q) - P * |R0 - lo + 1| := by rw [hRdef]; ring
    rw [this]; exact dvd_sub (hR0 q hq hqz) (dvd_mul_of_dvd_left hqP _)
  set s := probSieve lo R N z with hs
  set L := levelL z ξ with hLdef
  have hLP : L ⊆ s.prodPrimes.divisors := filter_subset _ _
  have hL1 : 1 ∈ L := by
    simp only [hLdef, levelL, mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, (primorial_pos _).ne'⟩, hξ⟩
  have hLcl : ∀ m ∈ L, ∀ d, d ∣ m → d ∈ L := by
    intro m hm d hd
    simp only [hLdef, levelL, mem_filter, Nat.mem_divisors] at hm ⊢
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm.1.1 (primorial_pos _)
    exact ⟨⟨hd.trans hm.1.1, hm.1.2⟩, (Nat.le_of_dvd hm0 hd).trans hm.2⟩
  have hLdvd : ∀ d ∈ L, d ∣ primorial (z - 1) := fun d hd =>
    (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  set w := selbergW s L with hw
  have hupper := s.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w (selbergW_one hLP hL1))
  rw [mainSum_selbergW hLP hL1 hLcl, probSieve_siftedSum hR N z hcrt] at hupper
  have hGeq : selbergG s L = selG z ξ := by
    unfold selbergG selG
    exact sum_congr rfl fun l hl => probSieve_selbergTerms hR N z (hLdvd l hl)
  have hmain : s.totalMass * (1 / selbergG s L) = N / selG z ξ := by
    change (N : ℝ) * _ = _; rw [hGeq]; ring
  have hw0 : ∀ d, d ∉ L → w d = 0 := fun d hd => by simp [hw, selbergW, hd]
  have hwle : ∀ d ∈ L, |w d| ≤ ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := fun d hd =>
    (abs_selbergW_le hLP hLcl hd hL1).trans
      (le_of_eq (probSieve_selbergTerms_div_nu hR N z (hLdvd d hd)))
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ selE z ξ ^ 2 := by
    refine (errSum_lambdaSquared_le s w).trans ?_
    have hrest : ∀ d1 ∈ s.prodPrimes.divisors, d1 ∉ L →
        ∑ d2 ∈ s.prodPrimes.divisors, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| = 0 :=
      fun d1 _ hd1 => sum_eq_zero fun d2 _ => by simp [hw0 d1 hd1]
    rw [← sum_subset hLP hrest]
    have hrest2 : ∀ d1, ∀ d2 ∈ s.prodPrimes.divisors, d2 ∉ L →
        |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| = 0 :=
      fun d1 d2 _ hd2 => by simp [hw0 d2 hd2]
    simp_rw [← sum_subset hLP (hrest2 _)]
    calc ∑ d1 ∈ L, ∑ d2 ∈ L, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)|
        ≤ ∑ d1 ∈ L, ∑ d2 ∈ L, (∏ p ∈ d1.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
            (∏ p ∈ d2.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
          refine sum_le_sum fun d1 hd1 => sum_le_sum fun d2 hd2 => ?_
          have hl : Nat.lcm d1 d2 ∣ primorial (z - 1) := Nat.lcm_dvd (hLdvd d1 hd1) (hLdvd d2 hd2)
          have hrem := probSieve_abs_rem_le hR N z hl
          have h1 := hwle d1 hd1; have h2 := hwle d2 hd2
          calc |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| ≤ |w d1| * |w d2| * 1 := by
                gcongr
            _ ≤ _ := by rw [mul_one]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = selE z ξ ^ 2 := by rw [sq, selE, sum_mul_sum]
  linarith

/-- **Selberg's upper bound** for the extremal count. -/
theorem siftMax_le_selberg (N z ξ : ℕ) (hξ : 1 ≤ ξ) :
    (siftMax N z : ℝ) ≤ N / selG z ξ + selE z ξ ^ 2 := by
  obtain ⟨lo, r, hr⟩ := Nat.sSup_mem (s := {c | ∃ lo r, c = sift lo N r z})
    ⟨_, 0, fun _ => 0, rfl⟩ (bddAbove_sift N z)
  change siftMax N z = _ at hr
  rw [hr]
  exact sift_le_selberg lo N r z ξ hξ

end LeanFormalizations.Erdos385.LinearSieve
