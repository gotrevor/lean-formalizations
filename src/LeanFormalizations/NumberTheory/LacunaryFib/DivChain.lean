/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.LacunaryFib.Boundary
import LeanFormalizations.Literature.Diophantine

/-!
# Divisibility chains: ratio-two rigidity from Roth (2026-10-05)

If `n k ∣ n (k + 1)` for every `k`, then `F_(n k) ∣ F_(n J)` for `k ≤ J` (`Nat.fib_dvd`), so the
partial sum `S_J = ∑_(k ≤ J) 1/F_(n k)` has denominator dividing the single number `F_(n J)`, not
the product.  The error `x − S_J` is about `1/F_(n (J+1))`, so `|x − S_J| ≪ q^(−n_(J+1)/n_J)` with
`q = F_(n J)`.  In a chain the ratio `n_(J+1)/n_J` is an integer `≥ 2`.  If it is not eventually
`2`, it is `≥ 3` infinitely often, and exponent `3 > 2` contradicts Roth for algebraic irrational
`x`.  Exponent `> 1` already excludes rational `x`, since the tail is positive.  If it is eventually
`2`, Millin makes `x` algebraic (`algebraic_of_eventually_doubling`).

So `RatioTwoRigidity` holds on divisibility chains, and in particular `RestrictedRigidity` (every
`2^(e k)`) holds outright.  The Sturmian case left open in `Boundary.lean` is **closed**: it was
open only in my map, not in mathematics.  The leftover crux is sequences **without** divisibility
(`n_(k+1) = 2 n_k + 1`), where the partial-sum denominators are products.

Novelty: modest (~40%).  It is the "small denominators" group of Nguyen 2022's introduction
(Mignotte, Badea), run at the ratio-two boundary with the chain structure.  The `iff`
classification was not found in the sources read so far.  Strip the specific (not yet stated): the
`→` direction needs only a strong divisibility sequence with exponential growth.  The `←` direction
needs Millin's telescoping, i.e. a Lucas sequence whose root `α` is a unit of norm `−1` (Fibonacci,
Pell).
-/

namespace LeanFormalizations.LacunaryFib

open Filter Real LeanFormalizations.Literature
open scoped goldenRatio

/-- Binet lower bound, two steps at a time. -/
theorem gold_pow_le_fib (m : ℕ) : φ ^ m ≤ Nat.fib (m + 2) ∧ φ ^ (m + 1) ≤ Nat.fib (m + 3) := by
  induction m with
  | zero => norm_num [Nat.fib_add_two]; linarith [goldenRatio_lt_two]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h := Nat.fib_add_two (n := m + 2)
    rw [show m + 1 + 3 = m + 2 + 2 by ring, h]; push_cast
    have : φ ^ (m + 1 + 1) = φ ^ m * φ ^ 2 := by ring
    rw [this, goldenRatio_sq, show m + 2 + 1 = m + 3 by ring]
    nlinarith [ih.1, ih.2, pow_succ φ m]

/-- Binet upper bound, two steps at a time. -/
theorem fib_le_gold_pow (m : ℕ) : (Nat.fib (m + 1) : ℝ) ≤ φ ^ m ∧ (Nat.fib (m + 2) : ℝ) ≤ φ ^ (m + 1) := by
  induction m with
  | zero => norm_num; linarith [one_lt_goldenRatio]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h := Nat.fib_add_two (n := m + 1)
    rw [show m + 1 + 2 = m + 1 + 2 by ring, h]; push_cast
    have : φ ^ (m + 1 + 1) = φ ^ m * φ ^ 2 := by ring
    rw [this, goldenRatio_sq, show m + 1 + 1 = m + 2 by ring]
    nlinarith [ih.1, ih.2, pow_succ φ m]

/-- `φ^m ≤ φ² F_m` for `m ≥ 1`. -/
theorem gold_pow_le_sq_mul_fib {m : ℕ} (hm : 1 ≤ m) : φ ^ m ≤ φ ^ 2 * Nat.fib m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases k with _ | k
  · norm_num
  · have := (gold_pow_le_fib k).1
    rw [show k + 1 + 1 = k + 2 by ring, pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left this (by positivity)

/-- `F_m φ ≤ φ^m` for `m ≥ 1`. -/
theorem fib_mul_gold_le {m : ℕ} (hm : 1 ≤ m) : (Nat.fib m : ℝ) * φ ≤ φ ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]; exact mul_le_mul_of_nonneg_right (fib_le_gold_pow k).1 goldenRatio_pos.le

/-- A strictly monotone sequence of naturals gains at least one per step. -/
theorem strictMono_add_le {n : ℕ → ℕ} (hmono : StrictMono n) (a i : ℕ) : n a + i ≤ n (a + i) := by
  induction i with
  | zero => simp
  | succ i ih => have : n (a + i) < n (a + i + 1) := hmono (by omega); rw [show a + (i + 1) = a + i + 1 by ring]; omega

/-- `1/F_m ≤ φ²/φ^m` for `m ≥ 1`. -/
theorem inv_fib_le {m : ℕ} (hm : 1 ≤ m) : ((Nat.fib m : ℝ))⁻¹ ≤ φ ^ 2 / φ ^ m := by
  have hF : (0 : ℝ) < Nat.fib m := by exact_mod_cast Nat.fib_pos.2 (by omega)
  rw [inv_eq_one_div, div_le_div_iff₀ hF (by positivity)]
  linarith [gold_pow_le_sq_mul_fib hm]

/-- Tail bound: `0 < ∑_{i} 1/F_(n (i+a)) ≤ φ^4 / φ^(n a)`. -/
theorem tail_bound (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (a : ℕ) :
    Summable (fun i => ((Nat.fib (n (i + a)) : ℝ))⁻¹) ∧
    0 < ∑' i, ((Nat.fib (n (i + a)) : ℝ))⁻¹ ∧
    ∑' i, ((Nat.fib (n (i + a)) : ℝ))⁻¹ ≤ φ ^ 4 / φ ^ (n a) := by
  have hφ := one_lt_goldenRatio
  have hg : Summable (fun i : ℕ => φ ^ 2 / φ ^ (n a) * (φ⁻¹) ^ i) :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hφ)).mul_left _
  have hle : ∀ i, ((Nat.fib (n (i + a)) : ℝ))⁻¹ ≤ φ ^ 2 / φ ^ (n a) * (φ⁻¹) ^ i := by
    intro i
    refine (inv_fib_le (hpos _)).trans ?_
    have h1 : n a + i ≤ n (i + a) := by rw [add_comm i]; exact strictMono_add_le hmono a i
    rw [inv_pow, ← div_eq_mul_inv, div_div, ← pow_add]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hφ.le h1)
  have hs : Summable (fun i => ((Nat.fib (n (i + a)) : ℝ))⁻¹) :=
    hg.of_nonneg_of_le (fun i => by positivity) hle
  refine ⟨hs, ?_, ?_⟩
  · refine hs.tsum_pos (fun i => by positivity) 0 ?_
    have : 0 < Nat.fib (n (0 + a)) := Nat.fib_pos.2 (hpos _)
    positivity
  · refine (hs.tsum_le_tsum hle hg).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hφ)]
    have key : (1 - φ⁻¹)⁻¹ = φ ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      have h := goldenRatio_sq; have := goldenRatio_ne_zero
      rw [sub_mul, one_mul, pow_two, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
      linear_combination h
    rw [key]; ring

/-- **Divisibility-chain rigidity (proved, from Roth).**  Route in the module docstring:
partial sums `p / F_(n J)`, error `≤ 2 / F_(n (J+1))`, and Binet bounds
`φ^(m−2) ≤ F_m ≤ φ^(m−1)` turn ratio `≥ 3` into `|x − r| < C r.den^(−3)` for infinitely many
distinct `r`.  The reduced denominator only helps. -/
theorem divChain_rigidity (hR : Roth1955) (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (hmono : StrictMono n) (hdiv : ∀ k, n k ∣ n (k + 1)) :
    IsAlgebraic ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) ↔ ∀ᶠ k in atTop, n (k + 1) = 2 * n k := by
  constructor
  swap
  · exact algebraic_of_eventually_doubling n hpos
  intro halg
  by_contra hne
  have hφ := one_lt_goldenRatio
  have hφ0 := goldenRatio_pos
  set f : ℕ → ℝ := fun k => ((Nat.fib (n k) : ℝ))⁻¹ with hf
  have hFpos : ∀ k, (0 : ℝ) < Nat.fib (n k) := fun k => by exact_mod_cast Nat.fib_pos.2 (hpos k)
  have hs : Summable f := by
    have := (tail_bound n hpos hmono 0).1; simpa using this
  -- chain divisibility and ratio facts
  have hch : ∀ k j, k ≤ j → n k ∣ n j := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact dvd_rfl
    | succ j _ ih => exact ih.trans (hdiv j)
  have hratio : ∀ J, 2 * n J ≤ n (J + 1) ∧ (n (J + 1) ≠ 2 * n J → 3 * n J ≤ n (J + 1)) := by
    intro J
    obtain ⟨c, hc⟩ := hdiv J
    have hlt := hmono (Nat.lt_succ_self J)
    have hp := hpos J
    rw [hc] at hlt ⊢
    have hc2 : 2 ≤ c := by
      by_contra h; interval_cases c <;> simp at hlt
    refine ⟨by rw [mul_comm]; exact Nat.mul_le_mul_left _ hc2, fun h => ?_⟩
    have : c ≠ 2 := by rintro rfl; exact h (by ring)
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  -- partial sums
  let r : ℕ → ℚ := fun J => ∑ k ∈ Finset.range (J + 1), ((Nat.fib (n k) : ℚ))⁻¹
  let T : ℕ → ℝ := fun J => ∑' i, ((Nat.fib (n (i + (J + 1))) : ℝ))⁻¹
  have hsplit : ∀ J, ∑' k, f k = (r J : ℝ) + T J := by
    intro J
    rw [← hs.sum_add_tsum_nat_add (J + 1)]
    simp [r, T, f]
  have hP : ∀ J, (r J : ℝ) * Nat.fib (n J) =
      ((∑ k ∈ Finset.range (J + 1), Nat.fib (n J) / Nat.fib (n k) : ℕ) : ℝ) := by
    intro J
    simp only [r]; push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.cast_div (Nat.fib_dvd _ _ (hch k J (by simp at hk; omega))) (hFpos k).ne']
    field_simp [(hFpos k).ne']
  have hden : ∀ J, ((r J).den : ℝ) ≤ Nat.fib (n J) := by
    intro J
    set P := ∑ k ∈ Finset.range (J + 1), Nat.fib (n J) / Nat.fib (n k)
    have hq : r J = ((P : ℤ) : ℚ) / ((Nat.fib (n J) : ℤ) : ℚ) := by
      have h := hP J
      have hF : ((Nat.fib (n J) : ℚ)) ≠ 0 := by exact_mod_cast (hFpos J).ne'
      rw [eq_div_iff (by exact_mod_cast hF)]
      exact_mod_cast h
    have hd := Rat.den_dvd (P : ℤ) (Nat.fib (n J) : ℤ)
    rw [← Rat.divInt_eq_div] at hq
    rw [← hq] at hd
    have := Int.le_of_dvd (by exact_mod_cast Nat.fib_pos.2 (hpos J)) hd
    exact_mod_cast this
  have hT : ∀ J, 0 < T J ∧ T J * φ ^ n (J + 1) ≤ φ ^ 4 := by
    intro J
    obtain ⟨-, h1, h2⟩ := tail_bound n hpos hmono (J + 1)
    exact ⟨h1, by rwa [le_div_iff₀ (by positivity)] at h2⟩
  have hFle : ∀ J, (Nat.fib (n J) : ℝ) * φ ≤ φ ^ n J := fun J => fib_mul_gold_le (hpos J)
  have hid : ∀ J, J ≤ n J := hmono.id_le
  -- irrationality
  have hirr : Irrational (∑' k, f k) := by
    rintro ⟨q, hq⟩
    have key : ∀ J, φ ^ n J ≤ q.den * φ ^ 3 := by
      intro J
      set P := ∑ k ∈ Finset.range (J + 1), Nat.fib (n J) / Nat.fib (n k)
      have hx := hsplit J
      rw [← hq, Rat.cast_def] at hx
      have hden0 : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hz : (((q.num * Nat.fib (n J) - P * q.den : ℤ)) : ℝ) = q.den * Nat.fib (n J) * T J := by
        push_cast
        have := hP J
        have e : T J = q.num / q.den - r J := by linarith
        rw [e, mul_sub, ← this]; field_simp
      have hzpos : (0 : ℝ) < ((q.num * Nat.fib (n J) - P * q.den : ℤ) : ℝ) := by
        rw [hz]; have := (hT J).1; have := hFpos J; positivity
      have hz1 : (1 : ℝ) ≤ ((q.num * Nat.fib (n J) - P * q.den : ℤ) : ℝ) := by
        have : (0 : ℤ) < q.num * Nat.fib (n J) - P * q.den := by exact_mod_cast hzpos
        exact_mod_cast this
      rw [hz] at hz1
      -- 1 ≤ den F T, F φ ≤ φ^m, T φ^(2m) ≤ T φ^(n(J+1)) ≤ φ^4
      have hTm : T J * (φ ^ n J * φ ^ n J) ≤ φ ^ 4 := by
        refine le_trans ?_ (hT J).2
        rw [← pow_add]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hφ.le (by have := (hratio J).1; omega))
          (hT J).1.le
      have hu : 0 < φ ^ n J := by positivity
      have h1 : φ * φ ^ n J ≤ φ * (q.den * (Nat.fib (n J) * T J)) * φ ^ n J := by
        rw [show φ * φ ^ n J = φ * 1 * φ ^ n J by ring,
          show (q.den : ℝ) * (Nat.fib (n J) * T J) = q.den * Nat.fib (n J) * T J by ring]
        gcongr
      have h2 : φ * (q.den * (Nat.fib (n J) * T J)) * φ ^ n J
          = q.den * (Nat.fib (n J) * φ) * (T J * φ ^ n J) := by ring
      have h3 : (Nat.fib (n J) * φ) * (T J * φ ^ n J) ≤ φ ^ n J * (T J * φ ^ n J) :=
        mul_le_mul_of_nonneg_right (hFle J) (by have := (hT J).1; positivity)
      have h4 : φ ^ n J * (T J * φ ^ n J) ≤ φ ^ 4 := by nlinarith [hTm]
      have h5 : φ * φ ^ n J ≤ q.den * φ ^ 4 := by
        rw [h2] at h1
        calc φ * φ ^ n J ≤ q.den * (Nat.fib (n J) * φ) * (T J * φ ^ n J) := h1
          _ = q.den * ((Nat.fib (n J) * φ) * (T J * φ ^ n J)) := by ring
          _ ≤ q.den * φ ^ 4 := mul_le_mul_of_nonneg_left (h3.trans h4) hden0.le
      have : φ * φ ^ n J ≤ φ * (q.den * φ ^ 3) := by
        calc _ ≤ _ := h5
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hφ0
    obtain ⟨J, hJ⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hφ).eventually_gt_atTop
      ((q.den : ℝ) * φ ^ 3)).exists
    exact absurd ((pow_le_pow_right₀ hφ.le (hid J)).trans (key J)) (not_le.2 hJ)
  -- Roth
  have hfin := hR _ halg hirr (1 / 2) (by norm_num)
  have hrmono : StrictMono r := by
    refine strictMono_nat_of_lt_succ fun J => ?_
    simp only [r]
    rw [Finset.sum_range_succ _ (J + 1)]
    have : (0 : ℚ) < Nat.fib (n (J + 1)) := by exact_mod_cast Nat.fib_pos.2 (hpos _)
    linarith [inv_pos.2 this]
  have hA : ({J | n (J + 1) ≠ 2 * n J} \ Set.Iio 4).Infinite := by
    have : ∃ᶠ J in atTop, n (J + 1) ≠ 2 * n J := by
      exact Filter.not_eventually.1 hne
    exact (Nat.frequently_atTop_iff_infinite.1 this).sdiff (Set.finite_Iio 4)
  apply hA
  refine (hfin.preimage hrmono.injective.injOn).subset ?_
  rintro J ⟨hJ, hJ4⟩
  simp only [Set.mem_Iio, not_lt] at hJ4
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hx := hsplit J
  set m := n J with hm
  have hm4 : 4 ≤ m := (hJ4.trans (hid J))
  have hTJ := hT J
  rw [hx, add_sub_cancel_left, abs_of_pos hTJ.1]
  have hD1 : (1 : ℝ) ≤ (r J).den := by exact_mod_cast (r J).den_pos
  set F : ℝ := (Nat.fib m : ℝ)
  have hF := hFpos J
  -- T² F⁵ < 1
  set u := φ ^ m with hu
  have hu0 : 0 < u := by positivity
  have h1 : T J * u ^ 3 ≤ φ ^ 4 := by
    refine le_trans ?_ hTJ.2
    rw [hu, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hφ.le (by
      have := (hratio J).2 hJ; rw [← hm] at this; omega)) hTJ.1.le
  have h2 : F * φ ≤ u := hFle J
  have h3 : (T J * u ^ 3) ^ 2 * (F * φ) ^ 5 ≤ (φ ^ 4) ^ 2 * u ^ 5 :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) (pow_le_pow_left₀ (by positivity) h2 5)
      (by positivity) (by positivity)
  have h4 : φ ^ 3 < u := pow_lt_pow_right₀ hφ (by omega)
  have hTF : (T J) ^ 2 * F ^ 5 < 1 := by
    have : (T J) ^ 2 * F ^ 5 * (φ ^ 5 * u ^ 6) < 1 * (φ ^ 5 * u ^ 6) := by
      calc (T J) ^ 2 * F ^ 5 * (φ ^ 5 * u ^ 6) = (T J * u ^ 3) ^ 2 * (F * φ) ^ 5 := by ring
        _ ≤ (φ ^ 4) ^ 2 * u ^ 5 := h3
        _ = (φ ^ 5 * u ^ 5) * φ ^ 3 := by ring
        _ < (φ ^ 5 * u ^ 5) * u := mul_lt_mul_of_pos_left h4 (by positivity)
        _ = 1 * (φ ^ 5 * u ^ 6) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  -- convert to the rpow statement
  have hpow : ((r J).den : ℝ) ^ ((2 : ℝ) + 1 / 2) ≤ F ^ 2 * √F := by
    calc ((r J).den : ℝ) ^ ((2 : ℝ) + 1 / 2) ≤ F ^ ((2 : ℝ) + 1 / 2) :=
          Real.rpow_le_rpow (by positivity) (hden J) (by norm_num)
      _ = F ^ 2 * √F := by
          rw [Real.rpow_add hF, Real.rpow_two, Real.sqrt_eq_rpow]
  have hsq : √F ^ 2 = F := Real.sq_sqrt hF.le
  have hy : T J * (F ^ 2 * √F) < 1 := by
    have h0 : 0 ≤ T J * (F ^ 2 * √F) := by have := hTJ.1; positivity
    have : (T J * (F ^ 2 * √F)) ^ 2 < 1 := by
      calc (T J * (F ^ 2 * √F)) ^ 2 = (T J) ^ 2 * F ^ 4 * √F ^ 2 := by ring
        _ = (T J) ^ 2 * F ^ 5 := by rw [hsq]; ring
        _ < 1 := hTF
    nlinarith
  have hDpos : 0 < ((r J).den : ℝ) ^ ((2 : ℝ) + 1 / 2) := by positivity
  rw [lt_div_iff₀ hDpos]
  calc T J * ((r J).den : ℝ) ^ ((2 : ℝ) + 1 / 2) ≤ T J * (F ^ 2 * √F) :=
        mul_le_mul_of_nonneg_left hpow hTJ.1.le
    _ < 1 := hy

/-- **Restricted rigidity holds (proved, from Roth).**  Enumerate `K` increasingly (`Nat.Subtype.orderIsoOfNat`); `2^(e j)`
is a divisibility chain, and coinfinite `K` gives infinitely many gaps, so the ratio is `≥ 4`
infinitely often.  Then apply `divChain_rigidity`. -/
theorem restrictedRigidity_holds (hR : Roth1955) : RestrictedRigidity := by
  intro K hK hKc
  classical
  haveI : Infinite K := hK.to_subtype
  let ι := Nat.Subtype.orderIsoOfNat K
  let e : ℕ → ℕ := fun j => (ι j : ℕ)
  have hmono : StrictMono e := fun a b h => by
    simpa [e] using (ι.strictMono h)
  have hmem : ∀ j, e j ∈ K := fun j => (ι j).2
  have hsum : (∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)
      = ∑' j, ((Nat.fib (2 ^ e j) : ℝ))⁻¹ :=
    (ι.toEquiv.tsum_eq (fun k : K => ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)).symm
  rw [hsum]
  have hr := divChain_rigidity hR (fun j => 2 ^ e j) (fun j => by positivity)
    (fun a b hab => Nat.pow_lt_pow_right (by norm_num) (hmono hab))
    (fun j => Nat.pow_dvd_pow 2 (hmono (Nat.lt_succ_self j)).le)
  intro halg
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hr.1 halg)
  have hstep : ∀ j ≥ J, e (j + 1) = e j + 1 := fun j hj => by
    have := hJ j hj
    rw [show 2 * 2 ^ e j = 2 ^ (e j + 1) by ring] at this
    exact Nat.pow_right_injective le_rfl this
  have hlin : ∀ i, e (J + i) = e J + i := by
    intro i; induction i with
    | zero => rfl
    | succ i ih => rw [← add_assoc, hstep _ (by omega), ih]; ring
  apply hKc
  refine (Set.finite_lt_nat (e J)).subset fun m hm => ?_
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_lt] at hlt
  apply hm
  have := hmem (J + (m - e J))
  rwa [hlin, Nat.add_sub_cancel' hlt] at this

end LeanFormalizations.LacunaryFib
