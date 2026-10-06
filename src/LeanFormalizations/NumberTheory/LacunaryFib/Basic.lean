/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Lacunary Fibonacci reciprocal sums: the tiling bedrock (phase LF1)

Erdős #267 asked whether `∑ 1/F_(n_k)` is irrational when `n (k + 1) ≥ c · n k` with `c > 1`.
Snyder 2026 settled it (`ErdosDyadic.Snyder2026Erdos267`).  Nguyen 2022 proved transcendence for
`c > 2` (`Nguyen2022`), which is sharp because `∑ 1/F_(2^k) = (7 − √5)/2` (`millin`).  The open
question is what happens at and below the boundary `c = 2`.

**Why doubling is algebraic: a tiling.**  For even `n`, `1/F_n = √5 ∑_j φ^(−(2j+1)n)`
(`fib_inv_eq_tsum_of_even`), so a sum over `n_k = 2^k` is a power series in `φ⁻¹` supported on the
odd multiples of the `2^k`.  Those sets tile the positive integers, so the series collapses.  For
`k` restricted to a set `K`, the support is `{m : v₂ m ∈ K}` (`restricted_sum_eq_tiling`).  That
set is eventually periodic iff `K` is finite or cofinite (`vTwo_eventuallyPeriodic_iff`).

⚠️ **Numerics are blind here.**  At `P` digits, only the terms with `2^k ≲ 2.3 P` are visible.
So any `K` that agrees with a cofinite set up to `k ≈ log₂ P` looks algebraic to a polynomial
search; a 400-digit `findpoly` "found" `(5 − √5)/2` for a Sturmian `K` (2026-10-05).  This
conjecture can only be tested by proof.
-/

namespace LeanFormalizations.LacunaryFib

open Filter Real Topology

/-- **Node A (believed ~99%): the Lambert expansion for even `n`.**  `F_n = (φ^n − φ^(−n))/√5` when
`n` is even (Binet, `ψ^n = φ^(−n)`), so `1/F_n = √5 φ^(−n) / (1 − φ^(−2n))`. -/
theorem fib_inv_eq_tsum_of_even {n : ℕ} (hn : 0 < n) (he : Even n) :
    ((Nat.fib n : ℝ))⁻¹ = √5 * ∑' j : ℕ, (goldenRatio⁻¹) ^ ((2 * j + 1) * n) := by
  set x : ℝ := goldenRatio⁻¹ ^ n with hx
  have hφ : 1 < goldenRatio := one_lt_goldenRatio
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hφ) hn.ne'
  have hterm : ∀ j : ℕ, goldenRatio⁻¹ ^ ((2 * j + 1) * n) = x * (x ^ 2) ^ j := by
    intro j; rw [hx, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by nlinarith)]
  have hψ : goldenConj ^ n = x := by
    rw [hx, inv_goldenRatio, neg_pow, he.neg_one_pow, one_mul]
  have hφn : goldenRatio ^ n = x⁻¹ := by rw [hx, inv_pow, inv_inv]
  rw [coe_fib_eq, hψ, hφn]
  have h5 : (0:ℝ) < √5 := by positivity
  have : x⁻¹ - x ≠ 0 := by
    have : x < x⁻¹ := lt_trans hx1 (one_lt_inv₀ hx0 |>.2 hx1)
    linarith
  have h2 : 1 - x^2 ≠ 0 := by nlinarith
  field_simp

/-- Cassini, real-valued. -/
theorem cassiniR (k : ℕ) :
    (Nat.fib k : ℝ) * Nat.fib (k + 2) - (Nat.fib (k + 1) : ℝ) ^ 2 = (-1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Nat.fib_add_two (n := k); have h2 := Nat.fib_add_two (n := k + 1)
    push_cast [h1, h2] at ih ⊢
    rw [pow_succ]; linear_combination -ih

/-- **Node B (believed ~99%): Millin's step.**  For even `m > 0`,
`F_(m−1) F_(2m) − F_m F_(2m−1) = F_m`, so `1/F_(2m)` is a difference of consecutive convergent-like
ratios `F_(m−1)/F_m`.  Example: `m = 2` gives `1/3 = 1 − 2/3`. -/
theorem fib_two_mul_inv {m : ℕ} (hm : 0 < m) (he : Even m) :
    ((Nat.fib (2 * m) : ℝ))⁻¹ =
      (Nat.fib (m - 1) : ℝ) / Nat.fib m - (Nat.fib (2 * m - 1) : ℝ) / Nat.fib (2 * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : (-1 : ℝ) ^ (k + 1) = 1 := he.neg_one_pow
  have hc := cassiniR k
  rw [hk, Nat.fib_add_two] at hc
  have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
  have e2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
  rw [e1, e2, Nat.add_sub_cancel, Nat.fib_two_mul_add_two, Nat.fib_two_mul_add_one]
  have p1 : (0:ℝ) < Nat.fib (k + 1) := by exact_mod_cast Nat.fib_pos.2 (by omega)
  have p2 : (0:ℝ) < 2 * Nat.fib k + Nat.fib (k + 1) := by positivity
  push_cast at hc ⊢
  field_simp
  linear_combination (-1:ℝ) * hc

/-- Millin telescoping from any even start `b`. -/
theorem hasSum_doubling {b : ℕ} (hb : 0 < b) (he : Even b) :
    HasSum (fun k : ℕ => ((Nat.fib (b * 2 ^ (k + 1)) : ℝ))⁻¹)
      ((Nat.fib (b - 1) : ℝ) / Nat.fib b - goldenRatio⁻¹) := by
  set r : ℕ → ℝ := fun n => (Nat.fib (n - 1) : ℝ) / Nat.fib n with hr
  have hterm : ∀ k, ((Nat.fib (b * 2 ^ (k + 1)) : ℝ))⁻¹ = r (b * 2 ^ k) - r (b * 2 ^ (k + 1)) := by
    intro k
    have e : b * 2 ^ (k + 1) = 2 * (b * 2 ^ k) := by ring
    rw [hr]; dsimp only; rw [e]
    exact fib_two_mul_inv (by positivity) (he.mul_right _)
  have hlim : Tendsto (fun k => r (b * 2 ^ k)) atTop (𝓝 goldenRatio⁻¹) := by
    rw [inv_goldenRatio]
    have h1 : Tendsto (fun k : ℕ => b * 2 ^ k - 1) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) (tendsto_sub_atTop_nat 1 |>.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)))
      have : 2 ^ k ≤ b * 2 ^ k := Nat.le_mul_of_pos_left _ hb
      simp; omega
    refine (tendsto_fib_div_fib_succ_atTop.comp h1).congr (fun k => ?_)
    have : 0 < b * 2 ^ k := by positivity
    have : b * 2 ^ k - 1 + 1 = b * 2 ^ k := by omega
    simp only [Function.comp, hr, this]
  have hnn : ∀ k, 0 ≤ ((Nat.fib (b * 2 ^ (k + 1)) : ℝ))⁻¹ := fun k => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [hterm, Finset.sum_range_sub']
  have : r (b * 2 ^ 0) = (Nat.fib (b - 1) : ℝ) / Nat.fib b := by simp [hr]
  rw [← this]
  exact tendsto_const_nhds.sub hlim

theorem inv_gold_eq : goldenRatio⁻¹ = (√5 - 1) / 2 := by
  rw [inv_goldenRatio, goldenConj]; ring

/-- **Millin's series (the control, believed ~99%).**  Terms `k = 0, 1` give `2`; the rest
telescope by `fib_two_mul_inv` to `F_1/F_2 − 1/φ = (3 − √5)/2`. -/
theorem millin : ∑' k : ℕ, ((Nat.fib (2 ^ k) : ℝ))⁻¹ = (7 - √5) / 2 := by
  have h := hasSum_doubling (b := 2) (by norm_num) even_two
  have h' : HasSum (fun k : ℕ => ((Nat.fib (2 ^ (k + 2)) : ℝ))⁻¹)
      ((7 - √5) / 2 - ∑ i ∈ Finset.range 2, ((Nat.fib (2 ^ i) : ℝ))⁻¹) := by
    convert h using 1
    · ext k; congr 3; ring
    · rw [inv_gold_eq]; simp [Finset.sum_range_succ]; ring
  exact ((hasSum_nat_add_iff' 2).1 h').tsum_eq

theorem isAlgebraic_goldenRatio_inv : IsAlgebraic ℚ goldenRatio⁻¹ := by
  rw [inv_gold_eq]
  have h5 : IsAlgebraic ℚ (√5) := by
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rw [Real.sq_sqrt (by norm_num)]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 5
  have h1 : IsAlgebraic ℚ (1 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 1
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 2
  rw [div_eq_mul_inv]
  exact (h5.sub h1).mul h2.inv

theorem isAlgebraic_natCast (n : ℕ) : IsAlgebraic ℚ (n : ℝ) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) n

/-- **Node B′ (believed ~95%): every doubling tail is algebraic.**  Millin's telescoping applies
to `a·2^(k+1)` for every `a > 0`, since each step index `a·2^k` with `k ≥ 1` is even.  The value
lies in `ℚ(√5)`. -/
theorem doubling_tail_algebraic (a : ℕ) (ha : 0 < a) :
    IsAlgebraic ℚ (∑' k, ((Nat.fib (a * 2 ^ (k + 1)) : ℝ))⁻¹) := by
  have h := hasSum_doubling (b := 2 * a) (by omega) (even_two_mul a)
  have h' : HasSum (fun k : ℕ => ((Nat.fib (a * 2 ^ (k + 1 + 1)) : ℝ))⁻¹)
      (((Nat.fib (2 * a - 1) : ℝ) / Nat.fib (2 * a) - goldenRatio⁻¹ + ((Nat.fib (a * 2 ^ 1) : ℝ))⁻¹)
        - ∑ i ∈ Finset.range 1, ((Nat.fib (a * 2 ^ (i + 1)) : ℝ))⁻¹) := by
    convert h using 1
    · ext k; congr 3; ring
    · simp
  rw [((hasSum_nat_add_iff' 1).1 h').tsum_eq]
  rw [div_eq_mul_inv]
  exact (((isAlgebraic_natCast _).mul (isAlgebraic_natCast _).inv).sub
    isAlgebraic_goldenRatio_inv).add (isAlgebraic_natCast _).inv


theorem v2_eq_iff {x a : ℕ} (hx : x ≠ 0) :
    padicValNat 2 x = a ↔ 2 ^ a ∣ x ∧ ¬ 2 ^ (a + 1) ∣ x := by
  rw [padicValNat_dvd_iff_le hx, padicValNat_dvd_iff_le hx]; omega

/-- For `K ⊆ [0, N)`, the period `2^N` preserves membership of `v₂`. -/
theorem v2_add_pow_mem_iff {K : Set ℕ} {N : ℕ} (hK : ∀ k ∈ K, k < N) {m : ℕ} (hm : 0 < m) :
    padicValNat 2 (m + 2 ^ N) ∈ K ↔ padicValNat 2 m ∈ K := by
  have hm' : m ≠ 0 := hm.ne'
  have hmN : m + 2 ^ N ≠ 0 := by positivity
  by_cases hv : padicValNat 2 m < N
  · obtain ⟨h1, h2⟩ := (v2_eq_iff hm').1 rfl
    have hd : 2 ^ (padicValNat 2 m + 1) ∣ 2 ^ N := pow_dvd_pow 2 hv
    have : padicValNat 2 (m + 2 ^ N) = padicValNat 2 m :=
      (v2_eq_iff hmN).2 ⟨dvd_add h1 ((pow_dvd_pow 2 hv.le).trans dvd_rfl |>.trans
        (dvd_refl _)), fun h => h2 ((Nat.dvd_add_left hd).1 h)⟩
    rw [this]
  · push Not at hv
    have h1 : 2 ^ N ∣ m := (padicValNat_dvd_iff_le hm').2 hv
    have h2 : N ≤ padicValNat 2 (m + 2 ^ N) :=
      (padicValNat_dvd_iff_le hmN).1 (dvd_add h1 dvd_rfl)
    exact ⟨fun h => absurd (hK _ h) (by omega), fun h => absurd (hK _ h) (by omega)⟩

/-- **Node D (believed ~99%): which `2`-adic supports are periodic.**  If `K` is finite with
maximum `k₀`, the period `2^(k₀+1)` works (and the complement for cofinite `K`).  Conversely, if
`p = 2^a·b` with `b` odd is a period and `m` has `v₂ m > a`, then `v₂ (m + p) = a`, so every `k > a`
has the membership of `a`. -/
theorem vTwo_eventuallyPeriodic_iff (K : Set ℕ) :
    (∃ p > 0, ∀ᶠ m in atTop, (padicValNat 2 (m + p) ∈ K ↔ padicValNat 2 m ∈ K)) ↔
      K.Finite ∨ Kᶜ.Finite := by
  constructor
  · rintro ⟨p, hp, hev⟩
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    set a := padicValNat 2 p
    obtain ⟨hpa, hpa1⟩ := (v2_eq_iff (x := p) (a := a) hp.ne').1 rfl
    have key : ∀ k, a < k → (k ∈ K ↔ a ∈ K) := by
      intro k hk
      set m := 2 ^ k * (2 * M + 1)
      have hm0 : m ≠ 0 := by positivity
      have hMm : M ≤ m := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        calc M ≤ 1 * (2 * M + 1) := by omega
          _ ≤ m := Nat.mul_le_mul_right _ this
      have hvm : padicValNat 2 m = k := by
        refine (v2_eq_iff hm0).2 ⟨dvd_mul_right _ _, fun h => ?_⟩
        rw [pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)] at h
        omega
      have hda : 2 ^ (a + 1) ∣ m := (pow_dvd_pow 2 hk).trans (dvd_mul_right _ _)
      have hvmp : padicValNat 2 (m + p) = a :=
        (v2_eq_iff (by positivity)).2 ⟨dvd_add ((pow_dvd_pow 2 (Nat.le_succ a)).trans hda) hpa,
          fun h => hpa1 ((Nat.dvd_add_right hda).1 h)⟩
      have := hM m hMm
      rw [hvm, hvmp] at this
      exact this.symm
    by_cases ha : a ∈ K
    · right
      refine (Set.finite_Iic a).subset fun k hk => ?_
      by_contra h
      exact hk ((key k (by simpa using h)).2 ha)
    · left
      refine (Set.finite_Iic a).subset fun k hk => ?_
      by_contra h
      exact ha ((key k (by simpa using h)).1 hk)
  · have gen : ∀ L : Set ℕ, L.Finite →
        ∃ p > 0, ∀ᶠ m in atTop, (padicValNat 2 (m + p) ∈ L ↔ padicValNat 2 m ∈ L) := by
      intro L hL
      obtain ⟨N, hN⟩ := hL.bddAbove
      refine ⟨2 ^ (N + 1), by positivity, eventually_atTop.2 ⟨1, fun m hm => ?_⟩⟩
      exact v2_add_pow_mem_iff (fun k hk => Nat.lt_succ_of_le (hN hk)) hm
    rintro (h | h)
    · exact gen K h
    · obtain ⟨p, hp, hev⟩ := gen _ h
      exact ⟨p, hp, hev.mono fun m hm => by simpa using not_congr hm⟩

theorem v2_two_pow_mul_odd (k j : ℕ) : padicValNat 2 ((2 * j + 1) * 2 ^ k) = k := by
  refine (v2_eq_iff (by positivity)).2 ⟨dvd_mul_left _ _, fun h => ?_⟩
  rw [pow_succ, mul_comm (2 * j + 1), Nat.mul_dvd_mul_iff_left (by positivity)] at h
  omega

open scoped Classical in
/-- **Node E (believed ~97%): the tiling identity.**  For `K ⊆ {k ≥ 1}`, node A for each
`n = 2^k`, regrouped by the unique factorization `m = 2^(v₂ m) · odd`. -/
theorem restricted_sum_eq_tiling (K : Set ℕ) (hK : ∀ k ∈ K, 1 ≤ k) :
    ∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹ =
      √5 * ∑' m : ℕ, if 0 < m ∧ padicValNat 2 m ∈ K then (goldenRatio⁻¹) ^ m else 0 := by
  set x : ℝ := goldenRatio⁻¹
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  set g : ℕ → ℝ := fun m => if 0 < m ∧ padicValNat 2 m ∈ K then x ^ m else 0 with hg
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (summable_geometric_of_lt_one hx0 hx1)
    · simp only [hg]; split_ifs <;> positivity
    · simp only [hg]; split_ifs <;> first | exact le_rfl | positivity
  set e : K × ℕ → ℕ := fun p => (2 * p.2 + 1) * 2 ^ (p.1 : ℕ) with he
  have he_inj : Function.Injective e := by
    rintro ⟨⟨k, hk⟩, j⟩ ⟨⟨k', hk'⟩, j'⟩ h
    simp only [he] at h
    have hkk : k = k' := by rw [← v2_two_pow_mul_odd k j, h, v2_two_pow_mul_odd]
    subst hkk
    have : 2 * j + 1 = 2 * j' + 1 := Nat.eq_of_mul_eq_mul_right (by positivity) h
    simp only [Prod.mk.injEq, true_and]; omega
  have hrange : ∀ m, m ∉ Set.range e → g m = 0 := by
    intro m hm
    simp only [hg]
    split_ifs with h
    · exfalso; apply hm
      obtain ⟨k, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h.1.ne'
      obtain ⟨j, rfl⟩ := ho
      have hv : padicValNat 2 (2 ^ k * (2 * j + 1)) = k := by
        rw [mul_comm]; exact v2_two_pow_mul_odd k j
      refine ⟨(⟨k, hv ▸ h.2⟩, j), ?_⟩
      simp [he, mul_comm]
    · rfl
  have hcomp : g ∘ e = fun p => x ^ ((2 * p.2 + 1) * 2 ^ (p.1 : ℕ)) := by
    ext ⟨⟨k, hk⟩, j⟩
    simp only [Function.comp, hg, he]
    rw [if_pos ⟨by positivity, by rw [v2_two_pow_mul_odd]; exact hk⟩]
  have hsum : HasSum (fun p : K × ℕ => √5 * x ^ ((2 * p.2 + 1) * 2 ^ (p.1 : ℕ))) (√5 * ∑' m, g m) := by
    refine HasSum.mul_left _ ?_
    rw [← hcomp, he_inj.hasSum_iff hrange]; exact hgs.hasSum
  refine (hsum.prod_fiberwise fun k => ?_).tsum_eq
  have hk1 := hK k k.2
  have hev : Even (2 ^ (k : ℕ)) := (Nat.even_pow' (by omega)).2 even_two
  rw [fib_inv_eq_tsum_of_even (by positivity) hev]
  refine HasSum.mul_left _ (Summable.hasSum ?_)
  refine (summable_geometric_of_lt_one hx0 hx1).comp_injective fun j j' h => ?_
  simp only at h
  have := Nat.eq_of_mul_eq_mul_right (by positivity) h
  omega


end LeanFormalizations.LacunaryFib
