/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Montgomery–Vaughan mean value theorem (upper half) via a Fejér majorant

`∫_{-T}^{T} |Σ_{n≤N} a_n n^{-it}|² dt ≤ 32 (T + N) Σ |a_n|²`.

Route: fold `[-T,0]` onto `[0,T]` (`g(t) = |S(t)|² + |S(-t)|²` is a cosine sum), majorize
`1_{[0,T]} ≤ 2(1 - t/(2T))` on `[0,2T]`, integrate term by term to the explicit Fejér integral
`J(λ) = (1 - cos 2Tλ)/(2Tλ²)`, bound `|J(λ)| ≤ min(T, 1/(Tλ²)) ≤ 2TN²/(T²(n-m)² + N²)` using
`|log n - log m| ≥ |n - m|/N`, and sum rows by telescoping `1/(j+K) - 1/(j+1+K)`, `K = N/T`.
-/

open Real Finset Complex

namespace Erdos385.MVT

/-- Fejér-type integral `∫₀^{2T} (1 - t/(2T)) cos(λ t) dt`. -/
noncomputable def J (T l : ℝ) : ℝ := ∫ t in (0:ℝ)..(2*T), (1 - t/(2*T)) * Real.cos (l*t)

lemma J_abs_le_T {T : ℝ} (hT : 0 < T) (l : ℝ) : |J T l| ≤ T := by
  unfold J
  calc |∫ t in (0:ℝ)..(2*T), (1 - t/(2*T)) * Real.cos (l*t)|
      ≤ ∫ t in (0:ℝ)..(2*T), |(1 - t/(2*T)) * Real.cos (l*t)| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ t in (0:ℝ)..(2*T), (1 - t/(2*T)) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
        · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro t ht
        have h1 : 0 ≤ 1 - t/(2*T) := by
          rw [sub_nonneg, div_le_one (by linarith)]; exact ht.2
        rw [abs_mul, abs_of_nonneg h1]
        exact mul_le_of_le_one_right h1 (abs_cos_le_one _)
    _ = T := by
        simp [intervalIntegral.integral_sub, intervalIntegral.integral_div]
        field_simp; ring

lemma J_eq {T l : ℝ} (hT : 0 < T) (hl : l ≠ 0) :
    J T l = (1 - Real.cos (2*T*l)) / (2*T*l^2) := by
  unfold J
  have key : ∀ t ∈ Set.uIcc (0:ℝ) (2*T), HasDerivAt
      (fun t => (1 - t/(2*T)) * Real.sin (l*t) / l - Real.cos (l*t) / (2*T*l^2))
      ((1 - t/(2*T)) * Real.cos (l*t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => l*t) l t := by simpa using (hasDerivAt_id t).const_mul l
    have hs := (Real.hasDerivAt_sin (l*t)).comp t h1
    have hc := (Real.hasDerivAt_cos (l*t)).comp t h1
    have hlin : HasDerivAt (fun t : ℝ => 1 - t/(2*T)) (-(1/(2*T))) t := by
      simpa using ((hasDerivAt_id t).div_const (2*T)).const_sub 1
    have H := ((hlin.mul hs).div_const l).sub (hc.div_const (2*T*l^2))
    refine H.congr_deriv ?_
    simp only [Function.comp]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, sub_zero]
  field_simp; ring_nf

lemma J_abs_le_inv {T l : ℝ} (hT : 0 < T) (hl : l ≠ 0) : |J T l| ≤ 1 / (T*l^2) := by
  rw [J_eq hT hl, abs_div, abs_of_pos (by positivity : 0 < 2*T*l^2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := neg_one_le_cos (2*T*l); have := cos_le_one (2*T*l)
  have : |1 - Real.cos (2*T*l)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith [sq_nonneg l, mul_pos hT (by positivity : 0 < l^2)]

noncomputable def phi (T N x : ℝ) : ℝ := 2*T*N^2 / (T^2*x^2 + N^2)

lemma phi_nonneg {T N : ℝ} (hT : 0 < T) (hN : 0 < N) (x : ℝ) : 0 ≤ phi T N x := by
  unfold phi; positivity

lemma phi_neg (T N x : ℝ) : phi T N (-x) = phi T N x := by simp [phi]

lemma sum_phi_succ_le {T N : ℝ} (hT : 0 < T) (hN : 0 < N) (M : ℕ) :
    ∑ j ∈ range M, phi T N ((j:ℝ) + 1) ≤ 4 * N := by
  set g : ℕ → ℝ := fun j => T / (T * j + N) with hg
  have hpt : ∀ j : ℕ, phi T N ((j:ℝ) + 1) ≤ 4*N^2/T * (g j - g (j+1)) := by
    intro j
    have hx : (0:ℝ) ≤ j := j.cast_nonneg
    have hA : 0 < T*j + N := by positivity
    have hB : 0 < T*j + T + N := by positivity
    simp only [hg, phi]
    push_cast
    rw [div_sub_div _ _ hA.ne' (by nlinarith), mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    have : (T*j + N) * (T*(j+1) + N) ≤ 2*(T^2*(j+1)^2 + N^2) := by
      nlinarith [sq_nonneg (T*(j+1) - N), mul_pos hT hN]
    have e : T * (T*(j+1) + N) - (T*j + N) * T = T^2 := by ring
    rw [e]
    have h4 : 0 < T * N^2 := by positivity
    have e2 : 4*N^2/T*T^2 = 4*N^2*T := by field_simp
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left this h4.le]
  calc ∑ j ∈ range M, phi T N ((j:ℝ) + 1)
      ≤ ∑ j ∈ range M, 4*N^2/T * (g j - g (j+1)) := sum_le_sum fun j _ => hpt j
    _ = 4*N^2/T * (g 0 - g M) := by rw [← mul_sum, sum_range_sub']
    _ ≤ 4*N^2/T * g 0 := by
        gcongr; simp only [hg, sub_le_self_iff]; positivity
    _ = 4 * N := by simp [hg]; field_simp

lemma sum_phi_le {T N : ℝ} (hT : 0 < T) (hN : 0 < N) (M : ℕ) :
    ∑ j ∈ range M, phi T N (j:ℝ) ≤ 2*T + 4 * N := by
  cases M with
  | zero => simp; positivity
  | succ M =>
    rw [sum_range_succ']
    have h0 : phi T N ((0:ℕ):ℝ) = 2*T := by simp [phi]; field_simp
    rw [h0]; push_cast; linarith [sum_phi_succ_le hT hN M]

lemma row_sum_le {T N : ℝ} (hT : 0 < T) (hN : 0 < N) (K m : ℕ) (hm : m ≤ K) :
    ∑ n ∈ range (K+1), phi T N ((n:ℝ) - m) ≤ 4*T + 8*N := by
  rw [← sum_range_add_sum_Ico _ (by omega : m ≤ K+1), sum_Ico_eq_sum_range]
  have h1 : ∑ n ∈ range m, phi T N ((n:ℝ) - m) = ∑ j ∈ range m, phi T N ((j:ℝ) + 1) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [← phi_neg]; congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ∑ k ∈ range (K + 1 - m), phi T N (((m + k : ℕ):ℝ) - m)
      = ∑ k ∈ range (K + 1 - m), phi T N (k:ℝ) := by
    refine sum_congr rfl fun k _ => ?_; push_cast; ring_nf
  rw [h1, h2]
  linarith [sum_phi_succ_le hT hN m, sum_phi_le hT hN (K+1-m)]


lemma log_gap_aux {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ N) :
    (y - x) / N ≤ Real.log y - Real.log x := by
  have hy0 : 0 < y := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < y / x)
  rw [Real.log_div hy0.ne' hx.ne', inv_div] at h
  calc (y - x) / N ≤ (y - x) / y := div_le_div_of_nonneg_left (by linarith) hy0 hy
    _ = 1 - x / y := by field_simp
    _ ≤ _ := h

lemma log_gap_sq {x y N : ℝ} (hx : 0 < x) (hy : 0 < y) (hxN : x ≤ N) (hyN : y ≤ N) :
    (y - x)^2 / N^2 ≤ (Real.log y - Real.log x)^2 := by
  have hN : 0 < N := by linarith
  rw [← div_pow]
  rcases le_total x y with h | h
  · have := log_gap_aux hx h hyN
    exact pow_le_pow_left₀ (div_nonneg (by linarith) hN.le) this 2
  · have := log_gap_aux hy h hxN
    have e1 : (y - x)/N = -((x - y)/N) := by ring
    have e2 : Real.log y - Real.log x = -(Real.log x - Real.log y) := by ring
    rw [e1, e2, neg_sq, neg_sq]
    exact pow_le_pow_left₀ (div_nonneg (by linarith) hN.le) this 2

lemma J_le_phi {T x y N : ℝ} (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hxN : x ≤ N) (hyN : y ≤ N) :
    |J T (Real.log y - Real.log x)| ≤ phi T N (y - x) := by
  have hN : 0 < N := by linarith
  have hg := log_gap_sq hx hy hxN hyN
  set l := Real.log y - Real.log x
  set d := y - x
  unfold phi
  by_cases hc : T^2 * d^2 ≤ N^2
  · refine (J_abs_le_T hT l).trans ?_
    rw [le_div_iff₀ (by positivity)]; nlinarith
  · push Not at hc
    have hd : 0 < d^2 := by
      by_contra h; push Not at h; nlinarith [sq_nonneg d, sq_nonneg T]
    have hl2 : 0 < l^2 := lt_of_lt_of_le (by positivity) hg
    have hl : l ≠ 0 := by rintro h; simp [h] at hl2
    refine (J_abs_le_inv hT hl).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hg
    nlinarith [mul_le_mul_of_nonneg_left hg (by positivity : (0:ℝ) ≤ 2*T^2)]

/-- The generalized Dirichlet polynomial `Σ a_n e^{-i t ℓ_n}`. -/
noncomputable def S (s : Finset ℕ) (a : ℕ → ℂ) (ℓ : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (((-(t * ℓ n) : ℝ) : ℂ) * I)

lemma continuous_S (s : Finset ℕ) (a : ℕ → ℂ) (ℓ : ℕ → ℝ) : Continuous (S s a ℓ) := by
  unfold S; fun_prop

lemma normSq_S (s : Finset ℕ) (a : ℕ → ℂ) (ℓ : ℕ → ℝ) (t : ℝ) :
    ((‖S s a ℓ t‖^2 : ℝ) : ℂ) = ∑ m ∈ s, ∑ n ∈ s,
      a m * (starRingEnd ℂ) (a n) * Complex.exp (((t * (ℓ n - ℓ m) : ℝ) : ℂ) * I) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, S, map_sum, sum_mul_sum]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : a m * Complex.exp (((-(t * ℓ m) : ℝ) : ℂ) * I) *
      ((starRingEnd ℂ) (a n) * Complex.exp ((starRingEnd ℂ) (((-(t * ℓ n) : ℝ) : ℂ) * I))) =
      a m * (starRingEnd ℂ) (a n) * (Complex.exp (((-(t * ℓ m) : ℝ) : ℂ) * I) *
        Complex.exp ((starRingEnd ℂ) (((-(t * ℓ n) : ℝ) : ℂ) * I))) := by ring
  rw [this, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma sym_identity (s : Finset ℕ) (a : ℕ → ℂ) (ℓ : ℕ → ℝ) (t : ℝ) :
    ‖S s a ℓ t‖^2 + ‖S s a ℓ (-t)‖^2 = ∑ m ∈ s, ∑ n ∈ s,
      4 * (a m * (starRingEnd ℂ) (a n)).re * ((1/2) * Real.cos ((ℓ n - ℓ m) * t)) := by
  apply Complex.ofReal_injective
  have h := congrArg Complex.re (show ((‖S s a ℓ t‖^2 + ‖S s a ℓ (-t)‖^2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, ((2 * Real.cos ((ℓ n - ℓ m) * t) : ℝ) : ℂ) *
        (a m * (starRingEnd ℂ) (a n)) by
    rw [Complex.ofReal_add, normSq_S, normSq_S, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    push_cast
    rw [Complex.cos]
    rw [show (t:ℂ) * ((ℓ n:ℂ) - ℓ m) * I = ((ℓ n:ℂ) - ℓ m) * t * I by ring,
      show -(t:ℂ) * ((ℓ n:ℂ) - ℓ m) * I = -(((ℓ n:ℂ) - ℓ m) * t * I) by ring]
    rw [neg_mul]; ring)
  rw [Complex.ofReal_re] at h
  rw [h]; simp only [Complex.re_sum, Complex.re_ofReal_mul]
  push_cast
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  ring


lemma integral_le_weighted (s : Finset ℕ) (a : ℕ → ℂ) (ℓ : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖S s a ℓ t‖^2 ≤ ∑ m ∈ s, ∑ n ∈ s,
      4 * (a m * (starRingEnd ℂ) (a n)).re * J T (ℓ n - ℓ m) := by
  set f : ℝ → ℝ := fun t => ‖S s a ℓ t‖^2 with hf
  have fc : Continuous f := by have := continuous_S s a ℓ; fun_prop
  set g : ℝ → ℝ := fun t => f t + f (-t) with hg
  have gc : Continuous g := by fun_prop
  have g0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg, hf]; positivity
  set w : ℝ → ℝ := fun t => 2 * (1 - t/(2*T)) with hw
  have wc : Continuous w := by fun_prop
  have h1 : ∫ t in (-T)..T, f t = ∫ t in (0:ℝ)..T, g t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (fc.intervalIntegrable _ _) (fc.intervalIntegrable _ _)]
    have hneg : ∫ t in (0:ℝ)..T, f (-t) = ∫ t in (-T)..0, f t := by
      simpa using intervalIntegral.integral_comp_neg (a := 0) (b := T) f
    have hi : IntervalIntegrable (fun t => f (-t)) MeasureTheory.volume 0 T :=
      (fc.comp continuous_neg).intervalIntegrable _ _
    simp only [hg]
    rw [intervalIntegral.integral_add (fc.intervalIntegrable _ _) hi, hneg]; ring
  have h2 : ∫ t in (0:ℝ)..T, g t ≤ ∫ t in (0:ℝ)..T, w t * g t := by
    apply intervalIntegral.integral_mono_on hT.le (gc.intervalIntegrable _ _)
      ((wc.mul gc).intervalIntegrable _ _)
    intro t ht
    have : 1 ≤ w t := by
      simp only [hw]
      have : t/(2*T) ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith [ht.2]
      linarith
    exact le_mul_of_one_le_left (g0 t) this
  have h3 : ∫ t in (0:ℝ)..T, w t * g t ≤ ∫ t in (0:ℝ)..(2*T), w t * g t := by
    have wgc : Continuous (fun t => w t * g t) := wc.mul gc
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := T)
      (wgc.intervalIntegrable 0 T) (wgc.intervalIntegrable T (2*T))]
    have : 0 ≤ ∫ t in T..(2*T), w t * g t := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      have : 0 ≤ w t := by
        simp only [hw]
        have : t/(2*T) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith [ht.2]
        linarith
      exact mul_nonneg this (g0 t)
    linarith
  have h4 : ∫ t in (0:ℝ)..(2*T), w t * g t = ∑ m ∈ s, ∑ n ∈ s,
      4 * (a m * (starRingEnd ℂ) (a n)).re * J T (ℓ n - ℓ m) := by
    have : ∀ t, w t * g t = ∑ m ∈ s, ∑ n ∈ s,
        4 * (a m * (starRingEnd ℂ) (a n)).re * ((1 - t/(2*T)) * Real.cos ((ℓ n - ℓ m) * t)) := by
      intro t
      simp only [hw, hg, hf, sym_identity, mul_sum]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
      ring
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum (fun m _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    refine sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun n _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    refine sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  calc _ = ∫ t in (-T)..T, f t := rfl
    _ ≤ _ := h1.le.trans (h2.trans h3) |>.trans h4.le


lemma term_le {T : ℝ} (hT : 0 < T) {N : ℕ} (hN1 : 1 ≤ N) (a : ℕ → ℂ)
    (ha : ∀ n, (n = 0 ∨ N < n) → a n = 0)
    {m n : ℕ} (hm : m ∈ range (N+1)) (hn : n ∈ range (N+1)) :
    4 * (a m * (starRingEnd ℂ) (a n)).re * J T (Real.log n - Real.log m) ≤
      2 * (‖a m‖^2 + ‖a n‖^2) * phi T N ((n:ℝ) - m) := by
  rw [mem_range] at hm hn
  have hN : (0:ℝ) < N := by exact_mod_cast hN1
  have hφ := phi_nonneg hT hN ((n:ℝ) - m)
  by_cases h0 : a m = 0 ∨ a n = 0
  · rcases h0 with h | h <;> simp [h] <;> positivity
  push Not at h0
  have hm0 : m ≠ 0 := fun h => h0.1 (ha m (Or.inl h))
  have hn0 : n ≠ 0 := fun h => h0.2 (ha n (Or.inl h))
  have hJ := J_le_phi (N := N) hT (x := m) (y := n) (by positivity) (by positivity)
    (by exact_mod_cast (by omega : m ≤ N)) (by exact_mod_cast (by omega : n ≤ N))
  set c := a m * (starRingEnd ℂ) (a n)
  have hc : ‖c‖ = ‖a m‖ * ‖a n‖ := by simp [c]
  have h1 : c.re * J T (Real.log n - Real.log m) ≤ ‖c‖ * phi T N ((n:ℝ) - m) := by
    calc _ ≤ |c.re * J T (Real.log n - Real.log m)| := le_abs_self _
      _ = |c.re| * |J T (Real.log n - Real.log m)| := abs_mul _ _
      _ ≤ ‖c‖ * phi T N ((n:ℝ) - m) :=
        mul_le_mul (Complex.abs_re_le_norm c) hJ (abs_nonneg _) (norm_nonneg _)
  rw [hc] at h1
  have h2 : 2 * (‖a m‖ * ‖a n‖) ≤ ‖a m‖^2 + ‖a n‖^2 := by nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
  nlinarith [mul_le_mul_of_nonneg_right h2 hφ]

theorem mvt : ∀ (N : ℕ) (T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 0 < T →
    (∀ n, (n = 0 ∨ N < n) → a n = 0) →
    ∫ t in (-T)..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
      32 * (T + N) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  intro N T a hN1 hT ha
  have hN : (0:ℝ) < N := by exact_mod_cast hN1
  have hbridge : ∀ t : ℝ, ∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (-((t : ℂ) * I)) =
      S (range (N+1)) a (fun n => Real.log n) t := by
    intro t
    refine sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [ha n (Or.inl h)]
    congr 1
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h.ne')]
    congr 1
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_log n.cast_nonneg]
    push_cast; ring
  simp_rw [hbridge]
  refine (integral_le_weighted _ a _ hT).trans ?_
  set A : ℕ → ℝ := fun n => ‖a n‖^2
  have hA : ∀ n, 0 ≤ A n := fun n => by positivity
  have hrow : ∀ m ∈ range (N+1), ∑ n ∈ range (N+1), phi T N ((n:ℝ) - m) ≤ 4*T + 8*N := by
    intro m hm; rw [mem_range] at hm
    exact row_sum_le hT hN N m (by omega)
  calc _ ≤ ∑ m ∈ range (N+1), ∑ n ∈ range (N+1), 2 * (A m + A n) * phi T N ((n:ℝ) - m) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => term_le hT hN1 a ha hm hn
    _ = ∑ m ∈ range (N+1), 2 * A m * ∑ n ∈ range (N+1), phi T N ((n:ℝ) - m) +
        ∑ n ∈ range (N+1), 2 * A n * ∑ m ∈ range (N+1), phi T N ((m:ℝ) - n) := by
        have e : ∀ m n : ℕ, 2 * (A m + A n) * phi T N ((n:ℝ) - m) =
            2 * A m * phi T N ((n:ℝ) - m) + 2 * A n * phi T N ((m:ℝ) - n) := by
          intro m n; rw [← phi_neg T N ((m:ℝ) - n), neg_sub]; ring
        simp only [e, sum_add_distrib, mul_sum]
        congr 1
        exact sum_comm
    _ ≤ ∑ m ∈ range (N+1), 2 * A m * (4*T + 8*N) +
        ∑ n ∈ range (N+1), 2 * A n * (4*T + 8*N) := by
        apply add_le_add <;> apply sum_le_sum <;> intro m hm <;>
          exact mul_le_mul_of_nonneg_left (hrow m hm) (by linarith [hA m])
    _ = 4 * (4*T + 8*N) * ∑ n ∈ range (N+1), A n := by
        rw [mul_sum, ← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_; ring
    _ ≤ 32 * (T + N) * ∑ n ∈ range (N+1), A n := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (sum_nonneg fun n _ => hA n)

end Erdos385.MVT
