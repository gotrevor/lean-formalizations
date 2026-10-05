/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoDegreeTwo
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsAll
import LeanFormalizations.Literature.Primes

/-!
# Phase 62: the pieces of Saito's Type B argument (Saito 2025, §5–§6, §8)

Paper: Saito, arXiv:2508.16068 (`papers/saito-2025-transcendency-variants-mills.txt` in the main
checkout).  We work with `θ = 21/40` (Baker–Harman–Pintz) and an exponent sequence `C` whose
ratios `c_k = C(k+1)/C k` are eventually `≥ 29/10` (this covers Theorem E+, where `c_k → 3`).

## Why a ratio hypothesis and `Dubickas2022PisotGap` appear (2026-10-05)
* Saito's Lemma 5.2 builds a competitor `ζ < ξ` by a prime chain continued with Lemma 4.2, which
  is Matomäki's theorem; it is needed only for steps whose ratio `c` is below `40/19`, where the
  BHP window `[q^c, q^c + q^(21c/40)]` no longer fits under `(q+1)^c − 1`.  With `c_k ≥ 29/10`
  eventually, every chain step is one BHP prime (`bhp_step`), so Matomäki drops out.
* Saito's Lemma 6.1 bounds the Pisot degree by Lemma 5.14 = Dubickas 2022 Lemma 8
  (`Dubickas2022PisotGap`), whose complex-pair case is Baker's theorem (Saito Lemma 5.13).  The
  decay `‖β^n‖ ≤ K β^(−tn)` along a lacunary `n` gives no degree bound by itself when the
  dominant conjugates are a complex pair: exponential cancellation of `2|β₂|^n cos(nφ)` is not
  excluded without a lower bound for `‖nφ − 1/4‖`.  So the degree bound takes `hG`.

## Route (each item a declaration below)
1. `not_intCast_pow` — Saito (3.1): no `ξ^(C m)` is an integer (from `(B5′)`).
2. `exists_of_nested` — nested intervals: a chain of roots gives a `ζ` with prescribed floors.
3. `bhp_step` — one BHP prime in `[q^c, q^c + q^(21c/40)]`, and it stays below `(q+1)^c − 1`.
4. `window_of_least` — Saito Lemma 5.2 (case (I) false ⇒ (II)), via minimality of `ξ`.
5. `fract_lt_of_floor_lt` — Saito (5.1) (the half of Lemma 5.1 we need).
6. `fract_le_of_window` — Saito (5.17) (Lemma 5.3).
7. `isPisot_pow_gcd` — Saito Lemma 5.9 (Bugeaud–Dubickas).
8. `exists_pisot_of_decay_subseq` — Saito Lemma 6.1 (with `hG`).
9. `powTrace_eq_floor` — Saito Lemma 5.8.
10. `not_natDegree_two` — Saito Prop 3.1(iii) + §8, by a divisibility argument in place of the
    golden-ratio computation: for degree 2 the traces `v_n = β^n + w^n` satisfy `v_m ∣ v_(me)`
    for odd `e`, and both are primes.
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature LeanFormalizations.Mills Filter

/-- The Mills set for an exponent sequence `C`. -/
def millsSet (C : ℕ → ℕ) : Set ℝ := {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime}

/-- The `C k`-th root, `x ^ (1 / C k)`. -/
noncomputable def root (x : ℝ) (n : ℕ) : ℝ := x ^ ((n : ℝ)⁻¹)

/-- The ratio `c_k = C(k+1)/C k`. -/
noncomputable def ratio (C : ℕ → ℕ) (k : ℕ) : ℝ := (C (k + 1) : ℝ) / C k

theorem C_ge_one {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, 1 ≤ C k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · have := h2 n hn; have := ih hn; omega

theorem C_lt_succ {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, C k < C (k + 1) := by
  intro k hk
  have := h2 k hk; have := C_ge_one h1 h2 k hk; omega

theorem C_strictMonoOn {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : C a < C b := by
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact lt_trans (ih h) (C_lt_succ h1 h2 n (by omega))
    · subst h; exact C_lt_succ h1 h2 a ha

theorem le_C {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, k ≤ C k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · have := C_lt_succ h1 h2 n hn; have := ih hn; omega

/-- `(ξ^(C k))^(c_k) = ξ^(C(k+1))`. -/
theorem pow_ratio {C : ℕ → ℕ} {ξ : ℝ} (hξ : 0 < ξ) {k : ℕ} (hk : 0 < C k) :
    (ξ ^ C k) ^ ratio C k = ξ ^ C (k + 1) := by
  rw [← Real.rpow_natCast ξ (C k), ← Real.rpow_mul hξ.le, ratio,
    mul_div_cancel₀ _ (by exact_mod_cast hk.ne'), Real.rpow_natCast]

/-- The floors of a Mills number tend to infinity. -/
theorem floor_tendsto {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : 1 < ξ) : Tendsto (fun k => (⌊ξ ^ C k⌋₊ : ℝ)) atTop atTop := by
  have h0 : Tendsto (fun k : ℕ => ξ ^ k - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop_atTop_of_one_lt hξ)
  refine tendsto_atTop_mono' _ ?_ h0
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h1' : ξ ^ k ≤ ξ ^ C k := pow_le_pow_right₀ hξ.le (le_C h1 h2 k hk)
  have h2' := Nat.lt_floor_add_one (ξ ^ C k)
  linarith

/-- **Saito (3.1)**: under `(B5′)`, no power `ξ^(C m)`, `m ≥ 1`, of a Mills number is an
integer: `ξ^(C k) = (ξ^(C m))^(C k / C m)` with `C k / C m ≥ 2` would be a perfect power, not a
prime. -/
theorem not_intCast_pow {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    (h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ) := by
  intro m hm t ht
  obtain ⟨k, hkm, ⟨e, he⟩, -⟩ := h5 m hm
  have hCm := C_ge_one h1 h2 m hm
  have hCk : C (m + 1) ≤ C k := by
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · exact (C_strictMonoOn h1 h2 (by omega) h).le
    · rw [show k = m + 1 by omega]
  have hCm1 := h2 m hm
  have he2 : 2 ≤ e := by
    have : C m * 2 ≤ C m * e := by rw [← he]; omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hξ1 : 1 < ξ := hξ.1
  have ht1 : (1 : ℝ) < t := by
    rw [← ht]; exact one_lt_pow₀ hξ1 (by omega)
  have ht2 : 2 ≤ t := by
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = (u : ℤ) := ⟨t.toNat, by omega⟩
  have hu2 : 2 ≤ u := by omega
  have hpow : ξ ^ C k = ((u ^ e : ℕ) : ℝ) := by
    rw [he, pow_mul, ht]; push_cast; ring
  have hp := hξ.2 k (by omega)
  rw [hpow, Nat.floor_natCast] at hp
  rcases hp.eq_one_or_self_of_dvd u (dvd_pow_self u (by omega)) with h | h
  · omega
  · have : u ^ 1 < u ^ e := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one, ← h] at this
    exact lt_irrefl _ this

/-- **Nested intervals.**  If the roots `q_k^(1/C k)` increase weakly and the roots
`(q_k + 1)^(1/C k)` decrease strictly from `k₀` on, some `ζ > 0` has `⌊ζ^(C k)⌋₊ = q k` for all
`k ≥ k₀`. -/
theorem exists_of_nested {C : ℕ → ℕ} {q : ℕ → ℕ} {k₀ : ℕ} (hC : ∀ k ≥ k₀, 0 < C k)
    (hq : 1 ≤ q k₀)
    (hlo : ∀ k ≥ k₀, root (q k) (C k) ≤ root (q (k + 1)) (C (k + 1)))
    (hhi : ∀ k ≥ k₀, root (q (k + 1) + 1) (C (k + 1)) < root (q k + 1) (C k)) :
    ∃ ζ : ℝ, 0 < ζ ∧ (∀ k ≥ k₀, ⌊ζ ^ C k⌋₊ = q k) ∧
      ∀ k ≥ k₀, ζ < root (q k + 1) (C k) := by
  set L : ℕ → ℝ := fun k => root (q k) (C k) with hL
  set U : ℕ → ℝ := fun k => root (q k + 1) (C k) with hU
  have hLU : ∀ k ≥ k₀, L k < U k := by
    intro k hk
    exact Real.rpow_lt_rpow (by positivity) (by push_cast; linarith)
      (inv_pos.2 (by exact_mod_cast hC k hk))
  have hLmono : ∀ k ≥ k₀, ∀ d, L k ≤ L (k + d) := by
    intro k hk d
    induction d with
    | zero => simp
    | succ d ih => exact le_trans ih (hlo (k + d) (by omega))
  have hUanti : ∀ k ≥ k₀, ∀ d, U (k + d) ≤ U k := by
    intro k hk d
    induction d with
    | zero => simp
    | succ d ih => exact le_trans (hhi (k + d) (by omega)).le ih
  have hLU' : ∀ a ≥ k₀, ∀ b ≥ k₀, L a ≤ U b := by
    intro a ha b hb
    have h1 := hLmono a ha (max a b - a)
    have h2 := hUanti b hb (max a b - b)
    rw [show a + (max a b - a) = max a b by omega] at h1
    rw [show b + (max a b - b) = max a b by omega] at h2
    exact le_trans h1 (le_trans (hLU _ (le_trans ha (le_max_left _ _))).le h2)
  have hbdd : BddAbove (Set.range fun n => L (n + k₀)) :=
    ⟨U k₀, by rintro _ ⟨n, rfl⟩; exact hLU' _ (by omega) _ le_rfl⟩
  set ζ := ⨆ n, L (n + k₀) with hζ
  have hLζ : ∀ k ≥ k₀, L k ≤ ζ := by
    intro k hk
    have := le_ciSup hbdd (k - k₀)
    simpa [show k - k₀ + k₀ = k by omega] using this
  have hζU : ∀ k ≥ k₀, ζ < U k := by
    intro k hk
    have : ζ ≤ U (k + 1) := ciSup_le fun n => hLU' _ (by omega) _ (by omega)
    exact lt_of_le_of_lt this (hhi k hk)
  have hL1 : 1 ≤ L k₀ := Real.one_le_rpow (by exact_mod_cast hq) (by positivity)
  have hζ0 : 0 < ζ := by linarith [hLζ k₀ le_rfl]
  refine ⟨ζ, hζ0, fun k hk => ?_, hζU⟩
  have hCk : C k ≠ 0 := (hC k hk).ne'
  have hlo' : (q k : ℝ) ≤ ζ ^ C k := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hLζ k hk) (C k)
    change ((q k : ℝ) ^ ((C k : ℝ)⁻¹)) ^ C k ≤ _ at h
    rwa [Real.rpow_inv_natCast_pow (by positivity) hCk] at h
  have hhi' : ζ ^ C k < (q k : ℝ) + 1 := by
    have h := pow_lt_pow_left₀ (hζU k hk) hζ0.le hCk
    change _ < (((q k : ℝ) + 1) ^ ((C k : ℝ)⁻¹)) ^ C k at h
    rwa [Real.rpow_inv_natCast_pow (by positivity) hCk] at h
  rw [Nat.floor_eq_iff (by positivity)]
  exact ⟨hlo', hhi'⟩

theorem root_le_root {x y : ℝ} (hx : 0 ≤ x) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : x ^ ((n : ℝ) / m) ≤ y) : root x m ≤ root y n := by
  have e : root x m = (x ^ ((n : ℝ) / m)) ^ ((n : ℝ)⁻¹) := by
    rw [root, ← Real.rpow_mul hx]; congr 1; field_simp
  rw [e, root]
  exact Real.rpow_le_rpow (by positivity) h (by positivity)

theorem root_lt_root {x y : ℝ} (hx : 0 ≤ x) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : x ^ ((n : ℝ) / m) < y) : root x m < root y n := by
  have e : root x m = (x ^ ((n : ℝ) / m)) ^ ((n : ℝ)⁻¹) := by
    rw [root, ← Real.rpow_mul hx]; congr 1; field_simp
  rw [e, root]
  exact Real.rpow_lt_rpow (by positivity) h (inv_pos.2 (by exact_mod_cast hn))

theorem root_lt_root' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : x < y ^ ((m : ℝ) / n)) : root x m < root y n := by
  have e : root y n = (y ^ ((m : ℝ) / n)) ^ ((m : ℝ)⁻¹) := by
    rw [root, ← Real.rpow_mul hy]; congr 1; field_simp
  rw [e, root]
  exact Real.rpow_lt_rpow hx h (inv_pos.2 (by exact_mod_cast hm))

theorem root_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) : root x n ^ n = x :=
  Real.rpow_inv_natCast_pow hx hn.ne'

theorem pow_sub_pow_ge {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (n : ℕ) :
    n * y ^ (n - 1) * (x - y) ≤ x ^ n - y ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hb := one_add_mul_le_pow (a := (x - y) / y) (by
    have : 0 ≤ (x - y) / y := div_nonneg (by linarith) hy.le
    linarith) n
  have e1 : 1 + (x - y) / y = x / y := by field_simp; ring
  rw [e1, div_pow] at hb
  have hyn : 0 < y ^ n := pow_pos hy n
  have hyn' : y ^ n = y ^ (n - 1) * y := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [le_div_iff₀ hyn] at hb
  have : (1 + n * ((x - y) / y)) * y ^ n = y ^ n + n * y ^ (n - 1) * (x - y) := by
    rw [hyn']; field_simp
  linarith

theorem pow_sub_pow_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (n : ℕ) :
    x ^ n - y ^ n ≤ n * x ^ (n - 1) * (x - y) := by
  have h := abs_pow_sub_pow_le (a := x) (b := y) (n := n)
  rw [abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hy hyx n)), abs_of_nonneg (sub_nonneg.2 hyx),
    abs_of_nonneg (le_trans hy hyx), abs_of_nonneg hy, max_eq_left hyx] at h
  linarith

theorem exists_delta {C : ℕ → ℕ} {ξ : ℝ} (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    (hξ0 : 0 < ξ) :
    ∀ N, ∃ δ > (0 : ℝ), ∀ k, 1 ≤ k → k ≤ N → (⌊ξ ^ C k⌋₊ : ℝ) + δ ≤ ξ ^ C k := by
  intro N
  induction N with
  | zero => exact ⟨1, one_pos, fun k hk hk' => by omega⟩
  | succ N ih =>
    obtain ⟨δ, hδ, hδk⟩ := ih
    have hlt : (⌊ξ ^ C (N + 1)⌋₊ : ℝ) < ξ ^ C (N + 1) := by
      refine lt_of_le_of_ne (Nat.floor_le (by positivity)) ?_
      intro h
      exact hnot (N + 1) (by omega) (⌊ξ ^ C (N + 1)⌋₊ : ℤ) (by rw [Int.cast_natCast]; exact h.symm)
    refine ⟨min δ (ξ ^ C (N + 1) - ⌊ξ ^ C (N + 1)⌋₊), lt_min hδ (by linarith), fun k hk hk' => ?_⟩
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · have := hδk k hk (by omega); linarith [min_le_left δ (ξ ^ C (N + 1) - ⌊ξ ^ C (N + 1)⌋₊)]
    · have : k = N + 1 := by omega
      subst this
      linarith [min_le_right δ (ξ ^ C (N + 1) - ⌊ξ ^ C (N + 1)⌋₊)]

/-- **One BHP step.**  For all large `q` and every real `c ≥ 29/10` there is a prime `q'` with
`q^c ≤ q' ≤ q^c + q^(21c/40)` and `q' + 1 < (q + 1)^c`. -/
theorem bhp_step (hB : BakerHarmanPintz2001) :
    ∃ X : ℕ, ∀ q ≥ X, ∀ c : ℝ, 29 / 10 ≤ c → ∃ q' : ℕ, q'.Prime ∧
      (q : ℝ) ^ c ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ c + (q : ℝ) ^ (21 / 40 * c) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ c := by
  obtain ⟨d₀, hd₀, X, hX⟩ := hB
  refine ⟨max 2 ⌈X⌉₊, fun q hq c hc => ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_left _ _) hq
  have hqX : X ≤ q := le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hq0 : (0 : ℝ) < q := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  set x : ℝ := (q : ℝ) ^ c with hx
  have hxq : (q : ℝ) ≤ x := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le (by linarith) hc1
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hcount := hX x (le_trans hqX hxq)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hcpos : 0 < primesIn x (x + x ^ ((21:ℝ) / 40)) := by
    rcases Nat.eq_zero_or_pos (primesIn x (x + x ^ ((21:ℝ) / 40))) with h0 | h0
    · rw [h0] at hcount
      have : (0:ℝ) < d₀ * x ^ ((21:ℝ) / 40) / Real.log x :=
        div_pos (mul_pos hd₀ (Real.rpow_pos_of_pos hxpos _)) hlogx
      norm_num at hcount
      linarith
    · exact h0
  unfold primesIn at hcpos
  obtain ⟨p, hpmem⟩ := Finset.card_pos.1 hcpos
  simp only [Finset.mem_filter, Finset.mem_Icc] at hpmem
  obtain ⟨⟨hplo, hphi⟩, hp⟩ := hpmem
  have hxθ : x ^ ((21:ℝ) / 40) = (q : ℝ) ^ (21 / 40 * c) := by
    rw [hx, ← Real.rpow_mul hq0.le]; ring_nf
  have hplo' : x ≤ p := le_trans (Nat.le_ceil x) (by exact_mod_cast hplo)
  have hphi' : (p : ℝ) ≤ x + (q : ℝ) ^ (21 / 40 * c) := by
    rw [← hxθ]
    exact le_trans (by exact_mod_cast hphi) (Nat.floor_le (by positivity))
  refine ⟨p, hp, hplo', hphi', ?_⟩
  -- `(q+1)^c ≥ q^c + c q^(c−1)` (Bernoulli) and `q^(21c/40) + 1 ≤ 2 q^(c−1)`
  have hbern : x + c * (q : ℝ) ^ (c - 1) ≤ ((q : ℝ) + 1) ^ c := by
    have hb := one_add_mul_self_le_rpow_one_add (s := 1 / (q : ℝ)) (by
      have : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith) hc1
    have hsplit : ((q : ℝ) + 1) ^ c = (q : ℝ) ^ c * (1 + 1 / (q : ℝ)) ^ c := by
      rw [← Real.mul_rpow hq0.le (by positivity)]
      congr 1; field_simp
    have hqc1 : (q : ℝ) ^ (c - 1) = (q : ℝ) ^ c / q := Real.rpow_sub_one hq0.ne' c
    rw [hsplit, hqc1, hx]
    have hxp : 0 < (q : ℝ) ^ c := Real.rpow_pos_of_pos hq0 c
    calc (q : ℝ) ^ c + c * ((q : ℝ) ^ c / q) = (q : ℝ) ^ c * (1 + c * (1 / q)) := by
          field_simp
      _ ≤ (q : ℝ) ^ c * (1 + 1 / (q : ℝ)) ^ c := mul_le_mul_of_nonneg_left hb hxp.le
  have hθle : (q : ℝ) ^ (21 / 40 * c) ≤ (q : ℝ) ^ (c - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h1le : (1 : ℝ) ≤ (q : ℝ) ^ (c - 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hpos : 0 < (q : ℝ) ^ (c - 1) := by linarith
  nlinarith

/-- **Saito Lemma 5.2** (ratios eventually `≥ 29/10`, so BHP alone continues the chain).  If the
floors `p_k = ⌊ξ^(C k)⌋₊` of the least Mills number satisfy the lower chain condition
`p_k^(1/C k) ≤ p_(k+1)^(1/C(k+1))` from some `k₁` on, then eventually
`p_(k+1) ≤ p_k^(c_k) + p_k^(21 c_k/40)`. -/
theorem window_of_least (hB : BakerHarmanPintz2001) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    {k₁ : ℕ} (hlow : ∀ k ≥ k₁, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1))) :
    ∃ k₀, ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (21 / 40 * ratio C k) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hX⟩ := bhp_step hB
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  set k₁' := max (max k₁ K₀) 1 with hk₁'
  obtain ⟨δ, hδ, hδk⟩ := exists_delta hnot hξ0 k₁'
  set B : ℝ := (C k₁' : ℝ) * ξ ^ C k₁' with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop (X : ℝ))
  set M2 := ⌈B / δ⌉₊ + 1 with hM2
  obtain ⟨m, hm, hviol⟩ := hcon (max (max M1 M2) (k₁' + 1))
  have hmM1 : M1 ≤ m := by omega
  have hmM2 : M2 ≤ m := by omega
  have hmk : k₁' + 1 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := by omega
  -- the chain
  have hratio : ∀ k ≥ K₀, 1 ≤ k → (29 : ℝ) / 10 ≤ ratio C k := by
    intro k hk hk1
    have hCk : (0 : ℝ) < C k := by exact_mod_cast hCge k hk1
    rw [ratio, le_div_iff₀ hCk]; exact hEv k hk
  have hX' : ∀ q k : ℕ, ∃ q' : ℕ, X ≤ q → K₀ ≤ k → 1 ≤ k → (q'.Prime ∧
      (q : ℝ) ^ ratio C k ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ ratio C k + (q : ℝ) ^ (21 / 40 * ratio C k) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ ratio C k) := by
    intro q k
    by_cases h : X ≤ q ∧ K₀ ≤ k ∧ 1 ≤ k
    · obtain ⟨q', hq'⟩ := hX q h.1 (ratio C k) (hratio k h.2.1 h.2.2)
      exact ⟨q', fun _ _ _ => hq'⟩
    · exact ⟨0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose nxt hnxt using hX'
  let r : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (p m) (fun n r => nxt r (m + n)) n
  have hr0 : r 0 = p m := rfl
  have hrs : ∀ n, r (n + 1) = nxt (r n) (m + n) := fun n => rfl
  have hpmX : X ≤ p m := by exact_mod_cast hM1 m hmM1
  have hrX : ∀ n, X ≤ r n ∧ (r n).Prime := by
    intro n
    induction n with
    | zero => exact ⟨hpmX, hξS.2 m hm1⟩
    | succ n ih =>
      obtain ⟨hpr, hlo, -, -⟩ := hnxt (r n) (m + n) ih.1 (by omega) (by omega)
      refine ⟨?_, by rw [hrs]; exact hpr⟩
      rw [hrs]
      have hq1 : (1 : ℝ) ≤ (Nat.cast (r n) : ℝ) := by exact_mod_cast ih.2.one_lt.le
      have : ((r n : ℕ) : ℝ) ≤ ((r n : ℕ) : ℝ) ^ ratio C (m + n) := by
        calc ((r n : ℕ) : ℝ) = ((r n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1
              (by linarith [hratio (m + n) (by omega) (by omega)])
      have : ((r n : ℕ) : ℝ) ≤ nxt (r n) (m + n) := le_trans this hlo
      exact le_trans ih.1 (by exact_mod_cast this)
  set q : ℕ → ℕ := fun j => r (j - m) with hq
  have hqs : ∀ j ≥ m, q (j + 1) = nxt (q j) j := by
    intro j hj
    simp only [hq, show j + 1 - m = (j - m) + 1 by omega, hrs, show m + (j - m) = j by omega]
  have hstep : ∀ j ≥ m, ((q j : ℕ) : ℝ) ^ ratio C j ≤ ((q (j + 1) : ℕ) : ℝ) ∧
      ((q (j + 1) : ℕ) : ℝ) ≤ ((q j : ℕ) : ℝ) ^ ratio C j + ((q j : ℕ) : ℝ) ^ (21 / 40 * ratio C j) ∧
      ((q (j + 1) : ℕ) : ℝ) + 1 < (((q j : ℕ) : ℝ) + 1) ^ ratio C j := by
    intro j hj
    rw [hqs j hj]
    obtain ⟨-, a, b, c⟩ := hnxt (q j) j (hrX (j - m)).1 (by omega) (by omega)
    exact ⟨a, b, c⟩
  have hCpos : ∀ k ≥ m, 0 < C k := fun k hk => hCge k (by omega)
  have hrat_eq : ∀ k ≥ m, ratio C k = ((C (k + 1) : ℕ) : ℝ) / (C k : ℕ) := fun k _ => rfl
  obtain ⟨ζ, hζ0, hζfl, hζU⟩ := exists_of_nested (q := q) (k₀ := m) hCpos
    (by simp only [hq, Nat.sub_self, hr0]; exact (hξS.2 m hm1).one_lt.le)
    (fun j hj => root_le_root (Nat.cast_nonneg _) (hCpos j hj) (hCpos (j + 1) (by omega))
      (hstep j hj).1)
    (fun j hj => root_lt_root' (by positivity) (by positivity) (hCpos (j + 1) (by omega))
      (hCpos j hj) (hstep j hj).2.2)
  have hqm : q m = p m := by simp [hq, hr0]
  -- `ζ < ξ`
  have hq1lt : q (m + 1) + 1 ≤ p (m + 1) := by
    have h := (hstep m le_rfl).2.1
    rw [hqm] at h
    have : ((q (m + 1) : ℕ) : ℝ) < p (m + 1) := lt_of_le_of_lt h (hviol)
    exact_mod_cast this
  have hζξ : ζ < ξ := by
    have hU := hζU (m + 1) (by omega)
    have h2' : root (((q (m + 1) : ℕ) : ℝ) + 1) (C (m + 1)) ≤ root (ξ ^ C (m + 1)) (C (m + 1)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have : ((q (m + 1) + 1 : ℕ) : ℝ) ≤ p (m + 1) := by exact_mod_cast hq1lt
      push_cast at this
      exact le_trans this (Nat.floor_le (by positivity))
    have h3' : root (ξ ^ C (m + 1)) (C (m + 1)) = ξ :=
      Real.pow_rpow_inv_natCast hξ0.le (hCpos (m + 1) (by omega)).ne'
    linarith
  -- `ζ^(C m) ≥ p m`
  have hζm : (p m : ℝ) ≤ ζ ^ C m := by
    have := hζfl m le_rfl
    rw [hqm] at this
    rw [← this]; exact Nat.floor_le (by positivity)
  have hpm2 : (2 : ℝ) ≤ p m := by exact_mod_cast (hξS.2 m hm1).two_le
  have hζ1 : 1 < ζ := by
    by_contra h
    push_neg at h
    have : ζ ^ C m ≤ 1 := pow_le_one₀ hζ0.le h
    linarith
  -- closeness: `C m (ξ − ζ) < 1`
  have hclose : (C m : ℝ) * (ξ - ζ) < 1 := by
    have hge := pow_sub_pow_ge hζ0 hζξ.le (C m)
    have hlt : ξ ^ C m < (p m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpow1 : (1 : ℝ) ≤ ζ ^ (C m - 1) := one_le_pow₀ hζ1.le
    have hd : 0 ≤ ξ - ζ := by linarith
    have hCm0 : (0 : ℝ) ≤ C m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hCm0 hd)]
  -- the floors of `ζ`
  have hfloor : ∀ k ≥ 1, ⌊ζ ^ C k⌋₊ = p k ∨ ⌊ζ ^ C k⌋₊ = q k ∧ m ≤ k := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · left
      rw [Nat.floor_eq_iff (by positivity)]
      refine ⟨?_, lt_of_lt_of_le (pow_lt_pow_left₀ hζξ hζ0.le (by have := hCge k hk; omega))
        (Nat.lt_floor_add_one _).le⟩
      rcases Nat.lt_or_ge k k₁' with hk1 | hk1
      · -- the `δ` trick
        have hδ' := hδk k hk hk1.le
        have hle := pow_sub_pow_le hζ0.le hζξ.le (C k)
        have hCk : (C k : ℝ) ≤ C k₁' := by
          rcases Nat.lt_or_ge k k₁' with h | h
          · exact_mod_cast (C_strictMonoOn h1 h2 hk h).le
          · omega
        have hξk : ξ ^ (C k - 1) ≤ ξ ^ C k₁' :=
          pow_le_pow_right₀ hξ1.le (le_trans (Nat.sub_le _ _) (by exact_mod_cast hCk))
        have hBδ : B < (C m : ℝ) * δ := by
          have h1' : B / δ < M2 := by
            have := Nat.le_ceil (B / δ); rw [hM2]; push_cast; linarith
          have h2' : (M2 : ℝ) ≤ C m := by exact_mod_cast le_trans hmM2 (le_C h1 h2 m hm1)
          rw [div_lt_iff₀ hδ] at h1'
          nlinarith
        have hd : 0 ≤ ξ - ζ := by linarith
        have hkey : ξ ^ C k - ζ ^ C k < δ := by
          have e1 : (C k : ℝ) * ξ ^ (C k - 1) * (ξ - ζ) ≤ B * (ξ - ζ) := by
            apply mul_le_mul_of_nonneg_right _ hd
            exact mul_le_mul hCk hξk (by positivity) (by positivity)
          have hCm : (0 : ℝ) < C m := by exact_mod_cast hCge m hm1
          have e2 : B * (ξ - ζ) < δ := by
            by_cases hB0' : B = 0
            · rw [hB0']; simpa using hδ
            have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB0')
            have : B * (ξ - ζ) * C m < δ * C m := by
              calc B * (ξ - ζ) * C m = B * ((C m : ℝ) * (ξ - ζ)) := by ring
                _ < B * 1 := mul_lt_mul_of_pos_left hclose hBpos
                _ = B := by ring
                _ < (C m : ℝ) * δ := hBδ
                _ = δ * C m := by ring
            exact lt_of_mul_lt_mul_right this hCm.le
          linarith
        linarith
      · -- the lower chain from `k` to `m`
        have hchain : ∀ d, k + d ≤ m → root (p k) (C k) ≤ root (p (k + d)) (C (k + d)) := by
          intro d
          induction d with
          | zero => intro _; simp
          | succ d ih =>
            intro hd
            exact le_trans (ih (by omega)) (hlow (k + d) (by omega))
        have h1' := hchain (m - k) (by omega)
        rw [show k + (m - k) = m by omega] at h1'
        have h2' : root (p m) (C m) ≤ ζ := by
          have := Real.rpow_le_rpow (by positivity) hζm
            (inv_nonneg.2 (Nat.cast_nonneg (C m)))
          rwa [Real.pow_rpow_inv_natCast hζ0.le (hCpos m le_rfl).ne'] at this
        have h3' := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_trans h1' h2')
          (C k)
        rwa [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by have := hCge k hk; omega)]
          at h3'
    · right
      exact ⟨hζfl k hkm, hkm⟩
  have hζS : ζ ∈ millsSet C := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rcases hfloor k hk with h | ⟨h, hkm⟩
    · rw [h]; exact hξS.2 k hk
    · rw [h]; exact (hrX (k - m)).2
  exact absurd (hξ.2 hζS) (not_le.2 hζξ)

/-- Bernoulli for real exponents: `y^c + c y^(c−1)(x − y) ≤ x^c` for `1 ≤ y ≤ x`, `c ≥ 1`. -/
theorem bernoulli_rpow {x y c : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) (hc : 1 ≤ c) :
    y ^ c + c * (x - y) * y ^ (c - 1) ≤ x ^ c := by
  have hy0 : 0 < y := by linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := (x - y) / y) (by
    have : 0 ≤ (x - y) / y := div_nonneg (by linarith) hy0.le
    linarith) hc
  have e1 : 1 + (x - y) / y = x / y := by field_simp; ring
  rw [e1, Real.div_rpow (by linarith) hy0.le] at hb
  have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy0 c
  rw [le_div_iff₀ hyc] at hb
  have hyc1 : y ^ (c - 1) = y ^ c / y := Real.rpow_sub_one hy0.ne' c
  rw [hyc1]
  have : (1 + c * ((x - y) / y)) * y ^ c = y ^ c + c * (x - y) * (y ^ c / y) := by
    field_simp
  linarith

/-- **Saito (5.1)**: if `⌊x^c⌋ < ⌊x⌋^c` (`x ≥ 1`, `c ≥ 1`) then `c·{x}·⌊x⌋^(c−1) < 1`. -/
theorem fract_lt_of_floor_lt {x c : ℝ} (hx : 1 ≤ x) (hc : 1 ≤ c)
    (h : (⌊x ^ c⌋₊ : ℝ) < (⌊x⌋₊ : ℝ) ^ c) :
    c * Int.fract x * (⌊x⌋₊ : ℝ) ^ (c - 1) < 1 := by
  have hx0 : 0 ≤ x := by linarith
  set y : ℝ := (⌊x⌋₊ : ℝ) with hy
  have hy1 : 1 ≤ y := by
    have := Nat.floor_pos.2 hx; rw [hy]; exact_mod_cast this
  have hfr : Int.fract x = x - y := by
    rw [hy, Int.fract, ← Int.natCast_floor_eq_floor hx0]; push_cast; ring
  have hyx : y ≤ x := Nat.floor_le hx0
  have hb := bernoulli_rpow hy1 hyx hc
  have hlt : x ^ c < (⌊x ^ c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hfr]
  linarith

/-- **Saito (5.17)**: if `x^c < P + 1` with `P ≤ p^c + p^(θc)`, `p = ⌊x⌋ ≥ 1`, `c ≥ 1`,
`0 ≤ θ < 1`, then `{x} ≤ 2 / (c p^((1−θ)c − 1))`. -/
theorem fract_le_of_window {x c θ : ℝ} {P : ℕ} (hx : 1 ≤ x) (hc : 1 ≤ c) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hxc : x ^ c < (P : ℝ) + 1)
    (hP : (P : ℝ) ≤ (⌊x⌋₊ : ℝ) ^ c + (⌊x⌋₊ : ℝ) ^ (θ * c)) :
    Int.fract x ≤ 2 / (c * (⌊x⌋₊ : ℝ) ^ ((1 - θ) * c - 1)) := by
  have hx0 : 0 ≤ x := by linarith
  set y : ℝ := (⌊x⌋₊ : ℝ) with hy
  have hy1 : 1 ≤ y := by
    have := Nat.floor_pos.2 hx; rw [hy]; exact_mod_cast this
  have hy0 : 0 < y := by linarith
  have hfr : Int.fract x = x - y := by
    rw [hy, Int.fract, ← Int.natCast_floor_eq_floor hx0]; push_cast; ring
  have hyx : y ≤ x := Nat.floor_le hx0
  have hb := bernoulli_rpow hy1 hyx hc
  have hθc : y ^ (θ * c) ≥ 1 := Real.one_le_rpow hy1 (by positivity)
  -- `c y^(c−1) (x − y) < 2 y^(θc)`
  have hkey : c * (x - y) * y ^ (c - 1) < 2 * y ^ (θ * c) := by linarith
  have hsplit : y ^ (c - 1) = y ^ ((1 - θ) * c - 1) * y ^ (θ * c) := by
    rw [← Real.rpow_add hy0]; ring_nf
  have hpos : 0 < c * y ^ ((1 - θ) * c - 1) := by positivity
  rw [hfr, le_div_iff₀ hpos]
  have hθpos : 0 < y ^ (θ * c) := by positivity
  rw [hsplit] at hkey
  have : (x - y) * (c * y ^ ((1 - θ) * c - 1)) * y ^ (θ * c) < 2 * y ^ (θ * c) := by
    nlinarith
  exact (lt_of_mul_lt_mul_right this hθpos.le).le

/-- A root `z` of the minimal polynomial of `γ` has `z^e` a root of the minimal polynomial of
`γ^e`. -/
theorem pow_mem_aroots {γ : ℝ} (hγ : IsIntegral ℚ γ) {z : ℂ} (hz : z ∈ (minpoly ℚ γ).aroots ℂ)
    (e : ℕ) : z ^ e ∈ (minpoly ℚ (γ ^ e)).aroots ℂ := by
  open Polynomial in
  have hγe : IsIntegral ℚ (γ ^ e) := hγ.pow e
  set P := minpoly ℚ (γ ^ e) with hP
  have hP0 : P ≠ 0 := minpoly.ne_zero hγe
  have hdvd : minpoly ℚ γ ∣ P.comp (X ^ e) := by
    apply minpoly.dvd
    rw [aeval_comp, aeval_X_pow, hP, minpoly.aeval]
  rw [mem_aroots] at hz ⊢
  refine ⟨hP0, ?_⟩
  obtain ⟨R, hR⟩ := hdvd
  have := congrArg (aeval z) hR
  rw [map_mul, hz.2, zero_mul, aeval_comp, aeval_X_pow] at this
  exact this

/-- **Saito Lemma 5.9** (Bugeaud–Dubickas 2008, Lemma 8): if `α^a` and `α^b` are Pisot then so is
`α^(gcd a b)`. -/
theorem isPisot_pow_gcd {α : ℝ} (hα : 1 < α) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpa : IsPisot (α ^ a)) (hpb : IsPisot (α ^ b)) : IsPisot (α ^ Nat.gcd a b) := by
  classical
  set d := Nat.gcd a b with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  rw [← hd] at ha' hb'
  have hcop : Nat.gcd a' b' = 1 := by
    have := Nat.gcd_mul_left d a' b'
    rw [← ha', ← hb', ← hd] at this
    have h' : d * 1 = d * Nat.gcd a' b' := by rw [mul_one]; exact this
    exact (Nat.eq_of_mul_eq_mul_left hd0 h').symm
  have hαint : IsIntegral ℤ α := IsIntegral.of_pow ha hpa.2.1
  set γ := α ^ d with hγ
  have hγ1 : 1 < γ := one_lt_pow₀ hα hd0.ne'
  have hγint : IsIntegral ℤ γ := hαint.pow d
  refine ⟨hγ1, hγint, fun z hz => ?_⟩
  have hγQ : IsIntegral ℚ γ := hγint.tower_top
  have hsep : (minpoly ℚ γ).Separable := (minpoly.irreducible hγQ).separable
  have hnodup : ((minpoly ℚ γ).aroots ℂ).Nodup :=
    Polynomial.nodup_roots ((Polynomial.separable_map _).mpr hsep)
  have hzne : z ≠ (γ : ℂ) := (hnodup.mem_erase_iff.1 hz).1
  have hzr : z ∈ (minpoly ℚ γ).aroots ℂ := Multiset.mem_of_mem_erase hz
  by_contra hbig
  push_neg at hbig
  -- `z^e` is the dominant root of `α^(d e)` for `e = a', b'`
  have key : ∀ e : ℕ, 0 < e → IsPisot (α ^ (d * e)) → z ^ e = (γ : ℂ) ^ e := by
    intro e he hp
    have hmem := pow_mem_aroots hγQ hzr e
    have hγe : γ ^ e = α ^ (d * e) := by rw [hγ, pow_mul]
    rw [hγe] at hmem
    by_contra hne
    have hne' : z ^ e ≠ ((α ^ (d * e) : ℝ) : ℂ) := by
      rw [← hγe]; push_cast; exact hne
    have := hp.2.2 _ (Multiset.mem_erase_of_ne hne' |>.2 hmem)
    rw [norm_pow] at this
    have : (1 : ℝ) ≤ ‖z‖ ^ e := one_le_pow₀ hbig
    linarith
  have hza := key a' (by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h, mul_zero] at ha'; omega
    · exact h) (by rw [← ha']; exact hpa)
  have hzb := key b' (by
    rcases Nat.eq_zero_or_pos b' with h | h
    · rw [h, mul_zero] at hb'; omega
    · exact h) (by rw [← hb']; exact hpb)
  have hγ0 : (γ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : γ ≠ 0)
  set u := z / (γ : ℂ) with hu
  have hua : u ^ a' = 1 := by rw [hu, div_pow, hza, div_self (pow_ne_zero _ hγ0)]
  have hub : u ^ b' = 1 := by rw [hu, div_pow, hzb, div_self (pow_ne_zero _ hγ0)]
  have hu1 : u ^ Nat.gcd a' b' = 1 := pow_gcd_eq_one.2 ⟨hua, hub⟩
  rw [hcop, pow_one, hu, div_eq_one_iff_eq hγ0] at hu1
  exact hzne hu1

/-- **Dubickas's dichotomy under decay**: exponential decay of `‖α^(s k)‖` along `s` forces some
`α^(s m)` to be Pisot. -/
theorem exists_pisot_of_decay_dub (hD : Dubickas2022)
    {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {s : ℕ → ℕ} (hs : StrictMono s)
    (hs0 : 0 < s 0) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ k in atTop, |α ^ s k - (round (α ^ s k) : ℝ)| ≤ K * α ^ (-(μ * s k))) :
    ∃ m, IsPisot (α ^ s m) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hlogα : 0 < Real.log α := Real.log_pos hα
  rcases hD α halg hα 1 one_pos s hs hs0 with hpisot | hsep
  · exact hpisot
  exfalso
  set ε : ℝ := μ * Real.log α / 2 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨k₀, hk₀⟩ := hsep ε hε0
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 hdecay
  set k : ℕ := max k₀ (max k₁ (⌈K / ε⌉₊ + 1)) with hk
  have h1 := hk₀ k (le_max_left _ _)
  have h2 := hk₁ k (le_trans (le_max_left _ _) (le_max_right _ _))
  have hkK : ⌈K / ε⌉₊ + 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  set N : ℕ := s k with hN
  have hNk : k ≤ N := hs.id_le k
  simp only [Nat.cast_one, one_mul] at h1
  have hrw : (α ^ (-(μ * (N : ℝ))) : ℝ) = Real.exp (-(2 * ε * N)) := by
    rw [Real.rpow_def_of_pos hα0, hε]; ring_nf
  rw [hrw] at h2
  have hchain : Real.exp (-(ε * N)) < K * Real.exp (-(2 * ε * N)) := lt_of_lt_of_le h1 h2
  have hexp : Real.exp (ε * N) < K := by
    have h := mul_lt_mul_of_pos_right hchain (Real.exp_pos (2 * ε * (N:ℝ)))
    have e1 : Real.exp (-(ε * (N:ℝ))) * Real.exp (2 * ε * (N:ℝ)) = Real.exp (ε * (N:ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : K * Real.exp (-(2 * ε * (N:ℝ))) * Real.exp (2 * ε * (N:ℝ)) = K := by
      rw [mul_assoc, ← Real.exp_add, show -(2 * ε * (N:ℝ)) + 2 * ε * (N:ℝ) = 0 by ring,
        Real.exp_zero, mul_one]
    rwa [e1, e2] at h
  have hKlt : K < ε * N := by
    have h3 : (K / ε : ℝ) ≤ (⌈K / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h4 : ((⌈K / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      have : (⌈K / ε⌉₊ : ℕ) + 1 ≤ N := le_trans hkK hNk
      exact_mod_cast this
    have h5 : (K / ε : ℝ) < (N : ℝ) := by linarith
    calc K = ε * (K / ε) := by field_simp
      _ < ε * N := by exact mul_lt_mul_of_pos_left h5 hε0
  have := Real.add_one_le_exp (ε * (N : ℝ))
  linarith

/-- **Saito Lemma 6.1** (with `Dubickas2022PisotGap` for the degree bound).  If an algebraic
`α > 1` satisfies `|α^(s k) − round| ≤ K α^(−μ s k)` for all large `k`, along a strictly
increasing `s` with `s 0 > 0`, and no power `α^(s k)` is an integer, then some `α^g` is Pisot,
`g ∣ s k` eventually, `α^g` has degree `≥ 2`, and `(deg − 1) μ ≤ 1`. -/
theorem exists_pisot_of_decay_subseq (hD : Dubickas2022) (hG : Dubickas2022PisotGap)
    {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {s : ℕ → ℕ} (hs : StrictMono s)
    (hs0 : 0 < s 0) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ k in atTop, |α ^ s k - (round (α ^ s k) : ℝ)| ≤ K * α ^ (-(μ * s k)))
    (hnot : ∀ k, ∀ t : ℤ, α ^ s k ≠ (t : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ IsPisot (α ^ g) ∧ (∀ᶠ k in atTop, g ∣ s k) ∧
      2 ≤ (minpoly ℚ (α ^ g)).natDegree ∧
      ((Multiset.card (otherConj (α ^ g)) : ℝ)) * μ ≤ 1 := by
  classical
  have hα0 : (0 : ℝ) < α := by linarith
  have hspos : ∀ k, 0 < s k := fun k => lt_of_lt_of_le hs0 (hs.monotone (Nat.zero_le k))
  have hex : ∃ g, 1 ≤ g ∧ IsPisot (α ^ g) := by
    obtain ⟨m, hm⟩ := exists_pisot_of_decay_dub hD halg hα hs hs0 hμ hK hdecay
    exact ⟨s m, hspos m, hm⟩
  set g := Nat.find hex with hg
  obtain ⟨hg1, hpis⟩ := Nat.find_spec hex
  have hgmin : ∀ g' < g, ¬ (1 ≤ g' ∧ IsPisot (α ^ g')) := fun g' h => Nat.find_min hex h
  -- `g ∣ s k` eventually
  have hdiv : ∀ᶠ k in atTop, g ∣ s k := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop (hcon.and_eventually hdecay)
    have hs' : StrictMono (s ∘ φ) := hs.comp hφ
    obtain ⟨r, hr⟩ := exists_pisot_of_decay_dub hD halg hα hs' (hspos _) hμ hK
      (Eventually.of_forall fun n => (hφP n).2)
    have hgcd := isPisot_pow_gcd hα (by omega) (hspos _) hpis hr
    have hle : Nat.gcd g (s (φ r)) ≤ g := Nat.gcd_le_left _ (by omega)
    have hne : Nat.gcd g (s (φ r)) ≠ g := by
      intro h
      exact (hφP r).1 (h ▸ Nat.gcd_dvd_right g (s (φ r)))
    exact hgmin _ (lt_of_le_of_ne hle hne) ⟨Nat.gcd_pos_of_pos_left _ (by omega), hgcd⟩
  set β := α ^ g with hβ
  have hpow : ∀ k, g ∣ s k → β ^ (s k / g) = α ^ s k := by
    intro k hk; rw [hβ, ← pow_mul, Nat.mul_div_cancel' hk]
  obtain ⟨k₂, hk₂⟩ := eventually_atTop.1 hdiv
  have hnd : 2 ≤ (minpoly ℚ β).natDegree := by
    refine pisot_two_le_natDegree hpis fun t ht => ?_
    have h := hpow k₂ (hk₂ k₂ le_rfl)
    rw [ht] at h
    exact hnot k₂ (t ^ (s k₂ / g)) (by rw [← h]; push_cast; ring)
  -- the conjugate power sum is eventually `< 1/2`
  have hmax := conjMax_lt_one hpis
  have hmax0 := conjMax_nonneg β
  have htend : Tendsto
      (fun n : ℕ => (Multiset.card (otherConj β) : ℝ) * conjMax β ^ n) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hmax0 hmax
    simpa using this.const_mul (Multiset.card (otherConj β) : ℝ)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hdecay
  have hfreq : ∃ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ ≤ K * (β ^ (-(μ * n)) : ℝ) := by
    rw [frequently_atTop]
    intro a
    set k := max (max k₀ k₂) ((a + N₁) * g + 1) with hk
    have hkd : g ∣ s k := hk₂ k (by omega)
    set n := s k / g with hn
    have hng : (a + N₁) ≤ n := by
      rw [hn, Nat.le_div_iff_mul_le (by omega)]
      have h1 : (a + N₁) * g + 1 ≤ k := le_max_right _ _
      have h2 : k ≤ s k := hs.id_le k
      omega
    refine ⟨n, by omega, ?_⟩
    obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hpis n
    have hcps : conjPowSum β n = ((((t : ℝ) - β ^ n : ℝ)) : ℂ) := by
      push_cast
      push_cast at ht
      linear_combination ht
    have hnorm : ‖conjPowSum β n‖ = |β ^ n - (t : ℝ)| := by
      rw [hcps, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have hhalf : |β ^ n - (t : ℝ)| < 1 / 2 := by
      rw [← hnorm]
      exact lt_of_le_of_lt (norm_conjPowSum_le β n) (hN₁ n (by omega))
    have hround : round (β ^ n) = t := by
      have hz : round (β ^ n - (t : ℝ)) = 0 := by
        rw [round_eq_zero_iff]
        exact ⟨(abs_lt.1 hhalf).1.le, (abs_lt.1 hhalf).2⟩
      have := round_add_intCast (β ^ n - (t : ℝ)) t
      rw [hz, sub_add_cancel] at this
      simpa using this
    have hA := hk₀ k (by omega)
    rw [← hpow k hkd, ← hn, hround] at hA
    have hbeta : (β ^ (-(μ * (n : ℝ))) : ℝ) = α ^ (-(μ * (s k : ℝ))) := by
      rw [hβ, ← Real.rpow_natCast α g, ← Real.rpow_mul hα0.le]
      congr 1
      have : ((s k : ℕ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [hn]; exact_mod_cast (Nat.mul_div_cancel' hkd).symm
      rw [this]; ring
    rw [hnorm, hbeta]
    exact hA
  exact ⟨g, hg1, hpis, hdiv, hnd, pisot_degree_bound hG hpis hnd hμ hK hfreq⟩

/-- **Saito Lemma 5.8**: for a Pisot `β` and all large `N`, `Int.fract (β^N) < 1/2` forces
`Tr(β^N) = ⌊β^N⌋`. -/
theorem powTrace_eq_floor {β : ℝ} (hβ : IsPisot β) :
    ∀ᶠ N in atTop, Int.fract (β ^ N) < 1 / 2 → powTrace β N = ((⌊β ^ N⌋₊ : ℕ) : ℂ) := by
  sorry

/-- **No degree 2** (Saito Prop 3.1(iii) + §8, by divisibility).  A degree-2 Pisot `β` cannot have
`⌊β^(n k)⌋₊` prime with `Int.fract (β^(n k)) < 1/2` for all large `k`, along exponents `n` with
`n a ∣ n b`, `n a < n b` for infinitely many pairs `a < b`.  Here we state the form used: for
every `M` there are `M ≤ a < b` with `n a ∣ n b` and `n a < n b`. -/
theorem not_natDegree_two {β : ℝ} (hβ : IsPisot β) (hdeg : (minpoly ℚ β).natDegree = 2)
    {n : ℕ → ℕ} {K : ℕ}
    (hprime : ∀ k ≥ K, (⌊β ^ n k⌋₊).Prime)
    (hfrac : ∀ k ≥ K, Int.fract (β ^ n k) < 1 / 2)
    (hdiv : ∀ M, ∃ a ≥ M, ∃ b > a, n a ∣ n b ∧ n a < n b)
    (hlarge : Tendsto n atTop atTop) : False := by
  sorry

/-! ### Assembly lemmas -/

/-- **Case (I) of Saito Lemma 5.2 is impossible for algebraic `ξ`** (Saito Lemma 6.2, ratios
`≥ 29/10`): the lower chain condition holds eventually. -/
theorem eventually_low (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {C : ℕ → ℕ}
    (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    (halg : IsAlgebraic ℚ ξ) :
    ∃ k₁, ∀ k ≥ k₁, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1)) := by
  by_contra hcon
  push_neg at hcon
  have hξ1 : 1 < ξ := hξ.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  have hfreq : ∃ᶠ k in atTop, max K₀ 1 ≤ k ∧
      root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1)) < root ⌊ξ ^ C k⌋₊ (C k) := by
    rw [frequently_atTop]
    intro a
    obtain ⟨k, hk, hlt⟩ := hcon (max a (max K₀ 1))
    exact ⟨k, by omega, by omega, hlt⟩
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  have hφ1 : ∀ n, 1 ≤ φ n := fun n => by have := (hφP n).1; omega
  set s : ℕ → ℕ := fun n => C (φ n) with hs
  have hsmono : StrictMono s := fun a b hab =>
    C_strictMonoOn h1 h2 (hφ1 a) (hφ hab)
  have hdecay : ∀ᶠ n in atTop, |ξ ^ s n - (round (ξ ^ s n) : ℝ)| ≤
      4 * ξ ^ (-((19 / 10 : ℝ) * s n)) := by
    refine Eventually.of_forall fun n => ?_
    obtain ⟨hkK, hlt⟩ := hφP n
    set k := φ n with hk
    have hk1 : 1 ≤ k := by omega
    have hCk : 0 < C k := hCge k hk1
    have hc : (29 : ℝ) / 10 ≤ ratio C k := by
      have hCk' : (0 : ℝ) < C k := by exact_mod_cast hCk
      rw [ratio, le_div_iff₀ hCk']; exact hEv k (by omega)
    set x := ξ ^ C k with hx
    have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
    have hx0 : 0 < x := by linarith
    -- the failed lower condition: `⌊x^c⌋ < ⌊x⌋^c`
    have hfl : (⌊x ^ ratio C k⌋₊ : ℝ) < (⌊x⌋₊ : ℝ) ^ ratio C k := by
      rw [hx, pow_ratio hξ0 hCk]
      by_contra h
      push_neg at h
      exact absurd (root_le_root (Nat.cast_nonneg _) hCk (hCge _ (by omega)) h) (not_le.2 hlt)
    have hf := fract_lt_of_floor_lt hx1 (by linarith) hfl
    set p : ℝ := (⌊x⌋₊ : ℝ) with hp
    have hp1 : 1 ≤ p := by have := Nat.floor_pos.2 hx1; rw [hp]; exact_mod_cast this
    have hpx : x ≤ 2 * p := by have := Nat.lt_floor_add_one x; rw [hp]; linarith
    have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
      have := round_le x ⌊x⌋
      rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
    have hpow : p ^ (19 / 10 : ℝ) ≤ p ^ (ratio C k - 1) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hp0 : 0 < p ^ (19 / 10 : ℝ) := by positivity
    have hfr0 := Int.fract_nonneg x
    -- `fract x · p^(19/10) < 1`
    have h1' : Int.fract x * p ^ (19 / 10 : ℝ) < 1 := by
      have e1 : Int.fract x * p ^ (19 / 10 : ℝ) ≤ Int.fract x * p ^ (ratio C k - 1) :=
        mul_le_mul_of_nonneg_left hpow hfr0
      have e0 : 0 ≤ Int.fract x * p ^ (ratio C k - 1) := mul_nonneg hfr0 (by positivity)
      have e2 : Int.fract x * p ^ (ratio C k - 1) ≤ ratio C k * Int.fract x * p ^ (ratio C k - 1) := by
        rw [mul_assoc]; nlinarith
      linarith
    -- `p^(−19/10) ≤ 4 x^(−19/10)`
    have h2' : (p ^ (19 / 10 : ℝ))⁻¹ ≤ 4 * x ^ (-(19 / 10 : ℝ)) := by
      have hxp : x ^ (19 / 10 : ℝ) ≤ (2 * p) ^ (19 / 10 : ℝ) :=
        Real.rpow_le_rpow hx0.le hpx (by norm_num)
      have h2p : (2 * p) ^ (19 / 10 : ℝ) = 2 ^ (19 / 10 : ℝ) * p ^ (19 / 10 : ℝ) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h24 : (2 : ℝ) ^ (19 / 10 : ℝ) ≤ 4 := by
        calc (2 : ℝ) ^ (19 / 10 : ℝ) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
      have hx19 : 0 < x ^ (19 / 10 : ℝ) := by positivity
      rw [Real.rpow_neg hx0.le, inv_le_iff_one_le_mul₀ hp0]
      have : x ^ (19 / 10 : ℝ) ≤ 4 * p ^ (19 / 10 : ℝ) := by nlinarith
      calc (1 : ℝ) = (x ^ (19 / 10 : ℝ))⁻¹ * x ^ (19 / 10 : ℝ) := (inv_mul_cancel₀ hx19.ne').symm
        _ ≤ (x ^ (19 / 10 : ℝ))⁻¹ * (4 * p ^ (19 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 4 * (x ^ (19 / 10 : ℝ))⁻¹ * p ^ (19 / 10 : ℝ) := by ring
    have hxe : x ^ (-(19 / 10 : ℝ)) = ξ ^ (-((19 / 10 : ℝ) * s n)) := by
      rw [show s n = C k from rfl, hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
    have hfrac_le : Int.fract x ≤ (p ^ (19 / 10 : ℝ))⁻¹ := by
      rw [← one_div, le_div_iff₀ hp0]; exact h1'.le
    calc |ξ ^ s n - (round (ξ ^ s n) : ℝ)| = |x - (round x : ℝ)| := rfl
      _ ≤ Int.fract x := hround
      _ ≤ (p ^ (19 / 10 : ℝ))⁻¹ := hfrac_le
      _ ≤ 4 * x ^ (-(19 / 10 : ℝ)) := h2'
      _ = 4 * ξ ^ (-((19 / 10 : ℝ) * s n)) := by rw [hxe]
  have hnot' : ∀ n, ∀ t : ℤ, ξ ^ s n ≠ (t : ℝ) := fun n t => hnot _ (hφ1 n) t
  obtain ⟨g, -, hpis, -, hdeg, hcard⟩ := exists_pisot_of_decay_subseq hD hG halg hξ1 hsmono
    (hCge _ (hφ1 0)) (by norm_num) (by norm_num) hdecay hnot'
  have h' := card_otherConj_add_one hpis.2.1.tower_top
  have : (1 : ℝ) ≤ Multiset.card (otherConj (ξ ^ g)) := by exact_mod_cast (by omega :
    1 ≤ Multiset.card (otherConj (ξ ^ g)))
  linarith

/-- **Saito Lemma 5.3 at `θ = 21/40`, ratios `≥ 29/10`**: in case (II),
`{ξ^(C k)} ≤ 2 ⌊ξ^(C k)⌋^(−151/400)` eventually. -/
theorem eventually_fract_le {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {K₀ : ℕ} (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) {k₀ : ℕ}
    (hII : ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (21 / 40 * ratio C k)) :
    ∃ k₂, ∀ k ≥ k₂, Int.fract (ξ ^ C k) ≤ 2 * (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) := by
  refine ⟨max k₀ (max K₀ 1), fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hξ1 : 1 < ξ := hξ.1
  have hξ0 : 0 < ξ := by linarith
  have hCk : 0 < C k := C_ge_one h1 h2 k hk1
  have hc : (29 : ℝ) / 10 ≤ ratio C k := by
    have hCk' : (0 : ℝ) < C k := by exact_mod_cast hCk
    rw [ratio, le_div_iff₀ hCk']; exact hEv k (by omega)
  set x := ξ ^ C k with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ ratio C k < (⌊ξ ^ C (k + 1)⌋₊ : ℝ) + 1 := by
    rw [hx, pow_ratio hξ0 hCk]; exact Nat.lt_floor_add_one _
  have hw := fract_le_of_window (θ := 21 / 40) hx1 (by linarith) (by norm_num) (by norm_num) hxc
    (hII k (by omega))
  set p : ℝ := (⌊x⌋₊ : ℝ) with hp
  have hp1 : 1 ≤ p := by have := Nat.floor_pos.2 hx1; rw [hp]; exact_mod_cast this
  have hA : p ^ (151 / 400 : ℝ) ≤ p ^ ((1 - 21 / 40) * ratio C k - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hA0 : 0 < p ^ (151 / 400 : ℝ) := by positivity
  have hc1 : (1 : ℝ) ≤ ratio C k := by linarith
  calc Int.fract x ≤ 2 / (ratio C k * p ^ ((1 - 21 / 40) * ratio C k - 1)) := hw
    _ ≤ 2 / p ^ (151 / 400 : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hA0
        nlinarith
    _ = 2 * p ^ (-(151 / 400 : ℝ)) := by
        rw [Real.rpow_neg (by linarith), div_eq_mul_inv]


end LeanFormalizations.Mills.SaitoTypeB
