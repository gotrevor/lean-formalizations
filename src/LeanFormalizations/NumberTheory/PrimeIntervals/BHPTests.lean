/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Stress tests for `Literature.BakerHarmanPintz2001`

Theorem E+ (`Mills/SaitoTypeB.lean`) assumes `BakerHarmanPintz2001`.  A literature `Prop` stated
too strongly is false, and a false hypothesis makes every theorem assuming it vacuous.  This file
checks the definition against known answers, so a typo in the exponent, the interval or the
counting function shows up as a failed proof:

* **`primesIn` unit tests**: hand-counted values, including the clamping quirks (a negative left
  end counts from `0`; a reversed interval is empty).
* **The exponent family** `PrimesShortInterval θ`, with `BakerHarmanPintz2001` the case
  `θ = 21/40` *definitionally* (`bhp_iff`).
* **A false sibling**: `θ = 0` fails, since `[n! + 2, n! + 3]` holds no prime.
* **A true sibling**: `θ = 1` holds, from the Prime Number Theorem (Chebyshev bounds suffice).
* **A trusted upper witness**: RH (mathlib's `RiemannHypothesis`) with Schoenfeld's explicit
  error term implies BHP (`bhp_of_rh`).  A BHP stated too strongly (say an exponent below `1/2`)
  would not follow from RH, so this pins the statement from above.
* **Monotonicity in `θ`** on `(0, 1]`, so `θ = 21/40` sits inside the family between the false
  and true endpoints, and BHP implies the `θ = 1` statement through the family.
-/
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.PNT
import LeanFormalizations.NumberTheory.Mills.Schoenfeld

namespace LeanFormalizations.BHPTests

open LeanFormalizations.Literature Filter

/-! ## `primesIn` unit tests (hand-counted) -/

/-- `11, 13, 17, 19`. -/
theorem primesIn_10_20 : primesIn 10 20 = 4 := by
  have h1 : ⌈(10:ℝ)⌉₊ = 10 := by exact_mod_cast Nat.ceil_natCast 10
  have h2 : ⌊(20:ℝ)⌋₊ = 20 := by exact_mod_cast Nat.floor_natCast 20
  rw [primesIn, h1, h2]; decide

/-- Non-integer left end rounds up: `⌈10.5⌉ = 11`, so `11, 13`. -/
theorem primesIn_10_5_13 : primesIn 10.5 13 = 2 := by
  have h1 : ⌈(10.5:ℝ)⌉₊ = 11 := by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h2 : ⌊(13:ℝ)⌋₊ = 13 := by exact_mod_cast Nat.floor_natCast 13
  rw [primesIn, h1, h2]; decide

/-- `24, 25, 26, 27, 28` are all composite. -/
theorem primesIn_24_28 : primesIn 24 28 = 0 := by
  have h1 : ⌈(24:ℝ)⌉₊ = 24 := by exact_mod_cast Nat.ceil_natCast 24
  have h2 : ⌊(28:ℝ)⌋₊ = 28 := by exact_mod_cast Nat.floor_natCast 28
  rw [primesIn, h1, h2]; decide

/-- A degenerate interval at a prime counts it. -/
theorem primesIn_2_2 : primesIn 2 2 = 1 := by
  have h1 : ⌈(2:ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  have h2 : ⌊(2:ℝ)⌋₊ = 2 := by exact_mod_cast Nat.floor_natCast 2
  rw [primesIn, h1, h2]; decide

/-- A negative left end is clamped to `0` by `⌈·⌉₊`, so this counts `2, 3`. -/
theorem primesIn_neg5_3 : primesIn (-5) 3 = 2 := by
  have h1 : ⌈(-5:ℝ)⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by norm_num)
  have h2 : ⌊(3:ℝ)⌋₊ = 3 := by exact_mod_cast Nat.floor_natCast 3
  rw [primesIn, h1, h2]; decide

/-- A reversed interval is empty. -/
theorem primesIn_reversed : primesIn 5 3 = 0 := by
  have h1 : ⌈(5:ℝ)⌉₊ = 5 := by exact_mod_cast Nat.ceil_natCast 5
  have h2 : ⌊(3:ℝ)⌋₊ = 3 := by exact_mod_cast Nat.floor_natCast 3
  rw [primesIn, h1, h2]; decide

/-! ## Helpers -/

/-- `π(⌊2x⌋) − π(⌊x⌋) ≤ primesIn x (2x)`. -/
lemma pc_sub_le (x : ℝ) :
    (Nat.primeCounting ⌊x + x⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ ≤ primesIn x (x + x) := by
  have hsub : Nat.primesLE ⌊x + x⌋₊ \ Nat.primesLE ⌊x⌋₊ ⊆
      (Finset.Icc ⌈x⌉₊ ⌊x + x⌋₊).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have := Nat.ceil_le_floor_add_one x
    have : ⌊x⌋₊ < p := by by_contra hh; exact hp.2 ⟨by omega, hp.1.2⟩
    exact ⟨⟨by omega, hp.1.1⟩, hp.1.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.le_card_sdiff (Nat.primesLE ⌊x⌋₊) (Nat.primesLE ⌊x + x⌋₊)
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h2
  have h3 : ((Nat.primeCounting ⌊x + x⌋₊ - Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ primesIn x (x + x) := by
    rw [primesIn]; exact_mod_cast h2.trans h1
  have h4 : (Nat.primeCounting ⌊x + x⌋₊ : ℝ) ≤
      ((Nat.primeCounting ⌊x + x⌋₊ - Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) + Nat.primeCounting ⌊x⌋₊ := by
    exact_mod_cast le_tsub_add
  linarith

/-- Disjoint windows `[y i, y i + y i^θ]` inside `[a, b]` add up. -/
lemma sum_le_primesIn {θ a b : ℝ} (k : ℕ) (y : ℕ → ℝ)
    (ha : ∀ i < k, a ≤ y i) (hb : ∀ i < k, y i + y i ^ θ ≤ b)
    (hy0 : ∀ i < k, 0 ≤ y i)
    (hdisj : ∀ i j, i < j → j < k → y i + y i ^ θ < y j) :
    ∑ i ∈ Finset.range k, (primesIn (y i) (y i + y i ^ θ) : ℝ) ≤ primesIn a b := by
  classical
  let S : ℕ → Finset ℕ := fun i => (Finset.Icc ⌈y i⌉₊ ⌊y i + y i ^ θ⌋₊).filter Nat.Prime
  have hS : ∀ i ∈ Finset.range k, ∀ n ∈ S i, y i ≤ n ∧ (n : ℝ) ≤ y i + y i ^ θ := by
    intro i hi n hn
    rw [Finset.mem_range] at hi
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    have : 0 ≤ y i + y i ^ θ := by
      have := Real.rpow_nonneg (hy0 i hi) θ; linarith [hy0 i hi]
    exact ⟨Nat.ceil_le.1 hn.1.1, (Nat.le_floor_iff this).1 hn.1.2⟩
  have hpd : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint S := by
    intro i hi j hj hij
    show Disjoint (S i) (S j)
    rw [Finset.disjoint_left]
    intro n hni hnj
    rw [Finset.mem_coe] at hi hj
    have h1 := hS i hi n hni; have h2 := hS j hj n hnj
    rw [Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [hdisj i j h hj]
    · linarith [hdisj j i h hi]
  have hsub : (Finset.range k).biUnion S ⊆ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime := by
    intro n hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨i, hi, hn⟩ := hn
    have h := hS i hi n hn
    rw [Finset.mem_range] at hi
    simp only [S, Finset.mem_filter] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.ceil_le.2 ((ha i hi).trans h.1), Nat.le_floor (h.2.trans (hb i hi))⟩, hn.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_biUnion hpd] at this
  rw [primesIn]
  simp only [primesIn]
  exact_mod_cast this

/-! ## The exponent family -/

/-- `[x, x + x^θ]` holds `≫ x^θ / log x` primes for all large `x`. -/
def PrimesShortInterval (θ : ℝ) : Prop :=
  ∃ d₀ > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X,
    d₀ * x ^ θ / Real.log x ≤ (primesIn x (x + x ^ θ) : ℝ)

/-- `BakerHarmanPintz2001` is the `θ = 21/40` member, by definition. -/
theorem bhp_iff : BakerHarmanPintz2001 ↔ PrimesShortInterval ((21 : ℝ) / 40) := Iff.rfl

/-- **False sibling.**  At `θ = 0` the window `[x, x + 1]` is prime-free at `x = n! + 2`
(`n ≥ 3`), while `d₀ / log x > 0`. -/
theorem not_primesShortInterval_zero : ¬ PrimesShortInterval 0 := by
  rintro ⟨d₀, hd, X, hX⟩
  set n := max 3 ⌈X⌉₊ with hn
  have hn3 : 3 ≤ n := le_max_left _ _
  have hnf : n ≤ n.factorial := Nat.self_le_factorial n
  have hx : X ≤ ((n.factorial + 2 : ℕ) : ℝ) := by
    calc X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
      _ ≤ ((n.factorial + 2 : ℕ) : ℝ) := by
        exact_mod_cast (le_max_right 3 ⌈X⌉₊).trans (by omega)
  have h := hX _ hx
  rw [Real.rpow_zero] at h
  have hc : primesIn ((n.factorial + 2 : ℕ) : ℝ) (((n.factorial + 2 : ℕ) : ℝ) + 1) = 0 := by
    rw [primesIn, Nat.ceil_natCast, show ((n.factorial + 2 : ℕ) : ℝ) + 1
      = ((n.factorial + 3 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp hpr
    rw [Finset.mem_Icc] at hp
    have : p = n.factorial + 2 ∨ p = n.factorial + 3 := by omega
    rcases this with rfl | rfl
    · have h2 : 2 ∣ n.factorial + 2 :=
        (Nat.dvd_add_right (Nat.dvd_factorial (by norm_num) (by omega))).2 dvd_rfl
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).1 h2; omega
    · have h3 : 3 ∣ n.factorial + 3 :=
        (Nat.dvd_add_right (Nat.dvd_factorial (by norm_num) hn3)).2 dvd_rfl
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3; omega
  rw [hc] at h
  have hlog : 0 < Real.log ((n.factorial + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n.factorial + 2))
  have : 0 < d₀ * 1 / Real.log ((n.factorial + 2 : ℕ) : ℝ) := by positivity
  push_cast at h this; linarith

/-- **True sibling.**  `[x, 2x]` holds `≫ x / log x` primes: `π(2x) − π(x) ∼ x / log x` by
`prime_number_theorem`. -/
theorem primesShortInterval_one : PrimesShortInterval 1 := by
  have hT := prime_number_theorem
  have hA : ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) < 1.1 :=
    hT.eventually (gt_mem_nhds (by norm_num))
  have hB : ∀ᶠ x : ℝ in atTop, 0.9 < (Nat.primeCounting ⌊x + x⌋₊ : ℝ) / ((x + x) / Real.log (x + x)) :=
    (hT.comp (tendsto_atTop_atTop.2 fun b => ⟨max b 0, fun x hx => by
      have := le_max_left b 0; have := le_max_right b 0; linarith⟩)).eventually (lt_mem_nhds (by norm_num))
  obtain ⟨X, hX⟩ := (hA.and (hB.and (eventually_ge_atTop (256:ℝ)))).exists_forall_of_atTop
  refine ⟨1/2, by norm_num, X, fun x hx => ?_⟩
  obtain ⟨ha, hb, h256⟩ := hX x hx
  rw [Real.rpow_one]
  have hx0 : 0 < x := by linarith
  have hL : Real.log 256 ≤ Real.log x := Real.log_le_log (by norm_num) h256
  have h256' : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256:ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < Real.log x := by linarith
  have hxx : Real.log (x + x) = Real.log 2 + Real.log x := by
    rw [show x + x = 2 * x by ring, Real.log_mul (by norm_num) hx0.ne']
  rw [hxx] at hb
  have hLp2 : 0 < Real.log 2 + Real.log x := by linarith
  rw [div_lt_iff₀ (by positivity)] at ha
  rw [lt_div_iff₀ (by positivity)] at hb
  have key := pc_sub_le x
  -- 0.9 * 2x/(log2 + L) ≥ 1.6 x / L
  have h3 : 1.6 * x / Real.log x ≤ 0.9 * ((x + x) / (Real.log 2 + Real.log x)) := by
    rw [div_le_iff₀ hLp, show 0.9 * ((x + x) / (Real.log 2 + Real.log x)) * Real.log x
      = 1.8 * x * Real.log x / (Real.log 2 + Real.log x) by ring, le_div_iff₀ hLp2]
    nlinarith
  have h4 : 1.1 * (x / Real.log x) = 1.1 * x / Real.log x := by ring
  have h5 : 1 / 2 * x / Real.log x = 1.6 * x / Real.log x - 1.1 * x / Real.log x := by ring
  linarith

/-- **Monotone in `θ`.**  Tile `[x, x + x^θ']` by about `x^(θ' − θ)` disjoint windows
`[y, y + y^θ]` with `x ≤ y ≤ 2x`; each holds `≥ d₀ y^θ / log y ≫ x^θ / log x` primes. -/
theorem PrimesShortInterval.mono {θ θ' : ℝ} (h0 : 0 < θ) (hle : θ ≤ θ') (h1 : θ' ≤ 1) :
    PrimesShortInterval θ → PrimesShortInterval θ' := by
  rintro ⟨d₀, hd, X, hX⟩
  rcases hle.eq_or_lt with rfl | hlt
  · exact ⟨d₀, hd, X, hX⟩
  set δ := θ' - θ with hδ
  have hδ0 : 0 < δ := by linarith
  refine ⟨d₀ / 12, by positivity, max (max X 2) ((16:ℝ) ^ (1 / δ)), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left X 2).trans ((le_max_left _ _).trans hx)
  have hx2 : 2 ≤ x := (le_max_right X 2).trans ((le_max_left _ _).trans hx)
  have hx16 : (16:ℝ) ^ (1 / δ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxδ : 16 ≤ x ^ δ := by
    calc (16:ℝ) = ((16:ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ0.ne', Real.rpow_one]
      _ ≤ x ^ δ := Real.rpow_le_rpow (by positivity) hx16 hδ0.le
  set w := (2 * x) ^ θ with hw
  set h := x ^ θ' with hh
  set k := ⌊h / (w + 1)⌋₊ with hk
  let y : ℕ → ℝ := fun i => x + i * (w + 1)
  have hw0 : 0 ≤ w := by positivity
  have hxθ1 : 1 ≤ x ^ θ := Real.one_le_rpow (by linarith) h0.le
  have hwle : w + 1 ≤ 3 * x ^ θ := by
    have : (2:ℝ) ^ θ ≤ 2 := by
      calc (2:ℝ) ^ θ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    rw [hw, Real.mul_rpow (by norm_num) hx0.le]
    nlinarith
  have hhx : h ≤ x := by
    calc h ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1
      _ = x := Real.rpow_one x
  have hkle : (k : ℝ) * (w + 1) ≤ h := by
    have := Nat.floor_le (show 0 ≤ h / (w + 1) by positivity)
    rwa [le_div_iff₀ (by linarith)] at this
  have hy_ge : ∀ i, x ≤ y i := fun i => by simp only [y]; nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hy_end : ∀ i < k, y i + w ≤ x + h := by
    intro i hi
    have : ((i:ℝ) + 1) ≤ k := by exact_mod_cast hi
    simp only [y]; nlinarith
  have hy_le : ∀ i < k, y i ≤ 2 * x := fun i hi => by linarith [hy_end i hi]
  have hyθ : ∀ i < k, y i ^ θ ≤ w := fun i hi =>
    Real.rpow_le_rpow (by linarith [hy_ge i]) (hy_le i hi) h0.le
  have hsum := sum_le_primesIn (a := x) (b := x + x ^ θ') k y (fun i _ => hy_ge i)
    (fun i hi => by linarith [hyθ i hi, hy_end i hi]) (fun i _ => by linarith [hy_ge i])
    (fun i j hij hj => by
      have : (i:ℝ) + 1 ≤ j := by exact_mod_cast hij
      have := hyθ i (hij.trans hj)
      simp only [y] at this ⊢; nlinarith)
  -- each window
  have hL2 : 0 < Real.log (2 * x) := Real.log_pos (by linarith)
  have hwin : ∀ i < k, d₀ * x ^ θ / Real.log (2 * x) ≤ primesIn (y i) (y i + y i ^ θ) := by
    intro i hi
    refine le_trans ?_ (hX (y i) ((hxX).trans (hy_ge i)))
    have hyx := hy_ge i
    have hly : 0 < Real.log (y i) := Real.log_pos (by linarith)
    have : Real.log (y i) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (hy_le i hi)
    have : x ^ θ ≤ y i ^ θ := Real.rpow_le_rpow hx0.le hyx h0.le
    calc d₀ * x ^ θ / Real.log (2 * x) ≤ d₀ * y i ^ θ / Real.log (2 * x) := by gcongr
      _ ≤ d₀ * y i ^ θ / Real.log (y i) := by gcongr
  have hlow : (k:ℝ) * (d₀ * x ^ θ / Real.log (2 * x)) ≤ primesIn x (x + x ^ θ') := by
    refine le_trans ?_ hsum
    have := Finset.sum_const (s := Finset.range k) (d₀ * x ^ θ / Real.log (2 * x))
    rw [Finset.card_range, nsmul_eq_mul] at this
    rw [← this]
    exact Finset.sum_le_sum fun i hi => hwin i (Finset.mem_range.1 hi)
  -- k ≥ x^δ / 6
  have hk6 : x ^ δ / 6 ≤ k := by
    have hfl := Nat.lt_floor_add_one (h / (w + 1))
    have : x ^ δ / 3 ≤ h / (w + 1) := by
      rw [le_div_iff₀ (by linarith), hh, show θ' = δ + θ by ring, Real.rpow_add hx0]
      have : 0 ≤ x ^ δ := by positivity
      nlinarith
    rw [← hk] at hfl
    linarith
  have hL : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have := Real.log_le_log (by norm_num) hx2; linarith
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hθ' : x ^ θ' = x ^ δ * x ^ θ := by rw [show θ' = δ + θ by ring, Real.rpow_add hx0]
  refine le_trans ?_ hlow
  rw [hh, hθ']
  have hA : 0 ≤ d₀ * x ^ θ := by positivity
  calc d₀ / 12 * (x ^ δ * x ^ θ) / Real.log x
      = x ^ δ / 6 * (d₀ * x ^ θ / (2 * Real.log x)) := by field_simp; ring
    _ ≤ k * (d₀ * x ^ θ / Real.log (2 * x)) := by
      gcongr

/-- BHP implies the `θ = 1` statement through the family. -/
theorem primesShortInterval_one_of_bhp (h : BakerHarmanPintz2001) : PrimesShortInterval 1 :=
  PrimesShortInterval.mono (by norm_num) (by norm_num) le_rfl (bhp_iff.mp h)

/-- What Theorem E+ consumes: under BHP, every large `x` has a prime in `[x, x + x^(21/40)]`. -/
theorem exists_prime_of_bhp (h : BakerHarmanPintz2001) :
    ∃ X : ℝ, ∀ x ≥ X, ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + x ^ ((21 : ℝ) / 40) := by
  obtain ⟨d₀, hd, X, hX⟩ := bhp_iff.mp h
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_of_max_le_right hx
  have hpos : 0 < d₀ * x ^ ((21 : ℝ) / 40) / Real.log x := by
    have := Real.log_pos (by linarith : (1:ℝ) < x)
    have : 0 < x ^ ((21 : ℝ) / 40) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hc := hX x (le_of_max_le_left hx)
  have : 0 < primesIn x (x + x ^ ((21 : ℝ) / 40)) := by exact_mod_cast hpos.trans_le hc
  obtain ⟨p, hp⟩ := Finset.card_pos.1 this
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  refine ⟨p, hp.2, Nat.ceil_le.1 hp.1.1, ?_⟩
  have : 0 ≤ x + x ^ ((21 : ℝ) / 40) := by have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) ((21 : ℝ) / 40); linarith
  exact (Nat.le_floor_iff this).1 hp.1.2

/-! ## RH implies BHP -/

/-- **RH implies BHP.**  Believed, 97%.  Set `h = x^(21/40)`.  Schoenfeld bounds
`|π(t) − (C + ∫₂ᵗ 1/log)|` by `√t log t / (8π)` at `t = x` and `t = x + h`, so
`π(x + h) − π(x) ≥ ∫ₓ^(x+h) 1/log − √(x+h) log(x+h) / (4π) ≥ h / log(x + h) − √(x+h) log(x+h) / (4π)`
(`Mills.le_log_integral`).  Since `h / log x` beats `√x log x` by the factor
`x^(1/40) / log² x → ∞`, the right side is `≥ h / (4 log x)` for large `x`.  Finally
`primesIn x (x + h)` counts every prime in `(⌊x⌋, ⌊x + h⌋]`, so it is `≥ π(x + h) − π(x)`.
Reusable pieces: `Mills.le_log_integral`, `Mills.exists_prime_short_interval` (same estimate,
existence form). -/
theorem bhp_of_rh (hS : Schoenfeld1976) (hRH : RiemannHypothesis) : BakerHarmanPintz2001 := by
  sorry

/-! ## Li's 0.52 implies BHP -/

/-- **Li (0.52) implies BHP.**  Believed, 95%.  Apply `Li2023` with `ε = 1/400`, so
`θ₀ = 0.5225 < 21/40`.  Tile `[x, x + x^(21/40)]` by about `x^(21/40 − θ₀)` disjoint
left-anchored windows `[y − y^θ₀, y]` with `x ≤ y ≤ 2x`, exactly as in
`PrimesShortInterval.mono`; each window holds `≥ d₀ y^θ₀ / log y ≫ x^θ₀ / log x` primes, so
the whole interval holds `≫ x^(21/40) / log x`.  Evidence: the tiling argument already compiles
for right-anchored windows (`PrimesShortInterval.mono`); only the anchoring differs. -/
theorem bhp_of_li2023 (h : Li2023) : BakerHarmanPintz2001 := by
  sorry

end LeanFormalizations.BHPTests
