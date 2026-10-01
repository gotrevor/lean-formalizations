/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving
import LeanFormalizations.NumberTheory.Erdos385.Erdos463

/-!
# #463 with a power saving: helpers (phase E10)

* `almost_all_of_windowPowerSaving`: `almost_all_of_badWindowPowerSaving` for an arbitrary set `E`.
* `card_shift_le_split`: `card_shift_le` (E6's shifted windows) with the long average at any
  length `H` and the mean square of any majorant `G` (as `card_badWindow_le_of_split`).
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory LeanFormalizations.Literature

/-- Window counts with a power saving give a global power saving, for any `E ⊆ ℕ`. -/
theorem almost_all_of_windowPowerSaving {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (E : Set ℕ)
    (h : ∃ c' : ℝ, 0 < c' ∧ ∃ A : ℝ, 0 < A ∧ ∃ Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      (({n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}).ncard : ℝ) ≤ A * Z ^ (1 - c')) :
    ∃ c C : ℝ, 0 < c ∧ ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ) ≤ C * (X : ℝ) ^ (1 - c) := by
  classical
  obtain ⟨c', hc', A, hA, Z₁, hZ₁1, hwin⟩ := h
  obtain ⟨N₀, hcov⟩ := card_le_of_windows hδ hδ' Z₁
  set c := min (c' / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, (3 + N₀) + A * (1 + 4 / δ), hc0, fun X hX => ?_⟩
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0 : (0 : ℝ) < X := by linarith
  set Φ := (X : ℝ) ^ (1 - c) with hΦ
  have hsqΦ : √X ≤ Φ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hXr (by linarith [min_le_right (c' / 2) (1 / 2 : ℝ)])
  have hs1 : 1 ≤ √X := by rw [Real.one_le_sqrt]; exact hXr
  have hΦ1 : 1 ≤ Φ := hs1.trans hsqΦ
  have hrest : 0 ≤ A * (1 + 4 / δ) * Φ := by positivity
  show (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ _
  by_cases hXN : X < N₀
  · have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆ ↑(Finset.range (X + 1)) := fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le hn.1
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    have hc : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ N₀ := by exact_mod_cast (by omega)
    have : (N₀ : ℝ) ≤ N₀ * Φ := le_mul_of_one_le_right (by positivity) hΦ1
    nlinarith
  push Not at hXN
  set E' : Set ℕ := {n | n ∈ E ∧ 2 * √X ≤ n} with hE'
  have hsX0 : 0 < √X := by positivity
  set η := A * (√X) ^ (-c') with hη
  have hη0 : 0 < η := by positivity
  have hW : ∀ Z : ℝ, Z₁ ≤ Z →
      ({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) ≤ η * Z := by
    intro Z hZ
    have hZ0 : 0 < Z := by linarith
    by_cases hZs : Z < √X
    · have : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hE']
        rintro ⟨⟨_, h2⟩, _, h3⟩
        nlinarith
      rw [this, Set.ncard_empty, Nat.cast_zero]; positivity
    · push Not at hZs
      have hsub : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} ⊆
          {n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} := fun n ⟨⟨hn, _⟩, h1, h2⟩ => ⟨hn, h1, h2⟩
      have hfin : {n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.Finite :=
        (Set.finite_Iic ⌊(1 + δ / 2) * Z⌋₊).subset fun n hn => by
          simp only [Set.mem_Iic]; exact Nat.le_floor hn.2.2
      have h1 : ((({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℕ)
          : ℝ)) ≤ {n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard := by exact_mod_cast Set.ncard_le_ncard hsub hfin
      have hpow : Z ^ (1 - c') = Z * Z ^ (-c') := by
        rw [sub_eq_add_neg, Real.rpow_add hZ0, Real.rpow_one]
      have hmono : Z ^ (-c') ≤ (√X) ^ (-c') :=
        Real.rpow_le_rpow_of_nonpos hsX0 hZs (by linarith)
      calc _ ≤ ({n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) := h1
        _ ≤ A * Z ^ (1 - c') := hwin Z hZ
        _ = A * (Z * Z ^ (-c')) := by rw [hpow]
        _ ≤ A * (Z * (√X) ^ (-c')) := by gcongr
        _ = η * Z := by rw [hη]; ring
  have hcnt := hcov E' η hη0 hW X hXN
  -- η X ≤ A Φ
  have hηΦ : η * X ≤ A * Φ := by
    rw [hη, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, hΦ]
    calc (X : ℝ) ^ (1 / 2 * -c') * X = (X : ℝ) ^ (1 - c' / 2) := by
          rw [show (1 : ℝ) - c' / 2 = 1 / 2 * -c' + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
      _ ≤ (X : ℝ) ^ (1 - c) :=
          Real.rpow_le_rpow_of_exponent_le hXr (by linarith [min_le_left (c' / 2) (1 / 2 : ℝ)])
  have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆
      ↑(Finset.range ⌈2 * √X⌉₊) ∪ {n : ℕ | n ≤ X ∧ n ∈ E'} := by
    intro n ⟨hnX, hnE⟩
    by_cases hn : (n : ℝ) < 2 * √X
    · left; simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_ceil.2 hn
    · right; push Not at hn; exact ⟨hnX, hnE, hn⟩
  have hfin2 : {n : ℕ | n ≤ X ∧ n ∈ E'}.Finite :=
    (Set.finite_Iic X).subset fun n hn => hn.1
  have hA1 := Set.ncard_le_ncard hsub ((Finset.finite_toSet _).union hfin2)
  have hA2 := Set.ncard_union_le (↑(Finset.range ⌈2 * √X⌉₊) : Set ℕ) {n : ℕ | n ≤ X ∧ n ∈ E'}
  rw [Set.ncard_coe_finset, Finset.card_range] at hA2
  have hceil : (⌈2 * √X⌉₊ : ℝ) ≤ 2 * √X + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have htot : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤
      ⌈2 * √X⌉₊ + ({n : ℕ | n ≤ X ∧ n ∈ E'}.ncard : ℝ) := by
    exact_mod_cast hA1.trans hA2
  have hηX : η * (1 + 4 / δ) * X ≤ A * (1 + 4 / δ) * Φ := by
    have : η * X * (1 + 4 / δ) ≤ A * Φ * (1 + 4 / δ) :=
      mul_le_mul_of_nonneg_right hηΦ (by positivity)
    linarith
  have hN : (3 + (N₀ : ℝ)) * √X ≤ (3 + N₀) * Φ :=
    mul_le_mul_of_nonneg_left hsqΦ (by positivity)
  have hN' : 2 * √X + 1 + (N₀ : ℝ) ≤ (3 + N₀) * √X := by
    have : (0 : ℝ) ≤ N₀ := by positivity
    nlinarith
  nlinarith

/-- **Shifted windows, split form.** -/
theorem card_shift_le_split {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) {g : ℝ → ℝ} :
    ∀ᶠ Z : ℝ in atTop, ∀ (H μ ν : ℝ) (G : ℝ → ℝ), 0 < μ → (∀ x, 0 ≤ G x) →
      IntegrableOn G (Set.Ioc (paramX δ Z) (2 * paramX δ Z)) →
      (∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z → μ ≤ shortSum (coeffA δ g Z) x H / H) →
      (∀ x, paramX δ Z < x → x ≤ 2 * paramX δ Z →
        μ ≤ |shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
          shortSum (coeffA δ g Z) x H / H| → ν ≤ G x) →
      ∀ (T : Finset ℕ) (φ : ℕ → ℝ), (∀ n ∈ T, ∀ n' ∈ T, n < n' → φ n + 1 ≤ φ n') →
      (∀ n ∈ T, Z ≤ φ n ∧ φ n + 1 ≤ (1 + δ / 2) * Z ∧
        ∀ m : ℕ, φ n ≤ m → (m : ℝ) ≤ φ n + paramH δ Z / 2 → coeffA δ g Z m = 0) →
      (T.card : ℝ) * ν ≤ ∫ x in (paramX δ Z)..(2 * paramX δ Z), G x := by
  have hsq : Tendsto (fun Z : ℝ => δ / 4 * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 1, hsq.eventually_ge_atTop 2] with Z hZ hh H μ ν G hμ hG0
    hint hlong hGD T φ hφ hT
  set h := paramH δ Z with hhdef
  have hh' : 2 ≤ h := hh
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  have hH1 : paramH1 δ Z ≤ h / 2 - 1 := by
    unfold paramH1; have := Nat.floor_le (show 0 ≤ paramH δ Z / 2 by linarith); linarith
  have hH1' : 0 ≤ paramH1 δ Z := by
    unfold paramH1
    have : (1 : ℝ) ≤ ⌊paramH δ Z / 2⌋₊ := by
      have : 1 ≤ ⌊paramH δ Z / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  classical
  set J : ℕ → Set ℝ := fun n => Set.Ico (φ n) (φ n + 1)
  have hJ : ∀ n ∈ T, ∀ x ∈ J n, ν ≤ G x ∧ X < x ∧ x ≤ 2 * X := by
    intro n hn x hx
    obtain ⟨hn1, hn2, hn3⟩ := hT n hn
    obtain ⟨hx1, hx2⟩ := hx
    have hxZ : Z ≤ x := by linarith
    have hxZ' : x ≤ (1 + δ / 2) * Z := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have hS1 : shortSum (coeffA δ g Z) x (paramH1 δ Z) = 0 := by
        unfold shortSum
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        have hm1 : x ≤ m := (Nat.ceil_le).1 hm.1
        have hm2 : (m : ℝ) ≤ x + paramH1 δ Z :=
          (Nat.le_floor_iff (by linarith)).1 hm.2
        exact hn3 m (by linarith) (by linarith)
      have hl := hlong x hxZ hxZ'
      have hXx : X < x := by
        have : X < Z := by rw [hX, paramX]; nlinarith
        linarith
      have hx2 : x ≤ 2 * X := by
        have : (1 + δ / 2) * Z ≤ 2 * X := by rw [hX, paramX]; nlinarith
        linarith
      refine hGD x hXx hx2 ?_
      rw [hS1, zero_div, zero_sub, abs_neg]
      exact hl.trans (le_abs_self _)
    · have : X < Z := by rw [hX, paramX]; nlinarith
      linarith
    · have : (1 + δ / 2) * Z ≤ 2 * X := by rw [hX, paramX]; nlinarith
      linarith
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint J) := by
    intro n hn m hm hnm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hnm with h | h
    · have := hφ n hn m hm h
      linarith
    · have := hφ m hm n hn h
      linarith
  have hsub : (⋃ n ∈ T, J n) ⊆ Set.Ioc X (2 * X) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨(hJ n hn x hx).2.1, (hJ n hn x hx).2.2⟩
  have hfnn : ∀ x, 0 ≤ G x := hG0
  have key : (T.card : ℝ) * ν ≤ ∫ x in X..(2 * X), G x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc (T.card : ℝ) * ν = ∑ n ∈ T, ν * volume.real (J n) := by
          rw [Finset.sum_congr rfl fun n _ => by
            rw [show volume.real (J n) = 1 by
              simp only [J, Real.volume_real_Ico]; rw [max_eq_left (by linarith)]; ring, mul_one]]
          simp
      _ ≤ ∑ n ∈ T, ∫ x in J n, G x := Finset.sum_le_sum fun n hn =>
          setIntegral_ge_of_const_le_real measurableSet_Ico measure_Ico_lt_top.ne
            (fun x hx => (hJ n hn x hx).1) (hint.mono_set fun x hx => hsub (by
              simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩))
      _ = ∫ x in ⋃ n ∈ T, J n, G x := (integral_biUnion_finset T (fun _ _ => measurableSet_Ico)
          hdisj fun n hn => hint.mono_set fun x hx => hsub (by
            simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩)).symm
      _ ≤ ∫ x in Set.Ioc X (2 * X), G x :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => hfnn x)
            (Filter.Eventually.of_forall hsub)
  exact key

end LeanFormalizations.Erdos385

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory LeanFormalizations.Literature

/-- The `n` with no #463 witness at margin `δ√n`. -/
def NoWitness463 (δ : ℝ) : Set ℕ :=
  {n | ¬ ∃ m : ℕ, Composite m ∧ (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac}

set_option maxHeartbeats 1600000 in
/-- **Per-window power saving for #463** (E6's shifted windows on E9's two leaves, at
coefficient `1/8` and window parameter `1/16`). -/
theorem erdos463_windowPowerSaving (hL : LongAveragePower (1 / 8))
    (hS : DifferenceSplit (1 / 8)) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ A : ℝ, 0 < A ∧ ∃ Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      ({n : ℕ | n ∈ NoWitness463 δ ∧ Z + paramH (1 / 16) Z ≤ n ∧
        (n : ℝ) ≤ (1 + 1 / 16 / 2) * Z}.ncard : ℝ) ≤ A * Z ^ (1 - c') := by
  have hc : (0 : ℝ) < 1 / 8 := by norm_num
  have hc' : (1 / 8 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨g, hg⟩ := exists_admissible hc hc'
  obtain ⟨m1, hm1, hL⟩ := hL
  obtain ⟨m2, hm2, hS⟩ := hS
  set c₀ := min m1 m2
  have hc₀ : 0 < c₀ := lt_min hm1 hm2
  obtain ⟨c₁, hc₁, hlong⟩ := hL c₀ hc₀ (min_le_left _ _) g hg
  obtain ⟨c, C, hcpos, hsplit⟩ := hS c₀ hc₀ (min_le_right _ _) g hg
  have hlogt : Tendsto (fun Z : ℝ => Real.log Z) atTop atTop := Real.tendsto_log_atTop
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 ((card_shift_le_split hc hc' (g := g)).and
    (hlong.and (hsplit.and ((eventually_log_pow_le_rpow hcpos).and
      ((hlogt.eventually_ge_atTop (2 / (c₁ * (1 / 8)))).and (eventually_ge_atTop 10000))))))
  refine ⟨c / 2, by positivity, 4 * (|C| + 1) / (c₁ * (1 / 8)) ^ 2, by positivity, max Z₁ 1,
    le_max_right _ _, fun Z hZ => ?_⟩
  obtain ⟨hb, hl, ⟨Dfar, hint, hnear, hfar⟩, hlog4, hlogbig, hZ⟩ :=
    hZ₁ Z ((le_max_left _ _).trans hZ)
  have hZ1 : 1 < Z := by linarith
  have hlZ : 0 < Real.log Z := Real.log_pos hZ1
  set μ := c₁ * (1 / 8) / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hsmall : 1 / Real.log Z ^ 3 ≤ μ / 2 := by
    rw [hμ, div_le_iff₀ (by positivity)]
    have h2 : 2 ≤ Real.log Z * (c₁ * (1 / 8)) := by
      have := mul_le_mul_of_nonneg_right hlogbig (show 0 ≤ c₁ * (1 / 8) by positivity)
      have e : 2 / (c₁ * (1 / 8)) * (c₁ * (1 / 8)) = 2 := by field_simp
      linarith
    have e : c₁ * (1 / 8) / Real.log Z ^ 2 / 2 * Real.log Z ^ 3 =
        Real.log Z * (c₁ * (1 / 8)) / 2 := by field_simp
    rw [e]; linarith
  -- E6's window construction
  classical
  have hZ0 : 0 < Z := by linarith
  set s := √Z with hs
  have hss : s * s = Z := Real.mul_self_sqrt hZ0.le
  have hs100 : 100 ≤ s := by
    rw [hs, show (100 : ℝ) = √(100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  set E := NoWitness463 δ
  set W := {n : ℕ | n ∈ E ∧ Z + paramH (1 / 16) Z ≤ n ∧ (n : ℝ) ≤ (1 + 1 / 16 / 2) * Z}
  set T := (Finset.range (⌊(1 + 1 / 16 / 2) * Z⌋₊ + 1)).filter (· ∈ W)
  have hWT : W = ↑T := by
    ext n; simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn; refine ⟨?_, hn⟩
      have := Nat.le_floor hn.2.2; omega
    · exact fun h => h.2
  rw [hWT, Set.ncard_coe_finset]
  have hH0 : ∀ Z : ℝ, 0 ≤ paramH (1 / 16) Z := fun Z => by unfold paramH; positivity
  set φ : ℕ → ℝ := fun n => n + δ * √(n : ℝ) + 1 with hφ
  have hsn : ∀ n ∈ T, √(n : ℝ) ≤ 33 / 32 * s := by
    intro n hn
    have hn := (Finset.mem_filter.1 hn).2.2.2
    rw [hs, show 33 / 32 * √Z = √((33 / 32) ^ 2 * Z) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hT : ∀ n ∈ T, Z ≤ φ n ∧ φ n + 1 ≤ (1 + 1 / 8 / 2) * Z ∧
      ∀ m : ℕ, φ n ≤ m → (m : ℝ) ≤ φ n + paramH (1 / 8) Z / 2 → coeffA (1 / 8) g Z m = 0 := by
    intro n hn
    have hsn' := hsn n hn
    obtain ⟨hnE, hn1, hn2⟩ := (Finset.mem_filter.1 hn).2
    have hn0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hδs : δ * √(n : ℝ) ≤ s / 3 := by nlinarith
    have hH := hH0 Z
    refine ⟨by simp only [hφ]; nlinarith, by simp only [hφ]; nlinarith, fun m hm1 hm2 => ?_⟩
    by_contra ha
    obtain ⟨hcomp, hmin⟩ := coeffA_ne_zero_witness (by linarith) hg hc hc' ha
    refine hnE ⟨m, hcomp, by simp only [hφ] at hm1; linarith, ?_⟩
    have : (m : ℝ) < n + m.minFac := by
      simp only [hφ, paramH] at hm2
      rw [← hs] at hm2 hmin
      nlinarith
    exact_mod_cast this
  have hTφ : ∀ n ∈ T, ∀ n' ∈ T, n < n' → φ n + 1 ≤ φ n' := by
    intro n _ n' _ hlt
    have h1 : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hlt
    have h2 : √(n : ℝ) ≤ √(n' : ℝ) := Real.sqrt_le_sqrt (by linarith)
    simp only [hφ]; nlinarith
  have hkey0 := hb (powerH c₀ (1 / 8) Z) μ (μ ^ 2 / 4) (fun x => Dfar x ^ 2) hμ0
    (fun x => sq_nonneg _) hint hl (by
      intro x hx1 hx2 hD
      have hn := hnear x hx1 hx2
      unfold diffD at hn
      have h1 : μ / 2 ≤ |Dfar x| := by
        have := abs_sub_abs_le_abs_sub
          (shortSum (coeffA (1 / 8) g Z) x (paramH1 (1 / 8) Z) / paramH1 (1 / 8) Z -
            shortSum (coeffA (1 / 8) g Z) x (powerH c₀ (1 / 8) Z) / powerH c₀ (1 / 8) Z) (Dfar x)
        linarith
      have := pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at this
      nlinarith) T φ hTφ hT
  have hX0 : 0 < paramX (1 / 8) Z := by unfold paramX; nlinarith
  have hZc : 0 < Z ^ (-c) := by positivity
  have hfar' : ∫ x in (paramX (1 / 8) Z)..(2 * paramX (1 / 8) Z), Dfar x ^ 2 ≤
      (|C| + 1) * Z * Z ^ (-c) := by
    refine hfar.trans ?_
    have hXZ : paramX (1 / 8) Z ≤ Z := by unfold paramX; nlinarith
    have : C * paramX (1 / 8) Z ≤ (|C| + 1) * Z := by
      have := le_abs_self C
      nlinarith [abs_nonneg C]
    exact mul_le_mul_of_nonneg_right this hZc.le
  have hkey : (T.card : ℝ) * (μ ^ 2 / 4) ≤ (|C| + 1) * Z * Z ^ (-c) := hkey0.trans hfar'
  have hpow : Z * Z ^ (-c) * Real.log Z ^ 4 ≤ Z ^ (1 - c / 2) := by
    have e : Z ^ (1 - c / 2) = Z * Z ^ (-c) * Z ^ (c / 2) := by
      rw [show 1 - c / 2 = 1 + -c + c / 2 by ring, Real.rpow_add hZ0, Real.rpow_add hZ0,
        Real.rpow_one]
    rw [e]; exact mul_le_mul_of_nonneg_left hlog4 (by positivity)
  have hμ2 : μ ^ 2 / 4 = (c₁ * (1 / 8)) ^ 2 / (4 * Real.log Z ^ 4) := by rw [hμ]; field_simp
  rw [hμ2] at hkey
  have hcd : 0 < (c₁ * (1 / 8)) ^ 2 := by positivity
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hkey
  rw [show 4 * (|C| + 1) / (c₁ * (1 / 8)) ^ 2 * Z ^ (1 - c / 2) =
    4 * (|C| + 1) * Z ^ (1 - c / 2) / (c₁ * (1 / 8)) ^ 2 by ring, le_div_iff₀ hcd]
  have : (|C| + 1) * Z * Z ^ (-c) * (4 * Real.log Z ^ 4) ≤ 4 * (|C| + 1) * Z ^ (1 - c / 2) := by
    have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 * (|C| + 1) by positivity)
    linarith
  linarith

end LeanFormalizations.Erdos385
