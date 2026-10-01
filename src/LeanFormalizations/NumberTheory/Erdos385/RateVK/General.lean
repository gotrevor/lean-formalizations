/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385 E3 with a general exponent (phase E3d helper)

Parametrised copies of the E3 pipeline (`AlmostAll.lean`): the scale is
`T₀ = exp(κ (log Z)^a)` for any `0 < a < 1/3`, instead of the frozen `a = 1/10`.  The copies live in
the namespace `Gen`, so names resolve to the copies first; statements are the originals with
`(log ·)^{1/10}` replaced by `(log ·)^a`.  The PNT input becomes `PNTExp a` (error
`x exp(−c (log x)^a)`), which `DLVPStatement` implies for `a ≤ 1/2`.
-/

open Real Filter MeasureTheory Complex
open scoped Chebyshev

namespace LeanFormalizations.Erdos385.Gen

open LeanFormalizations.Literature LeanFormalizations.Erdos385


/-- PNT with error `x exp(−c (log x)^a)`. -/
def PNTExp (a : ℝ) : Prop :=
  ∃ c > 0, (ψ - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ a)

/-- `T₀ = exp(κ (log Z)^a)`. -/
noncomputable def paramT0 (a κ Z : ℝ) : ℝ := Real.exp (κ * Real.log Z ^ a)

/-- `h₂ = X / T₀³`. -/
noncomputable def paramH2 (a δ κ Z : ℝ) : ℝ := paramX δ Z / paramT0 a κ Z ^ 3

/-- The variance at scale `a`. -/
noncomputable def variance (a δ κ : ℝ) (g : ℝ → ℝ) (Z : ℝ) : ℝ :=
  (1 / paramX δ Z) * ∫ x in (paramX δ Z)..(2 * paramX δ Z),
    (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
      shortSum (coeffA δ g Z) x (paramH2 a δ κ Z) / paramH2 a δ κ Z) ^ 2


/-- **Short-interval PNT** (DOOR Prop 4, Lean form): for some `c > 0`, every `y ≥ y₀` and
`y exp(−c (log y)^{1/10}) ≤ H ≤ y` give `π(y + H) − π(y) ≥ H / (2 log 2y)`. -/
def ShortIntervalPNT (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, ∀ y H : ℝ, y₀ ≤ y →
    y * Real.exp (-c * Real.log y ^ a) ≤ H → H ≤ y →
    H / (2 * Real.log (2 * y)) ≤
      (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊

variable {a : ℝ} [hA0 : Fact (0 < a)] [hA1 : Fact (a < 1 / 3)]
include hA0 hA1


/-- The eventual size facts behind `shortIntervalPNT_of_mediumPNT`. -/
theorem shortIntervalPNT_eventually (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, 1 ≤ y ∧ 12 * K ≤ Real.exp (c / 2 * Real.log y ^ a) ∧
      Real.exp (c / 2 * Real.log y ^ a) ≤ y ^ ((1 : ℝ) / 8) ∧
      Real.log (2 * y) ≤ 2 * y ^ ((1 : ℝ) / 8) ∧ 32 ≤ y ^ ((1 : ℝ) / 4) := by
  have hL : Tendsto (fun y : ℝ => Real.log y ^ a) atTop atTop :=
    (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp Real.tendsto_log_atTop
  have hL9 : Tendsto (fun y : ℝ => Real.log y ^ (1 - a)) atTop atTop :=
    (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp Real.tendsto_log_atTop
  have hE : Tendsto (fun y : ℝ => Real.exp (c / 2 * Real.log y ^ a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have h2y : Tendsto (fun y : ℝ => 2 * y) atTop atTop := tendsto_id.const_mul_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
  filter_upwards [eventually_ge_atTop 1, hE.eventually_ge_atTop (12 * K),
    hL9.eventually_ge_atTop (4 * c), h2y.eventually hlog,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop 32,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with y hy1 hK h9 hl h32 hlpos
  refine ⟨hy1, hK, ?_, ?_, h32⟩
  · have hy0 : 0 < y := by linarith
    rw [Real.rpow_def_of_pos hy0]
    apply Real.exp_le_exp.2
    have hsplit : Real.log y ^ a * Real.log y ^ (1 - a) = Real.log y := by
      rw [← Real.rpow_add hlpos]; norm_num
    have : 0 ≤ Real.log y ^ a := by positivity
    nlinarith
  · have hy0 : 0 < y := by linarith
    simp only [Real.norm_eq_abs, one_mul] at hl
    rw [abs_of_pos (Real.log_pos (by linarith)), abs_of_pos (by positivity),
      Real.mul_rpow (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) hy0.le] at hl
    have : (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
        _ = 2 := Real.rpow_one 2
    have : 0 ≤ y ^ ((1 : ℝ) / 8) := by positivity
    nlinarith

/-- **Edge: `MediumPNT` ⇒ short-interval PNT.**  Difference `ψ(y + H) − ψ(y)`, discard prime powers
(`O(√y log y)`), partial summation; `c = c'/2`. -/
theorem shortIntervalPNT_of_mediumPNT (h : PNTExp a) : ShortIntervalPNT a := by
  obtain ⟨c, hc, hO⟩ := h
  obtain ⟨K, hK, hKw⟩ := hO.exists_pos
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 hKw.bound
  obtain ⟨y₂, hy₂⟩ := eventually_atTop.1 (shortIntervalPNT_eventually (a := a) c K hc)
  refine ⟨c / 2, by positivity, max (max x₁ 0) y₂, fun y H hy hH hHy => ?_⟩
  obtain ⟨hy1, hKe, he8, hlog, h32⟩ := hy₂ y (le_of_max_le_right hy)
  have hyx : x₁ ≤ y := (le_max_left _ _).trans (le_of_max_le_left hy)
  have hy0 : 0 < y := by linarith
  set L := Real.log y ^ a with hLdef
  set e := Real.exp (c / 2 * L) with hedef
  set f := Real.exp (-(c / 2) * L) with hfdef
  have hfe : f * e = 1 := by rw [hfdef, hedef, ← Real.exp_add]; simp
  have hf0 : 0 < f := Real.exp_pos _
  have he0 : 0 < e := Real.exp_pos _
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hyH : 0 < y + H := by linarith
  -- the MediumPNT error at y and y + H
  have hL' : L ≤ Real.log (y + H) ^ a :=
    Real.rpow_le_rpow (Real.log_nonneg hy1) (Real.log_le_log hy0 (by linarith)) (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
  have hEE : Real.exp (-c * Real.log (y + H) ^ a) ≤ f * f := by
    rw [hfdef, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have hEy : Real.exp (-c * L) = f * f := by rw [hfdef, ← Real.exp_add]; ring_nf
  have b1 := hx₁ (y + H) (by linarith)
  have b2 := hx₁ y hyx
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at b1 b2
  rw [abs_of_pos (by positivity : 0 < (y + H) * Real.exp (-c * Real.log (y + H) ^ a))]
    at b1
  rw [abs_of_pos (by positivity : 0 < y * Real.exp (-c * Real.log y ^ a))] at b2
  rw [← hLdef, hEy] at b2
  have hψ1 : (y + H) - K * (2 * y) * (f * f) ≤ ψ (y + H) := by
    have := (abs_le.1 b1).1
    have : K * ((y + H) * Real.exp (-c * Real.log (y + H) ^ a)) ≤
        K * (2 * y) * (f * f) := by
      rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul (by linarith) hEE (by positivity) (by positivity)
    linarith
  have hψ2 : ψ y ≤ y + K * y * (f * f) := by have := (abs_le.1 b2).2; linarith
  have hθ1 : ψ (y + H) - 2 * √(y + H) * Real.log (y + H) ≤ θ (y + H) := by
    have := Chebyshev.psi_sub_theta_le (show 1 ≤ y + H by linarith); linarith
  have hθ2 := Chebyshev.theta_le_psi y
  -- the prime-power and PNT errors are below H / 2
  have hsq : 2 * √(y + H) * Real.log (y + H) ≤ 2 * (2 * √y) * (2 * y ^ ((1 : ℝ) / 8)) := by
    have h1 : √(y + H) ≤ 2 * √y := by
      rw [show 2 * √y = √(4 * y) by rw [Real.sqrt_mul (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]; norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.log (y + H) ≤ 2 * y ^ ((1 : ℝ) / 8) :=
      (Real.log_le_log hyH (by linarith)).trans hlog
    have : 0 ≤ Real.log (y + H) := Real.log_nonneg (by linarith)
    have : 0 ≤ √(y + H) := Real.sqrt_nonneg _
    nlinarith
  have hr4 : y ^ ((1 : ℝ) / 4) = y ^ ((1 : ℝ) / 8) * y ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hy0]; norm_num
  have hs : √y = y ^ ((1 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]; norm_num
  have hyy : y = √y * √y := (Real.mul_self_sqrt hy0.le).symm
  have hA : 2 * (2 * √y) * (2 * y ^ ((1 : ℝ) / 8)) ≤ y * f / 4 := by
    -- multiply through by `e`
    have key : 32 * √y * y ^ ((1 : ℝ) / 8) * e ≤ y := by
      have h8 : 0 ≤ y ^ ((1 : ℝ) / 8) := by positivity
      have hsy : 0 ≤ √y := Real.sqrt_nonneg _
      calc 32 * √y * y ^ ((1 : ℝ) / 8) * e ≤ 32 * √y * y ^ ((1 : ℝ) / 8) * y ^ ((1 : ℝ) / 8) := by
            apply mul_le_mul_of_nonneg_left he8; positivity
        _ = 32 * √y * y ^ ((1 : ℝ) / 4) := by rw [hr4]; ring
        _ ≤ y ^ ((1 : ℝ) / 4) * √y * y ^ ((1 : ℝ) / 4) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h32 hsy); positivity
        _ = y := by
          rw [show y ^ ((1 : ℝ) / 4) * √y * y ^ ((1 : ℝ) / 4) =
            √y * (y ^ ((1 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) by ring, ← hs, ← hyy]
    have : y * f / 4 = y * f * e / (4 * e) := by field_simp
    rw [this, le_div_iff₀ (by positivity), mul_assoc y f e, hfe]
    nlinarith
  have hB : K * (2 * y) * (f * f) + K * y * (f * f) ≤ y * f / 4 := by
    have h12 : 12 * K * f ≤ 1 := by
      rw [← hfe]; exact (mul_le_mul_of_nonneg_right hKe hf0.le).trans_eq (mul_comm e f)
    have h0 : 0 ≤ y * f := by positivity
    have := mul_le_mul_of_nonneg_right h12 h0
    have h3 : K * (2 * y) * (f * f) + K * y * (f * f) = (12 * K * f) * (y * f) / 4 := by ring
    rw [h3]; linarith
  have hyf : y * f ≤ H := by simpa [hfdef, neg_mul, neg_div] using hH
  have hθd : H / 2 ≤ θ (y + H) - θ y := by linarith
  -- convert to π
  rw [Chebyshev.theta_eq_theta_coe_floor (y + H), Chebyshev.theta_eq_theta_coe_floor y] at hθd
  have hfl : ⌊y⌋₊ ≤ ⌊y + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hπ := theta_sub_le_primeCounting_sub hfl
  have hb1 : (1 : ℝ) ≤ ⌊y + H⌋₊ := by
    have : 1 ≤ ⌊y + H⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hblog : Real.log ⌊y + H⌋₊ ≤ Real.log (2 * y) :=
    Real.log_le_log (by linarith) ((Nat.floor_le hyH.le).trans (by linarith))
  have hπ0 : (0 : ℝ) ≤ (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ := by
    have := Nat.monotone_primeCounting hfl
    rw [sub_nonneg]; exact_mod_cast this
  have hl2 : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hblog hπ0
  linarith

/-- **W2 (Lemma 2 + Chebyshev).**  If the long average is `≥ μ` on `[Z, (1 + δ/2) Z]`, the bad `n` in
the window number at most `2 X D / μ²`. -/
theorem card_badWindow_le {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∀ᶠ Z : ℝ in atTop, ∀ μ : ℝ, 0 < μ →
      (∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        μ ≤ shortSum (coeffA δ g Z) x (paramH2 a δ κ Z) / paramH2 a δ κ Z) →
      ((badWindow δ Z).ncard : ℝ) ≤ 2 * paramX δ Z * variance a δ κ g Z / μ ^ 2 := by
  have hsq : Tendsto (fun Z : ℝ => δ / 4 * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 1, hsq.eventually_ge_atTop 2] with Z hZ hh μ hμ hlong
  set h := paramH δ Z with hhdef
  have hh' : 2 ≤ h := hh
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  set f := fun x => (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
      shortSum (coeffA δ g Z) x (paramH2 a δ κ Z) / paramH2 a δ κ Z) ^ 2 with hf
  have hH1 : paramH1 δ Z ≤ h / 2 - 1 := by
    unfold paramH1; have := Nat.floor_le (show 0 ≤ paramH δ Z / 2 by linarith); linarith
  have hH1' : 0 ≤ paramH1 δ Z := by
    unfold paramH1
    have : (1 : ℝ) ≤ ⌊paramH δ Z / 2⌋₊ := by
      have : 1 ≤ ⌊paramH δ Z / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  have hH2 : 0 ≤ paramH2 a δ κ Z := by unfold paramH2; rw [← hX]; exact div_nonneg hX0.le (by unfold paramT0; positivity)
  -- the bad set is finite
  classical
  set N := ⌊(1 + δ / 2) * Z⌋₊ + 1
  set T := (Finset.range N).filter (· ∈ badWindow δ Z)
  have hBT : badWindow δ Z = ↑T := by
    ext n; simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn; refine ⟨?_, hn⟩
      have := Nat.le_floor hn.2.1; omega
    · exact fun h => h.2
  rw [hBT, Set.ncard_coe_finset]
  -- unit intervals
  set J : ℕ → Set ℝ := fun n => Set.Ico ((n : ℝ) - h) ((n : ℝ) - h + 1)
  have hJ : ∀ n ∈ T, ∀ x ∈ J n, μ ^ 2 ≤ f x ∧ X < x ∧ x ≤ 2 * X := by
    intro n hn x hx
    obtain ⟨hn1, hn2, hn3⟩ := (Finset.mem_filter.1 hn).2
    obtain ⟨hx1, hx2⟩ := hx
    have hxZ : Z ≤ x := by linarith
    have hxZ' : x ≤ (1 + δ / 2) * Z := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have hS1 : shortSum (coeffA δ g Z) x (paramH1 δ Z) = 0 := by
        unfold shortSum
        refine Finset.sum_eq_zero fun m hm => ?_
        by_contra ha
        rw [Finset.mem_Icc] at hm
        have hm1 : x ≤ m := (Nat.ceil_le).1 hm.1
        have hm2 : (m : ℝ) ≤ x + paramH1 δ Z :=
          (Nat.le_floor_iff (by linarith)).1 hm.2
        have hmn : m < n := by
          have : (m : ℝ) < n := by linarith
          exact_mod_cast this
        have := witness_margin hδ hδ' hZ hg hn1 hn2 (by linarith) hmn ha
        linarith
      have := hlong x hxZ hxZ'
      simp only [hf, hS1, zero_div, zero_sub, neg_sq]
      exact pow_le_pow_left₀ hμ.le this 2
    · have : X < Z := by rw [hX, paramX]; nlinarith
      linarith
    · have : (1 + δ / 2) * Z ≤ 2 * X := by rw [hX, paramX]; nlinarith
      linarith
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint J) := by
    intro n _ m _ hnm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hnm with h | h
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
  have hint := integrableOn_sq_shortSum (coeffA δ g Z) (L := X) (U := 2 * X) hH1' hH2
  have hsub : (⋃ n ∈ T, J n) ⊆ Set.Ioc X (2 * X) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨(hJ n hn x hx).2.1, (hJ n hn x hx).2.2⟩
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have key : (T.card : ℝ) * μ ^ 2 ≤ ∫ x in X..(2 * X), f x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc (T.card : ℝ) * μ ^ 2 = ∑ n ∈ T, μ ^ 2 * volume.real (J n) := by
          rw [Finset.sum_congr rfl fun n _ => by
            rw [show volume.real (J n) = 1 by
              simp only [J, Real.volume_real_Ico]; rw [max_eq_left (by linarith)]; ring, mul_one]]
          simp [mul_comm]
      _ ≤ ∑ n ∈ T, ∫ x in J n, f x := Finset.sum_le_sum fun n hn =>
          setIntegral_ge_of_const_le_real measurableSet_Ico measure_Ico_lt_top.ne
            (fun x hx => (hJ n hn x hx).1) (hint.mono_set fun x hx => hsub (by
              simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩))
      _ = ∫ x in ⋃ n ∈ T, J n, f x := (integral_biUnion_finset T (fun _ _ => measurableSet_Ico)
          hdisj fun n hn => hint.mono_set fun x hx => hsub (by
            simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩)).symm
      _ ≤ ∫ x in Set.Ioc X (2 * X), f x :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => hfnn x)
            (Filter.Eventually.of_forall hsub)
  have hI0 : 0 ≤ ∫ x in X..(2 * X), f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => hfnn x
  unfold variance
  change (T.card : ℝ) ≤ 2 * X * (1 / X * ∫ x in X..(2 * X), f x) / μ ^ 2
  rw [show 2 * X * (1 / X * ∫ x in X..(2 * X), f x) = 2 * ∫ x in X..(2 * X), f x by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith


/-- `exp(−c (log y)^{1/10}) ≤ ε` for large `y`. -/
theorem eventually_exp_neg_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-c * Real.log y ^ a) ≤ ε := by
  have hL : Tendsto (fun y : ℝ => c * Real.log y ^ a) atTop atTop :=
    ((tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp Real.tendsto_log_atTop).const_mul_atTop hc
  filter_upwards [hL.eventually_ge_atTop (-Real.log ε)] with y hy
  calc Real.exp (-c * Real.log y ^ a) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.2 (by rw [neg_mul]; linarith)
    _ = ε := Real.exp_log hε

/-- The eventual size facts behind `longAverage_lower`. -/
theorem longAverage_eventually {c δ κ y₀ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hκ : 0 < κ) :
    ∀ᶠ Z : ℝ in atTop, 16 ≤ Z ∧ y₀ ≤ (1 - 7 * δ / 16) * √Z ∧
      Real.exp (-c * Real.log ((1 - 7 * δ / 16) * √Z) ^ a) ≤ δ / 8 ∧
      2 ≤ Real.exp (c / 4 * Real.log Z ^ a) ∧ 2 / δ ≤ paramT0 a κ Z := by
  have ha : Tendsto (fun Z : ℝ => (1 - 7 * δ / 16) * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by linarith)
  have hL : Tendsto (fun Z : ℝ => Real.log Z ^ a) atTop atTop :=
    (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp Real.tendsto_log_atTop
  have hE : Tendsto (fun Z : ℝ => Real.exp (c / 4 * Real.log Z ^ a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))
  have hT : Tendsto (fun Z : ℝ => paramT0 a κ Z) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop hκ)
  filter_upwards [eventually_ge_atTop 16, ha.eventually_ge_atTop y₀,
    ha.eventually (eventually_exp_neg_le (a := a) hc (show 0 < δ / 8 by positivity)),
    hE.eventually_ge_atTop 2, hT.eventually_ge_atTop (2 / δ)] with Z h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

theorem half_rpow_tenth_le {Z y : ℝ} (hlZ : 0 ≤ Real.log Z)
    (hlogy : Real.log Z / 2 ≤ Real.log y) :
    Real.log Z ^ a / 2 ≤ Real.log y ^ a := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 / 2 : ℝ) ^ a := ⟨_, rfl⟩
  have hr1 : 1 / 2 ≤ r := hr ▸ Real.self_le_rpow_of_le_one (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
    (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
  have hL0 : 0 ≤ Real.log Z ^ a := Real.rpow_nonneg hlZ _
  calc Real.log Z ^ a / 2 ≤ r * Real.log Z ^ a := by
        linarith only [mul_le_mul_of_nonneg_right hr1 hL0]
    _ = (Real.log Z / 2) ^ a := by
        rw [hr, div_eq_mul_inv (Real.log Z) 2, Real.mul_rpow hlZ (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]), mul_comm]
        congr 1; norm_num
    _ ≤ Real.log y ^ a :=
        Real.rpow_le_rpow (div_nonneg hlZ (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])) hlogy (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])

set_option maxHeartbeats 1600000 in
/-- **The `q`-count for one `p`** in `longAverage_lower`. -/
theorem qcount_lower {c y₀ δ κ Z x : ℝ} {p : ℕ}
    (hS : ∀ y H : ℝ, y₀ ≤ y → y * Real.exp (-c * Real.log y ^ a) ≤ H → H ≤ y →
      H / (2 * Real.log (2 * y)) ≤ (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊)
    (hc : 0 < c) (hκ : 0 < κ) (hκc : κ ≤ c / 12) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 16 ≤ Z)
    (hy₀ : y₀ ≤ (1 - 7 * δ / 16) * √Z) (hE2 : 2 ≤ Real.exp (c / 4 * Real.log Z ^ a))
    (hT : 2 / δ ≤ paramT0 a κ Z) (hx1 : Z ≤ x) (hx2 : x ≤ (1 + δ / 2) * Z)
    (hp1 : (1 - 7 * δ / 16) * √Z < p) (hp2 : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z) :
    paramH2 a δ κ Z / (2 * p * Real.log Z) ≤ ((primesIn (x / p) (paramH2 a δ κ Z / p)).card : ℝ) ∧
      ∀ q ∈ primesIn (x / p) (paramH2 a δ κ Z / p), q.Prime ∧ √Z ≤ q ∧
        (q : ℝ) ≤ (1 + 2 * δ) * √Z ∧ ⌈x⌉₊ ≤ p * q ∧ p * q ≤ ⌊x + paramH2 a δ κ Z⌋₊ := by
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]]
    exact Real.sqrt_le_sqrt hZ
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by nlinarith) hp1
  have hT3 : paramT0 a κ Z ^ 3 = Real.exp (3 * κ * Real.log Z ^ a) := by
    rw [paramT0, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hT1 : 1 ≤ paramT0 a κ Z := by
    rw [paramT0]
    exact Real.one_le_exp (mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _))
  set L := Real.log Z ^ a with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  set T0 := paramT0 a κ Z with hT0
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  set h2 := paramH2 a δ κ Z with hh2
  have hh2' : h2 = X / T0 ^ 3 := rfl
  have hh20 : 0 < h2 := by rw [hh2']; positivity
  have hh2X : h2 ≤ X := by rw [hh2']; exact div_le_self hX0.le (one_le_pow₀ hT1)
  have hXZ : X ≤ Z := by rw [hX, paramX]; nlinarith
  have hh2δ : h2 ≤ δ / 2 * Z := by
    rw [hh2']
    have : X ≤ Z := by rw [hX, paramX]; nlinarith
    have h3 : 2 / δ ≤ T0 ^ 3 := hT.trans (le_self_pow₀ hT1 (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]))
    rw [div_le_iff₀ (by positivity)]
    have : 2 / δ * δ = 2 := by field_simp
    nlinarith
  set y := x / p with hy
  set H := h2 / p with hH
  clear_value y H h2 X T0 L
  have hH0 : 0 < H := by rw [hH]; exact div_pos hh20 hp0
  have hyp : y * p = x := by rw [hy]; field_simp
  have hHp : H * p = h2 := by rw [hH]; field_simp
  have hlZp : 0 < Real.log Z := Real.log_pos (by linarith)
  -- `y ∈ [√Z, 2√Z]`
  have hy1 : √Z ≤ y := by
    rw [hy, le_div_iff₀ hp0]
    have : (p : ℝ) ≤ √Z := hp2.trans (by nlinarith)
    nlinarith
  have hy2 : y ≤ 2 * √Z := by
    rw [hy, div_le_iff₀ hp0]
    have : x ≤ 2 * √Z * ((1 - 7 * δ / 16) * √Z) := by
      have : 2 * √Z * ((1 - 7 * δ / 16) * √Z) = (2 - 7 * δ / 8) * Z := by
        linear_combination (2 - 7 * δ / 8) * hZsq
      rw [this]; nlinarith
    have : 2 * √Z * ((1 - 7 * δ / 16) * √Z) ≤ 2 * √Z * p :=
      mul_le_mul_of_nonneg_left hp1.le (by positivity)
    linarith
  have hy0 : 0 ≤ y := by linarith
  -- apply the short-interval PNT at `y`
  have hHy : H ≤ y := by
    rw [hH, hy]; exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hlow : y * Real.exp (-c * Real.log y ^ a) ≤ H := by
    have hlogy : Real.log Z / 2 ≤ Real.log y := by
      have : Real.log √Z = Real.log Z / 2 := by rw [Real.log_sqrt hZ0.le]
      rw [← this]; exact Real.log_le_log hsZ hy1
    have hlZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
    have hLy : L / 2 ≤ Real.log y ^ a := hL ▸ half_rpow_tenth_le (a := a) hlZ hlogy
    have hEy : Real.exp (-c * Real.log y ^ a) ≤ Real.exp (-(c / 2) * L) :=
      Real.exp_le_exp.2 (by linarith only [mul_le_mul_of_nonneg_left hLy hc.le])
    have hkey : 2 * Real.exp (-(c / 2) * L) ≤ Real.exp (-(3 * κ * L)) := by
      have : Real.exp (c / 4 * L) ≤ Real.exp ((c / 2 - 3 * κ) * L) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith only [hκc]) hL0)
      have h' := hE2.trans this
      have heq : Real.exp (-(c / 2) * L) * Real.exp ((c / 2 - 3 * κ) * L) =
          Real.exp (-(3 * κ * L)) := by rw [← Real.exp_add]; ring_nf
      have hm := mul_le_mul_of_nonneg_left h' (Real.exp_pos (-(c / 2) * L)).le
      linarith only [heq, hm]
    have hxX : x ≤ 2 * X := by
      rw [hX, paramX]; nlinarith only [hx2, hδ, hδ', hZ0]
    have hxE : x * Real.exp (-c * Real.log y ^ a) ≤ h2 := by
      rw [hh2', hT3, div_eq_mul_inv X, ← Real.exp_neg]
      calc x * Real.exp (-c * Real.log y ^ a)
          ≤ (2 * X) * Real.exp (-(c / 2) * L) :=
            mul_le_mul hxX hEy (Real.exp_pos _).le (by positivity)
        _ = X * (2 * Real.exp (-(c / 2) * L)) := by ring
        _ ≤ X * Real.exp (-(3 * κ * L)) := mul_le_mul_of_nonneg_left hkey hX0.le
    refine le_of_mul_le_mul_right ?_ hp0
    rw [hHp, mul_right_comm, hyp]; exact hxE
  have hcount := hS y H (hy₀.trans ((by nlinarith : (1 - 7 * δ / 16) * √Z ≤ √Z).trans hy1)) hlow hHy
  rw [← card_primesIn hH0.le] at hcount
  refine ⟨?_, fun q hq => ?_⟩
  · refine le_trans ?_ hcount
    have hlog2y : Real.log (2 * y) ≤ Real.log Z :=
      Real.log_le_log (by linarith) (by nlinarith)
    have hlog2y0 : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
    rw [hH, div_div, div_le_div_iff₀ (mul_pos (mul_pos two_pos hp0) hlZp)
      (mul_pos hp0 (mul_pos two_pos hlog2y0))]
    have := mul_le_mul_of_nonneg_left hlog2y (show 0 ≤ h2 * (p * 2) by positivity)
    linarith
  · obtain ⟨hqp, hq1, hq2⟩ := mem_primesIn hy0 hq
    refine ⟨hqp, by linarith, ?_, ?_, ?_⟩
    · have : y + H ≤ (1 + 2 * δ) * √Z := by
        rw [hy, hH, ← add_div, div_le_iff₀ hp0]
        have : x + h2 ≤ (1 + δ) * Z := by nlinarith
        have : (1 + δ) * Z ≤ (1 + 2 * δ) * √Z * ((1 - 7 * δ / 16) * √Z) := by
          have : (1 + 2 * δ) * √Z * ((1 - 7 * δ / 16) * √Z) =
            (1 + 2 * δ) * (1 - 7 * δ / 16) * Z := by
            linear_combination (1 + 2 * δ) * (1 - 7 * δ / 16) * hZsq
          rw [this]; nlinarith
        have : 0 ≤ (1 + 2 * δ) * √Z := by positivity
        nlinarith
      linarith
    · apply Nat.ceil_le.2
      have : x < p * q := by
        have := mul_lt_mul_of_pos_right hq1 hp0
        rw [hyp] at this; linarith
      push_cast; linarith
    · apply Nat.le_floor
      have : (p : ℝ) * q ≤ x + h2 := by
        have := mul_le_mul_of_nonneg_left hq2 hp0.le
        have e : (p : ℝ) * (y + H) = x + h2 := by rw [← hyp, ← hHp]; ring
        rw [e] at this; exact this
      push_cast; linarith

set_option maxHeartbeats 1600000 in
/-- **W2′ (Lemma 3).**  For `κ` small against `MediumPNT`'s constant, the long average is
`≥ c₁ δ / log² Z` on `[Z, (1 + δ/2) Z]`. -/
theorem longAverage_lower (hPNT : PNTExp a) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ g : ℝ → ℝ, Admissible δ g →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ Z : ℝ in atTop, ∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        c₁ * δ / Real.log Z ^ 2 ≤ shortSum (coeffA δ g Z) x (paramH2 a δ κ Z) / paramH2 a δ κ Z := by
  obtain ⟨c, hc, y₀, hS⟩ := shortIntervalPNT_of_mediumPNT (a := a) hPNT
  refine ⟨c / 12, by positivity, fun κ hκ hκc g hg => ⟨1 / 128, by norm_num, ?_⟩⟩
  filter_upwards [longAverage_eventually (a := a) (y₀ := y₀) hc hδ hδ' hκ] with Z ⟨hZ, hy₀, hEa, hE2, hT⟩
    x hx1 hx2
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]]
    exact Real.sqrt_le_sqrt hZ
  have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hh20 : 0 < paramH2 a δ κ Z := by
    unfold paramH2 paramX; exact div_pos (by nlinarith) (by unfold paramT0; positivity)
  set h2 := paramH2 a δ κ Z with hh2
  set y1 := (1 - 7 * δ / 16) * √Z with ha
  set Ha := δ / 8 * √Z with hHa
  have ha0 : 0 < y1 := by rw [ha]; nlinarith
  have hHa0 : 0 < Ha := by positivity
  -- the `p`-count
  have hPc : Ha / (2 * Real.log (2 * y1)) ≤ ((primesIn y1 Ha).card : ℝ) := by
    rw [card_primesIn hHa0.le]
    refine hS y1 Ha hy₀ ?_ (by rw [ha, hHa]; nlinarith)
    calc y1 * Real.exp (-c * Real.log y1 ^ a) ≤ y1 * (δ / 8) :=
          mul_le_mul_of_nonneg_left hEa ha0.le
      _ ≤ Ha := by rw [ha, hHa]; nlinarith
  have hl2a : Real.log (2 * y1) ≤ Real.log Z :=
    Real.log_le_log (by positivity) (by rw [ha]; nlinarith)
  have hl2a0 : 0 < Real.log (2 * y1) := Real.log_pos (by rw [ha]; nlinarith)
  have hP' : δ * √Z / (16 * Real.log Z) ≤ ((primesIn y1 Ha).card : ℝ) := by
    refine le_trans ?_ hPc
    rw [div_le_div_iff₀ (by positivity) (by positivity), hHa]
    have := mul_le_mul_of_nonneg_left hl2a (show 0 ≤ δ * √Z by positivity)
    nlinarith
  -- the `log p` lower bound
  have hlogp : ∀ p ∈ primesIn y1 Ha, Real.log Z / 4 ≤ Real.log p := by
    intro p hp
    obtain ⟨-, hp1, -⟩ := mem_primesIn ha0.le hp
    have : √Z / 2 ≤ y1 := by rw [ha]; nlinarith
    have h1 : Real.log (√Z / 2) ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hsZ.ne' (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]), Real.log_sqrt hZ0.le] at h1
    have : 4 * Real.log 2 ≤ Real.log Z := by
      rw [← Real.log_rpow (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]
      exact Real.log_le_log (by positivity) (by norm_num; linarith)
    linarith
  -- the double count
  set T : ℕ → ℕ → ℝ := fun m p =>
    if (m / p).Prime ∧ √Z ≤ ((m / p : ℕ) : ℝ) ∧ ((m / p : ℕ) : ℝ) ≤ (1 + 2 * δ) * √Z
    then Real.log p * g (p / √Z) else 0 with hTdef
  have hT0 : ∀ m p, 0 ≤ T m p := fun m p => by
    simp only [hTdef]; split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg p) (hg.2.1 _).1
    · exact le_rfl
  have hpair := sum_pairs_le_sum_primeFactors (Finset.Icc ⌈x⌉₊ ⌊x + h2⌋₊) (primesIn y1 Ha)
    (fun p => primesIn (x / p) (h2 / p)) T (fun p => Real.log p) hT0
    (fun p hp => by exact_mod_cast (mem_primesIn ha0.le hp).1.pos) (fun p hp q hq => by
      obtain ⟨hpp, hp1, hp2⟩ := mem_primesIn ha0.le hp
      have hp2' : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z := by
        have : y1 + Ha = (1 - 5 * δ / 16) * √Z := by rw [ha, hHa]; ring
        linarith
      obtain ⟨-, hQ⟩ := qcount_lower (a := a) hS hc hκ hκc hδ hδ' hZ hy₀ hE2 hT hx1 hx2 hp1 hp2'
      obtain ⟨hqp, hq1, hq2, hq3, hq4⟩ := hQ q hq
      refine ⟨Finset.mem_Icc.2 ⟨hq3, hq4⟩, Nat.mem_primeFactors.2 ⟨hpp, dvd_mul_right p q,
        mul_ne_zero hpp.ne_zero hqp.ne_zero⟩, ?_⟩
      simp only [hTdef]
      rw [Nat.mul_div_cancel_left q hpp.pos, if_pos ⟨hqp, hq1, hq2⟩]
      have : g (p / √Z) = 1 := hg.2.2.2 _ (by rw [le_div_iff₀ hsZ]; linarith)
        (by rw [div_le_iff₀ hsZ]; linarith)
      rw [this, mul_one])
  have hsum : ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h2⌋₊, ∑ p ∈ m.primeFactors, T m p =
      shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    unfold shortSum coeffA
    rw [← Finset.sum_div, div_mul_cancel₀ _ hlZ.ne']
  rw [hsum] at hpair
  -- each `p` contributes at least `h2 / (8 √Z)`
  have hper : ∀ p ∈ primesIn y1 Ha, h2 / (8 * √Z) ≤
      ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨hpp, hp1, hp2⟩ := mem_primesIn ha0.le hp
    have hp2' : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z := by
      have : y1 + Ha = (1 - 5 * δ / 16) * √Z := by rw [ha, hHa]; ring
      linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hpZ : (p : ℝ) ≤ √Z := hp2'.trans (by nlinarith)
    have hQc := (qcount_lower (a := a) hS hc hκ hκc hδ hδ' hZ hy₀ hE2 hT hx1 hx2 hp1 hp2').1
    have hlp := hlogp p hp
    have h1 : h2 / (2 * √Z * Real.log Z) ≤ h2 / (2 * p * Real.log Z) :=
      div_le_div_of_nonneg_left hh20.le (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith) hlZ.le)
    have h2' := le_trans h1 hQc
    calc h2 / (8 * √Z) = h2 / (2 * √Z * Real.log Z) * (Real.log Z / 4) := by
          field_simp; ring
      _ ≤ ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p :=
          mul_le_mul h2' hlp (by positivity) (by positivity)
  have hsumlow : ((primesIn y1 Ha).card : ℝ) * (h2 / (8 * √Z)) ≤
      shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hpair
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hper
  have hfin : δ * h2 / (128 * Real.log Z) ≤ shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hsumlow
    calc δ * h2 / (128 * Real.log Z) = δ * √Z / (16 * Real.log Z) * (h2 / (8 * √Z)) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hP' (by positivity)
  rw [le_div_iff₀ hh20]
  have : 1 / 128 * δ / Real.log Z ^ 2 * h2 = δ * h2 / (128 * Real.log Z) / Real.log Z := by
    field_simp
  rw [this, div_le_iff₀ hlZ]
  exact hfin


/-- **W3a.**  The variance in the norm form of `MR16Lemma14`. -/
theorem variance_eq_norm (δ κ : ℝ) (g : ℝ → ℝ) (Z : ℝ) :
    variance a δ κ g Z = (1 / paramX δ Z) * ∫ x in (paramX δ Z)..(2 * paramX δ Z),
      ‖shortSumC (coeffC δ g Z) x (paramH1 δ Z) / (paramH1 δ Z : ℂ) -
        shortSumC (coeffC δ g Z) x (paramH2 a δ κ Z) / (paramH2 a δ κ Z : ℂ)‖ ^ 2 := by
  unfold variance
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hc : ∀ h, shortSumC (coeffC δ g Z) x h = (shortSum (coeffA δ g Z) x h : ℂ) := fun h => by
    simp [shortSumC, shortSum, coeffC]
  simp only [hc]
  rw [← Complex.ofReal_div, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]


/-- W3d asymptotics in `L = log Z`. -/
theorem primeP_small_logFacts : ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧ 8 * L ^ a ≤ L ^ ((1 / 3 + a) / 2) ∧
    2 * L * Real.exp (-(L ^ ((1 / 3 + a) / 2) / 8)) ≤ 1 := by
  have h1 : ∀ᶠ L : ℝ in atTop, 8 ≤ L ^ ((1 / 3 + a) / 2 - a) :=
    (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).eventually (eventually_ge_atTop 8)
  have h2 : Tendsto (fun L : ℝ => (L ^ ((1 / 3 + a) / 2)) ^ (2 / (1 / 3 + a)) * Real.exp (-(1/8) * L ^ ((1 / 3 + a) / 2)))
      atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / (1 / 3 + a)) (1/8) (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp
      (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]))
  have h2' := h2.eventually (ge_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  filter_upwards [h1, h2', eventually_ge_atTop (3:ℝ)] with L hL1 hL2 hL3
  have hL0 : 0 ≤ L := by linarith
  refine ⟨hL3, ?_, ?_⟩
  · have : L ^ ((1 / 3 + a) / 2) = L ^ ((1 / 3 + a) / 2 - a) * L ^ a := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hL1 (by positivity)
  · have : (L ^ ((1 / 3 + a) / 2)) ^ (2 / (1 / 3 + a)) = L := by
      rw [← Real.rpow_mul hL0]
      have : (1 / 3 + a) / 2 * (2 / (1 / 3 + a)) = 1 := by
        have := hA0.out; field_simp
      rw [this, Real.rpow_one]
    rw [this] at hL2
    have : -(1/8) * L ^ ((1 / 3 + a) / 2) = -(L ^ ((1 / 3 + a) / 2) / 8) := by ring
    rw [this] at hL2
    linarith

/-- **W3d, parameters.**  With `P = √Z`, `T = 16Z`, `ε = 1/6`: the VK error, `1/P`, and the
prime-power error are all `≤ 1/T₀` after scaling. -/
theorem primeP_small_params {κ : ℝ} (_hκ : 0 < κ) (hκ' : κ ≤ 1) : ∀ᶠ Z : ℝ in atTop, 16 ≤ Z ∧
    Real.exp (-(Real.log √Z / Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2))) * Real.log (16 * Z) *
      paramT0 a κ Z ≤ 1 ∧ paramT0 a κ Z ≤ √Z ∧ 2 * (2 * √(√Z) * Real.log √Z) * paramT0 a κ Z ≤ √Z := by
  filter_upwards [Real.tendsto_log_atTop.eventually (primeP_small_logFacts (a := a)),
    eventually_gt_atTop (0:ℝ)] with Z ⟨hL3, h8, hexp⟩ hZ0
  set L := Real.log Z with hL
  have hZ : Z = Real.exp L := (Real.exp_log hZ0).symm
  have hL0 : 0 ≤ L := by linarith
  have hsq : √Z = Real.exp (L / 2) := by
    rw [hZ, Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  have hsq2 : √(√Z) = Real.exp (L / 4) := by
    rw [hsq, Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  have hlsq : Real.log √Z = L / 2 := by rw [hsq, Real.log_exp]
  have hl16 : Real.log 16 < 3 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  have hl16' : 0 < Real.log 16 := Real.log_pos (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])
  have hlog16 : Real.log (16 * Z) = Real.log 16 + L := Real.log_mul (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) hZ0.ne'
  have h16 : 16 ≤ Z := by
    rw [hZ]; have := Real.add_one_le_exp L
    have h3 : Real.exp 3 ≤ Real.exp L := Real.exp_le_exp.2 hL3
    have : (16:ℝ) ≤ Real.exp 3 := by
      have := Real.exp_one_gt_d9
      rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; nlinarith
    linarith
  have hT0 : paramT0 a κ Z ≤ Real.exp (L ^ a) := by
    rw [paramT0, ← hL]; apply Real.exp_le_exp.2
    have : 0 ≤ L ^ a := by positivity
    nlinarith
  have h16le : L ^ ((1 / 3 + a) / 2) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ L by linarith) (show (1 / 3 + a) / 2 ≤ 1 by linarith [hA1.out])
    simpa using this
  have hkey : L ^ a - L / 4 ≤ -(L ^ ((1 / 3 + a) / 2) / 8) := by linarith
  have hT0pos : 0 < paramT0 a κ Z := by rw [paramT0]; positivity
  refine ⟨h16, ?_, ?_, ?_⟩
  · -- (A)
    have hlo : L ≤ Real.log (16 * Z) := by rw [hlog16]; linarith
    have hhi : Real.log (16 * Z) ≤ 2 * L := by rw [hlog16]; linarith
    have hpow : Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2) ≤ 2 * L ^ (1 - (1 / 3 + a) / 2) := by
      calc Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2) ≤ (2 * L) ^ (1 - (1 / 3 + a) / 2) := by
            rw [show (2:ℝ)/3 + (1 / 3 - a) / 2 = 1 - (1 / 3 + a) / 2 by ring]
            exact Real.rpow_le_rpow (by linarith) hhi (by linarith [hA1.out])
        _ = 2 ^ (1 - (1 / 3 + a) / 2) * L ^ (1 - (1 / 3 + a) / 2) := Real.mul_rpow (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) hL0
        _ ≤ 2 * L ^ (1 - (1 / 3 + a) / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
              (show 1 - (1 / 3 + a) / 2 ≤ 1 by linarith [hA0.out])
            simpa using this
    have hL56 : 0 < L ^ (1 - (1 / 3 + a) / 2) := by positivity
    have hsplit : L = L ^ ((1 / 3 + a) / 2) * L ^ (1 - (1 / 3 + a) / 2) := by
      rw [← Real.rpow_add (by linarith), show (1 / 3 + a) / 2 + (1 - (1 / 3 + a) / 2) = 1 by ring,
        Real.rpow_one]
    have hratio : L ^ ((1 / 3 + a) / 2) / 4 ≤ Real.log √Z / Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2) := by
      rw [hlsq, le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _)]
      calc L ^ ((1 / 3 + a) / 2) / 4 * Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2)
          ≤ L ^ ((1 / 3 + a) / 2) / 4 * (2 * L ^ (1 - (1 / 3 + a) / 2)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = L / 2 := by nth_rewrite 3 [hsplit]; ring
    calc Real.exp (-(Real.log √Z / Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2))) * Real.log (16 * Z) *
          paramT0 a κ Z ≤ Real.exp (-(L ^ ((1 / 3 + a) / 2) / 4)) * (2 * L) * Real.exp (L ^ a) := by
          apply mul_le_mul (mul_le_mul (Real.exp_le_exp.2 (by linarith)) hhi (by linarith)
            (by positivity)) hT0 hT0pos.le (by positivity)
      _ = 2 * L * Real.exp (-(L ^ ((1 / 3 + a) / 2) / 4) + L ^ a) := by
          rw [Real.exp_add]; ring
      _ ≤ 2 * L * Real.exp (-(L ^ ((1 / 3 + a) / 2) / 8)) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
      _ ≤ 1 := hexp
  · rw [hsq]; exact hT0.trans (Real.exp_le_exp.2 (by linarith))
  · rw [hsq2, hlsq, hsq]
    calc 2 * (2 * Real.exp (L / 4) * (L / 2)) * paramT0 a κ Z
        ≤ 2 * (2 * Real.exp (L / 4) * (L / 2)) * Real.exp (L ^ a) :=
          mul_le_mul_of_nonneg_left hT0 (by positivity)
      _ = (2 * L * Real.exp (L ^ a - L / 4)) * Real.exp (L / 2) := by
          rw [Real.exp_sub, show L / 2 = L / 4 + L / 4 by ring, Real.exp_add]; field_simp; ring
      _ ≤ (2 * L * Real.exp (-(L ^ ((1 / 3 + a) / 2) / 8))) * Real.exp (L / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hkey) (by positivity)
      _ ≤ Real.exp (L / 2) := by
          have := Real.exp_pos (L / 2); nlinarith

/-- **W3d (Lemma 4).**  `|P(1 + it)| ≪ 1/T₀` for `T₀ ≤ |t| ≤ 8X`: the Mellin main term decays like
`1/|t|`, the VK error and the prime powers are smaller.  Confidence 90% (PROOF Lemma 4). -/
theorem primeP_small (hVK : SmoothPrimeSumVK) {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∃ K : ℝ, ∀ᶠ Z : ℝ in atTop, ∀ t : ℝ, paramT0 a κ Z ≤ |t| → |t| ≤ 8 * paramX δ Z →
      ‖primeP g Z (1 + t * I)‖ ≤ K / paramT0 a κ Z := by
  obtain ⟨hs, hc, ht, hsupp, -⟩ := cutoffDiv_facts hδ hδ' hg
  obtain ⟨Km, hKm⟩ := mellin_one_sub_mul_I_decay (f := cutoffDiv g) (by exact_mod_cast hs 1)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 ≤ 1) hsupp
  obtain ⟨C, hC⟩ := hVK (cutoffDiv g) hs hc ht ((1 / 3 - a) / 2) (by linarith [hA1.out])
  refine ⟨Km + 2 * |C| + 1, ?_⟩
  filter_upwards [primeP_small_params (a := a) hκ hκ'] with Z ⟨h16, hA, hB, hCc⟩ t ht0 htX
  set T0 := paramT0 a κ Z with hT0
  set P := √Z with hP
  have hT0pos : 0 < T0 := by rw [hT0, paramT0]; positivity
  have hP4 : 4 ≤ P := by
    rw [hP, show (4:ℝ) = √16 by rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]]
    exact Real.sqrt_le_sqrt h16
  have hPZ : P ≤ 16 * Z := by
    have : P ≤ P * P := by nlinarith
    rw [hP, Real.mul_self_sqrt (by linarith)] at this; linarith
  have hX : paramX δ Z ≤ Z := by rw [paramX]; nlinarith
  have htT : |t| ≤ 16 * Z / 2 := by linarith
  have hVKt := hC P (16 * Z) t (by linarith) (by linarith) hPZ htT
  set e := Real.exp (-(Real.log P / Real.log (16 * Z) ^ ((2:ℝ)/3 + (1 / 3 - a) / 2))) with he
  set S := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) *
    cutoffDiv g (n / P)
  set M := mellin (cutoffDiv g) (1 - t * I)
  have hdec := primeP_decomp hδ hδ' hg (by linarith : (1:ℝ) ≤ Z) t
  have hpsi : ψ P - θ P ≤ 2 * √P * Real.log P := Chebyshev.psi_sub_theta_le (by linarith)
  have hW : ‖M * (P : ℂ) ^ (1 - t * I)‖ = ‖M‖ * P := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]; simp
  have hMb : ‖M‖ * T0 ≤ Km := by
    have := hKm t
    exact (mul_le_mul_of_nonneg_left ht0 (norm_nonneg _)).trans this
  have htot : P * ‖primeP g Z (1 + t * I)‖ ≤
      2 * (2 * √P * Real.log P) + |C| * (P * e * Real.log (16 * Z) + 1) + ‖M‖ * P := by
    have h1 : P * ‖primeP g Z (1 + t * I)‖ = ‖(P : ℂ) * primeP g Z (1 + t * I)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h1]
    have hE0 : 0 ≤ P * e * Real.log (16 * Z) + 1 := by
      have : 0 ≤ Real.log (16 * Z) := Real.log_nonneg (by linarith)
      positivity
    calc ‖(P : ℂ) * primeP g Z (1 + t * I)‖
        ≤ ‖(P : ℂ) * primeP g Z (1 + t * I) - S‖ + ‖S - M * (P : ℂ) ^ (1 - t * I)‖ +
            ‖M * (P : ℂ) ^ (1 - t * I)‖ := by
          have := norm_add₃_le (a := (P : ℂ) * primeP g Z (1 + t * I) - S)
            (b := S - M * (P : ℂ) ^ (1 - t * I)) (c := M * (P : ℂ) ^ (1 - t * I))
          simpa using this
      _ ≤ 2 * (2 * √P * Real.log P) + |C| * (P * e * Real.log (16 * Z) + 1) + ‖M‖ * P := by
          rw [hW]
          gcongr
          · exact hdec.trans (by linarith)
          · exact hVKt.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hE0)
  rw [le_div_iff₀ hT0pos]
  have hP0 : 0 < P := by linarith
  -- multiply `htot` by `T0` and compare termwise with `P * K`
  have key : P * (‖primeP g Z (1 + t * I)‖ * T0) ≤ P * (Km + 2 * |C| + 1) := by
    have hCabs : 0 ≤ |C| := abs_nonneg C
    have e1 : 2 * (2 * √P * Real.log P) * T0 ≤ P := hCc
    have e2 : |C| * (P * e * Real.log (16 * Z)) * T0 ≤ |C| * P := by
      have : e * Real.log (16 * Z) * T0 ≤ 1 := hA
      rw [show |C| * (P * e * Real.log (16 * Z)) * T0 = |C| * P * (e * Real.log (16 * Z) * T0) by ring]
      exact mul_le_of_le_one_right (by positivity) this
    have e3 : |C| * T0 ≤ |C| * P := mul_le_mul_of_nonneg_left hB hCabs
    have e4 : ‖M‖ * P * T0 ≤ Km * P := by nlinarith
    have := mul_le_mul_of_nonneg_right htot hT0pos.le
    nlinarith
  exact le_of_mul_le_mul_left key hP0


/-- The eventual parameter facts behind `variance_small`. -/
theorem variance_params {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ) :
    ∀ᶠ Z : ℝ in atTop, 16 ≤ Z ∧ 1 ≤ Real.log Z ∧ 2 ≤ paramX δ Z ∧ 2 ≤ paramH1 δ Z ∧
      δ * √Z / 16 ≤ paramH1 δ Z ∧ paramH1 δ Z ≤ δ * √Z / 8 ∧ paramH1 δ Z ≤ paramH2 a δ κ Z ∧
      1 ≤ paramT0 a κ Z ∧ 8 * paramT0 a κ Z ≤ √Z := by
  have hL9 : Tendsto (fun Z : ℝ => Real.log Z ^ (1 - a)) atTop atTop :=
    (tendsto_rpow_atTop (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])).comp Real.tendsto_log_atTop
  have hs : Tendsto (fun Z : ℝ => δ * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop hδ
  filter_upwards [eventually_ge_atTop 16, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hL9.eventually_ge_atTop (12 * κ), hs.eventually_ge_atTop 64,
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * Real.log 8 + 4)] with Z hZ hlZ h9 hδs hl8
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hlZ0 : 0 < Real.log Z := by linarith
  -- `R = Z^{1/4}`
  set R := Real.exp (Real.log Z / 4) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hR2 : R * R = √Z := by
    rw [hR, ← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hZ0]; ring_nf
  have hR8 : 8 ≤ R := by
    rw [hR, show (8 : ℝ) = Real.exp (Real.log 8) by rw [Real.exp_log (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]]
    exact Real.exp_le_exp.2 (by linarith)
  have hT3 : paramT0 a κ Z ^ 3 ≤ R := by
    rw [paramT0, ← Real.exp_nat_mul, hR]
    apply Real.exp_le_exp.2
    have hsplit : Real.log Z ^ a * Real.log Z ^ (1 - a) = Real.log Z := by
      rw [← Real.rpow_add hlZ0]; norm_num
    have : 0 ≤ Real.log Z ^ a := by positivity
    push_cast; nlinarith
  have hT1 : 1 ≤ paramT0 a κ Z := by
    rw [paramT0]; exact Real.one_le_exp (by positivity)
  have hTR : paramT0 a κ Z ≤ R := le_trans (le_self_pow₀ hT1 (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])) hT3
  have hX : paramX δ Z = (1 - δ / 2) * Z := rfl
  have hH1lo : paramH1 δ Z ≥ δ * √Z / 8 - 2 := by
    unfold paramH1 paramH
    have := Nat.lt_floor_add_one (δ / 4 * √Z / 2)
    linarith
  have hH1hi : paramH1 δ Z ≤ δ * √Z / 8 := by
    unfold paramH1 paramH
    have := Nat.floor_le (show 0 ≤ δ / 4 * √Z / 2 by positivity)
    linarith
  refine ⟨hZ, hlZ, by rw [hX]; nlinarith, by linarith, by linarith, hH1hi, ?_, hT1, ?_⟩
  · -- `h₁ ≤ √Z ≤ h₂`
    have h2 : √Z ≤ paramH2 a δ κ Z := by
      unfold paramH2
      rw [le_div_iff₀ (by positivity), hX]
      have : √Z * paramT0 a κ Z ^ 3 ≤ √Z * R := mul_le_mul_of_nonneg_left hT3 hsZ.le
      have : √Z * R ≤ (1 - δ / 2) * Z := by
        rw [show √Z * R = R * R * R by rw [← hR2], show Z = R * R * (R * R) by rw [hR2, hZsq]]
        have h3 : 0 < R * R * R := by positivity
        have h4 := mul_le_mul_of_nonneg_left hR8 h3.le
        have h5 : 0 ≤ (1 - δ / 2 - 7 / 8) * (R * R * R * R) :=
          mul_nonneg (by linarith) (by positivity)
        nlinarith
      linarith
    have : δ * √Z / 8 ≤ √Z := by nlinarith
    linarith
  · nlinarith


set_option maxHeartbeats 3200000 in
/-- **W3 (Lemmas 4, 5, Proposition 6).**  `D ≤ C exp(−(κ/2)(log Z)^{1/10})` for large `Z`. -/
theorem variance_small (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT) (hVK : SmoothPrimeSumVK)
    (hPNT : PNTExp a) {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ)
    (hκ' : κ ≤ 1) {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∃ C : ℝ, ∀ᶠ Z : ℝ in atTop,
      variance a δ κ g Z ≤ C * Real.exp (-(κ / 2) * Real.log Z ^ a) := by
  obtain ⟨C, hMR⟩ := h1
  obtain ⟨K₁, hP⟩ := primeP_small (a := a) hVK hδ hδ' hκ hκ' hg
  obtain ⟨K₂, hQ⟩ := primeQ_meanSquare h2 hδ hδ'
  obtain ⟨K₃, hA⟩ := coeffC_meanSquare h2 hδ hδ' hg
  set K' : ℝ := 1 + K₁ ^ 2 * |K₂| * (16 / δ + 1) + (K₁ ^ 2 * |K₂| * (32 / δ + 2) + 48 * |K₃| / δ)
    with hK'
  refine ⟨|C| * K', ?_⟩
  filter_upwards [variance_params (a := a) hδ hδ' hκ, hP, hQ, hA] with Z
    ⟨hZ, hlZ, hX2, hh1, hh1lo, hh1hi, hh12, hT1, hT8⟩ hPZ hQZ hAZ
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hlZ0 : 0 < Real.log Z := by linarith
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out])]]
    exact Real.sqrt_le_sqrt hZ
  have hXZ : paramX δ Z ≤ Z := by unfold paramX; nlinarith
  have hXZ' : Z / 2 ≤ paramX δ Z := by unfold paramX; nlinarith
  have hh2eq : paramH2 a δ κ Z = paramX δ Z / paramT0 a κ Z ^ 3 := rfl
  set X := paramX δ Z with hX
  set T0 := paramT0 a κ Z with hT0
  set H1 := paramH1 δ Z with hH1
  set H2 := paramH2 a δ κ Z with hH2
  set aC := coeffC δ g Z with ha
  clear_value X T0 H1 H2
  have hT0pos : 0 < T0 := by linarith
  have hH1pos : 0 < H1 := by linarith
  -- `A = P Q / log Z`, continuity, and the pointwise bound
  have hAeq : ∀ t : ℝ, LSeries aC (1 + t * I) =
      primeP g Z (1 + t * I) * primeQ δ Z (1 + t * I) / (Real.log Z : ℂ) := fun t =>
    LSeries_coeffC_eq hδ hδ' hZ1 hg _
  have hAcont : Continuous fun t : ℝ => LSeries aC (1 + t * I) := by
    simp only [hAeq]
    exact ((continuous_primeP g Z).mul (continuous_primeQ δ Z)).div_const _
  have hApt : ∀ t : ℝ, T0 ≤ |t| → |t| ≤ 8 * X →
      ‖LSeries aC (1 + t * I)‖ ^ 2 ≤ (K₁ / T0) ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 := by
    intro t ht1 ht2
    have hp := hPZ t ht1 ht2
    have hn : ‖LSeries aC (1 + t * I)‖ ≤ K₁ / T0 * ‖primeQ δ Z (1 + t * I)‖ := by
      rw [hAeq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlZ0]
      rw [div_le_iff₀ hlZ0]
      have := mul_le_mul_of_nonneg_right hp (norm_nonneg (primeQ δ Z (1 + t * I)))
      have : 0 ≤ K₁ / T0 * ‖primeQ δ Z (1 + t * I)‖ :=
        le_trans (by positivity) this
      nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  -- sizes
  have hU : X / H1 ≤ 16 * √Z / δ := by
    rw [div_le_div_iff₀ hH1pos hδ]
    have : X * δ ≤ √Z * √Z * δ := by rw [hZsq]; exact mul_le_mul_of_nonneg_right hXZ hδ.le
    nlinarith
  have hU1 : 1 ≤ X / H1 := by
    rw [le_div_iff₀ hH1pos]
    have : δ * √Z / 8 ≤ √Z := by nlinarith
    have : √Z ≤ Z / 2 := by nlinarith
    linarith
  have hU8 : X / H1 ≤ 8 * X := by
    rw [div_le_iff₀ hH1pos]; nlinarith
  have hT0U : T0 ≤ X / (2 * H1) := by
    rw [le_div_iff₀ (by positivity)]
    have : T0 * (2 * H1) ≤ √Z / 8 * (δ * √Z / 4) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have : √Z / 8 * (δ * √Z / 4) = δ * Z / 32 := by linear_combination δ / 32 * hZsq
    nlinarith
  have hK1sq : (K₁ / T0) ^ 2 ≤ K₁ ^ 2 / T0 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) hT0pos
    nlinarith
  -- the middle term
  set S := {t : ℝ | T0 ≤ |t| ∧ |t| ≤ X / H1} with hS
  have hSmeas : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hM : ∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2 ≤ K₁ ^ 2 * |K₂| * (16 / δ + 1) / T0 := by
    have hcmp := setIntegral_normSq_le hAcont (continuous_primeQ δ Z) hSmeas (U := X / H1) (by linarith)
      (sq_nonneg (K₁ / T0)) (fun t ht => ⟨by have := ht.2; rw [abs_le] at this; linarith,
        by have := ht.2; rw [abs_le] at this; linarith⟩)
      (fun t ht => hApt t ht.1 (ht.2.trans hU8))
    have hq := hQZ (X / H1) hU1
    have hr : K₂ * (X / H1 + √Z) / √Z ≤ |K₂| * (16 / δ + 1) := by
      rw [div_le_iff₀ hsZ]
      have : X / H1 + √Z ≤ (16 / δ + 1) * √Z := by
        have : 16 * √Z / δ = 16 / δ * √Z := by ring
        linarith
      calc K₂ * (X / H1 + √Z) ≤ |K₂| * (X / H1 + √Z) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |K₂| * ((16 / δ + 1) * √Z) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring
    calc _ ≤ (K₁ / T0) ^ 2 * ∫ t in (-(X / H1))..(X / H1), ‖primeQ δ Z (1 + t * I)‖ ^ 2 := hcmp
      _ ≤ (K₁ / T0) ^ 2 * (|K₂| * (16 / δ + 1)) :=
          mul_le_mul_of_nonneg_left (hq.trans hr) (sq_nonneg _)
      _ ≤ K₁ ^ 2 / T0 * (|K₂| * (16 / δ + 1)) :=
          mul_le_mul_of_nonneg_right hK1sq (by positivity)
      _ = _ := by ring
  -- the tail
  set B := (K₁ ^ 2 * |K₂| * (32 / δ + 2) + 48 * |K₃| / δ) / T0 with hB
  have hB0 : 0 ≤ K₁ ^ 2 * |K₂| * (32 / δ + 2) := by positivity
  have hB1 : 0 ≤ 48 * |K₃| / δ := by positivity
  have hTail : ∀ T : ℝ, X / (2 * H1) ≤ T →
      X / (H1 * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries aC (1 + t * I)‖ ^ 2 ≤ B := by
    intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
    have hST : MeasurableSet {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} :=
      (measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    have hSsub : {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} ⊆ Set.Icc (-(2 * T)) (2 * T) := fun t ht =>
      ⟨by have := ht.2; rw [abs_le] at this; linarith,
        by have := ht.2; rw [abs_le] at this; linarith⟩
    have hXHT : X / (H1 * T) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hT; linarith
    have hXHT0 : 0 ≤ X / (H1 * T) := by positivity
    have hI0 : 0 ≤ ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries aC (1 + t * I)‖ ^ 2 :=
      setIntegral_nonneg hST fun t _ => sq_nonneg _
    by_cases hT4 : T ≤ 4 * X
    · have hcmp := setIntegral_normSq_le hAcont (continuous_primeQ δ Z) hST (U := 2 * T)
        (by linarith) (sq_nonneg (K₁ / T0)) hSsub
        (fun t ht => hApt t (hT0U.trans (hT.trans ht.1)) (ht.2.trans (by linarith)))
      have hq := hQZ (2 * T) (by
        have : 1 ≤ X / (2 * H1) := by
          rw [le_div_iff₀ (by positivity)]
          have : δ * √Z / 4 ≤ √Z := by nlinarith
          have : √Z ≤ Z / 2 := by nlinarith
          linarith
        linarith)
      -- `X/(H1 T) · (2T + √Z)/√Z ≤ 32/δ + 2`
      have hfac : X / (H1 * T) * ((2 * T + √Z) / √Z) ≤ 32 / δ + 2 := by
        have e : X / (H1 * T) * ((2 * T + √Z) / √Z) = 2 * (X / H1) / √Z + X / (H1 * T) := by
          field_simp
        rw [e]
        have : 2 * (X / H1) / √Z ≤ 32 / δ := by
          rw [div_le_iff₀ hsZ]
          have : 32 / δ * √Z = 2 * (16 * √Z / δ) := by ring
          linarith
        linarith
      calc X / (H1 * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries aC (1 + t * I)‖ ^ 2
          ≤ X / (H1 * T) * ((K₁ / T0) ^ 2 * (K₂ * (2 * T + √Z) / √Z)) :=
            mul_le_mul_of_nonneg_left (hcmp.trans
              (mul_le_mul_of_nonneg_left hq (sq_nonneg _))) hXHT0
        _ ≤ X / (H1 * T) * ((K₁ / T0) ^ 2 * (|K₂| * ((2 * T + √Z) / √Z))) := by
            apply mul_le_mul_of_nonneg_left _ hXHT0
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = (K₁ / T0) ^ 2 * |K₂| * (X / (H1 * T) * ((2 * T + √Z) / √Z)) := by ring
        _ ≤ (K₁ / T0) ^ 2 * |K₂| * (32 / δ + 2) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
        _ ≤ K₁ ^ 2 / T0 * |K₂| * (32 / δ + 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hK1sq (abs_nonneg _)
        _ ≤ B := by
            rw [hB, add_div]
            have : 0 ≤ 48 * |K₃| / δ / T0 := by positivity
            have : K₁ ^ 2 / T0 * |K₂| * (32 / δ + 2) = K₁ ^ 2 * |K₂| * (32 / δ + 2) / T0 := by ring
            linarith
    · push Not at hT4
      have hcmp := setIntegral_normSq_le hAcont hAcont hST (U := 2 * T) (by linarith) zero_le_one
        hSsub (fun t _ => by rw [one_mul])
      have ha := hAZ (2 * T) (by linarith)
      have hfac : X / (H1 * T) * ((2 * T + Z) / Z) ≤ 3 / H1 := by
        have e : X / (H1 * T) * ((2 * T + Z) / Z) = 2 * X / (H1 * Z) + X / (H1 * T) := by
          field_simp
        rw [e]
        have h1' : 2 * X / (H1 * Z) ≤ 2 / H1 := by
          rw [div_le_div_iff₀ (by positivity) hH1pos]; nlinarith
        have h2' : X / (H1 * T) ≤ 1 / H1 := by
          rw [div_le_div_iff₀ (by positivity) hH1pos]; nlinarith
        have : 2 / H1 + 1 / H1 = 3 / H1 := by ring
        linarith
      have h3H : 3 / H1 ≤ 48 / (δ * √Z) := by
        rw [div_le_div_iff₀ hH1pos (by positivity)]; nlinarith
      have h48 : 48 / (δ * √Z) ≤ 48 / δ / T0 := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by first | (norm_num; done) | linarith [hA0.out, hA1.out] | nlinarith [hA0.out, hA1.out]) (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
      calc X / (H1 * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries aC (1 + t * I)‖ ^ 2
          ≤ X / (H1 * T) * (K₃ * (2 * T + Z) / Z) :=
            mul_le_mul_of_nonneg_left (hcmp.trans (by rw [one_mul]; exact ha)) hXHT0
        _ ≤ X / (H1 * T) * (|K₃| * ((2 * T + Z) / Z)) := by
            apply mul_le_mul_of_nonneg_left _ hXHT0
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = |K₃| * (X / (H1 * T) * ((2 * T + Z) / Z)) := by ring
        _ ≤ |K₃| * (48 / δ / T0) :=
            mul_le_mul_of_nonneg_left (hfac.trans (h3H.trans h48)) (abs_nonneg _)
        _ ≤ B := by
            rw [hB, add_div]
            have : |K₃| * (48 / δ / T0) = 48 * |K₃| / δ / T0 := by ring
            have : 0 ≤ K₁ ^ 2 * |K₂| * (32 / δ + 2) / T0 := by positivity
            linarith
  -- apply MR16
  have hnorm : ∀ m, ‖aC m‖ ≤ 1 := fun m => by
    obtain ⟨h0, h12, -⟩ := coeffA_facts hδ hδ' hZ1 hg m
    rw [ha, coeffC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; linarith
  have hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → aC m = 0 := fun m hm => by
    by_contra hne
    have hne' : coeffA δ g Z m ≠ 0 := fun h0 => hne (by rw [ha, coeffC, h0, Complex.ofReal_zero])
    obtain ⟨-, -, h3⟩ := coeffA_facts hδ hδ' hZ1 hg m
    obtain ⟨hm1, hm2⟩ := h3 hne'
    rw [← hX] at hm1 hm2
    rcases hm with hm | hm <;> linarith
  have hmain := hMR X T0 H1 H2 aC hX2 hT1 hh1 hh12 (le_of_eq hh2eq) hnorm hsupp B hTail
  rw [variance_eq_norm (a := a)]
  rw [← hX, ← hH1, ← hH2]
  refine hmain.trans ?_
  have hM0 : 0 ≤ ∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2 := setIntegral_nonneg hSmeas fun t _ => sq_nonneg _
  have hsum : 1 / T0 + (∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2) + B ≤ K' / T0 := by
    rw [hK', hB]
    have : (1 + K₁ ^ 2 * |K₂| * (16 / δ + 1) + (K₁ ^ 2 * |K₂| * (32 / δ + 2) + 48 * |K₃| / δ)) / T0
        = 1 / T0 + K₁ ^ 2 * |K₂| * (16 / δ + 1) / T0 +
          (K₁ ^ 2 * |K₂| * (32 / δ + 2) + 48 * |K₃| / δ) / T0 := by ring
    rw [this]; linarith
  have hT0e : 1 / T0 = Real.exp (-κ * Real.log Z ^ a) := by
    rw [hT0, paramT0, one_div, ← Real.exp_neg, neg_mul]
  have hexp : Real.exp (-κ * Real.log Z ^ a) ≤
      Real.exp (-(κ / 2) * Real.log Z ^ a) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ Real.log Z ^ a := Real.rpow_nonneg hlZ0.le _
    nlinarith
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hpos : 0 ≤ 1 / T0 + (∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2) + B := by positivity
  calc C * (1 / T0 + (∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2) + B)
      ≤ |C| * (1 / T0 + (∫ t in S, ‖LSeries aC (1 + t * I)‖ ^ 2) + B) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    _ ≤ |C| * (K' / T0) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |C| * K' * (1 / T0) := by ring
    _ ≤ |C| * K' * Real.exp (-(κ / 2) * Real.log Z ^ a) := by
        rw [hT0e]; exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ## Headline -/

end LeanFormalizations.Erdos385.Gen
