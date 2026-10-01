/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Endpoint

/-!
# Erdős #463 for almost all `n` (phase E6, new mathematics)

#463 (formal-conjectures `ErdosProblems/463.lean`) asks for `f → ∞` such that for all large `n` some
composite `m` has `n + f(n) < m < n + p(m)`, `p(m) = minFac m`.  It is the upward mirror of #385 and
meets the same parity obstruction for all `n`.  The frozen statement here, `almost_all_erdos463`,
proves it for almost all `n` with the large margin `f(n) = δ√n`, assuming only Richert's bound (the
same base as `Endpoint.lean`).

## Route (70%): E3 with the witness window shifted above `n`

E3's W2 (`card_badWindow_le`) bounds the `n` whose window `[n − h, n − 1]` (`h = paramH δ Z`)
contains no `m` with `coeffA δ g Z m ≠ 0`; its proof only uses that the window is an `h`-interval
inside `[Z, (1+δ/2) Z]`-ish where the variance bound holds.  Mirror it:
1. **W1↑.**  If `m ∈ [n + ⌈δ√n⌉ + 1, n + ⌈δ√n⌉ + h]` and `coeffA δ g Z m ≠ 0`, then `m = p q` with
   `p ∈ [(1−δ/2)√Z, (1−δ/4)√Z]`, `q ≥ √Z > p`, so `minFac m = p`, `m` is composite, and
   `m − n ≤ δ√n + δ√Z/4 + 2 < (1 − δ/2)√Z ≤ p` (as `δ < 1/4`; compare `witness_margin`).
2. **W2↑.**  Copy `card_badWindow_le` for the shifted window (the `x`-range moves by `≍ δ√Z`, which
   is `o(Z)`, so the variance integral over `[X, 2X]` still covers it; enlarge the range slightly if
   needed).
3. **Assemble** as in `almost_all_F385` / `tendsto_density_zero_of_windows`, feeding the proved
   inputs (`mr16Lemma14_holds`, `montgomeryVaughanMVT_holds`, `mediumPNTStatement_holds`,
   `vkZeroFreeLogDeriv_of_richert h`).

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Filter MeasureTheory LeanFormalizations.Literature

/-- Structure of a witness: `coeffA m ≠ 0` forces `m = p q` composite with
`minFac m = p ≥ (1 − δ/2)√Z`. -/
theorem coeffA_ne_zero_witness {δ Z : ℝ} (hZ : 1 < Z) {g : ℝ → ℝ} (hg : Admissible δ g)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) {m : ℕ} (ha : coeffA δ g Z m ≠ 0) :
    Composite m ∧ (1 - δ / 2) * √Z ≤ (m.minFac : ℝ) := by
  have hsZ : 0 < √Z := Real.sqrt_pos.2 (by linarith)
  unfold coeffA at ha
  obtain ⟨p, hpm, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (div_ne_zero_iff.1 ha).1
  split_ifs at hp with hq <;> [skip; exact absurd rfl hp]
  obtain ⟨hqp, hq1, hq2⟩ := hq
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hgp : g (p / √Z) ≠ 0 := right_ne_zero_of_mul hp
  obtain ⟨hp1, hp2⟩ := hg.2.2.1 _ hgp
  rw [le_div_iff₀ hsZ] at hp1
  rw [div_le_iff₀ hsZ] at hp2
  set q := m / p with hqdef
  have hmpq : m = p * q := (Nat.mul_div_cancel' hpd).symm
  have hpq : (p : ℝ) < q := by nlinarith
  have hpq' : p < q := by exact_mod_cast hpq
  have hmin : m.minFac = p := by
    have hm1 : m ≠ 1 := fun h => by
      rw [hmpq] at h; exact hpp.ne_one (Nat.eq_one_of_mul_eq_one_right h)
    have hmp := Nat.minFac_prime hm1
    have hdvd : m.minFac ∣ p * q := hmpq ▸ Nat.minFac_dvd m
    rcases (Nat.Prime.dvd_mul hmp).1 hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hmp hpp).1 h
    · have := (Nat.prime_dvd_prime_iff_eq hmp hqp).1 h
      have := Nat.minFac_le_of_dvd hpp.two_le hpd
      omega
  have hcomp : Composite m := by
    refine ⟨by rw [hmpq]; nlinarith [hpp.two_le, hqp.two_le], fun hmP => ?_⟩
    have := (Nat.prime_mul_iff.1 (hmpq ▸ hmP))
    rcases this with ⟨-, h⟩ | ⟨-, h⟩
    · exact hqp.ne_one h
    · exact hpp.ne_one h
  exact ⟨hcomp, by rw [hmin]; linarith⟩

/-- **W2↑ (shifted windows).**  If the long average is `≥ μ` on `[Z, (1 + δ/2) Z]`, then any finite
family of unit-separated points `φ n ∈ [Z, (1 + δ/2) Z − 1]` whose windows `[φ n, φ n + h/2]` carry
no witness has at most `2 X D / μ²` members. -/
theorem card_shift_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) {κ : ℝ}
    {g : ℝ → ℝ} :
    ∀ᶠ Z : ℝ in atTop, ∀ μ : ℝ, 0 < μ →
      (∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        μ ≤ shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z) →
      ∀ (T : Finset ℕ) (φ : ℕ → ℝ), (∀ n ∈ T, ∀ n' ∈ T, n < n' → φ n + 1 ≤ φ n') →
      (∀ n ∈ T, Z ≤ φ n ∧ φ n + 1 ≤ (1 + δ / 2) * Z ∧
        ∀ m : ℕ, φ n ≤ m → (m : ℝ) ≤ φ n + paramH δ Z / 2 → coeffA δ g Z m = 0) →
      (T.card : ℝ) ≤ 2 * paramX δ Z * variance δ κ g Z / μ ^ 2 := by
  have hsq : Tendsto (fun Z : ℝ => δ / 4 * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 1, hsq.eventually_ge_atTop 2] with Z hZ hh μ hμ hlong
    T φ hφ hT
  set h := paramH δ Z with hhdef
  have hh' : 2 ≤ h := hh
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  set f := fun x => (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
      shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z) ^ 2 with hf
  have hH1 : paramH1 δ Z ≤ h / 2 - 1 := by
    unfold paramH1; have := Nat.floor_le (show 0 ≤ paramH δ Z / 2 by linarith); linarith
  have hH1' : 0 ≤ paramH1 δ Z := by
    unfold paramH1
    have : (1 : ℝ) ≤ ⌊paramH δ Z / 2⌋₊ := by
      have : 1 ≤ ⌊paramH δ Z / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  have hH2 : 0 ≤ paramH2 δ κ Z := by
    unfold paramH2; rw [← hX]; exact div_nonneg hX0.le (by unfold paramT0; positivity)
  classical
  set J : ℕ → Set ℝ := fun n => Set.Ico (φ n) (φ n + 1)
  have hJ : ∀ n ∈ T, ∀ x ∈ J n, μ ^ 2 ≤ f x ∧ X < x ∧ x ≤ 2 * X := by
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
      have := hlong x hxZ hxZ'
      simp only [hf, hS1, zero_div, zero_sub, neg_sq]
      exact pow_le_pow_left₀ hμ.le this 2
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
          simp
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


/-- **Erdős #463 for almost all `n`**, with margin `δ√n`: the `n ≤ X` having no composite `m` with
`n + δ√n < m < n + minFac m` are `o(X)`. -/
theorem almost_all_erdos463 (h : RichertZetaGrowth) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    Tendsto (fun X : ℕ => ({n : ℕ | n ≤ X ∧ ¬ ∃ m : ℕ, Composite m ∧
        (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac}.ncard : ℝ) / X) atTop (nhds 0) := by
  have hc : (0 : ℝ) < 1 / 8 := by norm_num
  have hc' : (1 / 8 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨g, hg⟩ := exists_admissible hc hc'
  obtain ⟨κ₀, hκ₀, hW2'⟩ := longAverage_lower _root_.Erdos385.mediumPNTStatement_holds hc hc'
  have hκ : 0 < min κ₀ 1 := lt_min hκ₀ one_pos
  obtain ⟨c₁, hc₁, hlong⟩ := hW2' (min κ₀ 1) hκ (min_le_left _ _) g hg
  obtain ⟨C, hvar⟩ := variance_small _root_.Erdos385.mr16Lemma14_holds _root_.Erdos385.montgomeryVaughanMVT_holds
    (smoothPrimeSumVK_of_VKZ (vkZeroFreeLogDeriv_of_richert h)) _root_.Erdos385.mediumPNTStatement_holds hc hc' hκ
    (min_le_right _ _) hg
  have hbad := card_shift_le hc hc' (κ := min κ₀ 1) (g := g)
  set κ := min κ₀ 1
  set E : Set ℕ := {n | ¬ ∃ m : ℕ, Composite m ∧
    (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac} with hE
  refine tendsto_density_zero_of_windows (δ := 1 / 16) (by norm_num) (by norm_num) E ?_
  intro η hη
  have hε := (tendsto_log_pow_four_mul_exp (show 0 < κ / 2 by positivity)).const_mul
    (2 * C / (c₁ * (1 / 8)) ^ 2)
  rw [mul_zero] at hε
  filter_upwards [hbad, hlong, hvar, hε.eventually (eventually_lt_nhds hη),
    eventually_ge_atTop (10000 : ℝ)] with Z hb hl hv hε' hZ
  classical
  have hZ0 : 0 < Z := by linarith
  set s := √Z with hs
  have hss : s * s = Z := Real.mul_self_sqrt hZ0.le
  have hs100 : 100 ≤ s := by
    rw [hs, show (100 : ℝ) = √(100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
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
  have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
  set μ := c₁ * (1 / 8) / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hb' := hb μ hμ0 hl T φ hTφ hT
  have hD0 : 0 ≤ variance (1 / 8) κ g Z := by
    unfold variance
    have : 0 < paramX (1 / 8) Z := by unfold paramX; nlinarith
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hX : paramX (1 / 8) Z ≤ Z := by unfold paramX; nlinarith
  set e := Real.exp (-(κ / 2) * Real.log Z ^ ((1 : ℝ) / 10))
  have hCe : 0 ≤ C * e := hD0.trans hv
  calc (T.card : ℝ) ≤ 2 * paramX (1 / 8) Z * variance (1 / 8) κ g Z / μ ^ 2 := hb'
    _ ≤ 2 * Z * (C * e) / μ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := mul_le_mul hX hv hD0 (by linarith)
        linarith
    _ = Z * (2 * C / (c₁ * (1 / 8)) ^ 2 * (Real.log Z ^ 4 * e)) := by
        rw [hμ]; field_simp
    _ ≤ η * Z := by rw [mul_comm η]; exact mul_le_mul_of_nonneg_left hε'.le (by linarith)

end LeanFormalizations.Erdos385
#print axioms LeanFormalizations.Erdos385.almost_all_erdos463
