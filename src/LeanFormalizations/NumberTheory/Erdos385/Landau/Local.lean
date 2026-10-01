/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Landau's local formula on a disc of any centre and radius (phase E2e)

PNT+ `FinalBound` / `ZerosBound` (sorry-free) are stated on the unit disc for `f(0) = 1`.  Here they
are transported to `g` on `closedBall c₀ δ` through `f z = g (c₀ + δ z) / g c₀`, with radii
`r' = 1/2, r = 5/8, R' = 3/4, R = 7/8` and `B = 2M/‖g c₀‖`.
-/

namespace LeanFormalizations.Erdos385.Landau

open Complex Metric

/-- A zero of an analytic function with only finitely many zeros nearby has order `≥ 1`. -/
lemma one_le_analyticOrderNatAt {f : ℂ → ℂ} {z : ℂ} {S : Set ℂ} (hS : S.Finite)
    (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hloc : ∀ᶠ w in nhds z, f w = 0 → w ∈ S) :
    1 ≤ analyticOrderNatAt f z := by
  have hne : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h1 : ∀ᶠ w in nhds z, w ∈ S := (htop.and hloc).mono fun w hw => hw.2 hw.1
    have h2 : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ∉ S \ {z} :=
      nhdsWithin_le_nhds ((hS.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
        (fun h => h.2 rfl))
    have h3 : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ≠ z := self_mem_nhdsWithin
    have h1' : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ∈ S := nhdsWithin_le_nhds h1
    obtain ⟨w, hw1, hw2, hw3⟩ := (h1'.and (h2.and h3)).exists
    exact hw2 ⟨hw1, hw3⟩
  have h0 : analyticOrderAt f z ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨hf, hz⟩
  unfold analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at h0 ⊢
  simp only [ENat.toNat_coe]
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h0)

/-- **Landau's local formula** (Titchmarsh Lemma 3.9 shape). -/
theorem local_landau : ∃ K₀ : ℝ, ∀ (g : ℂ → ℂ) (c₀ : ℂ) (δ M : ℝ), 0 < δ →
    AnalyticOnNhd ℂ g (closedBall c₀ δ) →
    {ρ | ρ ∈ closedBall c₀ δ ∧ g ρ = 0}.Finite → g c₀ ≠ 0 →
    (∀ s ∈ closedBall c₀ δ, ‖g s‖ ≤ M) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ, ρ ∈ Z ↔ g ρ = 0 ∧ ‖ρ - c₀‖ ≤ 5 / 8 * δ) ∧ (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, (m ρ : ℝ)) ≤ K₀ * Real.log (2 * M / ‖g c₀‖)) ∧
      ∀ s, ‖s - c₀‖ ≤ δ / 2 → g s ≠ 0 →
        ‖deriv g s / g s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
          K₀ * Real.log (2 * M / ‖g c₀‖) / δ := by
  set KF : ℝ := 16 * (5 / 8 : ℝ) ^ 2 / (5 / 8 - 1 / 2) ^ 3 +
    1 / (((7 / 8 : ℝ) ^ 2 / (3 / 4) - 3 / 4) * Real.log ((7 / 8) / (3 / 4))) with hKF
  set KZ : ℝ := 1 / Real.log ((7 / 8 : ℝ) / (5 / 8)) with hKZ
  have hKF0 : 0 ≤ KF := by
    have : 0 < Real.log ((7 / 8 : ℝ) / (3 / 4)) := Real.log_pos (by norm_num)
    have : 0 < ((7 / 8 : ℝ) ^ 2 / (3 / 4) - 3 / 4) := by norm_num
    positivity
  have hKZ0 : 0 ≤ KZ := by
    have : 0 < Real.log ((7 / 8 : ℝ) / (5 / 8)) := Real.log_pos (by norm_num)
    positivity
  refine ⟨KF + KZ, ?_⟩
  intro g c₀ δ M hδ hg hfin hg0 hM
  set a := g c₀ with ha
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr hg0
  have hMa : ‖a‖ ≤ M := hM c₀ (mem_closedBall_self hδ.le)
  set B := 2 * M / ‖a‖ with hB
  have hB1 : 1 < B := by
    rw [hB, lt_div_iff₀ ha0]; linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1.le
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  set f : ℂ → ℂ := fun z => g (c₀ + δ * z) / a with hf
  have hmap : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + δ * z ∈ closedBall c₀ δ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ]
    nlinarith [norm_nonneg z]
  have hfA : AnalyticOnNhd ℂ f (closedBall 0 1) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    have h1 : AnalyticAt ℂ (fun w : ℂ => c₀ + δ * w) z :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact (AnalyticAt.comp (g := g) (f := fun w : ℂ => c₀ + δ * w) (hg _ (hmap z hz')) h1).div_const
  have hf0 : f 0 = 1 := by simp only [hf, mul_zero, add_zero]; exact div_self hg0
  have hfin' : (SetOfZeros 1 f).Finite := by
    refine (hfin.image (fun s => (s - c₀) / δ)).subset ?_
    rintro z ⟨hz1, hz0⟩
    refine ⟨c₀ + δ * z, ⟨hmap z hz1, ?_⟩, ?_⟩
    · simpa [hf, hg0] using hz0
    · simp only; field_simp; ring
  have hfB : ∀ z : ℂ, ‖z‖ ≤ 7 / 8 → ‖f z‖ ≤ B := by
    intro z hz
    have := hM _ (hmap z (by linarith))
    simp only [hf, norm_div]
    rw [hB, div_le_div_iff_of_pos_right ha0]
    linarith
  set Zf := (finiteSetOfZeros_mono (r := 5 / 8) (by norm_num) hfin').toFinset with hZf
  have hmemZf : ∀ z, z ∈ Zf ↔ ‖z‖ ≤ 5 / 8 ∧ f z = 0 := by
    intro z; rw [hZf, Set.Finite.mem_toFinset]; rfl
  set φ : ℂ → ℂ := fun z => c₀ + δ * z with hφ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    simp only [hφ] at hxy
    exact mul_left_cancel₀ hδC (add_left_cancel hxy)
  have hφinv : ∀ z, (φ z - c₀) / δ = z := by
    intro z; simp only [hφ]; field_simp; ring
  set Z := Zf.image φ with hZ
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ((ρ - c₀) / δ) with hm
  refine ⟨Z, m, ?_, ?_, ?_, ?_⟩
  · intro ρ
    rw [hZ, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hmemZf] at hz
      refine ⟨by simpa [hf, hg0] using hz.2, ?_⟩
      simp only [hφ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ]
      nlinarith [norm_nonneg z]
    · rintro ⟨h0, hd⟩
      refine ⟨(ρ - c₀) / δ, ?_, ?_⟩
      · rw [hmemZf]
        refine ⟨?_, ?_⟩
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, div_le_iff₀ hδ]
          linarith
        · simp only [hf]; rw [show c₀ + δ * ((ρ - c₀) / δ) = ρ by field_simp; ring, h0,
            zero_div]
      · simp only [hφ]; field_simp; ring
  · intro ρ hρ
    rw [hZ, Finset.mem_image] at hρ
    obtain ⟨z, hz, rfl⟩ := hρ
    rw [hmemZf] at hz
    simp only [hm, hφinv]
    refine one_le_analyticOrderNatAt hfin' (hfA z (by simp; linarith)) hz.2 ?_
    have : ∀ᶠ w in nhds z, w ∈ ball (0 : ℂ) 1 :=
      isOpen_ball.mem_nhds (by simp; linarith)
    exact this.mono fun w hw h0 => ⟨by simpa using (le_of_lt (by simpa using hw)), h0⟩
  · rw [hZ, Finset.sum_image (fun x _ y _ h => hφinj h)]
    simp only [hm, hφinv]
    have := ZerosBound (r := 5 / 8) (R := 7 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hfA hf0 hfin' hfB
    push_cast at this
    calc _ ≤ KZ * Real.log B := this
      _ ≤ (KF + KZ) * Real.log B := by nlinarith
  · intro s hs hgs
    set z := (s - c₀) / δ with hzdef
    have hsz : φ z = s := by simp only [hφ, hzdef]; field_simp; ring
    have hz : ‖z‖ ≤ 1 / 2 := by
      rw [hzdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, div_le_iff₀ hδ]
      linarith
    have hfz : f z ≠ 0 := by
      simp only [hf]; rw [show c₀ + δ * z = s from hsz]; exact div_ne_zero hgs hg0
    have hzmem : z ∈ closedBall (0 : ℂ) (1 / 2) \ SetOfZeros (3 / 4) f := by
      refine ⟨by simpa using hz, fun h => hfz h.2⟩
    have hFB := FinalBound (r' := 1 / 2) (r := 5 / 8) (R' := 3 / 4) (R := 7 / 8) hB1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hfA hf0 hfin' hfB hzmem
    -- derivative of f
    have hgd : HasDerivAt g (deriv g s) s :=
      (hg s (by rw [mem_closedBall, dist_eq_norm]; linarith)).differentiableAt.hasDerivAt
    have hφd : HasDerivAt φ (δ : ℂ) z := by
      have h := ((hasDerivAt_id' z).const_mul (δ : ℂ)).const_add c₀
      simp only [mul_one] at h; exact h
    have hfd : HasDerivAt f (deriv g s * δ / a) z := by
      have := (hgd.comp_of_eq z hφd hsz.symm).div_const a
      exact this
    have hfz' : f z = g s / a := by simp only [hf]; rw [show c₀ + δ * z = s from hsz]
    have hlog : deriv f z / f z = δ * (deriv g s / g s) := by
      rw [hfd.deriv, hfz']; field_simp
    have hsum : ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) =
        δ * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) := by
      rw [hZ, Finset.sum_image (fun x _ y _ h => hφinj h), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp only [hm, hφinv]
      have hne : s - φ ρ ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [hmemZf] at hρ
        apply hgs
        rw [h]
        have := hρ.2
        simp only [hf, div_eq_zero_iff, hg0, or_false] at this
        simpa [hφ] using this
      have : z - ρ = (s - φ ρ) / δ := by simp only [hzdef, hφ]; field_simp; ring
      rw [this]; field_simp
    rw [hlog, hsum, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ] at hFB
    rw [le_div_iff₀ hδ]
    calc _ = δ * ‖deriv g s / g s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by ring
      _ ≤ KF * Real.log B := hFB
      _ ≤ (KF + KZ) * Real.log B := by nlinarith

end LeanFormalizations.Erdos385.Landau
