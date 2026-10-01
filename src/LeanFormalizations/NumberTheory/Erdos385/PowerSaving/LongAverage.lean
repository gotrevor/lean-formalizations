/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385 power saving: the long average for an arbitrary long length (phase E9b)

`longAverage_core`: `Gen.longAverage_lower`'s double count with the long length `h₂` free and the
prime input abstracted to `PrimeCountAt K Z h₂` (primes in `(y, y + H]` number `≥ H/(K log 2y)` for
`y ≍ √Z`, `h₂/(2√Z) ≤ H ≤ y`).  Output: `S(x, h₂)/h₂ ≥ δ/(32K² log² Z)` on the window, for every
`0 < h₂ ≤ δZ/4`.
-/

namespace LeanFormalizations.Erdos385

open Real

/-- The prime input of the long average at scale `Z`, long length `h₂`. -/
def PrimeCountAt (K Z h₂ : ℝ) : Prop :=
  ∀ y H : ℝ, √Z / 2 ≤ y → y ≤ 2 * √Z → h₂ / (2 * √Z) ≤ H → H ≤ y →
    H / (K * Real.log (2 * y)) ≤ ((primesIn y H).card : ℝ)

set_option maxHeartbeats 1600000 in
theorem qcount_core {K δ Z h2 x : ℝ} {p : ℕ} (hS : PrimeCountAt K Z h2) (hK : 0 < K)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 16 ≤ Z) (hh20 : 0 < h2) (hh2δ : h2 ≤ δ / 4 * Z)
    (hx1 : Z ≤ x) (hx2 : x ≤ (1 + δ / 2) * Z)
    (hp1 : (1 - 7 * δ / 16) * √Z < p) (hp2 : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z) :
    h2 / (K * p * Real.log Z) ≤ ((primesIn (x / p) (h2 / p)).card : ℝ) ∧
      ∀ q ∈ primesIn (x / p) (h2 / p), q.Prime ∧ √Z ≤ q ∧
        (q : ℝ) ≤ (1 + 2 * δ) * √Z ∧ ⌈x⌉₊ ≤ p * q ∧ p * q ≤ ⌊x + h2⌋₊ := by
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by nlinarith) hp1
  set y := x / p with hy
  set H := h2 / p with hH
  have hH0 : 0 < H := by rw [hH]; exact div_pos hh20 hp0
  have hyp : y * p = x := by rw [hy]; field_simp
  have hHp : H * p = h2 := by rw [hH]; field_simp
  have hlZp : 0 < Real.log Z := Real.log_pos (by linarith)
  have hpZ : (p : ℝ) ≤ √Z := hp2.trans (by nlinarith)
  have hy1 : √Z ≤ y := by
    rw [hy, le_div_iff₀ hp0]
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
  have hHy : H ≤ y := by
    rw [hH, hy]; exact div_le_div_of_nonneg_right (by nlinarith) hp0.le
  have hHlow : h2 / (2 * √Z) ≤ H := by
    rw [hH]; exact div_le_div_of_nonneg_left hh20.le hp0 (by linarith)
  have hcount := hS y H (by linarith) hy2 hHlow hHy
  refine ⟨?_, fun q hq => ?_⟩
  · refine le_trans ?_ hcount
    have hlog2y : Real.log (2 * y) ≤ Real.log Z :=
      Real.log_le_log (by linarith) (by nlinarith)
    have hlog2y0 : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
    rw [hH, div_div, div_le_div_iff₀ (mul_pos (mul_pos hK hp0) hlZp)
      (mul_pos hp0 (mul_pos hK hlog2y0))]
    have := mul_le_mul_of_nonneg_left hlog2y (show 0 ≤ h2 * (p * K) by positivity)
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
/-- **The long average for a free long length.** -/
theorem longAverage_core {K δ Z h2 x : ℝ} {g : ℝ → ℝ} (hg : Admissible δ g)
    (hS : PrimeCountAt K Z h2) (hK : 0 < K)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 16 ≤ Z) (hh20 : 0 < h2) (hh2δ : h2 ≤ δ / 4 * Z)
    (hx1 : Z ≤ x) (hx2 : x ≤ (1 + δ / 2) * Z) :
    1 / (32 * K ^ 2) * δ / Real.log Z ^ 2 ≤ shortSum (coeffA δ g Z) x h2 / h2 := by
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ
  have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
  set y1 := (1 - 7 * δ / 16) * √Z with ha
  set Ha := δ / 8 * √Z with hHa
  have ha0 : 0 < y1 := by rw [ha]; nlinarith
  have hHa0 : 0 < Ha := by positivity
  have hPc : Ha / (K * Real.log (2 * y1)) ≤ ((primesIn y1 Ha).card : ℝ) := by
    refine hS y1 Ha (by rw [ha]; nlinarith) (by rw [ha]; nlinarith) ?_ (by rw [ha, hHa]; nlinarith)
    rw [hHa, div_le_iff₀ (by positivity)]
    have : δ / 8 * √Z * (2 * √Z) = δ / 4 * Z := by linear_combination (δ / 4) * hZsq
    linarith
  have hl2a : Real.log (2 * y1) ≤ Real.log Z :=
    Real.log_le_log (by positivity) (by rw [ha]; nlinarith)
  have hl2a0 : 0 < Real.log (2 * y1) := Real.log_pos (by rw [ha]; nlinarith)
  have hP' : δ * √Z / (8 * K * Real.log Z) ≤ ((primesIn y1 Ha).card : ℝ) := by
    refine le_trans ?_ hPc
    rw [div_le_div_iff₀ (by positivity) (by positivity), hHa]
    have := mul_le_mul_of_nonneg_left hl2a (show 0 ≤ δ * √Z * K by positivity)
    nlinarith
  have hlogp : ∀ p ∈ primesIn y1 Ha, Real.log Z / 4 ≤ Real.log p := by
    intro p hp
    obtain ⟨-, hp1, -⟩ := mem_primesIn ha0.le hp
    have : √Z / 2 ≤ y1 := by rw [ha]; nlinarith
    have h1 : Real.log (√Z / 2) ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hsZ.ne' (by norm_num), Real.log_sqrt hZ0.le] at h1
    have : 4 * Real.log 2 ≤ Real.log Z := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by positivity) (by norm_num; linarith)
    linarith
  set T : ℕ → ℕ → ℝ := fun m p =>
    if (m / p).Prime ∧ √Z ≤ ((m / p : ℕ) : ℝ) ∧ ((m / p : ℕ) : ℝ) ≤ (1 + 2 * δ) * √Z
    then Real.log p * g (p / √Z) else 0 with hTdef
  have hT0 : ∀ m p, 0 ≤ T m p := fun m p => by
    simp only [hTdef]; split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg p) (hg.2.1 _).1
    · exact le_rfl
  have hp2of : ∀ p ∈ primesIn y1 Ha, (1 - 7 * δ / 16) * √Z < p ∧
      (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z := by
    intro p hp
    obtain ⟨-, hp1, hp2⟩ := mem_primesIn ha0.le hp
    have : y1 + Ha = (1 - 5 * δ / 16) * √Z := by rw [ha, hHa]; ring
    exact ⟨hp1, by linarith⟩
  have hpair := sum_pairs_le_sum_primeFactors (Finset.Icc ⌈x⌉₊ ⌊x + h2⌋₊) (primesIn y1 Ha)
    (fun p => primesIn (x / p) (h2 / p)) T (fun p => Real.log p) hT0
    (fun p hp => by exact_mod_cast (mem_primesIn ha0.le hp).1.pos) (fun p hp q hq => by
      obtain ⟨hpp, -, -⟩ := mem_primesIn ha0.le hp
      obtain ⟨hp1, hp2'⟩ := hp2of p hp
      obtain ⟨-, hQ⟩ := qcount_core hS hK hδ hδ' hZ hh20 hh2δ hx1 hx2 hp1 hp2'
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
  have hper : ∀ p ∈ primesIn y1 Ha, h2 / (4 * K * √Z) ≤
      ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨hp1, hp2'⟩ := hp2of p hp
    have hp0 : (0 : ℝ) < p := by nlinarith
    have hpZ : (p : ℝ) ≤ √Z := hp2'.trans (by nlinarith)
    have hQc := (qcount_core hS hK hδ hδ' hZ hh20 hh2δ hx1 hx2 hp1 hp2').1
    have hlp := hlogp p hp
    have h1 : h2 / (K * √Z * Real.log Z) ≤ h2 / (K * p * Real.log Z) :=
      div_le_div_of_nonneg_left hh20.le (by positivity)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpZ hK.le) hlZ.le)
    have h2' := le_trans h1 hQc
    calc h2 / (4 * K * √Z) = h2 / (K * √Z * Real.log Z) * (Real.log Z / 4) := by
          field_simp
      _ ≤ ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p :=
          mul_le_mul h2' hlp (by positivity) (by positivity)
  have hsumlow : ((primesIn y1 Ha).card : ℝ) * (h2 / (4 * K * √Z)) ≤
      shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hpair
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hper
  have hfin : δ * h2 / (32 * K ^ 2 * Real.log Z) ≤ shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hsumlow
    calc δ * h2 / (32 * K ^ 2 * Real.log Z) = δ * √Z / (8 * K * Real.log Z) * (h2 / (4 * K * √Z)) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hP' (by positivity)
  rw [le_div_iff₀ hh20]
  have : 1 / (32 * K ^ 2) * δ / Real.log Z ^ 2 * h2 =
      δ * h2 / (32 * K ^ 2 * Real.log Z) / Real.log Z := by
    field_simp
  rw [this, div_le_iff₀ hlZ]
  exact hfin

end LeanFormalizations.Erdos385
