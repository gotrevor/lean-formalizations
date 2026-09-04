/-
# Partial sums of the shifted alternating series `Σ (-1)^w / (w + a)^q`

The N2 assembly evaluates `r_n` by *partial sums* (the `q = 1` pieces are only conditionally
convergent), so we need, for every half-integer shift `a = k - m + ½` (`|k - m| ≤ m`),

    T q a W := Σ_{w<W} (-1)^w / (w + a)^q  →  (-1)^{k+m} · 2^q · L_q + F,

where `L_q = lim E_q` with `E_q(W) = Σ_{ℓ<W} (-1)^ℓ/(2ℓ+1)^q` (so `L_q = β(q)` for `q ≥ 2`) and
`F` is a rational with `d_n^q F ∈ ℤ`.  Instead of reflecting integer-indexed sums we use the
one-step recursion

    T q (a+1) W = 1/a^q - T q a (W+1),

read forwards (`a ↦ a+1`) and backwards (`a+1 ↦ a`) from the base point `a = ½`, where
`T q ½ = 2^q E_q`.  The correction denominators that appear are `(2j+1)^q` with `2j+1 ≤ n-1`,
all dividing `d_n^q`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Beta
import LeanFormalizations.NumberTheory.DirichletBeta.PartialFractions

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- `E_q(W) = Σ_{ℓ<W} (-1)^ℓ/(2ℓ+1)^q`. -/
noncomputable def Eps (q W : ℕ) : ℝ := ∑ l ∈ range W, (-1 : ℝ) ^ l / (2 * (l : ℝ) + 1) ^ q

/-- `T q a W = Σ_{w<W} (-1)^w / (w + a)^q`. -/
noncomputable def Tps (q : ℕ) (a : ℝ) (W : ℕ) : ℝ := ∑ w ∈ range W, (-1 : ℝ) ^ w / ((w : ℝ) + a) ^ q

/-- The limit `L_q` exists for every `q ≥ 1` (alternating series test). -/
lemma exists_tendsto_Eps {q : ℕ} (hq : 1 ≤ q) : ∃ L : ℝ, Tendsto (Eps q) atTop (𝓝 L) := by
  have hanti : Antitone (fun l : ℕ => 1 / (2 * (l : ℝ) + 1) ^ q) := by
    intro a b hab
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) q
  have h0 : Tendsto (fun l : ℕ => 1 / (2 * (l : ℝ) + 1) ^ q) atTop (𝓝 0) := by
    have h1 : Tendsto (fun l : ℕ => (2 * (l : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Tendsto (fun l : ℕ => 2 * (l : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (this.const_mul_atTop (by norm_num))
      exact tendsto_inv_atTop_zero.comp h2
    have h3 : Tendsto (fun l : ℕ => ((2 * (l : ℝ) + 1)⁻¹) ^ q) atTop (𝓝 (0 ^ q)) :=
      h1.pow q
    rw [zero_pow (by omega)] at h3
    refine h3.congr fun l => ?_
    rw [inv_pow, one_div]
  obtain ⟨L, hL⟩ := hanti.tendsto_alternating_series_of_tendsto_zero h0
  refine ⟨L, hL.congr fun W => ?_⟩
  simp only [Eps]
  refine sum_congr rfl fun l _ => ?_
  ring

/-- For `q ≥ 2`, `E_q → β(q)`. -/
lemma tendsto_Eps_beta {q : ℕ} (hq : 2 ≤ q) : Tendsto (Eps q) atTop (𝓝 (dirichletBeta q)) :=
  (summable_betaTerm hq).hasSum.tendsto_sum_nat

/-- The base point: `T q ½ = 2^q E_q`. -/
lemma Tps_half (q W : ℕ) : Tps q (1 / 2) W = 2 ^ q * Eps q W := by
  simp only [Tps, Eps, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  have : ((w : ℝ) + 1 / 2) ^ q = (2 * (w : ℝ) + 1) ^ q / 2 ^ q := by
    rw [← div_pow]; congr 1; ring
  rw [this]
  field_simp

/-- The one-step recursion `T q (a+1) W = 1/a^q - T q a (W+1)`. -/
lemma Tps_succ_shift (q : ℕ) (a : ℝ) (W : ℕ) : Tps q (a + 1) W = 1 / a ^ q - Tps q a (W + 1) := by
  simp only [Tps]
  have h : ∀ w ∈ range W, (-1 : ℝ) ^ w / ((w : ℝ) + (a + 1)) ^ q
      = -((-1) ^ (w + 1) / (((w + 1 : ℕ) : ℝ) + a) ^ q) := by
    intro w _
    push_cast
    rw [pow_succ, show ((w : ℝ) + 1 + a) = w + (a + 1) by ring]
    ring
  rw [sum_range_succ', sum_congr rfl h, sum_neg_distrib]
  simp only [Nat.cast_zero, zero_add, pow_zero]
  ring

lemma tendsto_Tps_succ {q : ℕ} {a : ℝ} {ℓ : ℝ} (h : Tendsto (Tps q a) atTop (𝓝 ℓ)) :
    Tendsto (Tps q (a + 1)) atTop (𝓝 (1 / a ^ q - ℓ)) := by
  have h1 : Tendsto (fun W => Tps q a (W + 1)) atTop (𝓝 ℓ) := (tendsto_add_atTop_iff_nat 1).2 h
  have := h1.const_sub (1 / a ^ q)
  exact this.congr fun W => (Tps_succ_shift q a W).symm

lemma tendsto_Tps_pred {q : ℕ} {a : ℝ} {ℓ : ℝ} (h : Tendsto (Tps q (a + 1)) atTop (𝓝 ℓ)) :
    Tendsto (Tps q a) atTop (𝓝 (1 / a ^ q - ℓ)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have := h.const_sub (1 / a ^ q)
  refine this.congr fun W => ?_
  rw [Tps_succ_shift]; ring

/-- The correction denominators: `d_n^q · 2^q / (2j+1)^q ∈ 2ℤ` for `2j+1 ≤ n`, `q ≥ 1`. -/
lemma corr_int (n q j : ℕ) (hq : 1 ≤ q) (hj : 2 * j + 1 ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ q * (2 ^ q / ((2 * (j : ℚ) + 1) ^ q)) = 2 * z := by
  obtain ⟨z, hz⟩ := lcmUpto_pow_div_int n (2 * j + 1) (by omega) (by omega) q
  refine ⟨2 ^ (q - 1) * z, ?_⟩
  push_cast at hz ⊢
  rw [← hz, show q = (q - 1) + 1 by omega, pow_succ]
  simp only [Nat.add_sub_cancel]
  ring

/-- Forward induction: `T q (k + ½) → (-1)^k 2^q L + F` with `d_n^q F ∈ ℤ`, for `2k ≤ n`. -/
lemma tendsto_Tps_pos {q : ℕ} (hq : 1 ≤ q) {L : ℝ} (hL : Tendsto (Eps q) atTop (𝓝 L)) (n : ℕ) :
    ∀ k : ℕ, 2 * k ≤ n → ∃ F : ℚ, (∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ q * F = 2 * z) ∧
      Tendsto (Tps q ((k : ℝ) + 1 / 2)) atTop (𝓝 ((-1) ^ k * 2 ^ q * L + F)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, ⟨0, by simp⟩, ?_⟩
    simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, Rat.cast_zero, add_zero]
    refine (hL.const_mul (2 ^ q)).congr fun W => ?_
    rw [Tps_half]
  | succ k ih =>
    intro hk
    obtain ⟨F, hF, hT⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := corr_int n q k hq (by omega)
    refine ⟨2 ^ q / (2 * (k : ℚ) + 1) ^ q - F, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hF
      exact ⟨z - w, by push_cast; linear_combination hz - hw⟩
    · have := tendsto_Tps_succ hT
      have e : ((k + 1 : ℕ) : ℝ) + 1 / 2 = (k : ℝ) + 1 / 2 + 1 := by push_cast; ring
      rw [e]
      convert this using 2
      push_cast
      have h2 : (2 : ℝ) * k + 1 ≠ 0 := by positivity
      rw [show ((k : ℝ) + 1 / 2) ^ q = (2 * k + 1) ^ q / 2 ^ q by rw [← div_pow]; congr 1; ring]
      field_simp
      ring

/-- Backward induction: `T q (½ - k) → (-1)^k 2^q L + F` with `d_n^q F ∈ ℤ`, for `2k ≤ n`. -/
lemma tendsto_Tps_neg {q : ℕ} (hq : 1 ≤ q) {L : ℝ} (hL : Tendsto (Eps q) atTop (𝓝 L)) (n : ℕ) :
    ∀ k : ℕ, 2 * k ≤ n → ∃ F : ℚ, (∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ q * F = 2 * z) ∧
      Tendsto (Tps q (1 / 2 - (k : ℝ))) atTop (𝓝 ((-1) ^ k * 2 ^ q * L + F)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, ⟨0, by simp⟩, ?_⟩
    simp only [Nat.cast_zero, sub_zero, pow_zero, one_mul, Rat.cast_zero, add_zero]
    refine (hL.const_mul (2 ^ q)).congr fun W => ?_
    rw [Tps_half]
  | succ k ih =>
    intro hk
    obtain ⟨F, hF, hT⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := corr_int n q k hq (by omega)
    refine ⟨(-1) ^ q * (2 ^ q / (2 * (k : ℚ) + 1) ^ q) - F, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hF
      exact ⟨(-1) ^ q * z - w, by push_cast; linear_combination (-1 : ℚ) ^ q * hz - hw⟩
    · have e : (1 / 2 : ℝ) - (k : ℝ) = (1 / 2 - ((k + 1 : ℕ) : ℝ)) + 1 := by push_cast; ring
      rw [e] at hT
      have := tendsto_Tps_pred hT
      convert this using 2
      push_cast
      have h2 : (2 : ℝ) * k + 1 ≠ 0 := by positivity
      have e2 : (1 / 2 - ((k : ℝ) + 1)) = -((2 * k + 1) / 2) := by ring
      rw [e2, neg_pow (((2 : ℝ) * k + 1) / 2), div_pow]
      rcases neg_one_pow_eq_or ℝ q with h | h <;> rw [h] <;> field_simp <;> ring

end LeanFormalizations.DirichletBeta
