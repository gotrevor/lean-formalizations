/-
# The symmetry `R_n(-t-n) = R_n(t)` and the symmetrized partial fractions

For odd `s` and even `n`, `R_n(-t-n) = R_n(t)`.  Given *any* level-`s` representation
`a` of `R_n` (from `Blocks.lean`), the symmetrized coefficients

    ã i k := (a i k + (-1)^{i+1} a i (n-k)) / 2

again represent `R_n`, satisfy `ã i (n-k) = (-1)^{i+1} ã i k`, and are half-integral in the
lattice sense (`2 d_n^{s-1-i} ã i k ∈ ℤ`).  The symmetry forces `Σ_k (-1)^{k+1} ã i k = 0` for
even `i`, i.e. the coefficients of `L_{i+1}` with `i+1` odd vanish — no uniqueness theorem for
partial fractions is needed.

Also here: the bridge `Rval s n u = R_n(n + u + ½)` and the vanishing `R_n(w + ½ - m) = 0` for
`w < 3m` (`n = 2m`), which is what lets the partial sums start at Zudilin's `ν = 1 - m`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Blocks
import LeanFormalizations.NumberTheory.DirichletBeta.Rational

namespace LeanFormalizations.DirichletBeta

open Finset

/-! ### The reflection -/

lemma prod_range_reflect_cast (n : ℕ) (f : ℚ → ℚ) :
    ∏ j ∈ range n, f ((n : ℚ) - 1 - j) = ∏ j ∈ range n, f j := by
  rw [← prod_range_reflect (fun j => f j) n]
  refine prod_congr rfl fun j hj => ?_
  have := mem_range.1 hj
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem Rfun_symm {s n : ℕ} (hodd : Odd s) (hn : Even n) (t : ℚ) :
    Rfun s n (-t - n) = Rfun s n t := by
  simp only [Rfun]
  -- numerator product
  have hnum : ∏ j ∈ range (3 * n), (-t - n - n + (j + 1) - 1 / 2)
      = ∏ j ∈ range (3 * n), (t - n + (j + 1) - 1 / 2) := by
    have := prod_range_reflect_cast (3 * n) (fun j => (-t - n - n + (j + 1) - 1 / 2))
    rw [← this]
    have hc : ∏ j ∈ range (3 * n), (t - n + (j + 1) - 1 / 2)
        = ∏ j ∈ range (3 * n), ((-1) * (-t - n - n + (((3 * n : ℕ) : ℚ) - 1 - j + 1) - 1 / 2)) :=
      prod_congr rfl fun j _ => by push_cast; ring
    rw [hc, prod_mul_distrib, prod_const, card_range]
    have h3 : Even (3 * n) := hn.mul_left 3
    rw [h3.neg_one_pow, one_mul]
  -- denominator product
  have hden : ∏ j ∈ range (n + 1), (-t - n + j) ^ s = - ∏ j ∈ range (n + 1), (t + j) ^ s := by
    have := prod_range_reflect_cast (n + 1) (fun j => (-t - n + j) ^ s)
    rw [← this]
    have hc : ∀ j ∈ range (n + 1), (-t - n + (((n + 1 : ℕ) : ℚ) - 1 - j)) ^ s = (-1) * (t + j) ^ s := by
      intro j _
      rw [show (-t - n + (((n + 1 : ℕ) : ℚ) - 1 - j)) = -(t + j) by push_cast; ring, neg_pow,
        hodd.neg_one_pow]
    rw [prod_congr rfl hc, prod_mul_distrib, prod_const, card_range]
    have h1 : Odd (n + 1) := hn.add_one
    rw [h1.neg_one_pow]; ring
  rw [hnum, hden]
  rw [show (2 * (-t - n) + n) = -(2 * t + n) by ring]
  ring

lemma NonPole.reflect {n : ℕ} {t : ℚ} (ht : NonPole n t) : NonPole n (-t - n) := by
  intro k hk
  have hk' := mem_range.1 hk
  have := ht (n - k) (mem_range.2 (by omega))
  rw [Nat.cast_sub (by omega)] at this
  intro h; apply this; linear_combination -h

/-! ### The symmetrized representation -/

/-- Symmetrized coefficients. -/
noncomputable def symCoef (n : ℕ) (a : ℕ → ℕ → ℚ) (i k : ℕ) : ℚ :=
  (a i k + (-1) ^ (i + 1) * a i (n - k)) / 2

lemma symCoef_reflect (n : ℕ) (a : ℕ → ℕ → ℚ) (i k : ℕ) (hk : k ≤ n) :
    symCoef n a i (n - k) = (-1) ^ (i + 1) * symCoef n a i k := by
  simp only [symCoef]
  rw [Nat.sub_sub_self hk]
  rcases neg_one_pow_eq_or ℚ (i + 1) with h | h <;> rw [h] <;> ring

/-- `pfSum a (-t-n) = pfSum (reflected a) t`. -/
lemma pfSum_reflect (n σ : ℕ) (a : ℕ → ℕ → ℚ) (t : ℚ) :
    pfSum n σ a (-t - n)
      = ∑ k ∈ range (n + 1), ∑ i ∈ range σ, (-1) ^ (i + 1) * a i (n - k) / (t + k) ^ (i + 1) := by
  simp only [pfSum]
  rw [← sum_range_reflect (fun k => ∑ i ∈ range σ, (-1 : ℚ) ^ (i + 1) * a i (n - k) / (t + k) ^ (i + 1))
    (n + 1)]
  refine sum_congr rfl fun k hk => sum_congr rfl fun i _ => ?_
  have hk' := mem_range.1 hk
  rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self (by omega), Nat.cast_sub (by omega)]
  rw [show -t - n + (k : ℚ) = -(t + ((n : ℚ) - k)) by ring, neg_pow]
  rcases neg_one_pow_eq_or ℚ (i + 1) with h | h <;> rw [h]
  · ring
  · rw [neg_one_mul, div_neg, neg_one_mul, neg_div]

theorem Rep.symmetrize {s n : ℕ} (hodd : Odd s) (hn : Even n) (h : Rep n s (Rfun s n)) :
    ∃ b : ℕ → ℕ → ℚ,
      (∀ i ∈ range s, ∀ k ∈ range (n + 1), ∃ z : ℤ, 2 * (Nat.lcmUpto n : ℚ) ^ (s - 1 - i) * b i k = z)
      ∧ (∀ i, ∀ k ≤ n, b i (n - k) = (-1) ^ (i + 1) * b i k)
      ∧ ∀ t, NonPole n t → Rfun s n t = pfSum n s b t := by
  obtain ⟨a, ha, hfa⟩ := h
  refine ⟨symCoef n a, fun i hi k hk => ?_, fun i k hk => symCoef_reflect n a i k hk, fun t ht => ?_⟩
  · obtain ⟨z, hz⟩ := ha i hi k hk
    obtain ⟨w, hw⟩ := ha i hi (n - k) (mem_range.2 (by have := mem_range.1 hk; omega))
    refine ⟨z + (-1) ^ (i + 1) * w, ?_⟩
    simp only [symCoef]
    push_cast
    rw [← hz, ← hw]; ring
  · have h1 := hfa t ht
    have h2 := hfa (-t - n) ht.reflect
    rw [Rfun_symm hodd hn, pfSum_reflect] at h2
    have : Rfun s n t = (pfSum n s a t + ∑ k ∈ range (n + 1), ∑ i ∈ range s,
        (-1) ^ (i + 1) * a i (n - k) / (t + k) ^ (i + 1)) / 2 := by
      rw [← h1, ← h2]; ring
    rw [this]
    simp only [pfSum, symCoef, ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
    ring

/-- The odd-`L` coefficients vanish: for even `i` (and even `n`), `Σ_k (-1)^{k+1} b i k = 0`. -/
lemma sum_sign_symCoef_eq_zero {n : ℕ} (hn : Even n) (b : ℕ → ℕ → ℚ)
    (hb : ∀ i, ∀ k ≤ n, b i (n - k) = (-1) ^ (i + 1) * b i k) {i : ℕ} (hi : Even i) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (k + 1) * b i k = 0 := by
  have hrefl := sum_range_reflect (fun k => (-1 : ℚ) ^ (k + 1) * b i k) (n + 1)
  have hterm : ∀ k ∈ range (n + 1),
      (-1 : ℚ) ^ (n + 1 - 1 - k + 1) * b i (n + 1 - 1 - k) = -((-1) ^ (k + 1) * b i k) := by
    intro k hk
    have hk' := mem_range.1 hk
    rw [show n + 1 - 1 - k = n - k by omega, hb i k (by omega), hi.add_one.neg_one_pow]
    have : (-1 : ℚ) ^ (n - k + 1) = (-1) ^ (k + 1) := by
      obtain ⟨m, hm⟩ := hn
      rw [neg_one_pow_eq_pow_mod_two (n := n - k + 1), neg_one_pow_eq_pow_mod_two (n := k + 1)]
      congr 1
      omega
    rw [this]; ring
  rw [sum_congr rfl hterm, sum_neg_distrib] at hrefl
  linarith

/-! ### The bridge to `Rval` and the early vanishing -/

lemma prod_range_add_one_eq_factorial_div (u M : ℕ) :
    ∏ j ∈ range M, ((u : ℚ) + j + 1) = (Nat.factorial (u + M) : ℚ) / (Nat.factorial u : ℚ) := by
  rw [eq_div_iff (by positivity), ← Nat.factorial_mul_ascFactorial u M,
    Nat.ascFactorial_eq_prod_range]
  push_cast
  rw [mul_comm]
  congr 1
  exact prod_congr rfl fun j _ => by ring

/-- `Rval s n u = R_n(n + u + ½)`. -/
theorem Rval_eq_Rfun (s n u : ℕ) : Rval s n u = Rfun s n ((n : ℚ) + u + 1 / 2) := by
  simp only [Rval, Rfun]
  have h1 : ∏ j ∈ range (3 * n), ((n : ℚ) + u + 1 / 2 - n + (j + 1) - 1 / 2)
      = (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ) := by
    rw [← prod_range_add_one_eq_factorial_div]
    exact prod_congr rfl fun j _ => by ring
  have h2 : ∏ j ∈ range (n + 1), (((n : ℚ) + u + 1 / 2 + j) ^ s)
      = ∏ j ∈ range (n + 1), ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s :=
    prod_congr rfl fun j _ => by congr 1; ring
  rw [h1, h2]
  push_cast
  ring

/-- `R_n(w + ½ - m) = 0` for `w < 3m` where `n = 2m`. -/
theorem Rfun_vanish (s m w : ℕ) (hw : w < 3 * m) :
    Rfun s (m + m) ((w : ℚ) + 1 / 2 - m) = 0 := by
  simp only [Rfun]
  have : ∏ j ∈ range (3 * (m + m)), ((w : ℚ) + 1 / 2 - m - ((m + m : ℕ) : ℚ) + (j + 1) - 1 / 2) = 0 := by
    refine prod_eq_zero (i := 3 * m - 1 - w) (mem_range.2 (by omega)) ?_
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]; simp

end LeanFormalizations.DirichletBeta
