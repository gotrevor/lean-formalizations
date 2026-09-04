/-
# N4 — the real-place bound: `|r_21,n| ≤ exp(-21.3 n)` eventually

The elementary route, made even more elementary by `Integral.lean`: the crux proof gives the
*exact* identity `r_n = -C_n (N(0) - N(1))` with `0 < N(0) - N(1) ≤ N(0) ≤ M_0`, so

    |r_n| ≤ C_n · M_0,     C_n = 2^{6n} (3n+1)!/(n!)^3,     M_0 = B_0^{21},

and `B_0 = 2^{2n+2} (2n)! (2n+1)! / (4n+2)! ≤ 4 · 4^{-n}` (a central-binomial bound), while
`(3n+1)!/(n!)^3 ≤ (3n+1) 2^{5n}` (two binomials `≤ 2^k`).  Altogether

    |r_n| ≤ (3n+1) · 4^{21} · 2^{-31 n},        31 · log 2 = 21.488 > 21.3.

The true rate at `s = 21` is `lim |r_n|^{1/n} = e^{-21.657}` (`papers/catalan-beta-ledger.py`); the
bound `C_n M_0` has exactly that rate, and the crude `2^{5n}` for the trinomial coefficient costs
the `0.17` that brings it to `21.488`.  The constant frozen below is **`-21.3`**.

Ledger arithmetic that this constant must satisfy, together with `Lcm.lean`'s `1.01`:

    21 · 1.01 = 21.21  <  21.3.

⚠️ Do **not** tighten `-21.3`; the margin is the whole point, and any constant in
`(-21.488, -21.21)` closes the proof.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Rational
import LeanFormalizations.NumberTheory.DirichletBeta.Integral

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-! ### `B_0 ≤ 4 · 4^{-n}` -/

/-- Interleaving: `∏_{j<m} (a+2j) · ∏_{j<m} (a+1+2j) = ∏_{k<2m} (a+k)`. -/
lemma prod_interleave (a m : ℕ) :
    (∏ j ∈ range m, (a + 2 * j)) * (∏ j ∈ range m, (a + 1 + 2 * j)) = ∏ k ∈ range (2 * m), (a + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      prod_range_succ, prod_range_succ, ← ih]
    ring

/-- `2^{4n} (2n)! (2n+1)! ≤ (4n+2)!`. -/
lemma two_pow_mul_factorial_le (n : ℕ) :
    2 ^ (4 * n) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1) ≤ Nat.factorial (4 * n + 2) := by
  have hc := Nat.choose_mul_factorial_mul_factorial (show 2 * n + 1 ≤ 4 * n + 2 by omega)
  rw [show 4 * n + 2 - (2 * n + 1) = 2 * n + 1 by omega] at hc
  have hb := Nat.four_pow_le_two_mul_add_one_mul_central_binom (2 * n + 1)
  rw [show 2 * (2 * n + 1) = 4 * n + 2 by ring] at hb
  have h4 : 4 ^ (2 * n + 1) = 4 * 2 ^ (4 * n) := by
    rw [pow_succ, show (4 : ℕ) ^ (2 * n) = 2 ^ (4 * n) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; ring]
    ring
  rw [h4] at hb
  have hf : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) := Nat.factorial_succ _
  rw [← hc]
  -- `2^{4n} ≤ (2n+1) C` since `4·2^{4n} ≤ (4n+3) C ≤ 3 (2n+1) C`
  have hkey : 2 ^ (4 * n) ≤ (2 * n + 1) * Nat.choose (4 * n + 2) (2 * n + 1) := by nlinarith
  calc 2 ^ (4 * n) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1)
      ≤ (2 * n + 1) * Nat.choose (4 * n + 2) (2 * n + 1) * Nat.factorial (2 * n)
          * Nat.factorial (2 * n + 1) := by gcongr
    _ = Nat.choose (4 * n + 2) (2 * n + 1) * Nat.factorial (2 * n + 1) * Nat.factorial (2 * n + 1) := by
          rw [hf]; ring

/-- The odd product `O = ∏_{j≤n} (2n+1+2j)` satisfies `(2n)! · O · E = (4n+2)!` where
`E = ∏_{j≤n} (2n+2+2j) = 2^{n+1} (2n+1)!/n!`. -/
lemma odd_prod_identities (n : ℕ) :
    Nat.factorial (2 * n) * ((∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j))
        * ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j)) = Nat.factorial (4 * n + 2) ∧
    Nat.factorial n * ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j)
        = 2 ^ (n + 1) * Nat.factorial (2 * n + 1) := by
  constructor
  · have h := prod_interleave (2 * n + 1) (n + 1)
    rw [show ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j) = ∏ j ∈ range (n + 1), (2 * n + 1 + 1 + 2 * j)
      from prod_congr rfl fun j _ => by ring, h, show 2 * (n + 1) = 2 * n + 2 by ring,
      ← Nat.ascFactorial_eq_prod_range, Nat.factorial_mul_ascFactorial]
    congr 1; ring
  · have h : ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j) = 2 ^ (n + 1) * ∏ j ∈ range (n + 1), (n + 1 + j) := by
      have : ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j) = ∏ j ∈ range (n + 1), (2 * (n + 1 + j)) :=
        prod_congr rfl fun j _ => by ring
      rw [this, prod_mul_distrib, prod_const, card_range]
    rw [h, ← Nat.ascFactorial_eq_prod_range, ← mul_assoc, mul_comm (Nat.factorial n),
      mul_assoc, Nat.factorial_mul_ascFactorial]
    congr 2; ring

/-- `B_0 ≤ 4 / 4^n`. -/
lemma Bseq_zero_le (n : ℕ) : Bseq n 0 ≤ 4 / 4 ^ n := by
  obtain ⟨h1, h2⟩ := odd_prod_identities n
  have hkey := two_pow_mul_factorial_le n
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  -- the ℕ inequality `n! 2^{n+1} 4^n · X ≤ 4 O · X` with `X = 2^{n+1} (2n)! (2n+1)!`
  have hX : 0 < 2 ^ (n + 1) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1) := by positivity
  have hnat : Nat.factorial n * 2 ^ (n + 1) * 4 ^ n
      ≤ 4 * ∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j) := by
    refine Nat.le_of_mul_le_mul_right ?_ hX
    calc Nat.factorial n * 2 ^ (n + 1) * 4 ^ n
          * (2 ^ (n + 1) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1))
        = 4 * Nat.factorial n * (2 ^ (4 * n) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1)) := by
          rw [h4]; ring
      _ ≤ 4 * Nat.factorial n * Nat.factorial (4 * n + 2) := by gcongr
      _ = 4 * (∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j))
            * (Nat.factorial (2 * n) * (Nat.factorial n * ∏ j ∈ range (n + 1), (2 * n + 2 + 2 * j))) := by
          rw [← h1]; ring
      _ = 4 * (∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j))
            * (2 ^ (n + 1) * Nat.factorial (2 * n) * Nat.factorial (2 * n + 1)) := by
          rw [h2]; ring
  -- `P = O / 2^{n+1}` in ℝ
  have hP : ∏ j ∈ range (n + 1), ((2 * ((n : ℝ) + 1 + ((0 : ℕ) : ℝ) + j) - 1) / 2)
      = ((∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j) : ℕ) : ℝ) / 2 ^ (n + 1) := by
    have : ∏ j ∈ range (n + 1), ((2 * ((n : ℝ) + 1 + ((0 : ℕ) : ℝ) + j) - 1) / 2)
        = ∏ j ∈ range (n + 1), (((2 * n + 1 + 2 * j : ℕ) : ℝ) / 2) :=
      prod_congr rfl fun j _ => by push_cast; ring
    rw [this, prod_div_distrib, prod_const, card_range, Nat.cast_prod]
  have hO0 : (0 : ℝ) < ((∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun j _ => by omega
  simp only [Bseq]
  rw [hP, div_div_eq_mul_div, div_le_div_iff₀ hO0 (by positivity)]
  have hnat' : ((Nat.factorial n * 2 ^ (n + 1) * 4 ^ n : ℕ) : ℝ)
      ≤ ((4 * ∏ j ∈ range (n + 1), (2 * n + 1 + 2 * j) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hnat'
  push_cast
  linarith

/-! ### `C_n ≤ (3n+1) 2^{11 n}` -/

lemma factorial_three_mul_le (n : ℕ) :
    Nat.factorial (3 * n) ≤ 2 ^ (5 * n) * Nat.factorial n ^ 3 := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  rw [show 3 * n - n = 2 * n by omega] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h2
  have b1 := Nat.choose_le_two_pow (3 * n) n
  have b2 := Nat.choose_le_two_pow (2 * n) n
  rw [← h1, ← h2, show 5 * n = 3 * n + 2 * n by ring, pow_add]
  calc Nat.choose (3 * n) n * Nat.factorial n * (Nat.choose (2 * n) n * Nat.factorial n * Nat.factorial n)
      ≤ 2 ^ (3 * n) * Nat.factorial n * (2 ^ (2 * n) * Nat.factorial n * Nat.factorial n) := by gcongr
    _ = 2 ^ (3 * n) * 2 ^ (2 * n) * Nat.factorial n ^ 3 := by ring

lemma Cn_le (n : ℕ) : Cn n ≤ (3 * n + 1 : ℝ) * 2 ^ (11 * n) := by
  unfold Cn
  rw [div_le_iff₀ (by positivity)]
  have h := factorial_three_mul_le n
  have h' : ((Nat.factorial (3 * n + 1) : ℕ) : ℝ) ≤ (((3 * n + 1) * (2 ^ (5 * n) * Nat.factorial n ^ 3) : ℕ) : ℝ) := by
    exact_mod_cast (by rw [Nat.factorial_succ]; exact Nat.mul_le_mul_left _ h)
  push_cast at h'
  calc (2 : ℝ) ^ (6 * n) * (Nat.factorial (3 * n + 1) : ℝ)
      ≤ 2 ^ (6 * n) * ((3 * n + 1) * (2 ^ (5 * n) * (Nat.factorial n : ℝ) ^ 3)) := by gcongr
    _ = (3 * n + 1 : ℝ) * 2 ^ (11 * n) * (Nat.factorial n : ℝ) ^ 3 := by
        rw [show 11 * n = 6 * n + 5 * n by ring, pow_add]; ring

/-- The explicit bound `|r_n| ≤ (3n+1) 4^{21} 2^{-31 n}` for even `n`. -/
theorem abs_rForm_le_explicit {n : ℕ} (hn : Even n) :
    |rForm 21 n| ≤ (3 * n + 1 : ℝ) * 4 ^ 21 / 2 ^ (31 * n) := by
  refine (abs_rForm_le_Cn_mul_Mseq (by norm_num) hn).trans ?_
  have hB := Bseq_zero_le n
  have hB0 := (strictCM_Bseq n).pos 0
  have hC := Cn_le n
  have hC0 := (Cn_pos n).le
  rw [Mseq_apply]
  calc Cn n * Bseq n 0 ^ 21 ≤ ((3 * n + 1 : ℝ) * 2 ^ (11 * n)) * (4 / 4 ^ n) ^ 21 := by gcongr
    _ = (3 * n + 1 : ℝ) * 4 ^ 21 / 2 ^ (31 * n) := by
        rw [div_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        rw [show 2 * (n * 21) = 11 * n + 31 * n by ring, pow_add]
        field_simp

/-- **N4 (real-place bound).**  At `s = 21`, `|r_n| ≤ e^{-21.3 n}` for all large even `n`. -/
theorem abs_rForm_le_exp :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → |rForm 21 n| ≤ Real.exp (-21.3 * n) := by
  -- the geometric ratio `r = e^{21.3} / 2^{31} < 1`
  set r : ℝ := Real.exp 21.3 / 2 ^ 31 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]
    have h2 : (2 : ℝ) ^ 31 = Real.exp (31 * Real.log 2) := by
      rw [show (31 : ℝ) = ((31 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2, Real.exp_lt_exp]
    have := Real.log_two_gt_d9
    linarith
  have hT := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 (abs_of_pos hr0 ▸ hr1)
  have hev := hT.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 4 ^ 22 by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N 1, fun n hn hev' => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnr := hN n (le_trans (le_max_left _ _) hn)
  simp only [pow_one] at hnr
  refine (abs_rForm_le_explicit hev').trans ?_
  -- `2^{-31n} = r^n · e^{-21.3 n}`
  have hpow : (2 : ℝ) ^ (31 * n) = Real.exp (21.3 * n) / r ^ n := by
    rw [hr, div_pow, ← Real.exp_nat_mul, pow_mul, mul_comm (n : ℝ) 21.3]
    field_simp
  rw [hpow, div_div_eq_mul_div, div_le_iff₀ (by positivity), ← Real.exp_add]
  rw [show (-21.3 * n + 21.3 * n : ℝ) = 0 by ring, Real.exp_zero]
  -- `(3n+1) 4^21 r^n ≤ 4n · 4^21 r^n ≤ 1`
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrn : 0 ≤ r ^ n := by positivity
  have h3 : (3 * n + 1 : ℝ) ≤ 4 * n := by linarith
  calc (3 * n + 1 : ℝ) * 4 ^ 21 * r ^ n ≤ 4 * n * 4 ^ 21 * r ^ n := by gcongr
    _ = 4 ^ 22 * (n * r ^ n) := by ring
    _ ≤ 4 ^ 22 * (1 / 4 ^ 22) := by gcongr
    _ = 1 := by norm_num

end LeanFormalizations.DirichletBeta
