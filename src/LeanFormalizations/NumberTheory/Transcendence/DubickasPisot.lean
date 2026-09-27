/-
# Dubickas (2022), Lemmas 9 and §5 for monic quadratics

`DubickasGrowth.lean` produced the growth constant `α > 1` with `|y_n − α^(2ⁿ)| ≤ C α^(−2ⁿ)` for
the *exact* recursion `y_{n+1} = y_n² − c`.  This file closes the arithmetic half, in the
`d = 2`, `a₀ = 1` case:

* **Lemma 9 step 1.**  `2 y_n ∈ ℤ` and `|2α^(2ⁿ) − 2y_n| ≤ 2C α^(−2ⁿ)` refute the
  "`‖q α^(s_k)‖ > e^(−ε s_k)`" alternative of `Dubickas2022` at `q = 2`, `s_k = 2^k`,
  `ε = (log α)/2`.  So `β := α^(2^m)` is a **Pisot number** for some `m`.
* **Step 2.**  `β^N + Σ_{j≥2} β_jᴺ` is a rational integer (`pisot_conjPowSum_add_mem_int`) and
  differs from `y_{m+j}` by `o(1)`; both doubled are integers, so `y_{m+j} = trace(β^(2^j))`
  exactly, for all large `j`.
* **Step 3 (the identity that replaces Dubickas's Lemmas 7 and 10).**  Squaring the trace,
  `T_N² = T_{2N} + 2β^N S_N + (S_N² − S_{2N})` with `S_N = Σ_{j≥2} β_jᴺ`, and `T_{2N} = T_N² − c`
  gives `c = 2 β^N S_N + S_N² − S_{2N}` for `N = 2^j`, `j` large.  The last two terms are
  `O(|β₂|^(2N))`, hence bounded, so `‖S_N‖ ≤ K β^(−N)`: exactly the decay hypothesis of
  `pisot_degree_bound` at `μ = 1`, which forces `deg β ≤ 2`.
* **Step 4.**  `deg β = 1` gives `S_N = 0`, so `c = 0`.  `deg β = 2` gives `S_N = γᴺ`, so
  `c = 2(βγ)^N` for `N` and `2N` alike, whence `c/2 = (c/2)²` and `c ∈ {0, 2}`.

In Dubickas's coordinates `c = (a₁² − 2a₁ − 4a₂)/4`, so `c ∈ {0, 2}` is precisely his (17)/(18).
-/
import LeanFormalizations.NumberTheory.Mills.SaitoPisot
import LeanFormalizations.NumberTheory.Transcendence.DubickasGrowth

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- **Dubickas (2022), Lemma 9 for `d = 2`, `a₀ = 1`**: an algebraic growth constant `α` has a
power `β = α^(2^m)` that is a Pisot number.  The `q = 2` of the statement is what makes
`q y_n = 2 x_n + a₁` an integer. -/
theorem exists_pisot_pow (hD : Dubickas2022) {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α)
    {C : ℝ} (hC : 0 < C) {y : ℕ → ℝ} {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hlogα : 0 < Real.log α := Real.log_pos hα
  have hs : StrictMono (fun n : ℕ ↦ 2 ^ n) := fun a b h ↦ Nat.pow_lt_pow_right (by norm_num) h
  rcases hD α halg hα 2 (by norm_num) (fun n ↦ 2 ^ n) hs (by norm_num) with hpisot | halt
  · obtain ⟨m, hm⟩ := hpisot
    exact ⟨m, by simpa using hm⟩
  -- refute the second alternative
  obtain ⟨k₀, hk₀⟩ := halt (Real.log α / 2) (by positivity)
  -- choose `k` large enough that `2C ≤ exp(2ᵏ (log α)/2)`
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1
    ((tendsto_pow_two_pow_atTop (show (1:ℝ) < Real.exp (Real.log α / 2) from by
      rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.2 (by positivity))).eventually_ge_atTop (2 * C))
  set k : ℕ := max (max k₀ n₀) k₁ with hkdef
  have hkk₀ : k₀ ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hkn₀ : n₀ ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hkk₁ : k₁ ≤ k := le_max_right _ _
  have hlarge : 2 * C ≤ Real.exp (Real.log α / 2) ^ 2 ^ k := hk₁ k hkk₁
  have hp0 : (0 : ℝ) < α ^ 2 ^ k := by positivity
  -- the bound from the recursion side
  obtain ⟨j, hj⟩ := hyint k
  have hnear : |2 * α ^ 2 ^ k - (j : ℝ)| ≤ 2 * C / α ^ 2 ^ k := by
    have h := hbnd k hkn₀
    rw [show 2 * α ^ 2 ^ k - (j : ℝ) = -(2 * (y k - α ^ 2 ^ k)) from by rw [← hj]; ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show 2 * C / α ^ 2 ^ k = 2 * (C / α ^ 2 ^ k) from by ring]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hround : |2 * α ^ 2 ^ k - (round (2 * α ^ 2 ^ k) : ℝ)| ≤ 2 * C / α ^ 2 ^ k :=
    le_trans (round_le _ j) hnear
  -- the bound from the Dubickas alternative
  have hcontra := hk₀ k hkk₀
  push_cast at hcontra
  -- `exp(−(log α / 2) · 2ᵏ) = (exp (log α / 2))^(−2ᵏ)`, and `2C · α^(−2ᵏ) ≤` that
  have hkey : 2 * C / α ^ 2 ^ k ≤ Real.exp (-(Real.log α / 2 * 2 ^ k)) := by
    have he : Real.exp (-(Real.log α / 2 * 2 ^ k)) = (Real.exp (Real.log α / 2) ^ 2 ^ k)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    have hE0 : (0 : ℝ) < Real.exp (Real.log α / 2) ^ 2 ^ k := by positivity
    rw [he, div_le_iff₀ hp0, inv_mul_eq_div, le_div_iff₀ hE0]
    have h1 : Real.exp (Real.log α / 2) ^ 2 = α := by
      rw [← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (Real.log α / 2) = Real.log α from by push_cast; ring,
        Real.exp_log hα0]
    have hαE : α ^ 2 ^ k = (Real.exp (Real.log α / 2) ^ 2 ^ k) ^ 2 := by
      calc α ^ 2 ^ k = (Real.exp (Real.log α / 2) ^ 2) ^ 2 ^ k := by rw [h1]
        _ = (Real.exp (Real.log α / 2) ^ 2 ^ k) ^ 2 := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hαE]
    nlinarith [hlarge, hE0, hC]
  exact absurd hround (not_le.2 (lt_of_le_of_lt hkey hcontra))

end LeanFormalizations.Transcendence.Dubickas
