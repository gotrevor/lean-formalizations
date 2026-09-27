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

/-- `2ᵏ → ∞`. -/
theorem tendsto_two_pow_atTop : Tendsto (fun j : ℕ ↦ 2 ^ j) atTop atTop :=
  tendsto_atTop_mono (fun j ↦ (Nat.lt_two_pow_self (n := j)).le) tendsto_id

/-- **Steps 2–4 of Dubickas's §5 for `d = 2`, `a₀ = 1`.**  If the growth constant `α` of the
exact recursion `y_{n+1} = y_n² − c` is algebraic (and `2 y_n ∈ ℤ`), then `c ∈ {0, 2}` —
Dubickas's conditions (17) and (18). -/
theorem c_eq_zero_or_two (hD : Dubickas2022) (hG : Dubickas2022PisotGap)
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    c = 0 ∨ c = 2 := by
  classical
  obtain ⟨m, hβ⟩ := exists_pisot_pow hD halg hα hC hyint hbnd
  set β : ℝ := α ^ 2 ^ m with hβdef
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  have halgβ : IsIntegral ℚ β := hβ.2.1.tower_top
  have hconv : ∀ j : ℕ, α ^ 2 ^ (m + j) = β ^ 2 ^ j := by
    intro j; rw [hβdef, ← pow_mul, pow_add]
  set ρ : ℝ := conjMax β with hρdef
  have hρ0 : 0 ≤ ρ := conjMax_nonneg β
  have hρ1 : ρ < 1 := conjMax_lt_one hβ
  set L : ℕ := Multiset.card (otherConj β) with hLdef
  have hSbnd : ∀ N : ℕ, ‖conjPowSum β N‖ ≤ (L : ℝ) * ρ ^ N := fun N ↦ norm_conjPowSum_le β N
  have hBnorm : ∀ N : ℕ, ‖(β : ℂ) ^ N‖ = β ^ N := by
    intro N; rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hpowB : ∀ j : ℕ, (β : ℂ) ^ 2 ^ (j + 1) = ((β : ℂ) ^ 2 ^ j) ^ 2 := by
    intro j; rw [← pow_mul, pow_succ]
  -- **Step 2**: `y_{m+j}` *is* the trace of `β^(2^j)`, for all large `j`.
  have htrace : ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ((y (m + j) : ℝ) : ℂ) = (β : ℂ) ^ 2 ^ j + conjPowSum β (2 ^ j) := by
    have hto1 : Tendsto (fun j : ℕ ↦ 2 * C / β ^ 2 ^ j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_two_pow_atTop hβ1)
    have hto2 : Tendsto (fun j : ℕ ↦ 2 * (L : ℝ) * ρ ^ 2 ^ j) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp tendsto_two_pow_atTop
      simpa using (this.const_mul (2 * (L : ℝ)))
    have hto12 : Tendsto (fun j : ℕ ↦ 2 * C / β ^ 2 ^ j + 2 * (L : ℝ) * ρ ^ 2 ^ j)
        atTop (𝓝 0) := by simpa using hto1.add hto2
    have hsmall : ∀ᶠ j : ℕ in atTop, 2 * C / β ^ 2 ^ j + 2 * (L : ℝ) * ρ ^ 2 ^ j < 1 :=
      hto12.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.1
      (hsmall.and (eventually_ge_atTop (α := ℕ) n₀))
    refine ⟨j₀ + m + n₀, fun j hj ↦ ?_⟩
    obtain ⟨hlt, -⟩ := hj₀ j (by omega)
    obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ (2 ^ j)
    obtain ⟨k, hk⟩ := hyint (m + j)
    -- both `k` and `2t` are integers within distance `< 1`
    have hb : |y (m + j) - β ^ 2 ^ j| ≤ C / β ^ 2 ^ j := by
      have := hbnd (m + j) (by omega)
      rwa [hconv j] at this
    have hdiff : |(t : ℝ) - β ^ 2 ^ j| ≤ (L : ℝ) * ρ ^ 2 ^ j := by
      have hcast : (((t : ℝ) - β ^ 2 ^ j : ℝ) : ℂ) = conjPowSum β (2 ^ j) := by
        push_cast; rw [← ht]; ring
      have : ‖(((t : ℝ) - β ^ 2 ^ j : ℝ) : ℂ)‖ ≤ (L : ℝ) * ρ ^ 2 ^ j := by
        rw [hcast]; exact hSbnd _
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have hkeq : k = 2 * t := by
      have hlt1 : |(k : ℝ) - ((2 * t : ℤ) : ℝ)| < 1 := by
        have : (k : ℝ) - ((2 * t : ℤ) : ℝ) = 2 * (y (m + j) - β ^ 2 ^ j) - 2 * ((t:ℝ) - β ^ 2 ^ j) :=
          by rw [← hk]; push_cast; ring
        rw [this]
        calc |2 * (y (m + j) - β ^ 2 ^ j) - 2 * ((t:ℝ) - β ^ 2 ^ j)|
            ≤ |2 * (y (m + j) - β ^ 2 ^ j)| + |2 * ((t:ℝ) - β ^ 2 ^ j)| := abs_sub _ _
          _ = 2 * |y (m + j) - β ^ 2 ^ j| + 2 * |(t:ℝ) - β ^ 2 ^ j| := by
              rw [abs_mul, abs_mul]; norm_num
          _ ≤ 2 * (C / β ^ 2 ^ j) + 2 * ((L : ℝ) * ρ ^ 2 ^ j) := by
              gcongr
          _ < 1 := by
              have : 2 * (C / β ^ 2 ^ j) = 2 * C / β ^ 2 ^ j := by ring
              linarith [hlt, this]
      have : |(k : ℝ) - ((2 * t : ℤ) : ℝ)| = |((k - 2 * t : ℤ) : ℝ)| := by push_cast; ring_nf
      rw [this] at hlt1
      have := Int.abs_lt_one_iff.1 (by exact_mod_cast hlt1)
      omega
    have : y (m + j) = (t : ℝ) := by
      have : 2 * y (m + j) = 2 * (t : ℝ) := by rw [hk, hkeq]; push_cast; ring
      linarith
    rw [this, ht]
    push_cast
    ring
  obtain ⟨j₀, htr⟩ := htrace
  -- **Step 3**: the squaring identity that replaces Dubickas's Lemmas 7 and 10.
  have hident : ∀ j ≥ j₀, (c : ℂ) = 2 * (β : ℂ) ^ 2 ^ j * conjPowSum β (2 ^ j)
      + conjPowSum β (2 ^ j) ^ 2 - conjPowSum β (2 ^ (j + 1)) := by
    intro j hj
    have h1 := htr j hj
    have h2 := htr (j + 1) (by omega)
    have h3 : ((y (m + (j + 1)) : ℝ) : ℂ) = ((y (m + j) : ℝ) : ℂ) ^ 2 - (c : ℂ) := by
      rw [show m + (j + 1) = (m + j) + 1 from by omega, hrec]
      push_cast
      ring
    rw [h1, h2, hpowB j] at h3
    linear_combination h3
  -- **Step 4**: the decay bound, hence `deg β ≤ 2`.
  set K : ℝ := |c| + (L : ℝ) ^ 2 + (L : ℝ) + 1 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hdecay : ∀ j ≥ j₀, ‖conjPowSum β (2 ^ j)‖ ≤ K * (β ^ (-(1 * ((2 ^ j : ℕ) : ℝ))) : ℝ) := by
    intro j hj
    have hid := hident j hj
    set S : ℂ := conjPowSum β (2 ^ j) with hS
    set S' : ℂ := conjPowSum β (2 ^ (j + 1)) with hS'
    have hρ1' : ρ ^ 2 ^ j ≤ 1 := pow_le_one₀ hρ0 hρ1.le
    have hρ2' : ρ ^ 2 ^ (j + 1) ≤ 1 := pow_le_one₀ hρ0 hρ1.le
    have hSb : ‖S‖ ≤ (L : ℝ) * ρ ^ 2 ^ j := hSbnd _
    have hS'b : ‖S'‖ ≤ (L : ℝ) * ρ ^ 2 ^ (j + 1) := hSbnd _
    have hLn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    -- `‖2 βᴺ S‖ = 2 βᴺ ‖S‖ ≤ |c| + L² + L`
    have hlhs : ‖2 * (β : ℂ) ^ 2 ^ j * S‖ = 2 * β ^ 2 ^ j * ‖S‖ := by
      rw [norm_mul, norm_mul, hBnorm]
      norm_num
    have hrhs : ‖2 * (β : ℂ) ^ 2 ^ j * S‖ ≤ |c| + (L : ℝ) ^ 2 + (L : ℝ) := by
      have heq : 2 * (β : ℂ) ^ 2 ^ j * S = (c : ℂ) - S ^ 2 + S' := by
        rw [hid]; ring
      rw [heq]
      calc ‖(c : ℂ) - S ^ 2 + S'‖ ≤ ‖(c : ℂ) - S ^ 2‖ + ‖S'‖ := norm_add_le _ _
        _ ≤ (‖(c : ℂ)‖ + ‖S ^ 2‖) + ‖S'‖ := by gcongr; exact norm_sub_le _ _
        _ = |c| + ‖S‖ ^ 2 + ‖S'‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_pow]
        _ ≤ |c| + ((L : ℝ) * ρ ^ 2 ^ j) ^ 2 + (L : ℝ) * ρ ^ 2 ^ (j + 1) := by
            gcongr
        _ ≤ |c| + (L : ℝ) ^ 2 + (L : ℝ) := by
            have hr0 : (0 : ℝ) ≤ ρ ^ 2 ^ j := pow_nonneg hρ0 _
            have hr0' : (0 : ℝ) ≤ ρ ^ 2 ^ (j + 1) := pow_nonneg hρ0 _
            have h1 : ((L : ℝ) * ρ ^ 2 ^ j) ^ 2 ≤ (L : ℝ) ^ 2 := by
              rw [mul_pow]
              have hsq : (ρ ^ 2 ^ j) ^ 2 ≤ 1 := by nlinarith
              nlinarith [sq_nonneg ((L : ℝ)), hsq]
            have h2 : (L : ℝ) * ρ ^ 2 ^ (j + 1) ≤ (L : ℝ) := by nlinarith [hρ2']
            linarith
    -- convert to the rpow form
    have hpow0 : (0 : ℝ) < β ^ 2 ^ j := by positivity
    have hrp : (β ^ (-(1 * ((2 ^ j : ℕ) : ℝ))) : ℝ) = (β ^ 2 ^ j)⁻¹ := by
      rw [one_mul, Real.rpow_neg hβ0.le, Real.rpow_natCast]
    rw [hrp]
    rw [← div_eq_mul_inv, le_div_iff₀ hpow0]
    nlinarith [hlhs, hrhs, hpow0, norm_nonneg S, hKdef]
  have hL1 : L ≤ 1 := by
    rcases le_or_gt 2 (minpoly ℚ β).natDegree with hdeg | hdeg
    · have hfreq : ∃ᶠ n : ℕ in atTop,
          ‖conjPowSum β n‖ ≤ K * (β ^ (-(1 * (n : ℝ))) : ℝ) := by
        rw [frequently_atTop]
        intro a
        refine ⟨2 ^ (max j₀ a), le_trans (le_max_right j₀ a) (Nat.lt_two_pow_self).le, ?_⟩
        have := hdecay (max j₀ a) (le_max_left _ _)
        simpa using this
      have hb := pisot_degree_bound hG hβ hdeg (μ := 1) one_pos hK0 hfreq
      rw [mul_one] at hb
      exact_mod_cast hb
    · have hcard := card_otherConj_add_one halgβ
      omega
  -- **Step 4 (cases)**
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · -- degree 1: the conjugate sum is empty, so `c = 0`
    left
    have hempty : otherConj β = 0 :=
      Multiset.card_eq_zero.1 (show (otherConj β).card = 0 from by rw [← hLdef]; exact hL0)
    have hz : ∀ N : ℕ, conjPowSum β N = 0 := by
      intro N; rw [conjPowSum, hempty]; simp
    have := hident j₀ le_rfl
    rw [hz, hz] at this
    simpa using this
  · -- degree 2: `c/2` is both `w^N` and `w^(2N)`, so `c/2 = (c/2)²`
    have hLc : L = 1 := le_antisymm hL1 hLpos
    obtain ⟨γ, hγ⟩ := Multiset.card_eq_one.1
      (show (otherConj β).card = 1 from by rw [← hLdef]; exact hLc)
    have hz : ∀ N : ℕ, conjPowSum β N = γ ^ N := by
      intro N; rw [conjPowSum, hγ]; simp
    have hkey : ∀ j ≥ j₀, (c : ℂ) = 2 * ((β : ℂ) * γ) ^ 2 ^ j := by
      intro j hj
      have h := hident j hj
      rw [hz, hz, show (2:ℕ) ^ (j + 1) = 2 ^ j * 2 from by rw [pow_succ], pow_mul] at h
      rw [mul_pow]
      linear_combination h
    have e1 := hkey j₀ le_rfl
    have e2 := hkey (j₀ + 1) (by omega)
    rw [show (2:ℕ) ^ (j₀ + 1) = 2 ^ j₀ * 2 from by rw [pow_succ], pow_mul] at e2
    have hW : ((β : ℂ) * γ) ^ 2 ^ j₀ = (c : ℂ) / 2 := by linear_combination -e1 / 2
    rw [hW] at e2
    have hcc : c = c ^ 2 / 2 := by
      have hcc2 : (c : ℂ) = (c : ℂ) ^ 2 / 2 := by linear_combination e2
      exact_mod_cast hcc2
    have : c * (c - 2) = 0 := by nlinarith [hcc]
    rcases mul_eq_zero.1 this with h | h
    · left; exact h
    · right; linarith

end LeanFormalizations.Transcendence.Dubickas
