/-
# Dubickas (2022), formula (6) for monic quadratics

For an integer sequence `x_{n+1} = x_n² + a₁ x_n + a₂` tending to `∞`, the substitution
`y_n = x_n + a₁/2` of Dubickas's (4) turns the recursion into the **exact** one-parameter form

`y_{n+1} = y_n² - c`,  `c = (a₁² − 2a₁ − 4a₂)/4`,

with no error term at all (the `O(y_n^(d−2))` of (5) is a constant when `d = 2`).  This file
proves Dubickas's (6) in that setting: the growth constant `α = lim y_n^(2^(−n))` exists, is
`> 1`, and `y_n = α^(2ⁿ) + O(α^(−2ⁿ))`.

The proof is Dubickas's own (§1): `log y_{n+1} − 2 log y_n = log(1 − c/y_n²)` is `O(y_n^(−2))`,
so `a_n := 2^(−n) log y_n` is Cauchy with a tail bounded by `2|c| 2^(−n) y_n^(−2)`; exponentiating
the tail bound gives the `O(α^(−2ⁿ))` rate.
-/
import Mathlib

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology

/-- `|log u| ≤ 2 |u − 1|` for `u ≥ 1/2`. -/
theorem abs_log_le_two_mul {u : ℝ} (hu : (1 : ℝ) / 2 ≤ u) : |Real.log u| ≤ 2 * |u - 1| := by
  have hu0 : (0 : ℝ) < u := by linarith
  rcases le_or_gt 1 u with h1 | h1
  · have hlog0 : 0 ≤ Real.log u := Real.log_nonneg h1
    have := Real.log_le_sub_one_of_pos hu0
    rw [abs_of_nonneg hlog0, abs_of_nonneg (by linarith : (0:ℝ) ≤ u - 1)]
    linarith
  · have hlogneg : Real.log u ≤ 0 := Real.log_nonpos hu0.le h1.le
    have hinv : Real.log u⁻¹ ≤ u⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hinv
    have hu1 : u⁻¹ - 1 = (1 - u) / u := by field_simp
    have hub : (1 - u) / u ≤ 2 * (1 - u) := by
      rw [div_le_iff₀ hu0]
      nlinarith
    rw [abs_of_nonpos hlogneg, abs_of_nonpos (by linarith : u - 1 ≤ 0)]
    linarith [hinv, hu1.symm ▸ hub]

/-- **Dubickas (2022), formula (6) for `d = 2`, `a₀ = 1`.**  A real sequence obeying
`y_{n+1} = y_n² − c` and tending to `∞` has a growth constant `α > 1` with
`|y_n − α^(2ⁿ)| ≤ C α^(−2ⁿ)` from some point on. -/
theorem exists_growth_const {c : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (htop : Tendsto y atTop atTop) :
    ∃ α : ℝ, 1 < α ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, (∀ n ≥ n₀, 2 ≤ y n) ∧
      ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n := by
  classical
  have hc0 : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hcle : c ≤ |c| := le_abs_self c
  set M : ℝ := 2 + |c| with hMdef
  have hM2 : (2 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have h2cM : 2 * |c| ≤ M ^ 2 := by rw [hMdef]; nlinarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (htop.eventually_ge_atTop M)
  have hyM : ∀ n, n₀ ≤ n → M ≤ y n := hn₀
  have hy2 : ∀ n, n₀ ≤ n → (2 : ℝ) ≤ y n := fun n hn => le_trans hM2 (hyM n hn)
  have hy0 : ∀ n, n₀ ≤ n → (0 : ℝ) < y n := fun n hn => by linarith [hy2 n hn]
  -- the sequence is increasing past `n₀`
  have hstep : ∀ n, n₀ ≤ n → y n ≤ y (n + 1) := by
    intro n hn
    have h := hyM n hn
    rw [hrec n, hMdef] at *
    nlinarith [sq_nonneg (y n - 2 - |c|)]
  have hmono : ∀ m n, n₀ ≤ m → m ≤ n → y m ≤ y n := by
    intro m n hm hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (hstep n (hm.trans hn))
  -- the logarithmic step bound
  have hlogstep : ∀ n, n₀ ≤ n →
      |Real.log (y (n + 1)) - 2 * Real.log (y n)| ≤ 2 * |c| / y n ^ 2 := by
    intro n hn
    have hyn := hy0 n hn
    have hyn2 : (0 : ℝ) < y n ^ 2 := by positivity
    have hMy : M ≤ y n := hyM n hn
    have hyle : M ^ 2 ≤ y n ^ 2 := by nlinarith
    set u : ℝ := y (n + 1) / y n ^ 2 with hu
    have hun : y (n + 1) = u * y n ^ 2 := by rw [hu]; field_simp
    have hu1 : u - 1 = -c / y n ^ 2 := by rw [hu, hrec n]; field_simp; ring
    have habs : |u - 1| = |c| / y n ^ 2 := by
      rw [hu1, abs_div, abs_neg, abs_of_pos hyn2]
    have hbnd : |u - 1| ≤ 1 / 2 := by
      rw [habs, div_le_iff₀ hyn2]; nlinarith
    have hu12 : (1 : ℝ) / 2 ≤ u := by have := abs_le.1 hbnd; linarith [this.1]
    have hlog : Real.log (y (n + 1)) = Real.log u + 2 * Real.log (y n) := by
      rw [hun, Real.log_mul (by linarith) (by positivity), Real.log_pow]
      push_cast; ring
    rw [hlog]
    simp only [add_sub_cancel_right]
    calc |Real.log u| ≤ 2 * |u - 1| := abs_log_le_two_mul hu12
      _ = 2 * |c| / y n ^ 2 := by rw [habs]; ring
  -- the Cauchy sequence `aₙ = 2⁻ⁿ log yₙ`, shifted to start at `n₀`
  set f : ℕ → ℝ := fun k => Real.log (y (n₀ + k)) / 2 ^ (n₀ + k) with hf
  set d : ℕ → ℝ := fun k => 2 * |c| / (y (n₀ + k) ^ 2 * 2 ^ (n₀ + k + 1)) with hd
  have hypos : ∀ k : ℕ, (0 : ℝ) < y (n₀ + k) := fun k => hy0 _ (Nat.le_add_right _ _)
  have hdnn : ∀ k, 0 ≤ d k := by
    intro k; rw [hd]; have := hypos k; positivity
  have hfd : ∀ k, dist (f k) (f (k + 1)) ≤ d k := by
    intro k
    have hyk := hypos k
    have hpow : (0 : ℝ) < 2 ^ (n₀ + k) := by positivity
    have hstepk := hlogstep (n₀ + k) (Nat.le_add_right _ _)
    rw [Real.dist_eq, hf, hd]
    have he : Real.log (y (n₀ + k)) / 2 ^ (n₀ + k) - Real.log (y (n₀ + (k + 1))) / 2 ^ (n₀ + (k+1))
        = -(Real.log (y (n₀ + k + 1)) - 2 * Real.log (y (n₀ + k))) / 2 ^ (n₀ + k + 1) := by
      rw [show n₀ + (k + 1) = n₀ + k + 1 from rfl, pow_succ]
      field_simp
      ring
    rw [he, abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 ^ (n₀ + k + 1))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (0 : ℝ) < 2 ^ (n₀ + k + 1) := by positivity
    have hy2k : (0 : ℝ) < y (n₀ + k) ^ 2 := by positivity
    calc |Real.log (y (n₀ + k + 1)) - 2 * Real.log (y (n₀ + k))| * (y (n₀ + k) ^ 2 * 2 ^ (n₀+k+1))
        ≤ (2 * |c| / y (n₀ + k) ^ 2) * (y (n₀ + k) ^ 2 * 2 ^ (n₀+k+1)) := by
          exact mul_le_mul_of_nonneg_right hstepk (by positivity)
      _ = 2 * |c| * 2 ^ (n₀ + k + 1) := by field_simp
  -- `d` is summable, dominated by a geometric series
  have hdle : ∀ k, d k ≤ (2 * |c| / (M ^ 2 * 2 ^ (n₀ + 1))) * (1 / 2) ^ k := by
    intro k
    have hyk := hypos k
    have hMy : M ≤ y (n₀ + k) := hyM _ (Nat.le_add_right _ _)
    have hyle : M ^ 2 ≤ y (n₀ + k) ^ 2 := by nlinarith
    rw [hd]
    rw [div_le_iff₀ (by positivity)]
    have hrw : (2 * |c| / (M ^ 2 * 2 ^ (n₀ + 1)) * (1 / 2) ^ k) * (y (n₀+k) ^ 2 * 2 ^ (n₀+k+1))
        = 2 * |c| * (y (n₀+k) ^ 2 / M ^ 2) := by
      rw [show ((1:ℝ)/2) ^ k = ((2:ℝ) ^ k)⁻¹ from by rw [one_div, inv_pow],
        show n₀ + k + 1 = (n₀ + 1) + k from by omega, pow_add]
      field_simp
      ring
    rw [hrw]
    have h1 : (1 : ℝ) ≤ y (n₀+k) ^ 2 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hdsum : Summable d := by
    refine Summable.of_nonneg_of_le hdnn hdle ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hfd hdsum)
  -- the tail bound
  have htail : ∀ k : ℕ, |f k - A| ≤ 2 * |c| / (y (n₀ + k) ^ 2 * 2 ^ (n₀ + k)) := by
    intro k
    have hbase := dist_le_tsum_of_dist_le_of_tendsto d hfd hdsum hA k
    rw [Real.dist_eq] at hbase
    refine hbase.trans ?_
    have hyk := hypos k
    have hdom : ∀ m, d (k + m) ≤ (2 * |c| / (y (n₀ + k) ^ 2 * 2 ^ (n₀ + k + 1))) * (1/2) ^ m := by
      intro m
      have hMy : y (n₀ + k) ≤ y (n₀ + k + m) := hmono _ _ (Nat.le_add_right _ _) (by omega)
      have hykm : (0 : ℝ) < y (n₀ + k + m) := hy0 _ (by omega)
      have hyle : y (n₀ + k) ^ 2 ≤ y (n₀ + k + m) ^ 2 := by nlinarith
      simp only [hd, ← Nat.add_assoc]
      rw [div_le_iff₀ (by positivity)]
      have hrw : (2 * |c| / (y (n₀+k) ^ 2 * 2 ^ (n₀ + k + 1)) * (1/2) ^ m)
            * (y (n₀+k+m) ^ 2 * 2 ^ (n₀ + k + m + 1))
          = 2 * |c| * (y (n₀+k+m) ^ 2 / y (n₀+k) ^ 2) := by
        rw [show ((1:ℝ)/2) ^ m = ((2:ℝ) ^ m)⁻¹ from by rw [one_div, inv_pow],
          show n₀ + k + m + 1 = (n₀ + k + 1) + m from by omega, pow_add]
        field_simp
        ring
      rw [hrw]
      have h1 : (1 : ℝ) ≤ y (n₀+k+m) ^ 2 / y (n₀+k) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    have hsum2 : Summable fun m => d (k + m) := hdsum.comp_injective (add_right_injective k)
    have hgeo : Summable fun m : ℕ => (2 * |c| / (y (n₀ + k) ^ 2 * 2 ^ (n₀ + k + 1))) * (1/2) ^ m :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine (hsum2.tsum_le_tsum hdom hgeo).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    refine le_of_eq ?_
    rw [pow_succ (2:ℝ) (n₀ + k)]
    field_simp
    ring
  -- rewrite the tail bound at the index `n = n₀ + k`
  have hkey : ∀ n, n₀ ≤ n → |Real.log (y n) - 2 ^ n * A| ≤ 2 * |c| / y n ^ 2 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h := htail k
    rw [hf] at h
    have hpow : (0 : ℝ) < 2 ^ (n₀ + k) := by positivity
    have hyk := hypos k
    rw [show Real.log (y (n₀ + k)) / 2 ^ (n₀ + k) - A
        = (Real.log (y (n₀ + k)) - 2 ^ (n₀ + k) * A) / 2 ^ (n₀ + k) from by field_simp,
      abs_div, abs_of_pos hpow, div_le_div_iff₀ hpow (by positivity)] at h
    rw [le_div_iff₀ (by positivity : (0:ℝ) < y (n₀ + k) ^ 2)]
    nlinarith [h, hpow]
  -- `A > 0`
  have hApos : 0 < A := by
    obtain ⟨n, hn, hyn⟩ : ∃ n, n₀ ≤ n ∧ Real.exp (2 * |c| / M ^ 2 + 1) ≤ y n := by
      obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (htop.eventually_ge_atTop
        (Real.exp (2 * |c| / M ^ 2 + 1)))
      exact ⟨max n₀ n₁, le_max_left _ _, hn₁ _ (le_max_right _ _)⟩
    have hy0n := hy0 n hn
    have hlogn : 2 * |c| / M ^ 2 + 1 ≤ Real.log (y n) := by
      rw [← Real.log_exp (2 * |c| / M ^ 2 + 1)]
      exact Real.log_le_log (Real.exp_pos _) hyn
    have hMy : M ≤ y n := hyM n hn
    have hyle : M ^ 2 ≤ y n ^ 2 := by nlinarith
    have hdle2 : 2 * |c| / y n ^ 2 ≤ 2 * |c| / M ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hyle
    have h := abs_le.1 (hkey n hn)
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [h.2, hpow]
  refine ⟨Real.exp A, by simpa using Real.exp_lt_exp.2 hApos, 36 * |c| + 1, by positivity, n₀,
    hy2, ?_⟩
  intro n hn
  have hy0n := hy0 n hn
  have hMy : M ≤ y n := hyM n hn
  have hyle : M ^ 2 ≤ y n ^ 2 := by nlinarith
  -- `P = α ^ 2ⁿ = exp (2ⁿ A)`
  have hP : Real.exp A ^ 2 ^ n = Real.exp ((2 : ℝ) ^ n * A) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  set P : ℝ := Real.exp A ^ 2 ^ n with hPdef
  have hP0 : 0 < P := by rw [hPdef]; positivity
  set t : ℝ := Real.log (y n) - (2 : ℝ) ^ n * A with ht
  have habst : |t| ≤ 2 * |c| / y n ^ 2 := hkey n hn
  have habst1 : |t| ≤ 1 := by
    refine habst.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hyeq : y n = P * Real.exp t := by
    rw [hP, ht, ← Real.exp_add]
    rw [show (2:ℝ) ^ n * A + (Real.log (y n) - (2:ℝ) ^ n * A) = Real.log (y n) from by ring,
      Real.exp_log hy0n]
  -- `|exp t − 1| ≤ 2|t|`
  have hexp : |Real.exp t - 1| ≤ 2 * |t| := Real.abs_exp_sub_one_le habst1
  have he3 : Real.exp t ≤ 3 := by
    have : t ≤ 1 := (abs_le.1 habst1).2
    calc Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 this
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have heinv : Real.exp (-t) ≤ 3 := by
    have : -t ≤ 1 := by linarith [(abs_le.1 habst1).1]
    calc Real.exp (-t) ≤ Real.exp 1 := Real.exp_le_exp.2 this
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hPy : P ≤ 3 * y n := by
    have : P = y n * Real.exp (-t) := by
      rw [hyeq, Real.exp_neg]; field_simp
    rw [this]
    nlinarith [heinv, hy0n]
  have hyP : (1 : ℝ) / y n ≤ 3 / P := by
    rw [div_le_div_iff₀ hy0n hP0]
    nlinarith [hPy]
  -- assemble
  have hdiff : |y n - P| ≤ 12 * |c| / y n := by
    have : y n - P = P * (Real.exp t - 1) := by rw [hyeq]; ring
    rw [this, abs_mul, abs_of_pos hP0]
    have h1 : P * |Real.exp t - 1| ≤ (3 * y n) * (2 * |t|) := by
      refine mul_le_mul hPy hexp (by positivity) (by positivity)
    refine h1.trans ?_
    rw [le_div_iff₀ hy0n]
    have habst' : |t| * y n ^ 2 ≤ 2 * |c| := by
      rw [← le_div_iff₀ (by positivity : (0:ℝ) < y n ^ 2)]; exact habst
    nlinarith [habst', hy0n, abs_nonneg t]
  refine hdiff.trans ?_
  have h12 : 12 * |c| / y n = (12 * |c|) * (1 / y n) := by ring
  rw [h12]
  calc (12 * |c|) * (1 / y n) ≤ (12 * |c|) * (3 / P) := by
        exact mul_le_mul_of_nonneg_left hyP (by positivity)
    _ = 36 * |c| / P := by ring
    _ ≤ (36 * |c| + 1) / P := by
        rw [div_le_div_iff₀ hP0 hP0]; nlinarith [hP0]

/-- `α ^ 2ⁿ → ∞` for `α > 1`. -/
theorem tendsto_pow_two_pow_atTop {α : ℝ} (hα : 1 < α) :
    Tendsto (fun n : ℕ ↦ α ^ 2 ^ n) atTop atTop := by
  refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_pow_atTop_atTop_of_one_lt hα)
  exact pow_le_pow_right₀ hα.le (Nat.lt_two_pow_self (n := n)).le

/-- **`z_n^(2^(−n)) → α`** whenever `z_n` stays within a bounded distance of `α^(2ⁿ)`.  This is
what turns Dubickas's (6) into the statement that `α` *is* the growth constant, and it applies
equally to `y_n` and to `x_n = y_n − a₁/2`. -/
theorem tendsto_rpow_growth {α C : ℝ} (hα : 1 < α) {z : ℕ → ℝ} {n₀ : ℕ}
    (hz : ∀ n ≥ n₀, |z n - α ^ 2 ^ n| ≤ C) :
    Tendsto (fun n ↦ z n ^ ((1 : ℝ) / 2 ^ n)) atTop (𝓝 α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hz n₀ le_rfl)
  have hpow := tendsto_pow_two_pow_atTop hα
  have hlogα : 0 < Real.log α := Real.log_pos hα
  -- eventually `αˣ/2 ≤ z n ≤ 2 αˣ` with `x = 2ⁿ`
  have hev : ∀ᶠ n : ℕ in atTop, |Real.log (z n) / 2 ^ n - Real.log α| ≤ Real.log 2 / 2 ^ n := by
    filter_upwards [hpow.eventually_ge_atTop (2 * C + 1), eventually_ge_atTop n₀] with n hn hn0
    have hp0 : (0 : ℝ) < α ^ 2 ^ n := by positivity
    have hzb := abs_le.1 (hz n hn0)
    have hzlo : α ^ 2 ^ n / 2 ≤ z n := by linarith [hzb.1]
    have hzhi : z n ≤ 2 * α ^ 2 ^ n := by linarith [hzb.2]
    have hz0 : (0 : ℝ) < z n := by nlinarith
    have hlo : Real.log (α ^ 2 ^ n / 2) ≤ Real.log (z n) := Real.log_le_log (by positivity) hzlo
    have hhi : Real.log (z n) ≤ Real.log (2 * α ^ 2 ^ n) := Real.log_le_log hz0 hzhi
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlo
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhi
    have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    push_cast at hlo hhi
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · rw [← sub_nonneg,
        show Real.log (z n) / 2 ^ n - Real.log α - -(Real.log 2 / 2 ^ n)
          = (Real.log (z n) - 2 ^ n * Real.log α + Real.log 2) / 2 ^ n from by field_simp; ring]
      exact div_nonneg (by linarith) hp.le
    · rw [← sub_nonneg,
        show Real.log 2 / 2 ^ n - (Real.log (z n) / 2 ^ n - Real.log α)
          = (Real.log 2 - Real.log (z n) + 2 ^ n * Real.log α) / 2 ^ n from by field_simp; ring]
      exact div_nonneg (by linarith) hp.le
  have hg : Tendsto (fun n : ℕ ↦ Real.log (z n) / 2 ^ n) atTop (𝓝 (Real.log α)) := by
    rw [← sub_zero (Real.log α), ← zero_add (Real.log α - 0)]
    have h0 : Tendsto (fun n : ℕ ↦ Real.log (z n) / 2 ^ n - Real.log α) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (hev.mono fun n hn ↦ by simpa using hn) ?_
      exact tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
    simpa using h0.add (tendsto_const_nhds (x := Real.log α) (f := atTop (α := ℕ)))
  have hfinal : Tendsto (fun n : ℕ ↦ Real.exp (Real.log (z n) / 2 ^ n)) atTop (𝓝 α) := by
    have := (Real.continuous_exp.tendsto (Real.log α)).comp hg
    rwa [Real.exp_log hα0] at this
  refine hfinal.congr' ?_
  filter_upwards [hpow.eventually_ge_atTop (2 * C + 1), eventually_ge_atTop n₀] with n hn hn0
  have hp0 : (0 : ℝ) < α ^ 2 ^ n := by positivity
  have hzb := abs_le.1 (hz n hn0)
  have hz0 : (0 : ℝ) < z n := by nlinarith [hzb.1]
  rw [Real.rpow_def_of_pos hz0]
  ring_nf

end LeanFormalizations.Transcendence.Dubickas
