/-
# Dubickas (2022), monic quadratics, without Lemma 8 (phase 8 probe)

`c_eq_zero_or_two` (`DubickasPisot.lean`) is the only place Dubickas's Theorem 2 for `d = 2`
consumes `Dubickas2022PisotGap` (his Lemma 8: Smyth / Mignotte / Baker).  It uses it once, in
`hL1`, to turn the decay `‖S_N‖ ≤ K β^(−N)` (`N = 2^j`, `j ≥ j₀`) into `deg β ≤ 2` via
`pisot_degree_bound`.  The goal here is the same conclusion `c ∈ {0, 2}` from `Dubickas2022`
alone, using the exact algebra that the quadratic recursion hands us.  Removing `hG` is one of the
two hypotheses standing between `oeis_constants` and an unconditional statement.

## Leads (Ren, 2026-09-27; unverified, may be wrong)

Notation as in `c_eq_zero_or_two`: `β = α^(2^m)` Pisot, conjugates `β = β₁, β₂, …, β_d`,
`S_N = Σ_{l≥2} β_lᴺ`, and for `N = 2^j`, `j ≥ j₀`, the exact identity
`c = 2 βᴺ S_N + S_N² − S_{2N}` (`hident` there).  Equivalently, with
`E_k(N) := e_k(β₁ᴺ, …, β_dᴺ) ∈ ℤ` (coefficients of the char. poly of `βᴺ`, integers since `β` is
an algebraic integer): `E_1(N) = T_N = y_{m+j}` and **`E_2(N) = c/2`** for all large `j`.

* `E_2(N) ∈ ℤ` gives `c ∈ 2ℤ` for free.
* `E_k(N) = e_k(others) + βᴺ e_{k−1}(others)`, where `e_k(others)` is `O(ρ^(kN))`, `ρ < 1`.
* Graeffe: the char. poly of `β^(2N)` is determined by that of `βᴺ`
  (`e_k(x²) = Σ_{i+i'=2k} (−1)^(i+k) e_i e_{i'}`), so `E_2(2N) = E_2(N)` together with
  `T_N → ∞` constrains `E_3, E_4, …`: e.g. `c/2 = c²/4 − 2 T_N E_3(N) + 2 E_4(N)`.
* Squaring `βᴺ S_N → c/2` gives `β^(2N) e_2(others) → c(c − 2)/8`, so `c ∉ {0, 2}` means the
  pair products `(β β_k β β_l)ᴺ` do NOT die out.  Look for the contradiction there, against
  `|N(β)| ≥ 1` (`pisot_one_le_prod_norm`) and the integrality of the `E_k`.
* Only `c ∈ {0, 2}` is needed, not `deg β ≤ 2`.

If the elementary route is blocked, a written obstruction (why every such argument needs a
Lemma-8-strength lower bound on `|S_N|`) is a valid outcome: record it in
`PROBE-DUBICKAS-NOGAP.md` and leave the `sorry`.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- `‖γ‖` for a conjugate `γ` of `β`, raised to `2^j`, bounds the `2^j`-th power. -/
private theorem norm_pow_le_conjMax_pow {β : ℝ} {z : ℂ} (hz : z ∈ otherConj β) (n : ℕ) :
    ‖z ^ n‖ ≤ conjMax β ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) (norm_le_conjMax hz) n

/-- `β^(2^j) → ∞`. -/
private theorem tendsto_beta_two_pow {β : ℝ} (hβ : 1 < β) :
    Tendsto (fun j : ℕ ↦ β ^ 2 ^ j) atTop atTop := tendsto_pow_two_pow_atTop hβ

/-- **`c_eq_zero_or_two` without Lemma 8**: Dubickas's conditions (17)/(18) from `Dubickas2022`
alone, in the `d = 2`, `a₀ = 1` case. -/
theorem c_eq_zero_or_two_noGap (hD : Dubickas2022)
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    c = 0 ∨ c = 2 := by
  classical
  obtain ⟨β, j₀, hβ, hident⟩ := exists_pisot_trace_ident hD hrec halg hα hC hyint hbnd
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  have halgβ : IsIntegral ℚ β := hβ.2.1.tower_top
  set ρ : ℝ := conjMax β with hρdef
  have hρ0 : 0 ≤ ρ := conjMax_nonneg β
  have hρ1 : ρ < 1 := conjMax_lt_one hβ
  set L : ℕ := Multiset.card (otherConj β) with hLdef
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℂ, ∀ j, S j = conjPowSum β (2 ^ j) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℂ, ∀ j, σ j = (S j ^ 2 - S (j + 1)) / 2 := ⟨_, fun _ ↦ rfl⟩
  -- powers of `β` and of `ρ`
  have hb0 : ∀ j : ℕ, (0 : ℝ) < β ^ 2 ^ j := fun j ↦ by positivity
  have hbsq : ∀ j : ℕ, β ^ 2 ^ (j + 1) = (β ^ 2 ^ j) ^ 2 := by
    intro j; rw [← pow_mul, pow_succ]
  have hBn : ∀ j : ℕ, ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
    intro j; rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hr1 : ∀ j : ℕ, ρ ^ 2 ^ j ≤ 1 := fun j ↦ pow_le_one₀ hρ0 hρ1.le
  -- `‖S j‖ ≤ L ρ^(2^j)`
  have hSb : ∀ j : ℕ, ‖S j‖ ≤ (L : ℝ) * ρ ^ 2 ^ j := by
    intro j; rw [hS]; exact norm_conjPowSum_le β _
  have hLn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  -- the identity, rewritten with `σ`
  have hid2 : ∀ j ≥ j₀, (c : ℂ) = 2 * (β : ℂ) ^ 2 ^ j * S j + 2 * σ j := by
    intro j hj
    have h := hident j hj
    simp only [hσ, hS]
    linear_combination h
  -- a uniform bound `D` on `‖σ j‖`
  set D : ℝ := ((L : ℝ) ^ 2 + (L : ℝ)) / 2 with hDdef
  have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
  have hσD : ∀ j : ℕ, ‖σ j‖ ≤ D := by
    intro j
    rw [hσ]
    have h1 : ‖S j ^ 2 - S (j + 1)‖ ≤ ‖S j‖ ^ 2 + ‖S (j + 1)‖ := by
      calc ‖S j ^ 2 - S (j + 1)‖ ≤ ‖S j ^ 2‖ + ‖S (j + 1)‖ := norm_sub_le _ _
        _ = ‖S j‖ ^ 2 + ‖S (j + 1)‖ := by rw [norm_pow]
    have h2 : ‖S j‖ ^ 2 ≤ (L : ℝ) ^ 2 := by
      have := hSb j
      have hle : ‖S j‖ ≤ (L : ℝ) := le_trans this (by nlinarith [hr1 j, pow_nonneg hρ0 (2 ^ j)])
      nlinarith [norm_nonneg (S j)]
    have h3 : ‖S (j + 1)‖ ≤ (L : ℝ) := le_trans (hSb (j + 1))
      (by nlinarith [hr1 (j + 1), pow_nonneg hρ0 (2 ^ (j + 1))])
    rw [norm_div, Complex.norm_ofNat]
    rw [hDdef]
    have := norm_nonneg (S j ^ 2 - S (j + 1))
    linarith [h1, h2, h3]
  set U : ℝ := |c| / 2 + D with hUdef
  have hU0 : (0 : ℝ) ≤ U := by rw [hUdef]; positivity
  -- `βᴺ S_N = c/2 − σ_N`
  have hBS : ∀ j ≥ j₀, (β : ℂ) ^ 2 ^ j * S j = (c : ℂ) / 2 - σ j := by
    intro j hj
    have h := hid2 j hj
    linear_combination -h / 2
  have hSu : ∀ j ≥ j₀, β ^ 2 ^ j * ‖S j‖ ≤ U := by
    intro j hj
    have h := hBS j hj
    have : β ^ 2 ^ j * ‖S j‖ = ‖(β : ℂ) ^ 2 ^ j * S j‖ := by rw [norm_mul, hBn]
    rw [this, h, hUdef]
    calc ‖(c : ℂ) / 2 - σ j‖ ≤ ‖(c : ℂ) / 2‖ + ‖σ j‖ := norm_sub_le _ _
      _ ≤ |c| / 2 + D := by
          gcongr
          · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
          · exact hσD j
  -- **the key quadratic decay**: `β^(2N) σ_N` is bounded
  set K₂ : ℝ := (U ^ 2 + U) / 2 with hK2def
  have hK20 : (0 : ℝ) ≤ K₂ := by rw [hK2def]; positivity
  have hkey : ∀ j ≥ j₀, (β ^ 2 ^ j) ^ 2 * ‖σ j‖ ≤ K₂ := by
    intro j hj
    have h1 := hBS j hj
    have h2 := hBS (j + 1) (by omega)
    have hsq : ((β : ℂ) ^ 2 ^ (j + 1)) = ((β : ℂ) ^ 2 ^ j) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hsq] at h2
    have hexp : ((β : ℂ) ^ 2 ^ j) ^ 2 * σ j
        = (((c : ℂ) / 2 - σ j) ^ 2 - ((c : ℂ) / 2 - σ (j + 1))) / 2 := by
      have hs : 2 * σ j = S j ^ 2 - S (j + 1) := by rw [hσ]; ring
      linear_combination (((β:ℂ) ^ 2 ^ j) ^ 2 / 2) * hs
        + (((c:ℂ)/2 - σ j) + (β:ℂ) ^ 2 ^ j * S j) / 2 * h1 - h2 / 2
    have hnn : (β ^ 2 ^ j) ^ 2 * ‖σ j‖ = ‖((β : ℂ) ^ 2 ^ j) ^ 2 * σ j‖ := by
      rw [norm_mul, norm_pow, hBn]
    rw [hnn, hexp]
    have hc2 : ‖(c : ℂ) / 2‖ = |c| / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    calc ‖(((c : ℂ) / 2 - σ j) ^ 2 - ((c : ℂ) / 2 - σ (j + 1))) / 2‖
        = ‖((c : ℂ) / 2 - σ j) ^ 2 - ((c : ℂ) / 2 - σ (j + 1))‖ / 2 := by
          rw [norm_div, Complex.norm_ofNat]
      _ ≤ (‖(c : ℂ) / 2 - σ j‖ ^ 2 + ‖(c : ℂ) / 2 - σ (j + 1)‖) / 2 := by
          gcongr
          calc ‖((c : ℂ) / 2 - σ j) ^ 2 - ((c : ℂ) / 2 - σ (j + 1))‖
              ≤ ‖((c : ℂ) / 2 - σ j) ^ 2‖ + ‖(c : ℂ) / 2 - σ (j + 1)‖ := norm_sub_le _ _
            _ = ‖(c : ℂ) / 2 - σ j‖ ^ 2 + ‖(c : ℂ) / 2 - σ (j + 1)‖ := by rw [norm_pow]
      _ ≤ (U ^ 2 + U) / 2 := by
          have e1 : ‖(c : ℂ) / 2 - σ j‖ ≤ U := by
            calc ‖(c : ℂ) / 2 - σ j‖ ≤ ‖(c : ℂ) / 2‖ + ‖σ j‖ := norm_sub_le _ _
              _ ≤ U := by rw [hc2, hUdef]; linarith [hσD j]
          have e2 : ‖(c : ℂ) / 2 - σ (j + 1)‖ ≤ U := by
            calc ‖(c : ℂ) / 2 - σ (j + 1)‖ ≤ ‖(c : ℂ) / 2‖ + ‖σ (j + 1)‖ := norm_sub_le _ _
              _ ≤ U := by rw [hc2, hUdef]; linarith [hσD (j + 1)]
          have := norm_nonneg ((c : ℂ) / 2 - σ j)
          nlinarith
      _ = K₂ := by rw [hK2def]
  sorry

end LeanFormalizations.Transcendence.Dubickas
