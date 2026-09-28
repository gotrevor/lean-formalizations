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

set_option maxHeartbeats 1000000 in
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
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, Multiset.card (otherConj β) = L := ⟨_, rfl⟩
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
    intro j; rw [hS, ← hLdef]; exact norm_conjPowSum_le β _
  have hLn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  -- the identity, rewritten with `σ`
  have hid2 : ∀ j ≥ j₀, (c : ℂ) = 2 * (β : ℂ) ^ 2 ^ j * S j + 2 * σ j := by
    intro j hj
    have h := hident j hj
    simp only [hσ, hS]
    linear_combination h
  -- a uniform bound `D` on `‖σ j‖`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((L : ℝ) ^ 2 + (L : ℝ)) / 2 := ⟨_, rfl⟩
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
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = |c| / 2 + D := ⟨_, rfl⟩
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
  obtain ⟨K₂, hK2def⟩ : ∃ K₂ : ℝ, K₂ = (U ^ 2 + U) / 2 := ⟨_, rfl⟩
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
  -- `ρ^(2^j) → 0` and `β^(2^j) → ∞`
  have hρto : Tendsto (fun j : ℕ ↦ ρ ^ 2 ^ j) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp tendsto_two_pow_atTop
  have hbto : Tendsto (fun j : ℕ ↦ β ^ 2 ^ j) atTop atTop := tendsto_beta_two_pow hβ1
  have hb1 : ∀ j : ℕ, (1 : ℝ) ≤ β ^ 2 ^ j := fun j ↦ one_le_pow₀ hβ1.le
  -- normalized form of the bounds: `q j = β^(−2^j) ∈ (0, 1]`
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ j, q j = (β ^ 2 ^ j)⁻¹ := ⟨_, fun _ ↦ rfl⟩
  have hq0 : ∀ j, (0 : ℝ) < q j := fun j ↦ by rw [hq]; positivity
  have hq1 : ∀ j, q j ≤ 1 := fun j ↦ by
    rw [hq]; exact inv_le_one_of_one_le₀ (hb1 j)
  have hqb : ∀ j, q j * β ^ 2 ^ j = 1 := fun j ↦ by
    rw [hq]; exact inv_mul_cancel₀ (ne_of_gt (hb0 j))
  have hqsucc : ∀ j, q (j + 1) = q j ^ 2 := fun j ↦ by
    rw [hq, hq, hbsq, ← inv_pow]
  have hσq : ∀ j ≥ j₀, ‖σ j‖ ≤ K₂ * q j ^ 2 := by
    intro j hj
    have h1 := hkey j hj
    have h2 : q j ^ 2 * (β ^ 2 ^ j) ^ 2 = 1 := by
      rw [← mul_pow, hqb]; norm_num
    nlinarith [hq0 j, norm_nonneg (σ j), sq_nonneg (q j)]
  have hSq : ∀ j ≥ j₀, ‖S j‖ ≤ U * q j := by
    intro j hj
    have h1 := hSu j hj
    have h2 := hqb j
    nlinarith [hq0 j, norm_nonneg (S j)]
  -- **the case analysis on `L = deg β − 1`**
  rcases (show L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ 5 ≤ L by omega)
    with hLc | hLc | hLc | hLc | hLc | hLc
  · -- `deg β = 1`: no other conjugates, so `S = σ = 0` and `c = 0`
    left
    have hempty : otherConj β = 0 := Multiset.card_eq_zero.1 (by rw [hLdef, hLc])
    have hz : ∀ j, S j = 0 := by intro j; rw [hS, conjPowSum, hempty]; simp
    have h := hid2 j₀ le_rfl
    rw [hz, hσ, hz, hz] at h
    simpa using h
  · -- `deg β = 2`: `S_N = γᴺ`, so `σ = 0` and `c = 2(βγ)ᴺ` — Dubickas's own final step
    obtain ⟨γ, hγ⟩ := Multiset.card_eq_one.1 (by rw [hLdef, hLc] : Multiset.card (otherConj β) = 1)
    have hz : ∀ j, S j = γ ^ 2 ^ j := by intro j; rw [hS, conjPowSum, hγ]; simp
    have hσ0 : ∀ j, σ j = 0 := by
      intro j
      have e : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
      rw [hσ, hz, hz, e, pow_mul]; ring
    have hkc : ∀ j ≥ j₀, (c : ℂ) = 2 * ((β : ℂ) * γ) ^ 2 ^ j := by
      intro j hj
      have h := hid2 j hj
      rw [hz, hσ0] at h
      rw [mul_pow]
      linear_combination h
    have e1 := hkc j₀ le_rfl
    have e2 := hkc (j₀ + 1) (by omega)
    rw [show (2 : ℕ) ^ (j₀ + 1) = 2 ^ j₀ * 2 from pow_succ 2 j₀, pow_mul] at e2
    have hW : ((β : ℂ) * γ) ^ 2 ^ j₀ = (c : ℂ) / 2 := by linear_combination -e1 / 2
    rw [hW] at e2
    have hcc : c = c ^ 2 / 2 := by
      have hcc2 : (c : ℂ) = (c : ℂ) ^ 2 / 2 := by linear_combination e2
      exact_mod_cast hcc2
    have : c * (c - 2) = 0 := by nlinarith [hcc]
    rcases mul_eq_zero.1 this with h | h
    · left; exact h
    · right; linarith
  · -- `deg β = 3`: `σ_N = (γδ)ᴺ` has modulus `≥ β^(−N)`, contradicting `β^(2N)σ_N` bounded
    exfalso
    obtain ⟨γ, δ, hγδ⟩ := Multiset.card_eq_two.1 (by rw [hLdef, hLc])
    have hz : ∀ j, S j = γ ^ 2 ^ j + δ ^ 2 ^ j := by
      intro j; rw [hS, conjPowSum, hγδ]; simp
    have hσv : ∀ j, σ j = (γ * δ) ^ 2 ^ j := by
      intro j
      have e : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
      rw [hσ, hz, hz, e, pow_mul, pow_mul, mul_pow]; ring
    have hprod : 1 ≤ β * (‖γ‖ * ‖δ‖) := by
      have h := pisot_one_le_prod_norm hβ
      rw [hγδ] at h; simpa using h
    have hlow : ∀ j : ℕ, (β ^ 2 ^ j)⁻¹ ≤ ‖σ j‖ := by
      intro j
      rw [hσv, norm_pow, norm_mul]
      have h1 : β⁻¹ ≤ ‖γ‖ * ‖δ‖ := by
        rw [inv_le_iff_one_le_mul₀' hβ0]; linarith
      calc (β ^ 2 ^ j)⁻¹ = (β⁻¹) ^ 2 ^ j := by rw [inv_pow]
        _ ≤ (‖γ‖ * ‖δ‖) ^ 2 ^ j := by
            refine pow_le_pow_left₀ (by positivity) h1 _
    have hfin : ∀ j ≥ j₀, β ^ 2 ^ j ≤ K₂ := by
      intro j hj
      have h1 := hkey j hj
      have h2 := hlow j
      have h3 : (0 : ℝ) < β ^ 2 ^ j := hb0 j
      have h4 : (β ^ 2 ^ j) ^ 2 * (β ^ 2 ^ j)⁻¹ = β ^ 2 ^ j := by
        field_simp
      nlinarith [h1, h2, h3, h4]
    obtain ⟨j, hj1, hj2⟩ := ((hbto.eventually_gt_atTop K₂).and (eventually_ge_atTop j₀)).exists
    exact absurd (hfin j hj2) (not_le.2 hj1)
  · -- `deg β = 4`: `2 S_N (γδε)ᴺ = σ_N² − σ_(2N)` forces `‖S_N‖ = O(β^(−3N))`, hence `c = 0`
    left
    obtain ⟨γ, δ, ε, hγδε⟩ := Multiset.card_eq_three.1 (by rw [hLdef, hLc])
    have hz : ∀ j, S j = γ ^ 2 ^ j + δ ^ 2 ^ j + ε ^ 2 ^ j := by
      intro j
      rw [hS, conjPowSum, hγδε]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      ring
    have hid3 : ∀ j, σ (j + 1) = σ j ^ 2 - 2 * S j * (γ * δ * ε) ^ 2 ^ j := by
      intro j
      simp only [hσ, hz, pow_succ, pow_mul, mul_pow]
      ring
    have hprod : 1 ≤ β * (‖γ‖ * (‖δ‖ * ‖ε‖)) := by
      have h := pisot_one_le_prod_norm hβ
      rw [hγδε] at h; simpa using h
    have hlow : ∀ j, q j ≤ ‖(γ * δ * ε) ^ 2 ^ j‖ := by
      intro j
      rw [norm_pow, norm_mul, norm_mul, hq, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [inv_le_iff_one_le_mul₀' hβ0]
      nlinarith [hprod]
    -- `‖S_N‖ ≤ (K₂² + K₂)/2 · q³`
    have hS3 : ∀ j ≥ j₀, 2 * ‖S j‖ ≤ (K₂ ^ 2 + K₂) * q j ^ 3 := by
      intro j hj
      have h1 : 2 * ‖S j‖ * q j ≤ ‖σ j‖ ^ 2 + ‖σ (j + 1)‖ := by
        have hnorm : ‖2 * S j * (γ * δ * ε) ^ 2 ^ j‖ = 2 * ‖S j‖ * ‖(γ * δ * ε) ^ 2 ^ j‖ := by
          rw [norm_mul, norm_mul]; norm_num
        have hle : ‖2 * S j * (γ * δ * ε) ^ 2 ^ j‖ ≤ ‖σ j‖ ^ 2 + ‖σ (j + 1)‖ := by
          rw [show 2 * S j * (γ * δ * ε) ^ 2 ^ j = σ j ^ 2 - σ (j + 1) from by
            linear_combination hid3 j]
          calc ‖σ j ^ 2 - σ (j + 1)‖ ≤ ‖σ j ^ 2‖ + ‖σ (j + 1)‖ := norm_sub_le _ _
            _ = ‖σ j‖ ^ 2 + ‖σ (j + 1)‖ := by rw [norm_pow]
        rw [hnorm] at hle
        nlinarith [hlow j, norm_nonneg (S j), hq0 j]
      have h2 := hσq j hj
      have h3 : ‖σ (j + 1)‖ ≤ K₂ * q j ^ 4 := by
        have := hσq (j + 1) (by omega)
        rw [hqsucc] at this
        calc ‖σ (j + 1)‖ ≤ K₂ * (q j ^ 2) ^ 2 := this
          _ = K₂ * q j ^ 4 := by ring
      have h4 : ‖σ j‖ ^ 2 ≤ K₂ ^ 2 * q j ^ 4 := by
        nlinarith [norm_nonneg (σ j), hK20, pow_nonneg (hq0 j).le 2]
      -- divide `h1` by `q j`
      have hqpos := hq0 j
      have hkey2 : 2 * ‖S j‖ * q j ≤ (K₂ ^ 2 + K₂) * q j ^ 4 := by linarith
      nlinarith [hkey2, hqpos, norm_nonneg (S j), pow_pos hqpos 3]
    -- so `|c| · q⁻¹` is bounded, forcing `c = 0`
    have hcb : ∀ j ≥ j₀, |c| ≤ (K₂ ^ 2 + 3 * K₂) * q j := by
      intro j hj
      have h1 : |c| ≤ 2 * (β ^ 2 ^ j * ‖S j‖) + 2 * ‖σ j‖ := by
        have h := hid2 j hj
        have : |c| = ‖(c : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
        rw [this, h]
        calc ‖2 * (β : ℂ) ^ 2 ^ j * S j + 2 * σ j‖
            ≤ ‖2 * (β : ℂ) ^ 2 ^ j * S j‖ + ‖2 * σ j‖ := norm_add_le _ _
          _ = 2 * (β ^ 2 ^ j * ‖S j‖) + 2 * ‖σ j‖ := by
              rw [norm_mul, norm_mul, norm_mul, hBn, Complex.norm_ofNat]; ring
      have h2 := hS3 j hj
      have h3 := hσq j hj
      have h5 : β ^ 2 ^ j * q j ^ 3 = q j ^ 2 := by
        linear_combination (q j ^ 2) * hqb j
      have e3 : 2 * (β ^ 2 ^ j * ‖S j‖) ≤ (K₂ ^ 2 + K₂) * q j ^ 2 := by
        have h := mul_le_mul_of_nonneg_left h2 (hb0 j).le
        calc 2 * (β ^ 2 ^ j * ‖S j‖) = β ^ 2 ^ j * (2 * ‖S j‖) := by ring
          _ ≤ β ^ 2 ^ j * ((K₂ ^ 2 + K₂) * q j ^ 3) := h
          _ = (K₂ ^ 2 + K₂) * (β ^ 2 ^ j * q j ^ 3) := by ring
          _ = (K₂ ^ 2 + K₂) * q j ^ 2 := by rw [h5]
      have e4 : q j ^ 2 ≤ q j := by
        have h := mul_le_of_le_one_right (hq0 j).le (hq1 j)
        simpa [pow_two] using h
      have hKpos : (0 : ℝ) ≤ K₂ ^ 2 + 3 * K₂ := by positivity
      have e5 : (K₂ ^ 2 + 3 * K₂) * q j ^ 2 ≤ (K₂ ^ 2 + 3 * K₂) * q j :=
        mul_le_mul_of_nonneg_left e4 hKpos
      linarith only [h1, e3, h3, e5]
    -- `q j → 0`
    have hqto : Tendsto q atTop (𝓝 0) := by
      have h : Tendsto (fun j : ℕ ↦ (β ^ 2 ^ j)⁻¹) atTop (𝓝 0) := hbto.inv_tendsto_atTop
      exact h.congr fun j ↦ (hq j).symm
    have habs : |c| = 0 := by
      by_contra hne
      have hpos : 0 < |c| := lt_of_le_of_ne (abs_nonneg c) (Ne.symm hne)
      have hto : Tendsto (fun j : ℕ ↦ (K₂ ^ 2 + 3 * K₂) * q j) atTop (𝓝 0) := by
        simpa using hqto.const_mul (K₂ ^ 2 + 3 * K₂)
      obtain ⟨j, hj1, hj2⟩ :=
        ((hto.eventually (eventually_lt_nhds hpos)).and (eventually_ge_atTop j₀)).exists
      exact absurd (hcb j hj2) (not_le.2 hj1)
    exact abs_eq_zero.1 habs
  · -- `deg β = 5`: the quartic product `(γδεζ)ᴺ` survives in `σ_(2N) = σ_N² − 2S_N σ₃ + 2(γδεζ)ᴺ`
    exfalso
    obtain ⟨γ, δ, ε, ζ, h4⟩ := Multiset.card_eq_four.1 (by rw [hLdef, hLc])
    have hmem : ∀ z ∈ ({γ, δ, ε, ζ} : Multiset ℂ), ‖z‖ ≤ ρ := by
      intro z hz
      exact norm_le_conjMax (by rw [h4]; exact hz)
    have hgn : ‖γ‖ ≤ ρ := hmem γ (by simp)
    have hdn : ‖δ‖ ≤ ρ := hmem δ (by simp)
    have hen : ‖ε‖ ≤ ρ := hmem ε (by simp)
    have hzn : ‖ζ‖ ≤ ρ := hmem ζ (by simp)
    have hz : ∀ j, S j = γ ^ 2 ^ j + δ ^ 2 ^ j + ε ^ 2 ^ j + ζ ^ 2 ^ j := by
      intro j
      rw [hS, conjPowSum, h4]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      ring
    have hid4 : ∀ j, σ (j + 1) = σ j ^ 2
        - 2 * S j * ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
          + (δ * ε * ζ) ^ 2 ^ j) + 2 * (γ * δ * ε * ζ) ^ 2 ^ j := by
      intro j
      simp only [hσ, hz, pow_succ, pow_mul, mul_pow]
      ring
    have hprod : 1 ≤ β * (‖γ‖ * (‖δ‖ * (‖ε‖ * ‖ζ‖))) := by
      have h := pisot_one_le_prod_norm hβ
      rw [h4] at h; simpa using h
    have hlowP : ∀ j, q j ≤ ‖(γ * δ * ε * ζ) ^ 2 ^ j‖ := by
      intro j
      rw [norm_pow, norm_mul, norm_mul, norm_mul, hq, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [inv_le_iff_one_le_mul₀' hβ0]
      nlinarith [hprod]
    have hTb : ∀ j, ‖(γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
        + (δ * ε * ζ) ^ 2 ^ j‖ ≤ 4 * (ρ ^ 2 ^ j) ^ 3 := by
      intro j
      have hone : ∀ a b c : ℂ, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖c‖ ≤ ρ →
          ‖(a * b * c) ^ 2 ^ j‖ ≤ (ρ ^ 2 ^ j) ^ 3 := by
        intro a b c ha hb hc
        rw [norm_pow, norm_mul, norm_mul]
        calc (‖a‖ * ‖b‖ * ‖c‖) ^ 2 ^ j ≤ (ρ * ρ * ρ) ^ 2 ^ j := by
              refine pow_le_pow_left₀ (by positivity) ?_ _
              have h1 : ‖a‖ * ‖b‖ ≤ ρ * ρ :=
                mul_le_mul ha hb (norm_nonneg b) (le_trans (norm_nonneg a) ha)
              exact mul_le_mul h1 hc (norm_nonneg c) (by positivity)
          _ = (ρ ^ 2 ^ j) ^ 3 := by
              rw [show ρ * ρ * ρ = ρ ^ 3 from by ring, ← pow_mul, ← pow_mul, Nat.mul_comm]
      have h1 := hone γ δ ε hgn hdn hen
      have h2 := hone γ δ ζ hgn hdn hzn
      have h3 := hone γ ε ζ hgn hen hzn
      have h4' := hone δ ε ζ hdn hen hzn
      calc ‖(γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
            + (δ * ε * ζ) ^ 2 ^ j‖
          ≤ ‖(γ * δ * ε) ^ 2 ^ j‖ + ‖(γ * δ * ζ) ^ 2 ^ j‖ + ‖(γ * ε * ζ) ^ 2 ^ j‖
            + ‖(δ * ε * ζ) ^ 2 ^ j‖ := by
            refine le_trans (norm_add_le _ _) ?_
            gcongr
            refine le_trans (norm_add_le _ _) ?_
            gcongr
            exact norm_add_le _ _
        _ ≤ 4 * (ρ ^ 2 ^ j) ^ 3 := by linarith
    -- the contradiction: `2 ≤ (K₂ + K₂²) q + 8 U ρ^(3N)`, both terms `→ 0`
    have hfin : ∀ j ≥ j₀, 2 ≤ (K₂ + K₂ ^ 2) * q j + 8 * U * (ρ ^ 2 ^ j) ^ 3 := by
      intro j hj
      have hP := hlowP j
      have hT := hTb j
      have hSj := hSq j hj
      have h2 := hσq j hj
      have h3 : ‖σ (j + 1)‖ ≤ K₂ * q j ^ 4 := by
        have := hσq (j + 1) (by omega)
        rw [hqsucc] at this
        calc ‖σ (j + 1)‖ ≤ K₂ * (q j ^ 2) ^ 2 := this
          _ = K₂ * q j ^ 4 := by ring
      have h4' : ‖σ j‖ ^ 2 ≤ K₂ ^ 2 * q j ^ 4 := by
        nlinarith [norm_nonneg (σ j), hK20, pow_nonneg (hq0 j).le 2]
      -- norm the identity
      have hexp : 2 * (γ * δ * ε * ζ) ^ 2 ^ j = σ (j + 1) - σ j ^ 2
          + 2 * S j * ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
            + (δ * ε * ζ) ^ 2 ^ j) := by linear_combination -hid4 j
      have hnb : 2 * ‖(γ * δ * ε * ζ) ^ 2 ^ j‖ ≤ ‖σ (j + 1)‖ + ‖σ j‖ ^ 2
          + 2 * (‖S j‖ * ‖(γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
            + (δ * ε * ζ) ^ 2 ^ j‖) := by
        have hA : 2 * ‖(γ * δ * ε * ζ) ^ 2 ^ j‖
            = ‖σ (j + 1) - σ j ^ 2 + 2 * S j * ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j
              + (γ * ε * ζ) ^ 2 ^ j + (δ * ε * ζ) ^ 2 ^ j)‖ := by
          rw [← hexp, norm_mul, Complex.norm_ofNat]
        rw [hA]
        calc ‖σ (j + 1) - σ j ^ 2 + 2 * S j * ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j
              + (γ * ε * ζ) ^ 2 ^ j + (δ * ε * ζ) ^ 2 ^ j)‖
            ≤ ‖σ (j + 1) - σ j ^ 2‖ + ‖2 * S j * ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j
              + (γ * ε * ζ) ^ 2 ^ j + (δ * ε * ζ) ^ 2 ^ j)‖ := norm_add_le _ _
          _ ≤ (‖σ (j + 1)‖ + ‖σ j‖ ^ 2) + 2 * (‖S j‖ * ‖(γ * δ * ε) ^ 2 ^ j
              + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j + (δ * ε * ζ) ^ 2 ^ j‖) := by
              refine add_le_add ?_ ?_
              · calc ‖σ (j + 1) - σ j ^ 2‖ ≤ ‖σ (j + 1)‖ + ‖σ j ^ 2‖ := norm_sub_le _ _
                  _ = ‖σ (j + 1)‖ + ‖σ j‖ ^ 2 := by rw [norm_pow]
              · rw [norm_mul, norm_mul, Complex.norm_ofNat, mul_assoc]
          _ = ‖σ (j + 1)‖ + ‖σ j‖ ^ 2 + 2 * (‖S j‖ * ‖(γ * δ * ε) ^ 2 ^ j
              + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j + (δ * ε * ζ) ^ 2 ^ j‖) := by ring
      -- assemble: `2 q ≤ (K₂+K₂²) q⁴ + 8 U q ρ^(3N)`, then divide by `q`
      have hrn : (0 : ℝ) ≤ (ρ ^ 2 ^ j) ^ 3 := by positivity
      have hcomb : 2 * q j ≤ (K₂ + K₂ ^ 2) * q j ^ 4 + 8 * U * (q j * (ρ ^ 2 ^ j) ^ 3) := by
        nlinarith [hnb, hP, hT, hSj, h3, h4', norm_nonneg (S j), hU0, hq0 j, hrn,
          norm_nonneg ((γ * δ * ε) ^ 2 ^ j + (γ * δ * ζ) ^ 2 ^ j + (γ * ε * ζ) ^ 2 ^ j
            + (δ * ε * ζ) ^ 2 ^ j)]
      have hKK : (0 : ℝ) ≤ K₂ + K₂ ^ 2 := by positivity
      have e1 : q j ^ 4 ≤ q j ^ 2 :=
        pow_le_pow_of_le_one (hq0 j).le (hq1 j) (by norm_num)
      have e2 : (K₂ + K₂ ^ 2) * q j ^ 4 ≤ (K₂ + K₂ ^ 2) * q j ^ 2 :=
        mul_le_mul_of_nonneg_left e1 hKK
      have e3 : q j * 2 ≤ q j * ((K₂ + K₂ ^ 2) * q j + 8 * U * (ρ ^ 2 ^ j) ^ 3) := by
        nlinarith only [hcomb, e2]
      exact le_of_mul_le_mul_left e3 (hq0 j)
    have hqto : Tendsto q atTop (𝓝 0) := by
      have h : Tendsto (fun j : ℕ ↦ (β ^ 2 ^ j)⁻¹) atTop (𝓝 0) := hbto.inv_tendsto_atTop
      exact h.congr fun j ↦ (hq j).symm
    have hto : Tendsto (fun j : ℕ ↦ (K₂ + K₂ ^ 2) * q j + 8 * U * (ρ ^ 2 ^ j) ^ 3)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ ↦ (K₂ + K₂ ^ 2) * q j) atTop (𝓝 0) := by
        simpa using hqto.const_mul (K₂ + K₂ ^ 2)
      have h2 : Tendsto (fun j : ℕ ↦ 8 * U * (ρ ^ 2 ^ j) ^ 3) atTop (𝓝 0) := by
        have := (hρto.pow 3).const_mul (8 * U)
        simpa using this
      simpa using h1.add h2
    obtain ⟨j, hj1, hj2⟩ :=
      ((hto.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 2))).and (eventually_ge_atTop j₀)).exists
    exact absurd (hfin j hj2) (not_le.2 hj1)
  · -- `deg β ≥ 6`: OPEN.  See `PROBE-DUBICKAS-NOGAP.md`.
    sorry

end LeanFormalizations.Transcendence.Dubickas
