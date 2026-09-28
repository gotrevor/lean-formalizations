/-
# The normalized symmetric functions `A n j` and the vanishing of odd `Eₙ`

Step 4 of the Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`), part 1.  With
`B_j = β^(2^j)` and the parity weight `pw`, set

    A n j := e_n(2^j) · B_j^(pw n).

`weight_bound` says exactly that each `A n ·` is *bounded* on a tail.  This file adds the two
structural facts the recursion needs:

* `eFull_eq_zero_of_odd` — for odd `n ≥ 3`, `E_n(2^j) = 0` for all large `j`
  (`‖E_n‖ ≤ C' ρ^{nN} + C q_j → 0` and `n!·E_n ∈ ℤ`);
* `AA_odd_succ` — hence `A_{2u+1} j = − A_{2u} j` for `u ≥ 1` and large `j`;
* `AA_eq_zero_of_card_lt` — `A n j = 0` once `n > deg β − 1`, which is what makes the limit
  sequence `b` finitely supported.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasWeight

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Transcendence LeanFormalizations.Mills
open LeanFormalizations.Literature

variable {β : ℝ}

/-- `eₖ(s) = 0` once `k` exceeds the cardinality of `s`. -/
theorem Multiset.esymm_eq_zero_of_card_lt {R : Type*} [CommSemiring R] {s : Multiset R} {k : ℕ}
    (h : Multiset.card s < k) : s.esymm k = 0 := by
  have hc : Multiset.card (s.powersetCard k) = 0 := by
    rw [Multiset.card_powersetCard, Nat.choose_eq_zero_of_lt h]
  rw [Multiset.esymm, Multiset.card_eq_zero.1 hc]
  simp

theorem eSmall_eq_zero_of_card_lt (β : ℝ) {k : ℕ} (h : Multiset.card (otherConj β) < k) (N : ℕ) :
    eSmall β k N = 0 := by
  refine Multiset.esymm_eq_zero_of_card_lt ?_
  rwa [Multiset.card_map]

/-- **For odd `n ≥ 3`, `Eₙ(2^j)` vanishes for all large `j`.** -/
theorem eFull_eq_zero_of_odd (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) {n : ℕ} (hodd : n % 2 = 1)
    (hn3 : 3 ≤ n) : ∃ J : ℕ, ∀ j ≥ J, eFull β n (2 ^ j) = 0 := by
  classical
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hρ0 : 0 ≤ conjMax β := conjMax_nonneg β
  have hρ1 : conjMax β < 1 := conjMax_lt_one hβ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmpar : m % 2 = 0 := by omega
  obtain ⟨C, hC0, J, hJ⟩ := weight_bound hβ hbase m
  obtain ⟨Ccr, hCcr⟩ : ∃ Ccr : ℝ,
      Ccr = ((Multiset.card (otherConj β)).choose (m + 1) : ℝ) := ⟨_, rfl⟩
  have hCcr0 : 0 ≤ Ccr := by rw [hCcr]; positivity
  have hto : Tendsto (fun j : ℕ => (((m + 1).factorial : ℝ)) *
      (Ccr * (conjMax β ^ 2 ^ j) ^ (m + 1) + C * qq β j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (conjMax β ^ 2 ^ j) ^ (m + 1)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp tendsto_two_pow_atTop
      simpa using this.pow (m + 1)
    have h2 : Tendsto (fun j : ℕ => Ccr * (conjMax β ^ 2 ^ j) ^ (m + 1) + C * qq β j)
        atTop (𝓝 0) := by
      simpa using (h1.const_mul Ccr).add ((qq_tendsto hβ1).const_mul C)
    simpa using h2.const_mul (((m + 1).factorial : ℝ))
  obtain ⟨J', hJ'⟩ := (hto.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).and
    (eventually_ge_atTop J) |>.exists_forall_of_atTop
  refine ⟨J', fun j hj => ?_⟩
  obtain ⟨hlt, hge⟩ := hJ' j hj
  have hsplit := eFull_succ halg m (2 ^ j)
  have hb1 : ‖eSmall β (m + 1) (2 ^ j)‖ ≤ Ccr * (conjMax β ^ 2 ^ j) ^ (m + 1) := by
    rw [hCcr]; exact norm_eSmall_le β (m + 1) (2 ^ j)
  have hnb : ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hn2 : ‖eSmall β m (2 ^ j)‖ ≤ C * qq β j ^ 2 := by
    have := hJ m hm1 le_rfl j hge
    have hpwm : pw m = 2 := by unfold pw; simp [hmpar]
    rwa [hpwm] at this
  have hb2 : ‖(β : ℂ) ^ 2 ^ j * eSmall β m (2 ^ j)‖ ≤ C * qq β j := by
    rw [norm_mul, hnb]
    have hthis : β ^ 2 ^ j * qq β j ^ 2 = qq β j := by
      rw [pow_two, ← mul_assoc, beta_mul_qq hβ1 j, one_mul]
    calc β ^ 2 ^ j * ‖eSmall β m (2 ^ j)‖
        ≤ β ^ 2 ^ j * (C * qq β j ^ 2) := mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ = C * (β ^ 2 ^ j * qq β j ^ 2) := by ring
      _ = C * qq β j := by rw [hthis]
  have hbound : ‖((m + 1).factorial : ℂ) * eFull β (m + 1) (2 ^ j)‖ < 1 := by
    have hsum : ‖eFull β (m + 1) (2 ^ j)‖
        ≤ Ccr * (conjMax β ^ 2 ^ j) ^ (m + 1) + C * qq β j := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
    rw [norm_mul, Complex.norm_natCast]
    calc ((m + 1).factorial : ℝ) * ‖eFull β (m + 1) (2 ^ j)‖
        ≤ ((m + 1).factorial : ℝ) * (Ccr * (conjMax β ^ 2 ^ j) ^ (m + 1) + C * qq β j) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ < 1 := hlt
  have hz := eq_zero_of_isRatInt_of_norm_lt_one
    (isRatInt_factorial_mul_eFull hβ (m + 1) (2 ^ j)) hbound
  have hfne : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hfne
  · exact h

/-! ### The normalized quantities -/

/-- `A n j = e_n(2^j) · β^(2^j · pw n)`. -/
noncomputable def AA (β : ℝ) (n j : ℕ) : ℂ := eSmall β n (2 ^ j) * ((β : ℂ) ^ 2 ^ j) ^ pw n

theorem AA_eq_zero_of_card_lt (β : ℝ) {n : ℕ} (h : Multiset.card (otherConj β) < n) (j : ℕ) :
    AA β n j = 0 := by
  rw [AA, eSmall_eq_zero_of_card_lt β h, zero_mul]

/-- `‖A n j‖ ≤ C` on a tail: the parity-weight bound in normalized form. -/
theorem norm_AA_le (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ J : ℕ, ∀ i, 1 ≤ i → i ≤ n → ∀ j ≥ J, ‖AA β i j‖ ≤ C := by
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  obtain ⟨C, hC0, J, hJ⟩ := weight_bound hβ hbase n
  refine ⟨C, hC0, J, fun i h1 h2 j hj => ?_⟩
  have hnb : ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hbq : (β ^ 2 ^ j) ^ pw i * qq β j ^ pw i = 1 := by
    rw [← mul_pow, beta_mul_qq hβ1 j, one_pow]
  rw [AA, norm_mul, norm_pow, hnb]
  calc ‖eSmall β i (2 ^ j)‖ * (β ^ 2 ^ j) ^ pw i
      ≤ (C * qq β j ^ pw i) * (β ^ 2 ^ j) ^ pw i :=
        mul_le_mul_of_nonneg_right (hJ i h1 h2 j hj) (by positivity)
    _ = C := by
        calc (C * qq β j ^ pw i) * (β ^ 2 ^ j) ^ pw i
            = C * ((β ^ 2 ^ j) ^ pw i * qq β j ^ pw i) := by ring
          _ = C := by rw [hbq, mul_one]

/-- **`A_{2u+1} j = − A_{2u} j`** for `u ≥ 1` and all large `j`. -/
theorem AA_odd_succ (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) {u : ℕ} (hu : 1 ≤ u) :
    ∃ J : ℕ, ∀ j ≥ J, AA β (2 * u + 1) j = -AA β (2 * u) j := by
  have hβ1 : 1 < β := hβ.1
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  obtain ⟨J, hJ⟩ := eFull_eq_zero_of_odd hβ hbase (n := 2 * u + 1) (by omega) (by omega)
  refine ⟨J, fun j hj => ?_⟩
  have hsplit := eFull_succ halg (2 * u) (2 ^ j)
  rw [hJ j hj] at hsplit
  have hpo : pw (2 * u + 1) = 1 := by unfold pw; simp [Nat.mul_add_mod]
  have hpe : pw (2 * u) = 2 := by unfold pw; simp [Nat.mul_mod_right]
  rw [AA, AA, hpo, hpe, pow_one]
  have h2 : eSmall β (2 * u + 1) (2 ^ j) = -((β : ℂ) ^ 2 ^ j * eSmall β (2 * u) (2 ^ j)) := by
    linear_combination -hsplit
  rw [h2]
  ring

end LeanFormalizations.Transcendence.Dubickas
