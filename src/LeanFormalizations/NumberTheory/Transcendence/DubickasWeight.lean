/-
# The parity-weight induction

Step 3 of the Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`).  With `q_j = β^(−2^j)`:

    ‖e_n(2^j)‖ ≤ C · q_j²   (n even),      ‖e_n(2^j)‖ ≤ C · q_j   (n odd),

for a single constant `C` and threshold `J` covering all indices `1 ≤ i ≤ n`.  The base case is
`n = 1`, i.e. the hypothesis `‖S_N‖ ≤ U β^(−N)` that the Dubickas recursion supplies.

* **odd step** (`n` odd, from `n − 1` even): `‖E_n‖ ≤ ‖e_n‖ + β^N‖e_{n−1}‖ ≤ C' ρ^{nN} + C q_j`
  tends to `0`, and `n!·E_n ∈ ℤ`, so `E_n = 0`; hence `e_n = −β^N e_{n−1}` and
  `‖e_n‖ ≤ β^N · C q_j² = C q_j`.
* **even step** (`n = 2k`, `k ≥ 1`): the Graeffe identity isolates
  `2 e_{2k}(j) = (−1)^k e_k(j+1) − Σ_{i=1}^{2k−1} (−1)^i e_i(j) e_{2k−i}(j)`; the first term has
  weight `2·w(k) ≥ 2` since `q_{j+1} = q_j²`, and each product pairs two indices of the *same*
  parity, so has weight `≥ 2`.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasEsymm

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Transcendence LeanFormalizations.Mills
open LeanFormalizations.Literature

/-- The parity weight of an index: `2` for even, `1` for odd. -/
def pw (n : ℕ) : ℕ := if n % 2 = 0 then 2 else 1

theorem pw_pos (n : ℕ) : 0 < pw n := by unfold pw; split <;> norm_num
theorem pw_le_two (n : ℕ) : pw n ≤ 2 := by unfold pw; split <;> norm_num
theorem two_le_pw_add (m n : ℕ) (h : m % 2 = n % 2) : 2 ≤ pw m + pw n := by
  unfold pw; rw [h]; split <;> omega

/-- The Graeffe identity for the small-conjugate symmetric functions along `N = 2^j`. -/
theorem eSmall_graeffe (β : ℝ) (n j : ℕ) :
    (-1 : ℂ) ^ n * eSmall β n (2 ^ (j + 1))
      = ∑ p ∈ Finset.antidiagonal (2 * n),
          (-1) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j) := by
  have hmap : (otherConj β).map (· ^ 2 ^ (j + 1))
      = ((otherConj β).map (· ^ 2 ^ j)).map (· ^ 2) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun z _ => by
      rw [Function.comp_apply, ← pow_mul, pow_succ]
  simp only [eSmall, hmap]
  exact esymm_map_sq _ n

/-- Isolating the two extreme terms of the Graeffe identity. -/
theorem eSmall_graeffe_isolate (β : ℝ) {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    2 * eSmall β (2 * k) (2 ^ j)
      = (-1 : ℂ) ^ k * eSmall β k (2 ^ (j + 1))
        - ∑ p ∈ {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0},
            (-1) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (2 * k))
    (fun p : ℕ × ℕ => p.1 ≠ 0 ∧ p.2 ≠ 0)
    (fun p => (-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j))
  have hset : {p ∈ Finset.antidiagonal (2 * k) | ¬(p.1 ≠ 0 ∧ p.2 ≠ 0)}
      = {((0 : ℕ), 2 * k), (2 * k, (0 : ℕ))} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
      Finset.mem_singleton, not_and_or, not_not, Prod.ext_iff]
    constructor
    · rintro ⟨hsum, h0 | h0⟩ <;> omega
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  rw [hset] at hsplit
  have hne : ((0 : ℕ), 2 * k) ≠ (2 * k, (0 : ℕ)) := by
    simp only [ne_eq, Prod.ext_iff]; omega
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton] at hsplit
  have he0 : eSmall β 0 (2 ^ j) = 1 := Multiset.esymm_zero' _
  rw [he0] at hsplit
  have hsign : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul]; norm_num
  rw [hsign] at hsplit
  rw [← eSmall_graeffe β k j] at hsplit
  linear_combination hsplit

variable {β : ℝ}

/-- `q_j = β^(−2^j)`. -/
noncomputable def qq (β : ℝ) (j : ℕ) : ℝ := (β ^ 2 ^ j)⁻¹

theorem qq_pos (hβ : 1 < β) (j : ℕ) : 0 < qq β j := by
  unfold qq; have : (0:ℝ) < β := by linarith
  positivity

theorem qq_le_one (hβ : 1 < β) (j : ℕ) : qq β j ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ hβ.le)

theorem qq_succ (hβ : 1 < β) (j : ℕ) : qq β (j + 1) = qq β j ^ 2 := by
  unfold qq
  rw [inv_pow, ← pow_mul, ← pow_succ]

theorem beta_mul_qq (hβ : 1 < β) (j : ℕ) : β ^ 2 ^ j * qq β j = 1 := by
  unfold qq
  exact mul_inv_cancel₀ (by positivity)

theorem qq_tendsto (hβ : 1 < β) : Tendsto (qq β) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => β ^ 2 ^ j) atTop atTop :=
    tendsto_pow_two_pow_atTop hβ
  exact h.inv_tendsto_atTop

theorem qq_pow_le (hβ : 1 < β) {j a b : ℕ} (hab : b ≤ a) : qq β j ^ a ≤ qq β j ^ b :=
  pow_le_pow_of_le_one (qq_pos hβ j).le (qq_le_one hβ j) hab

/-! ### The induction -/

/-- **The parity-weight bound.**  A single constant and threshold serve all indices `1 ≤ i ≤ n`. -/
theorem weight_bound (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ J : ℕ, ∀ i, 1 ≤ i → i ≤ n → ∀ j ≥ J,
      ‖eSmall β i (2 ^ j)‖ ≤ C * qq β j ^ pw i := by
  classical
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hρ0 : 0 ≤ conjMax β := conjMax_nonneg β
  have hρ1 : conjMax β < 1 := conjMax_lt_one hβ
  induction n with
  | zero => exact ⟨0, le_rfl, 0, fun i h1 h2 => by omega⟩
  | succ n ih =>
    obtain ⟨C, hC0, J, hJ⟩ := ih
    -- it suffices to handle the single new index `n + 1`
    rcases Nat.lt_or_ge n 1 with hn | hn
    · -- `n + 1 = 1`: the base case
      have hn0 : n = 0 := by omega
      refine ⟨max C U, le_max_of_le_left hC0, max J J₀, fun i h1 h2 j hj => ?_⟩
      have hi : i = 1 := by omega
      subst hi
      have := hbase j (le_trans (le_max_right J J₀) hj)
      calc ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j := this
        _ ≤ max C U * qq β j ^ pw 1 := by
            have : pw 1 = 1 := by unfold pw; norm_num
            rw [this, pow_one]
            exact mul_le_mul_of_nonneg_right (le_max_right C U) (qq_pos hβ1 j).le
    · -- `n + 1 ≥ 2`
      by_cases hpar : (n + 1) % 2 = 0
      · -- even: `n + 1 = 2k` with `1 ≤ k ≤ n`
        obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 * k := ⟨(n + 1) / 2, by omega⟩
        have hk1 : 1 ≤ k := by omega
        have hkn : k ≤ n := by omega
        refine ⟨max C ((C + (2 * k + 1) * C ^ 2) / 2), le_max_of_le_left hC0, J,
          fun i h1 h2 j hj => ?_⟩
        rcases Nat.lt_or_ge i (n + 1) with hi | hi
        · exact le_trans (hJ i h1 (by omega) j hj)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (qq_pos hβ1 j).le _))
        · have hieq : i = n + 1 := by omega
          subst hieq
          have hpwi : pw (2 * k) = 2 := by unfold pw; simp [Nat.mul_mod_right]
          rw [hk, hpwi]
          -- the Graeffe isolation
          have hiso := eSmall_graeffe_isolate β hk1 j
          -- bound the first term
          have hterm1 : ‖(-1 : ℂ) ^ k * eSmall β k (2 ^ (j + 1))‖ ≤ C * qq β j ^ 2 := by
            rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
            calc ‖eSmall β k (2 ^ (j + 1))‖ ≤ C * qq β (j + 1) ^ pw k :=
                  hJ k hk1 hkn (j + 1) (by omega)
              _ = C * qq β j ^ (2 * pw k) := by rw [qq_succ hβ1, ← pow_mul, Nat.mul_comm]
              _ ≤ C * qq β j ^ 2 :=
                  mul_le_mul_of_nonneg_left (qq_pow_le hβ1 (by have := pw_pos k; omega)) hC0
          -- bound the sum
          have hterm2 : ‖∑ p ∈ {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0},
              (-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j)‖
              ≤ (2 * k + 1) * (C ^ 2 * qq β j ^ 2) := by
            refine le_trans (norm_sum_le _ _) ?_
            have hb : ∀ p ∈ {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0},
                ‖(-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j)‖
                  ≤ C ^ 2 * qq β j ^ 2 := by
              intro p hp
              rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
              obtain ⟨hsum, hp1, hp2⟩ := hp
              have h1 : ‖eSmall β p.1 (2 ^ j)‖ ≤ C * qq β j ^ pw p.1 :=
                hJ p.1 (by omega) (by omega) j hj
              have h2 : ‖eSmall β p.2 (2 ^ j)‖ ≤ C * qq β j ^ pw p.2 :=
                hJ p.2 (by omega) (by omega) j hj
              have hpar2 : p.1 % 2 = p.2 % 2 := by omega
              have hple : qq β j ^ (pw p.1 + pw p.2) ≤ qq β j ^ 2 :=
                qq_pow_le hβ1 (two_le_pw_add _ _ hpar2)
              rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              calc ‖eSmall β p.1 (2 ^ j)‖ * ‖eSmall β p.2 (2 ^ j)‖
                  ≤ (C * qq β j ^ pw p.1) * (C * qq β j ^ pw p.2) := by
                    exact mul_le_mul h1 h2 (norm_nonneg _)
                      (mul_nonneg hC0 (pow_nonneg (qq_pos hβ1 j).le _))
                _ = C ^ 2 * qq β j ^ (pw p.1 + pw p.2) := by rw [pow_add]; ring
                _ ≤ C ^ 2 * qq β j ^ 2 :=
                    mul_le_mul_of_nonneg_left hple (by positivity)
            calc ∑ p ∈ {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0},
                  ‖(-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j)‖
                ≤ ∑ _p ∈ {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0},
                    C ^ 2 * qq β j ^ 2 := Finset.sum_le_sum hb
              _ = ({p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0}.card : ℝ)
                    * (C ^ 2 * qq β j ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (2 * k + 1) * (C ^ 2 * qq β j ^ 2) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  have := Finset.card_filter_le (Finset.antidiagonal (2 * k))
                    (fun p : ℕ × ℕ => p.1 ≠ 0 ∧ p.2 ≠ 0)
                  rw [Finset.Nat.card_antidiagonal] at this
                  exact_mod_cast this
          have hfin : 2 * ‖eSmall β (2 * k) (2 ^ j)‖ ≤ C * qq β j ^ 2
              + (2 * k + 1) * (C ^ 2 * qq β j ^ 2) := by
            have h := hiso
            have : ‖2 * eSmall β (2 * k) (2 ^ j)‖ ≤ C * qq β j ^ 2
                + (2 * k + 1) * (C ^ 2 * qq β j ^ 2) := by
              rw [h]
              exact le_trans (norm_sub_le _ _) (add_le_add hterm1 hterm2)
            rw [norm_mul, Complex.norm_ofNat] at this
            exact this
          have hq2 : (0 : ℝ) ≤ qq β j ^ 2 := by positivity
          have hle : (C + (2 * k + 1) * C ^ 2) / 2 ≤ max C ((C + (2 * k + 1) * C ^ 2) / 2) :=
            le_max_right _ _
          nlinarith [hfin, hq2, hle]
      · -- odd `n + 1 ≥ 3`: integrality forces `E_{n+1} = 0`
        have hnpar : n % 2 = 0 := by omega
        have hn1 : 1 ≤ n := hn
        obtain ⟨Ccr, hCcr⟩ : ∃ Ccr : ℝ,
            Ccr = ((Multiset.card (otherConj β)).choose (n + 1) : ℝ) := ⟨_, rfl⟩
        have hCcr0 : 0 ≤ Ccr := by rw [hCcr]; positivity
        -- the quantity that must vanish
        have hto : Tendsto (fun j : ℕ => (((n + 1).factorial : ℝ)) *
            (Ccr * (conjMax β ^ 2 ^ j) ^ (n + 1) + C * qq β j)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun j : ℕ => (conjMax β ^ 2 ^ j) ^ (n + 1)) atTop (𝓝 0) := by
            have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp tendsto_two_pow_atTop
            simpa using this.pow (n + 1)
          have h2 : Tendsto (fun j : ℕ => Ccr * (conjMax β ^ 2 ^ j) ^ (n + 1) + C * qq β j)
              atTop (𝓝 0) := by
            simpa using (h1.const_mul Ccr).add ((qq_tendsto hβ1).const_mul C)
          simpa using h2.const_mul (((n + 1).factorial : ℝ))
        obtain ⟨J', hJ'⟩ := (hto.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).and
          (eventually_ge_atTop J) |>.exists_forall_of_atTop
        refine ⟨C, hC0, J', fun i h1 h2 j hj => ?_⟩
        obtain ⟨hlt, hge⟩ := hJ' j hj
        rcases Nat.lt_or_ge i (n + 1) with hi | hi
        · exact hJ i h1 (by omega) j hge
        · have hieq : i = n + 1 := by omega
          subst hieq
          have hpwi : pw (n + 1) = 1 := by unfold pw; simp [hpar]
          rw [hpwi, pow_one]
          -- `E_{n+1}(2^j) = 0`
          have hEn : eFull β (n + 1) (2 ^ j) = 0 := by
            have hsplit := eFull_succ halg n (2 ^ j)
            have hbound : ‖((n + 1).factorial : ℂ) * eFull β (n + 1) (2 ^ j)‖ < 1 := by
              have hb1 : ‖eSmall β (n + 1) (2 ^ j)‖ ≤ Ccr * (conjMax β ^ 2 ^ j) ^ (n + 1) := by
                rw [hCcr]; exact norm_eSmall_le β (n + 1) (2 ^ j)
              have hb2 : ‖(β : ℂ) ^ 2 ^ j * eSmall β n (2 ^ j)‖ ≤ C * qq β j := by
                have hn2 : ‖eSmall β n (2 ^ j)‖ ≤ C * qq β j ^ 2 := by
                  have := hJ n hn1 le_rfl j hge
                  have hpwn : pw n = 2 := by unfold pw; simp [hnpar]
                  rwa [hpwn] at this
                have hnb : ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
                  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
                rw [norm_mul, hnb]
                have hqb := beta_mul_qq hβ1 j
                calc β ^ 2 ^ j * ‖eSmall β n (2 ^ j)‖
                    ≤ β ^ 2 ^ j * (C * qq β j ^ 2) :=
                      mul_le_mul_of_nonneg_left hn2 (by positivity)
                  _ = C * qq β j := by
                      have hthis : β ^ 2 ^ j * qq β j ^ 2 = qq β j := by
                        rw [pow_two, ← mul_assoc, hqb, one_mul]
                      calc β ^ 2 ^ j * (C * qq β j ^ 2)
                          = C * (β ^ 2 ^ j * qq β j ^ 2) := by ring
                        _ = C * qq β j := by rw [hthis]
              have hsum : ‖eFull β (n + 1) (2 ^ j)‖
                  ≤ Ccr * (conjMax β ^ 2 ^ j) ^ (n + 1) + C * qq β j := by
                rw [hsplit]
                exact le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
              rw [norm_mul, Complex.norm_natCast]
              calc ((n + 1).factorial : ℝ) * ‖eFull β (n + 1) (2 ^ j)‖
                  ≤ ((n + 1).factorial : ℝ) *
                      (Ccr * (conjMax β ^ 2 ^ j) ^ (n + 1) + C * qq β j) :=
                    mul_le_mul_of_nonneg_left hsum (by positivity)
                _ < 1 := hlt
            have := eq_zero_of_isRatInt_of_norm_lt_one
              (isRatInt_factorial_mul_eFull hβ (n + 1) (2 ^ j)) hbound
            have hfne : ((n + 1).factorial : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
            rcases mul_eq_zero.1 this with h | h
            · exact absurd h hfne
            · exact h
          -- hence `e_{n+1} = −β^N e_n`
          have hsplit := eFull_succ halg n (2 ^ j)
          rw [hEn] at hsplit
          have heq : eSmall β (n + 1) (2 ^ j) = -((β : ℂ) ^ 2 ^ j * eSmall β n (2 ^ j)) := by
            linear_combination -hsplit
          rw [heq, norm_neg, norm_mul]
          have hnb : ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
          rw [hnb]
          have hn2 : ‖eSmall β n (2 ^ j)‖ ≤ C * qq β j ^ 2 := by
            have := hJ n hn1 le_rfl j hge
            have hpwn : pw n = 2 := by unfold pw; simp [hnpar]
            rwa [hpwn] at this
          have hqb := beta_mul_qq hβ1 j
          calc β ^ 2 ^ j * ‖eSmall β n (2 ^ j)‖
              ≤ β ^ 2 ^ j * (C * qq β j ^ 2) := mul_le_mul_of_nonneg_left hn2 (by positivity)
            _ = C * qq β j := by
                have hthis : β ^ 2 ^ j * qq β j ^ 2 = qq β j := by
                  rw [pow_two, ← mul_assoc, hqb, one_mul]
                calc β ^ 2 ^ j * (C * qq β j ^ 2)
                    = C * (β ^ 2 ^ j * qq β j ^ 2) := by ring
                  _ = C * qq β j := by rw [hthis]

end LeanFormalizations.Transcendence.Dubickas
