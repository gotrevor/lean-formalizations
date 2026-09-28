/-
# The limit of the `b`-sequence and the conclusion `E₂ ∈ {0, 1}`

Steps 4–5 of the Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`), assembled.

Hypothesis: `β` is Pisot and `E₂(2^j) = z` is *constant* for all large `j` — which is exactly
what the Dubickas recursion `y_{n+1} = y_n² − c` supplies, with `z = c/2`.

Conclusion: `z = 0 ∨ z = 1`, i.e. `c ∈ {0, 2}`, **with no appeal to Lemma 8**.

Route: `E₂ = e₂ + β^N e₁` bounds `‖e₁‖ ≤ U q_j` (the base of the parity-weight induction); then
`bb k ·` is bounded (`norm_AA_le`) and satisfies the recursion up to `O(q_j²)`
(`bb_rec_approx`), so by induction every `bb k ·` converges; the limits satisfy the exact
recursion of `eq_zero_or_one_of_bRec_finite_support`, with `b 0 = −z` and finite support because
`e_n ≡ 0` for `n > deg β − 1`.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasBSeq
import LeanFormalizations.NumberTheory.Transcendence.DubickasBRec

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Transcendence LeanFormalizations.Mills
open LeanFormalizations.Literature

variable {β : ℝ}

/-- From the constancy of `E₂`, the base bound `‖e₁(2^j)‖ ≤ U q_j`. -/
theorem base_bound_of_eFull_two (hβ : IsPisot β) {z : ℂ} {J₀ : ℕ}
    (hE2 : ∀ j ≥ J₀, eFull β 2 (2 ^ j) = z) :
    ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖
      ≤ (‖z‖ + ((Multiset.card (otherConj β)).choose 2 : ℝ)) * qq β j := by
  intro j hj
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hsplit := eFull_succ halg 1 (2 ^ j)
  rw [hE2 j hj] at hsplit
  have he2 : ‖eSmall β 2 (2 ^ j)‖ ≤ ((Multiset.card (otherConj β)).choose 2 : ℝ) := by
    refine le_trans (norm_eSmall_le β 2 (2 ^ j)) ?_
    have h1 : (conjMax β ^ 2 ^ j) ^ 2 ≤ 1 := by
      have h2 : conjMax β ^ 2 ^ j ≤ 1 := pow_le_one₀ (conjMax_nonneg β) (conjMax_lt_one hβ).le
      nlinarith [pow_nonneg (conjMax_nonneg β) (2 ^ j)]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((Multiset.card (otherConj β)).choose 2),
      pow_nonneg (pow_nonneg (conjMax_nonneg β) (2 ^ j)) 2]
  have hnb : ‖(β : ℂ) ^ 2 ^ j‖ = β ^ 2 ^ j := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hBe : (β : ℂ) ^ 2 ^ j * eSmall β 1 (2 ^ j) = z - eSmall β 2 (2 ^ j) := by
    linear_combination -hsplit
  have hnorm : β ^ 2 ^ j * ‖eSmall β 1 (2 ^ j)‖ ≤ ‖z‖ + ((Multiset.card (otherConj β)).choose 2 : ℝ) := by
    have : β ^ 2 ^ j * ‖eSmall β 1 (2 ^ j)‖ = ‖(β : ℂ) ^ 2 ^ j * eSmall β 1 (2 ^ j)‖ := by
      rw [norm_mul, hnb]
    rw [this, hBe]
    exact le_trans (norm_sub_le _ _) (by gcongr)
  have hqb := beta_mul_qq hβ1 j
  nlinarith [hnorm, qq_pos hβ1 j, norm_nonneg (eSmall β 1 (2 ^ j)), hqb]

/-- `bb 0 j = e₂(2^j) − z`, hence `bb 0 · → −z`. -/
theorem bb_zero_tendsto (hβ : IsPisot β) {z : ℂ} {J₀ : ℕ}
    (hE2 : ∀ j ≥ J₀, eFull β 2 (2 ^ j) = z) :
    Tendsto (fun j => bb β 0 j) atTop (𝓝 (-z)) := by
  have hβ1 : 1 < β := hβ.1
  have halg : IsIntegral ℚ β := hβ.2.1.tower_top
  have hev : ∀ j ≥ J₀, bb β 0 j = eSmall β 2 (2 ^ j) - z := by
    intro j hj
    have hsplit := eFull_succ halg 1 (2 ^ j)
    rw [hE2 j hj] at hsplit
    rw [bb, AA, pw_odd 0]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one]
    linear_combination hsplit
  have hto : Tendsto (fun j => eSmall β 2 (2 ^ j) - z) atTop (𝓝 (0 - z)) := by
    refine Tendsto.sub ?_ tendsto_const_nhds
    refine squeeze_zero_norm' (a := fun j => ((Multiset.card (otherConj β)).choose 2 : ℝ)
      * (conjMax β ^ 2 ^ j) ^ 2) (Eventually.of_forall fun j => norm_eSmall_le β 2 (2 ^ j)) ?_
    have h1 : Tendsto (fun j : ℕ => (conjMax β ^ 2 ^ j) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (conjMax_nonneg β)
        (conjMax_lt_one hβ)).comp tendsto_two_pow_atTop
      simpa using this.pow 2
    simpa using h1.const_mul (((Multiset.card (otherConj β)).choose 2 : ℝ))
  rw [zero_sub] at hto
  exact hto.congr' (eventually_atTop.2 ⟨J₀, fun j hj => (hev j hj).symm⟩)

/-- **Every `bb k ·` converges.** -/
theorem bb_tendsto_exists (hβ : IsPisot β) {z : ℂ} {J₀ : ℕ}
    (hE2 : ∀ j ≥ J₀, eFull β 2 (2 ^ j) = z) (k : ℕ) :
    ∃ f : ℕ → ℂ, ∀ u ≤ k, Tendsto (fun j => bb β u j) atTop (𝓝 (f u)) := by
  classical
  have hβ1 : 1 < β := hβ.1
  have hbase := base_bound_of_eFull_two hβ hE2
  induction k with
  | zero =>
      exact ⟨fun _ => -z, fun u hu => by
        obtain rfl : u = 0 := by omega
        exact bb_zero_tendsto hβ hE2⟩
  | succ k ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨M, hM0, J, hJ⟩ := bb_rec_approx hβ hbase (k := k + 1) (by omega)
      -- the right-hand side converges
      set R : ℂ := (∑ p ∈ Finset.antidiagonal k, f p.1 * f p.2)
        + (if (k + 1) % 2 = 1 then f (k / 2) else 0) with hRdef
      have hRto : Tendsto (fun j => (∑ p ∈ Finset.antidiagonal k, bb β p.1 j * bb β p.2 j)
          + (if (k + 1) % 2 = 1 then bb β (k / 2) (j + 1) else 0)) atTop (𝓝 R) := by
        refine Tendsto.add ?_ ?_
        · refine tendsto_finsetSum _ fun p hp => ?_
          rw [Finset.mem_antidiagonal] at hp
          exact (hf p.1 (by omega)).mul (hf p.2 (by omega))
        · by_cases hpar : (k + 1) % 2 = 1
          · simp only [if_pos hpar]
            exact (hf (k / 2) (by omega)).comp (tendsto_add_atTop_nat 1)
          · simp only [if_neg hpar]; exact tendsto_const_nhds
      -- the error tends to zero
      have herr : Tendsto (fun j => 2 * bb β (k + 1) j
          - ((∑ p ∈ Finset.antidiagonal k, bb β p.1 j * bb β p.2 j)
            + (if (k + 1) % 2 = 1 then bb β (k / 2) (j + 1) else 0))) atTop (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun j => M * qq β j ^ 2)
          (eventually_atTop.2 ⟨J, fun j hj => ?_⟩) ?_
        · have := hJ j hj
          simpa using this
        · have h1 : Tendsto (fun j : ℕ => qq β j ^ 2) atTop (𝓝 0) := by
            simpa using (qq_tendsto hβ1).pow 2
          simpa using h1.const_mul M
      have h2to : Tendsto (fun j => 2 * bb β (k + 1) j) atTop (𝓝 (0 + R)) := by
        have := herr.add hRto
        simpa using this
      have hfin : Tendsto (fun j => bb β (k + 1) j) atTop (𝓝 (R / 2)) := by
        have := h2to.div_const 2
        rw [zero_add] at this
        exact this.congr fun j => by ring
      refine ⟨Function.update f (k + 1) (R / 2), fun u hu => ?_⟩
      rcases Nat.lt_or_ge u (k + 1) with hlt | hge
      · rw [Function.update_of_ne (by omega)]
        exact hf u (by omega)
      · obtain rfl : u = k + 1 := by omega
        rw [Function.update_self]
        exact hfin

/-- **The no-gap conclusion**: a Pisot `β` whose `E₂(2^j)` is eventually constant equal to `z`
forces `z = 0` or `z = 1`. -/
theorem eFull_two_const_eq_zero_or_one (hβ : IsPisot β) {z : ℂ} {J₀ : ℕ}
    (hE2 : ∀ j ≥ J₀, eFull β 2 (2 ^ j) = z) : z = 0 ∨ z = 1 := by
  classical
  have hβ1 : 1 < β := hβ.1
  have hbase := base_bound_of_eFull_two hβ hE2
  -- choose the limits coherently
  have hex : ∀ k : ℕ, ∃ w : ℂ, Tendsto (fun j => bb β k j) atTop (𝓝 w) := by
    intro k
    obtain ⟨f, hf⟩ := bb_tendsto_exists hβ hE2 k
    exact ⟨f k, hf k le_rfl⟩
  choose b hb using hex
  -- `b 0 = −z`
  have hb0 : b 0 = -z := tendsto_nhds_unique (hb 0) (bb_zero_tendsto hβ hE2)
  -- the limits satisfy the recursion
  have hrec : ∀ n : ℕ, 2 * b (n + 1)
      = (∑ p ∈ Finset.antidiagonal n, b p.1 * b p.2)
        + (if n % 2 = 0 then b (n / 2) else 0) := by
    intro n
    obtain ⟨M, hM0, J, hJ⟩ := bb_rec_approx hβ hbase (k := n + 1) (by omega)
    have hparity : ∀ j : ℕ, (if (n + 1) % 2 = 1 then bb β (n / 2) (j + 1) else 0)
        = (if n % 2 = 0 then bb β (n / 2) (j + 1) else 0) := by
      intro j
      by_cases h : n % 2 = 0
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    set R : ℂ := (∑ p ∈ Finset.antidiagonal n, b p.1 * b p.2)
      + (if n % 2 = 0 then b (n / 2) else 0) with hRdef
    have hRto : Tendsto (fun j => (∑ p ∈ Finset.antidiagonal n, bb β p.1 j * bb β p.2 j)
        + (if n % 2 = 0 then bb β (n / 2) (j + 1) else 0)) atTop (𝓝 R) := by
      refine Tendsto.add (tendsto_finsetSum _ fun p _ => (hb p.1).mul (hb p.2)) ?_
      by_cases hpar : n % 2 = 0
      · simp only [if_pos hpar]
        exact (hb (n / 2)).comp (tendsto_add_atTop_nat 1)
      · simp only [if_neg hpar]; exact tendsto_const_nhds
    have herr : Tendsto (fun j => 2 * bb β (n + 1) j
        - ((∑ p ∈ Finset.antidiagonal n, bb β p.1 j * bb β p.2 j)
          + (if n % 2 = 0 then bb β (n / 2) (j + 1) else 0))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun j => M * qq β j ^ 2)
        (eventually_atTop.2 ⟨J, fun j hj => ?_⟩) ?_
      · have h := hJ j hj
        simp only [Nat.add_sub_cancel] at h
        rw [hparity j] at h
        simpa using h
      · have h1 : Tendsto (fun j : ℕ => qq β j ^ 2) atTop (𝓝 0) := by
          simpa using (qq_tendsto hβ1).pow 2
        simpa using h1.const_mul M
    have h2to : Tendsto (fun j => 2 * bb β (n + 1) j) atTop (𝓝 (0 + R)) := by
      have := herr.add hRto
      simpa using this
    rw [zero_add] at h2to
    have h2b : Tendsto (fun j => 2 * bb β (n + 1) j) atTop (𝓝 (2 * b (n + 1))) :=
      (hb (n + 1)).const_mul 2
    exact tendsto_nhds_unique h2b h2to
  -- finite support
  have hfin : ∃ K, ∀ k ≥ K, b k = 0 := by
    refine ⟨Multiset.card (otherConj β) + 1, fun k hk => ?_⟩
    have hz : ∀ j, bb β k j = 0 := by
      intro j
      rw [bb, AA_eq_zero_of_card_lt β (by omega) j, neg_zero]
    refine tendsto_nhds_unique (hb k) ?_
    simpa [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact eq_zero_or_one_of_bRec_finite_support hb0 hrec hfin

end LeanFormalizations.Transcendence.Dubickas
