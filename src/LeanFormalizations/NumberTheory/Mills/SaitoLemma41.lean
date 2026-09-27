/-
# Saito §4, Lemma 4.1 assembled (the case `μ > 1`, i.e. `b ≥ 5`)

`transcendental_of_decay` below is the whole of Saito's Lemma 4.1 in the regime where the
Claim of `Mills/SaitoPisot.lean` closes outright: `(ℓ−1)μ ≤ 1` together with `ℓ ≥ 2` and
`μ > 1` is a contradiction, so `ξ` cannot be algebraic.

It takes from §3 exactly one hypothesis — Saito's (4.1)+(4.2) combined,

    |A^(cᵏ) − round(A^(cᵏ))| ≤ K · A^(−μ cᵏ)   for all large `k`,

with `μ = b θ_b = 19c/40 − 1` — plus the statement that no `A^(cᵐ)` (`m ≥ 1`) is an integer,
which for a Mills number is immediate from primality of the digits.

## The two places the argument is delicate

* **Dubickas's dichotomy is applied at `s k = c^(k+1)`.**  Its second alternative is an
  `exp(−ε s k)` lower bound for *every* `ε > 0`; our upper bound is `K·A^(−μ c^(k+1))`
  `= K·exp(−μ log A · s k)`, so taking `ε := μ log A / 2` kills it (the constant `K` is absorbed
  because `exp(ε s k) → ∞`).  Hence some `β = A^(c^(m+1))` is Pisot.
* **The decay for `β` only holds along `n = c^j`, not for all `n`.**  That is why
  `pisot_degree_bound` and `le_of_pow_le_const_mul_pow` take `∃ᶠ` rather than `∀ᶠ`: the
  Dubickas–Corvaja–Zannier gap bound holds for all large `n`, and a *subsequence* suffices to
  conclude `|β₂| ≤ β^(−μ)`.  Along that subsequence `t_n = round(β^n)`, because the conjugate
  power sum is `< 1/2` in modulus once `n` is large (`conjMax_lt_one`, `norm_conjPowSum_le`).
-/
import LeanFormalizations.NumberTheory.Mills.SaitoPisot

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature Filter Polynomial

/-- **Saito (2024), Lemma 4.1, case `μ > 1`.**  A real `A > 1` whose `c`-power digits
approximate it at rate `A^(−μ cᵏ)` with `μ > 1`, and none of whose powers `A^(cᵐ)` (`m ≥ 1`) is
an integer, is transcendental. -/
theorem transcendental_of_decay (hD : Dubickas2022) (hG : Dubickas2022PisotGap)
    {A : ℝ} (hA1 : 1 < A) {c : ℕ} (hc : 2 ≤ c) {μ K : ℝ} (hμ : 1 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ k : ℕ in atTop,
      |A ^ (c ^ k) - (round (A ^ (c ^ k)) : ℝ)| ≤ K * (A ^ (-(μ * (c ^ k : ℕ))) : ℝ))
    (hnotint : ∀ m : ℕ, 1 ≤ m → ∀ t : ℤ, A ^ (c ^ m) ≠ (t : ℝ)) :
    Transcendental ℚ A := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hμ0 : (0 : ℝ) < μ := by linarith
  intro halg
  -- the exponent sequence Dubickas is applied at
  set s : ℕ → ℕ := fun k => c ^ (k + 1) with hs
  have hsmono : StrictMono s := by
    intro i j hij
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hs0 : 0 < s 0 := Nat.pow_pos (by omega)
  -- `A ^ (c^k) = A ^ (c^k : ℝ)` bookkeeping
  have hrpow : ∀ k : ℕ, (A ^ ((c : ℕ) ^ k) : ℝ) = A ^ (((c ^ k : ℕ) : ℝ)) := by
    intro k; rw [Real.rpow_natCast]
  rcases hD A halg hA1 1 one_pos s hsmono hs0 with hpisot | hsep
  · -- ### the Pisot branch: derive the degree contradiction
    obtain ⟨m, hβ⟩ := hpisot
    set β : ℝ := A ^ s m with hβdef
    have hsm : s m = c ^ (m + 1) := rfl
    have hβpow : ∀ j : ℕ, β ^ (c ^ j) = A ^ (c ^ (m + 1 + j)) := by
      intro j
      rw [hβdef, hsm, ← pow_mul, ← pow_add]
    have hnd : 2 ≤ (minpoly ℚ β).natDegree := by
      refine pisot_two_le_natDegree hβ fun t => ?_
      rw [hβdef, hsm]
      exact hnotint (m + 1) (by omega) t
    -- the conjugate power sum is eventually `< 1/2`, so `t_n = round (βⁿ)`
    have hmax := conjMax_lt_one hβ
    have hmax0 := conjMax_nonneg β
    have htend : Filter.Tendsto
        (fun n : ℕ => (Multiset.card (otherConj β) : ℝ) * conjMax β ^ n) atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hmax0 hmax
      simpa using this.const_mul (Multiset.card (otherConj β) : ℝ)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hdecay
    -- the frequent decay hypothesis for `β`
    have hfreq : ∃ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ ≤ K * (β ^ (-(μ * n)) : ℝ) := by
      rw [frequently_atTop]
      intro a
      refine ⟨c ^ (max a (max N₁ k₀)), ?_, ?_⟩
      · exact le_trans (le_max_left _ _) (Nat.lt_pow_self (by omega)).le
      · sorry
    have hclaim := pisot_degree_bound hG hβ hnd hμ0 hK hfreq
    have hcard : 1 ≤ Multiset.card (otherConj β) := by
      have := card_otherConj_add_one (β := β) (hβ.2.1.tower_top)
      omega
    have hcardR : (1 : ℝ) ≤ (Multiset.card (otherConj β) : ℝ) := by exact_mod_cast hcard
    nlinarith [hclaim, hcardR, hμ0]
  · -- ### the separation branch: contradicted by the decay hypothesis
    set ε : ℝ := μ * Real.log A / 2 with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨k₀, hk₀⟩ := hsep ε hε0
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 hdecay
    set k : ℕ := max k₀ (max k₁ (⌈K / ε⌉₊ + 1)) with hk
    have hkk₀ : k₀ ≤ k := le_max_left _ _
    have hkk₁ : k₁ ≤ k + 1 := by
      have h' : k₁ ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    have hkK : ⌈K / ε⌉₊ + 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have h1 := hk₀ k hkk₀
    have h2 := hk₁ (k + 1) hkk₁
    set N : ℕ := c ^ (k + 1) with hN
    have hNk : k + 1 ≤ N := (Nat.lt_pow_self (by omega)).le
    have hNR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNk
    have hsk : s k = N := rfl
    rw [hsk] at h1
    simp only [Nat.cast_one, one_mul] at h1
    -- rewrite the rpow bound as an exponential
    have hrw : (A ^ (-(μ * (N : ℝ))) : ℝ) = Real.exp (-(2 * ε * N)) := by
      rw [Real.rpow_def_of_pos hA0, hε]; ring_nf
    rw [hrw] at h2
    -- `exp(−εN) < K exp(−2εN)` forces `exp(εN) < K`
    have hchain : Real.exp (-(ε * N)) < K * Real.exp (-(2 * ε * N)) := lt_of_lt_of_le h1 h2
    have hexp : Real.exp (ε * N) < K := by
      have h := mul_lt_mul_of_pos_right hchain (Real.exp_pos (2 * ε * (N:ℝ)))
      have e1 : Real.exp (-(ε * (N:ℝ))) * Real.exp (2 * ε * (N:ℝ)) = Real.exp (ε * (N:ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : K * Real.exp (-(2 * ε * (N:ℝ))) * Real.exp (2 * ε * (N:ℝ)) = K := by
        rw [mul_assoc, ← Real.exp_add, show -(2 * ε * (N:ℝ)) + 2 * ε * (N:ℝ) = 0 by ring,
          Real.exp_zero, mul_one]
      rwa [e1, e2] at h
    -- but `exp(εN) ≥ 1 + εN > K`
    have hKlt : K < ε * N := by
      have h3 : (K / ε : ℝ) ≤ (⌈K / ε⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : ((⌈K / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
        have : (⌈K / ε⌉₊ : ℕ) + 1 ≤ k := hkK
        exact_mod_cast this
      have h5 : (K / ε : ℝ) < (N : ℝ) := by linarith
      calc K = ε * (K / ε) := by field_simp
        _ < ε * N := by exact mul_lt_mul_of_pos_left h5 hε0
    have := Real.add_one_le_exp (ε * (N : ℝ))
    linarith

end LeanFormalizations.Mills
