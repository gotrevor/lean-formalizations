/-
# Saito §3 for a general exponent `c ≥ 3`: existence of `ξ_c`

Generalises `primeBetweenCubes_of_BHP` and `exists_least_of_exists` (`Mills/Irrational.lean`,
`Mills/Basic.lean`) from `c = 3` to arbitrary integer `c ≥ 3`, giving Saito's Corollary 3.4:
`ξ_c` exists.  The `c = 3` statements are untouched.

The only arithmetic that changes: the Baker–Harman–Pintz window `[x, x + x^(21/40)]` at
`x = n^c` has width `n^(21c/40)`, which must fit inside the gap `(n+1)^c − n^c ≥ c·n^(c−1)`.
That needs `21c/40 ≤ c − 1`, i.e. `c ≥ 40/19`, so every `c ≥ 3` works (for `c = 3` this is the
familiar `63/40 ≤ 2`).  The gap bound itself is `pow_succ_ge_add_mul`, proved by induction.
-/
import LeanFormalizations.NumberTheory.Mills.BasicC
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- `nᶜ⁺¹ + (c+1)·nᶜ ≤ (n+1)ᶜ⁺¹` — the first two binomial terms. -/
theorem pow_succ_ge_add_mul (n : ℕ) : ∀ c : ℕ, n ^ (c + 1) + (c + 1) * n ^ c ≤ (n + 1) ^ (c + 1)
  | 0 => by ring_nf; omega
  | c + 1 => by
      have ih := pow_succ_ge_add_mul n c
      have h : (n ^ (c + 1) + (c + 1) * n ^ c) * (n + 1) ≤ (n + 1) ^ (c + 1) * (n + 1) :=
        Nat.mul_le_mul_right _ ih
      have hexp : (n + 1) ^ (c + 1) * (n + 1) = (n + 1) ^ (c + 2) := by ring
      have hlo : (n ^ (c + 1) + (c + 1) * n ^ c) * (n + 1)
          = n ^ (c + 2) + (c + 2) * n ^ (c + 1) + (c + 1) * n ^ c := by ring
      show n ^ (c + 2) + (c + 2) * n ^ (c + 1) ≤ (n + 1) ^ (c + 2)
      calc n ^ (c + 2) + (c + 2) * n ^ (c + 1)
          ≤ n ^ (c + 2) + (c + 2) * n ^ (c + 1) + (c + 1) * n ^ c := Nat.le_add_right _ _
        _ = (n ^ (c + 1) + (c + 1) * n ^ c) * (n + 1) := hlo.symm
        _ ≤ (n + 1) ^ (c + 1) * (n + 1) := h
        _ = (n + 1) ^ (c + 2) := hexp

/-- **Saito Corollary 3.4's analytic input for exponent `c ≥ 3`**: Baker–Harman–Pintz puts a
prime strictly between `nᶜ` and `(n+1)ᶜ` for all large `n`. -/
theorem primeBetweenPows_of_BHP (h : BakerHarmanPintz2001) {c : ℕ} (hc : 3 ≤ c) :
    ∃ N, PrimeBetweenPowsFrom c N := by
  obtain ⟨d₀, hd₀, X, hX⟩ := h
  refine ⟨max 2 (⌈X⌉₊ + 1), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn2r : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by linarith
  have hnX : X ≤ (n:ℝ) := by
    have h1 : ⌈X⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hcl : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast (show ⌈X⌉₊ ≤ n by omega)
    linarith
  set x : ℝ := (n:ℝ) ^ c with hx
  have hxpos : (0:ℝ) < x := by rw [hx]; positivity
  have hx2 : (2:ℝ) ≤ x := by
    have h1 : (2:ℝ) ^ c ≤ (n:ℝ) ^ c := pow_le_pow_left₀ (by norm_num) hn2r c
    have h2 : (2:ℝ) ^ (1:ℕ) ≤ (2:ℝ) ^ c := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_one] at h2; rw [hx]; linarith
  have hx1 : (1:ℝ) < x := by linarith
  have hxn : (n:ℝ) ≤ x := by
    have h1 : (n:ℝ) ^ (1:ℕ) ≤ (n:ℝ) ^ c := pow_le_pow_right₀ hn1r (by omega)
    rw [pow_one] at h1; rw [hx]; linarith
  have hcount := hX x (le_trans hnX hxn)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  -- the BHP window fits: `x^(21/40) ≤ n^(c−1)`
  have hsmall : x ^ ((21:ℝ) / 40) ≤ (n:ℝ) ^ (c - 1) := by
    have hxr : x = (n:ℝ) ^ ((c:ℕ) : ℝ) := by rw [hx, Real.rpow_natCast]
    rw [hxr, ← Real.rpow_mul (by linarith)]
    rw [show ((n:ℝ) ^ (c - 1)) = (n:ℝ) ^ (((c - 1 : ℕ)) : ℝ) by rw [Real.rpow_natCast]]
    refine Real.rpow_le_rpow_of_exponent_le hn1r ?_
    have hcr : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have : ((c - 1 : ℕ) : ℝ) = (c:ℝ) - 1 := by
      have : 1 ≤ c := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [this]; linarith
  -- a prime in the window
  have hcpos : 0 < primesIn x (x + x ^ ((21:ℝ) / 40)) := by
    rcases Nat.eq_zero_or_pos (primesIn x (x + x ^ ((21:ℝ) / 40))) with h0 | h0
    · rw [h0] at hcount
      have : (0:ℝ) < d₀ * x ^ ((21:ℝ) / 40) / Real.log x :=
        div_pos (mul_pos hd₀ (Real.rpow_pos_of_pos hxpos _)) hlogx
      norm_num at hcount
      linarith
    · exact h0
  unfold primesIn at hcpos
  obtain ⟨p, hpmem⟩ := Finset.card_pos.1 hcpos
  simp only [Finset.mem_filter, Finset.mem_Icc] at hpmem
  obtain ⟨⟨hplo, hphi⟩, hp⟩ := hpmem
  have hceil : ⌈x⌉₊ = n ^ c := by
    rw [hx, show ((n:ℝ)) ^ c = ((n ^ c : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [hceil] at hplo
  refine ⟨p, hp, ?_, ?_⟩
  · -- `nᶜ` itself is composite
    refine lt_of_le_of_ne hplo ?_
    intro hEq
    rw [← hEq] at hp
    have hdvd : n ∣ n ^ c := dvd_pow_self n (by omega)
    rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | h1
    · omega
    · have hltc : n ^ 1 < n ^ c := Nat.pow_lt_pow_right hn2 (by omega)
      rw [pow_one, ← h1] at hltc
      exact absurd hltc (lt_irrefl _)
  · -- `p ≤ nᶜ + n^(c−1) < (n+1)ᶜ`
    have hpr : (p : ℝ) ≤ x + x ^ ((21:ℝ) / 40) := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast hphi
    -- the nat gap bound
    obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := ⟨c - 1, by omega⟩
    have hgap : n ^ (b + 1) + (b + 1) * n ^ b ≤ (n + 1) ^ (b + 1) := pow_succ_ge_add_mul n b
    have hb : 3 ≤ b + 1 := hc
    have hbpos : 1 ≤ n ^ b := Nat.one_le_pow _ _ (by omega)
    have hnatlt : n ^ (b + 1) + n ^ b < (n + 1) ^ (b + 1) := by nlinarith [hgap, hbpos]
    have hlt : (p : ℝ) < (((n + 1) ^ (b + 1) : ℕ) : ℝ) := by
      have hsm : x ^ ((21:ℝ) / 40) ≤ (n:ℝ) ^ b := by
        simpa using hsmall
      have hcast : (((n ^ (b+1) + n ^ b : ℕ)) : ℝ) < (((n + 1) ^ (b + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnatlt
      push_cast at hcast ⊢
      have hxe : x = (n:ℝ) ^ (b + 1) := hx
      linarith
    exact_mod_cast hlt

/-- **A least Mills number for exponent `c` exists** as soon as one does.  Unconditional; the
`c = 3` case is `exists_least_of_exists`.  The only change is the explicit lower bound, which
for general `c` is `2^(1/c)` rather than the hand-computed `5/4`. -/
theorem exists_leastC_of_exists {c : ℕ} (hc : 2 ≤ c)
    (h : ∃ A : ℝ, A > 1 ∧ (∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊)) :
    ∃ A : ℝ, IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (c ^ (n : ℕ))⌋₊} A := by
  set S : Set ℝ := {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (c ^ (n : ℕ))⌋₊} with hS
  obtain ⟨A₀, hA₀1, hA₀⟩ := h
  have hne : S.Nonempty := ⟨A₀, hA₀1, hA₀⟩
  have hcpos : (0:ℝ) < (c:ℝ) := by
    have : (2:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    linarith
  set L : ℝ := (2:ℝ) ^ ((c:ℝ)⁻¹) with hL
  have hL1 : 1 < L := by
    rw [hL]
    exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2 (Or.inl ⟨by norm_num, by positivity⟩)
  have hLc : L ^ c = 2 := by
    rw [hL, ← Real.rpow_natCast ((2:ℝ) ^ ((c:ℝ)⁻¹)) c, ← Real.rpow_mul (by norm_num)]
    rw [inv_mul_cancel₀ (ne_of_gt hcpos), Real.rpow_one]
  have hlb : ∀ x ∈ S, L ≤ x := by
    rintro x ⟨hx1, hx⟩
    have hp := hx 1
    have hpow : ((2:ℕ) : ℝ) ≤ x ^ (c ^ ((1 : ℕ+) : ℕ)) := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast (Nat.prime_iff.mpr hp).two_le
    rw [show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_one] at hpow
    by_contra hcon
    push Not at hcon
    have : x ^ c < L ^ c := pow_lt_pow_left₀ hcon (by linarith) (by omega)
    rw [hLc] at this
    norm_num at hpow
    linarith
  have hbdd : BddBelow S := ⟨L, hlb⟩
  set m : ℝ := sInf S with hm
  have hmlb : L ≤ m := le_csInf hne hlb
  have hm1 : m > 1 := by linarith
  have hmpos : (0:ℝ) ≤ m := by linarith
  refine ⟨m, ⟨hm1, fun n => ?_⟩, fun x hx => csInf_le hbdd hx⟩
  set k : ℕ := c ^ ((n : ℕ)) with hk
  set q : ℕ := ⌊m ^ k⌋₊ with hq
  have hqle : (q : ℝ) ≤ m ^ k := Nat.floor_le (by positivity)
  have hqlt : m ^ k < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hopen : IsOpen {x : ℝ | x ^ k < (q : ℝ) + 1} :=
    isOpen_lt (continuous_pow k) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen m hqlt
  obtain ⟨A, hAS, hAlt⟩ := exists_lt_of_csInf_lt hne (show m < m + δ by linarith)
  have hmA : m ≤ A := csInf_le hbdd hAS
  have hAmem : A ∈ {x : ℝ | x ^ k < (q : ℝ) + 1} := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hAup : A ^ k < (q : ℝ) + 1 := hAmem
  have hAlo : (q : ℝ) ≤ A ^ k := le_trans hqle (pow_le_pow_left₀ hmpos hmA k)
  have hfl : ⌊A ^ k⌋₊ = q := by
    rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg q) hAlo)]
    exact ⟨hAlo, hAup⟩
  have := hAS.2 n
  rw [← hk, hfl] at this
  exact this

/-- **Saito Corollary 3.4**: a Mills number for exponent `c ≥ 3` exists, from BHP. -/
theorem exists_millsC_of_BHP (h : BakerHarmanPintz2001) {c : ℕ} (hc : 3 ≤ c) :
    ∃ A : ℝ, A > 1 ∧ (∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) :=
  let ⟨_, hN⟩ := primeBetweenPows_of_BHP h hc
  exists_millsC_of_primeBetweenPows (by omega) hN

/-- **`ξ_c` exists for every integer `c ≥ 3`** (Saito Corollary 3.4), from Baker–Harman–Pintz. -/
theorem exists_leastMillsC_of_BHP (h : BakerHarmanPintz2001) {c : ℕ} (hc : 3 ≤ c) :
    ∃ A : ℝ, IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (c ^ (n : ℕ))⌋₊} A :=
  exists_leastC_of_exists (by omega) (exists_millsC_of_BHP h hc)

end LeanFormalizations.Mills
