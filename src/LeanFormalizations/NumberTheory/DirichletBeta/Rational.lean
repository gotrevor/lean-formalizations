/-
# The rational function `R_n` and the linear form `r_n`

Zudilin 2019 (arXiv:1804.09922) §2, in the elementary rendering of his SIGMA 2018 paper.  For
odd `s ≥ 3` and even `n`,

    R_n(t) = 2^{6n} · (n!)^{s-3} · (2t+n) · ∏_{j=1}^{3n} (t - n + j - ½) / ∏_{j=0}^{n} (t+j)^s
    r_n    = Σ_{ν ≥ 1} (-1)^ν R_n(ν - ½).

The terms with `ν ≤ n` vanish (the `j = n+1-ν` factor of the numerator is `0`), so the sum really
starts at `ν = n+1`.  Substituting `ν = n + 1 + u` clears every subtraction and turns the
numerator product into a ratio of factorials:

    2t + n              = 3n + 1 + 2u
    ∏_{j=1}^{3n}(…)     = (u + 3n)! / u!
    t + j               = (2(n+1+u+j) - 1)/2.

`Rval` below is that shifted form — the one this development freezes.  ✅ Verified numerically
against the source form (termwise **exactly**, and as a sum to 12 digits) at
`(n,s) ∈ {(2,5),(4,5),(2,7),(4,7),(6,7),(2,21),(4,21),(6,21)}`:
`papers/catalan-beta-rval-check.py`.

Rates (`papers/catalan-beta-ledger.py`, `n = 40`): for `s = 21`,
`log|r_n|^{1/n} → -21.657`, while `d_n^{1/n} → e`.  Since `21 < 21.657`, the ledger closes.
-/
import Mathlib

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- `R_n(ν - ½)` at `ν = n + 1 + u`, in the subtraction-free shifted form.  Frozen: every
downstream statement is about this function.

`Rval s n u = 2^{6n} (n!)^{s-3} (3n+1+2u) · (u+3n)!/u! / ∏_{j=0}^{n} ((2(n+1+u+j) - 1)/2)^s`. -/
noncomputable def Rval (s n u : ℕ) : ℚ :=
  2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 + 2 * u : ℕ) : ℚ)
    * (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ)
    / ∏ j ∈ range (n + 1), ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s

/-- Every term of the shifted series is strictly positive. -/
theorem Rval_pos (s n u : ℕ) : 0 < Rval s n u := by
  unfold Rval
  have hf : ∀ j ∈ range (n + 1), (0 : ℚ) < ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s := by
    intro j _
    have h1 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℚ) ≤ u := Nat.cast_nonneg u
    have h3 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℚ) < 2 * ((n : ℚ) + 1 + u + j) - 1 := by linarith
    positivity
  have hp := Finset.prod_pos hf
  positivity

/-- `(u+m)!/u! = (u+1)⋯(u+m) ≤ (u+m)^m`. -/
lemma factorial_ratio_le (u m : ℕ) :
    (Nat.factorial (u + m) : ℚ) / (Nat.factorial u : ℚ) ≤ ((u + m : ℕ) : ℚ) ^ m := by
  rw [div_le_iff₀ (by positivity)]
  have h := Nat.factorial_mul_ascFactorial u m
  have h2 := Nat.ascFactorial_le_pow_add u m
  have : Nat.factorial (u + m) ≤ (u + m) ^ m * Nat.factorial u := by
    rw [← h, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  exact_mod_cast this

/-- The explicit decay bound behind R1: `Rval s n u ≤ K(s,n) / (2u+1)^2` for `s ≥ 3`. -/
lemma Rval_le_div_sq {s n : ℕ} (hs : 3 ≤ s) (u : ℕ) :
    Rval s n u ≤
      (2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 : ℕ) : ℚ) ^ (3 * n + 1)
        * 2 ^ (s * (n + 1))) / ((2 * u + 1 : ℕ) : ℚ) ^ 2 := by
  set Q : ℚ := ((2 * u + 1 : ℕ) : ℚ) with hQ
  have hQ1 : (1 : ℚ) ≤ Q := by rw [hQ]; exact_mod_cast Nat.le_add_left 1 (2 * u)
  have hQ0 : (0 : ℚ) < Q := lt_of_lt_of_le one_pos hQ1
  set K : ℚ := 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 : ℕ) : ℚ) ^ (3 * n + 1)
    with hK
  have hK0 : 0 ≤ K := by positivity
  -- the denominator product is at least `(Q/2)^{s(n+1)}`
  have hD : Q ^ (s * (n + 1)) / 2 ^ (s * (n + 1))
      ≤ ∏ j ∈ range (n + 1), ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s := by
    have hfac : ∀ j ∈ range (n + 1), (Q / 2) ^ s ≤ ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s := by
      intro j _
      refine pow_le_pow_left₀ (by positivity) ?_ s
      have h1 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      have h3 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      rw [hQ]; push_cast
      linarith
    calc Q ^ (s * (n + 1)) / 2 ^ (s * (n + 1)) = ∏ _j ∈ range (n + 1), (Q / 2) ^ s := by
          rw [prod_const, card_range, div_pow, pow_mul, pow_mul, div_pow]
      _ ≤ _ := Finset.prod_le_prod (fun j _ => by positivity) hfac
  -- the numerator is at most `K · Q^{3n+1}`
  have hN : 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 + 2 * u : ℕ) : ℚ)
      * (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ) ≤ K * Q ^ (3 * n + 1) := by
    have hc : ((3 * n + 1 + 2 * u : ℕ) : ℚ) ≤ ((3 * n + 1 : ℕ) : ℚ) * Q := by
      rw [hQ]; push_cast
      have h1 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      have h2 : (0 : ℚ) ≤ u := Nat.cast_nonneg u
      nlinarith
    have hf : (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ)
        ≤ (((3 * n + 1 : ℕ) : ℚ) * Q) ^ (3 * n) := by
      refine (factorial_ratio_le u (3 * n)).trans ?_
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [hQ]; push_cast
      have h1 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      have h2 : (0 : ℚ) ≤ u := Nat.cast_nonneg u
      nlinarith
    calc 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 + 2 * u : ℕ) : ℚ)
          * (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ)
        = 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * (((3 * n + 1 + 2 * u : ℕ) : ℚ)
          * ((Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ))) := by ring
      _ ≤ 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((((3 * n + 1 : ℕ) : ℚ) * Q)
          * (((3 * n + 1 : ℕ) : ℚ) * Q) ^ (3 * n)) := by
          gcongr
      _ = K * Q ^ (3 * n + 1) := by rw [hK]; ring
  have hexp : Q ^ (3 * n + 1) * Q ^ 2 ≤ Q ^ (s * (n + 1)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hQ1 (by nlinarith)
  unfold Rval
  calc _ ≤ (K * Q ^ (3 * n + 1)) / (Q ^ (s * (n + 1)) / 2 ^ (s * (n + 1))) := by
        gcongr
    _ = K * 2 ^ (s * (n + 1)) * (Q ^ (3 * n + 1) / Q ^ (s * (n + 1))) := by
        field_simp
    _ ≤ K * 2 ^ (s * (n + 1)) * (1 / Q ^ 2) := by
        have : Q ^ (3 * n + 1) / Q ^ (s * (n + 1)) ≤ 1 / Q ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]; exact hexp
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by rw [hK]; ring

/-- **The linear form.**  `r_n = Σ_{u ≥ 0} (-1)^{n+u+1} R_n(n+1+u-½)`, as a real number.  (For
even `n` the leading sign is `-1`, which is why `r_n < 0`; see `Integral.lean`.) -/
noncomputable def rForm (s n : ℕ) : ℝ :=
  ∑' u : ℕ, (-1 : ℝ) ^ (n + u + 1) * (Rval s n u : ℝ)

/-- **R1.**  The defining series of `rForm` converges absolutely for `s ≥ 3`: the terms decay
like `u^{3n + 1 - s(n+1)}`, an exponent `≤ -2` once `s ≥ 3`. -/
theorem summable_Rval {s n : ℕ} (hs : 3 ≤ s) :
    Summable (fun u : ℕ => (Rval s n u : ℝ)) := by
  set K : ℚ := 2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 : ℕ) : ℚ) ^ (3 * n + 1)
    * 2 ^ (s * (n + 1)) with hK
  have hsum : Summable (fun u : ℕ => (K : ℝ) / ((u : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine (this.mul_left (K : ℝ)).congr fun u => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun u => by exact_mod_cast (Rval_pos s n u).le)
    (fun u => ?_) hsum
  have h := Rval_le_div_sq (n := n) hs u
  have h' : ((Rval s n u : ℚ) : ℝ) ≤ ((K / ((2 * u + 1 : ℕ) : ℚ) ^ 2 : ℚ) : ℝ) :=
    Rat.cast_le.2 (by rw [hK]; exact h)
  refine h'.trans ?_
  push_cast
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by rw [hK]; positivity
  gcongr
  linarith

end LeanFormalizations.DirichletBeta
