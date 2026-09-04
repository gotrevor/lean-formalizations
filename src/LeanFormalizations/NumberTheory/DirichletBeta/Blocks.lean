/-
# The four simple-fraction blocks of `R_n`

`R_n(t) = 2^{6n} (n!)^{s-3} (2t+n) ∏_{j=1}^{3n}(t-n+j-½) / ∏_{j=0}^{n}(t+j)^s` factors as

    [(2t+n) · B_left] · B_mid · B_right · B_0^{s-3},

    B_b(t)  = 2^{2n} ∏_{j<n} (t + b + j + ½) / ∏_{j≤n} (t+j)      (b = -n, 0, n),
    B_0(t)  = n! / ∏_{j≤n} (t+j),

and every block is a *simple* fraction `Σ_k c_k/(t+k)` with **integer** residues (Zudilin's three
displayed identities).  This file proves that, by the residue formula for a proper fraction with
a degree-`≤ n` numerator (a polynomial with `n+1` roots vanishes) and the double-factorial
divisibilities `k!(n-k)! ∣ 2^n · (products of consecutive odd numbers)`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.PartialFractions

namespace LeanFormalizations.DirichletBeta

open Finset Polynomial

/-! ### The residue formula -/

/-- `∏_{j ≤ n, j ≠ k} (j - k) = (-1)^k k! (n-k)!`. -/
lemma prod_erase_sub (n k : ℕ) (hk : k ≤ n) :
    ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k)
      = (-1) ^ k * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) := by
  have hsplit : (range (n + 1)).erase k = range k ∪ Ico (k + 1) (n + 1) := by
    ext j
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range k) (Ico (k + 1) (n + 1)) := by
    rw [disjoint_left]
    intro j hj hj'
    simp only [mem_range] at hj
    simp only [mem_Ico] at hj'
    omega
  rw [hsplit, prod_union hdisj]
  have h1 : ∏ j ∈ range k, ((j : ℚ) - k) = (-1) ^ k * (Nat.factorial k : ℚ) := by
    rw [← prod_range_reflect (fun j => ((j : ℚ) - k)) k, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    have hc : (-1 : ℚ) ^ k = ∏ _x ∈ range k, (-1 : ℚ) := by simp
    rw [hc, ← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.1 hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have h2 : ∏ j ∈ Ico (k + 1) (n + 1), ((j : ℚ) - k) = (Nat.factorial (n - k) : ℚ) := by
    rw [prod_Ico_eq_prod_range, show n + 1 - (k + 1) = n - k by omega,
      ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    refine prod_congr rfl fun j _ => ?_
    ring
  rw [h1, h2]

/-- **Residue formula.**  For a polynomial `N` of degree `≤ n` and `t` not a pole,
`N(t) / ∏_{j≤n} (t+j) = Σ_k [N(-k) / ∏_{j≠k} (j-k)] / (t+k)`. -/
theorem residue_expansion {n : ℕ} (N : ℚ[X]) (hN : N.natDegree ≤ n) (t : ℚ) (ht : NonPole n t) :
    N.eval t / ∏ j ∈ range (n + 1), (t + j)
      = ∑ k ∈ range (n + 1),
          (N.eval (-(k : ℚ)) / ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k)) / (t + k) := by
  -- the Lagrange remainder polynomial
  set G : ℚ[X] := N - ∑ k ∈ range (n + 1),
    C (N.eval (-(k : ℚ)) / ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k))
      * ∏ j ∈ (range (n + 1)).erase k, (X + C (j : ℚ)) with hG
  have hGdeg : G.natDegree ≤ n := by
    refine (natDegree_sub_le _ _).trans (max_le hN ?_)
    refine (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
    calc ∑ j ∈ (range (n + 1)).erase k, (X + C (j : ℚ)).natDegree
        = ∑ j ∈ (range (n + 1)).erase k, 1 :=
          sum_congr rfl fun j _ => natDegree_X_add_C (j : ℚ)
      _ = ((range (n + 1)).erase k).card := by simp
      _ = n := by rw [card_erase_of_mem hk, card_range]; simp
  have hGeval : ∀ k ∈ range (n + 1), G.eval (-(k : ℚ)) = 0 := by
    intro k hk
    have hk' := mem_range.1 hk
    simp only [hG, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [sum_eq_single k]
    · have hne : ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k) ≠ 0 := by
        rw [prod_erase_sub n k (by omega)]
        positivity
      have : ∏ j ∈ (range (n + 1)).erase k, (-(k : ℚ) + j) = ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k) :=
        prod_congr rfl fun j _ => by ring
      rw [this, div_mul_cancel₀ _ hne, sub_self]
    · intro k' hk' hne
      have : ∏ j ∈ (range (n + 1)).erase k', (-(k : ℚ) + j) = 0 := by
        refine prod_eq_zero (mem_erase.2 ⟨hne.symm, hk⟩) ?_
        ring
      rw [this, mul_zero]
    · intro h; exact absurd hk h
  have hG0 : G = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' G
      ((range (n + 1)).image fun k : ℕ => -((k : ℕ) : ℚ)) (fun x hx => ?_) ?_
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
      exact hGeval k hk
    · rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      omega
  -- unfold `G = 0` at `t`
  have hval : N.eval t = ∑ k ∈ range (n + 1),
      (N.eval (-(k : ℚ)) / ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k))
        * ∏ j ∈ (range (n + 1)).erase k, (t + j) := by
    have := congrArg (eval t) hG0
    simp only [hG, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X,
      eval_zero] at this
    linarith
  rw [hval, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : t + k ≠ 0 := ht k hk
  have hP' : ∏ j ∈ (range (n + 1)).erase k, (t + (j : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun j hj => ht j (mem_of_mem_erase hj)
  rw [← mul_prod_erase (range (n + 1)) (fun j => t + (j : ℚ)) hk]
  field_simp


/-! ### Double factorials and the three divisibilities -/

/-- `DF m = 1 · 3 · 5 ⋯ (2m-1)`. -/
def DF (m : ℕ) : ℕ := ∏ i ∈ range m, (2 * i + 1)

lemma DF_pos (m : ℕ) : 0 < DF m := prod_pos fun _ _ => by omega

lemma two_pow_mul_factorial_mul_DF (m : ℕ) :
    2 ^ m * Nat.factorial m * DF m = Nat.factorial (2 * m) := by
  induction m with
  | zero => simp [DF]
  | succ m ih =>
    have e1 : Nat.factorial (2 * (m + 1)) = (2 * m + 2) * ((2 * m + 1) * Nat.factorial (2 * m)) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [DF, prod_range_succ, ← DF, e1, Nat.factorial_succ, ← ih, pow_succ]
    ring

lemma factorial_sq_dvd (m : ℕ) : Nat.factorial m * Nat.factorial m ∣ Nat.factorial (2 * m) := by
  have := Nat.factorial_mul_factorial_dvd_factorial (show m ≤ 2 * m by omega)
  rwa [show 2 * m - m = m by omega] at this

lemma factorial_mul_factorial_dvd (a b : ℕ) :
    Nat.factorial a * Nat.factorial b ∣ Nat.factorial (a + b) := by
  have := Nat.factorial_mul_factorial_dvd_factorial (show a ≤ a + b by omega)
  rwa [show a + b - a = b by omega] at this

/-- mid: `k! d! ∣ 2^{k+d} DF k DF d`. -/
lemma dvd_mid (k d : ℕ) : Nat.factorial k * Nat.factorial d ∣ 2 ^ (k + d) * DF k * DF d := by
  have h1 := two_pow_mul_factorial_mul_DF k
  have h2 := two_pow_mul_factorial_mul_DF d
  refine Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos d)) ?_
  have : 2 ^ (k + d) * DF k * DF d * (Nat.factorial k * Nat.factorial d)
      = Nat.factorial (2 * k) * Nat.factorial (2 * d) := by
    rw [← h1, ← h2, pow_add]; ring
  rw [this, show Nat.factorial k * Nat.factorial d * (Nat.factorial k * Nat.factorial d)
      = (Nat.factorial k * Nat.factorial k) * (Nat.factorial d * Nat.factorial d) by ring]
  exact mul_dvd_mul (factorial_sq_dvd k) (factorial_sq_dvd d)

/-- right: `k! d! DF d ∣ 2^{k+d} DF (2d + k)`. -/
lemma dvd_right (k d : ℕ) :
    Nat.factorial k * Nat.factorial d * DF d ∣ 2 ^ (k + d) * DF (d + (k + d)) := by
  have h1 := two_pow_mul_factorial_mul_DF (d + (k + d))
  have h2 := two_pow_mul_factorial_mul_DF d
  refine Nat.dvd_of_mul_dvd_mul_right
    (Nat.mul_pos (pow_pos two_pos (d + (k + d))) (Nat.factorial_pos (d + (k + d)))) ?_
  have hR : 2 ^ (k + d) * DF (d + (k + d)) * (2 ^ (d + (k + d)) * Nat.factorial (d + (k + d)))
      = 2 ^ (k + d) * Nat.factorial (2 * (d + (k + d))) := by rw [← h1]; ring
  have hL : Nat.factorial k * Nat.factorial d * DF d
      * (2 ^ (d + (k + d)) * Nat.factorial (d + (k + d)))
      = 2 ^ (k + d) * (Nat.factorial k * Nat.factorial (2 * d) * Nat.factorial (d + (k + d))) := by
    rw [← h2, show d + (k + d) = d + (k + d) by rfl, pow_add]; ring
  rw [hR, hL]
  refine mul_dvd_mul_left _ ?_
  -- `k! (2d)! (d+k+d)! ∣ (2(d+k+d))!`
  have e1 : Nat.factorial k * Nat.factorial (2 * d) ∣ Nat.factorial (d + (k + d)) := by
    have := factorial_mul_factorial_dvd k (2 * d)
    rwa [show k + 2 * d = d + (k + d) by ring] at this
  have e2 : Nat.factorial (d + (k + d)) * Nat.factorial (d + (k + d))
      ∣ Nat.factorial (2 * (d + (k + d))) := factorial_sq_dvd _
  exact (mul_dvd_mul e1 dvd_rfl).trans e2

/-- left: `k! d! DF k ∣ 2^{k+d} DF ((k+d) + k)`. -/
lemma dvd_left (k d : ℕ) :
    Nat.factorial k * Nat.factorial d * DF k ∣ 2 ^ (k + d) * DF ((k + d) + k) := by
  have h1 := two_pow_mul_factorial_mul_DF ((k + d) + k)
  have h2 := two_pow_mul_factorial_mul_DF k
  refine Nat.dvd_of_mul_dvd_mul_right
    (Nat.mul_pos (pow_pos two_pos ((k + d) + k)) (Nat.factorial_pos ((k + d) + k))) ?_
  have hR : 2 ^ (k + d) * DF ((k + d) + k) * (2 ^ ((k + d) + k) * Nat.factorial ((k + d) + k))
      = 2 ^ (k + d) * Nat.factorial (2 * ((k + d) + k)) := by rw [← h1]; ring
  have hL : Nat.factorial k * Nat.factorial d * DF k
      * (2 ^ ((k + d) + k) * Nat.factorial ((k + d) + k))
      = 2 ^ (k + d) * (Nat.factorial d * Nat.factorial ((k + d) + k) * Nat.factorial (2 * k)) := by
    rw [← h2, pow_add]; ring
  rw [hR, hL]
  refine mul_dvd_mul_left _ ?_
  have e1 : Nat.factorial d * Nat.factorial ((k + d) + k) ∣ Nat.factorial (2 * (k + d)) := by
    have := factorial_mul_factorial_dvd d ((k + d) + k)
    rwa [show d + ((k + d) + k) = 2 * (k + d) by ring] at this
  have e2 : Nat.factorial (2 * (k + d)) * Nat.factorial (2 * k) ∣ Nat.factorial (2 * ((k + d) + k)) := by
    have := factorial_mul_factorial_dvd (2 * (k + d)) (2 * k)
    rwa [show 2 * (k + d) + 2 * k = 2 * ((k + d) + k) by ring] at this
  exact (mul_dvd_mul e1 dvd_rfl).trans e2

/-! ### The blocks -/

/-- Simple fraction with integer residues (and no constant term), away from poles. -/
def Simple (n : ℕ) (g : ℚ → ℚ) : Prop :=
  ∃ e : ℕ → ℤ, ∀ t, NonPole n t → g t = ∑ j ∈ range (n + 1), (e j : ℚ) / (t + j)

/-- The block polynomial `2^{2n} ∏_{j<n} (X + b + j + ½)`. -/
noncomputable def blockPoly (n : ℕ) (b : ℤ) : ℚ[X] :=
  C ((2 : ℚ) ^ (2 * n)) * ∏ j ∈ range n, (X + C ((b : ℚ) + j + 1 / 2))

lemma blockPoly_eval (n : ℕ) (b : ℤ) (t : ℚ) :
    (blockPoly n b).eval t = 2 ^ (2 * n) * ∏ j ∈ range n, (t + b + j + 1 / 2) := by
  simp only [blockPoly, eval_mul, eval_C, eval_prod, eval_add, eval_X]
  congr 1
  exact prod_congr rfl fun j _ => by ring

lemma blockPoly_natDegree_le (n : ℕ) (b : ℤ) : (blockPoly n b).natDegree ≤ n := by
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans (le_of_eq ?_))
  calc ∑ j ∈ range n, (X + C ((b : ℚ) + j + 1 / 2)).natDegree
      = ∑ j ∈ range n, 1 := sum_congr rfl fun j _ => natDegree_X_add_C _
    _ = n := by simp

/-- The block function `B_b(t) = 2^{2n} ∏_{j<n} (t + b + j + ½) / ∏_{j≤n} (t+j)`. -/
noncomputable def block (n : ℕ) (b : ℤ) (t : ℚ) : ℚ :=
  2 ^ (2 * n) * (∏ j ∈ range n, (t + b + j + 1 / 2)) / ∏ j ∈ range (n + 1), (t + j)

/-- The residue of `B_b` at `t = -k`. -/
noncomputable def blockRes (n : ℕ) (b : ℤ) (k : ℕ) : ℚ :=
  (blockPoly n b).eval (-(k : ℚ)) / ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k)

lemma block_eq_sum (n : ℕ) (b : ℤ) (t : ℚ) (ht : NonPole n t) :
    block n b t = ∑ k ∈ range (n + 1), blockRes n b k / (t + k) := by
  have := residue_expansion (blockPoly n b) (blockPoly_natDegree_le n b) t ht
  rw [blockPoly_eval] at this
  exact this

/-- `2^{2n} ∏_{j<n} (y_j + ½) = 2^n ∏_{j<n} (2 y_j + 1)`. -/
lemma two_pow_prod_half (n : ℕ) (y : ℕ → ℚ) :
    (2 : ℚ) ^ (2 * n) * ∏ j ∈ range n, (y j + 1 / 2) = 2 ^ n * ∏ j ∈ range n, (2 * y j + 1) := by
  have : ∏ j ∈ range n, (2 * y j + 1) = ∏ j ∈ range n, (2 * (y j + 1 / 2)) :=
    prod_congr rfl fun j _ => by ring
  rw [this, prod_mul_distrib, prod_const, card_range, ← mul_assoc, ← pow_add]
  congr 2; ring

lemma blockRes_eq (n : ℕ) (b : ℤ) (k : ℕ) (hk : k ≤ n) :
    blockRes n b k = 2 ^ n * (∏ j ∈ range n, (2 * ((b : ℚ) - k + j) + 1))
      / ((-1) ^ k * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ)) := by
  rw [blockRes, blockPoly_eval, prod_erase_sub n k hk]
  have := two_pow_prod_half n (fun j => (b : ℚ) - k + j)
  rw [← this]
  congr 2
  exact prod_congr rfl fun j _ => by ring

/-- The reflected odd product `∏_{j<m} (2(c - 1 - j) + 1)`-type identities. -/
lemma prod_odd_neg (k : ℕ) :
    ∏ j ∈ range k, (2 * ((j : ℚ) - k) + 1) = (-1) ^ k * (DF k : ℚ) := by
  rw [← prod_range_reflect (fun j => 2 * ((j : ℚ) - k) + 1) k, DF]
  push_cast
  have hc : (-1 : ℚ) ^ k = ∏ _x ∈ range k, (-1 : ℚ) := by simp
  rw [hc, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have := mem_range.1 hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

lemma prod_odd_shift (c m : ℕ) :
    (DF c : ℚ) * ∏ j ∈ range m, (2 * ((c : ℚ) + j) + 1) = (DF (c + m) : ℚ) := by
  rw [DF, DF, prod_range_add]
  push_cast
  rfl

/-- **Integrality of the residues** for the three blocks `b ∈ {-n, 0, n}`. -/
lemma blockRes_int_mid (n k : ℕ) (hk : k ≤ n) : ∃ z : ℤ, blockRes n 0 k = z := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [blockRes_eq _ _ _ hk, Nat.add_sub_cancel_left]
  have hprod : ∏ j ∈ range (k + d), (2 * (((0 : ℤ) : ℚ) - k + j) + 1)
      = (-1) ^ k * (DF k : ℚ) * (DF d : ℚ) := by
    rw [prod_range_add, show ∏ j ∈ range k, (2 * (((0 : ℤ) : ℚ) - k + j) + 1)
        = ∏ j ∈ range k, (2 * ((j : ℚ) - k) + 1) from prod_congr rfl fun j _ => by push_cast; ring,
      prod_odd_neg]
    congr 1
    rw [DF]; push_cast
    exact prod_congr rfl fun j _ => by push_cast; ring
  rw [hprod]
  obtain ⟨z, hz⟩ := dvd_mid k d
  have hz' : ((2 ^ (k + d) * DF k * DF d : ℕ) : ℚ)
      = ((Nat.factorial k * Nat.factorial d * z : ℕ) : ℚ) := by rw [hz]
  push_cast at hz'
  have h1 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have h2 : (Nat.factorial d : ℚ) ≠ 0 := by positivity
  refine ⟨z, ?_⟩
  rcases neg_one_pow_eq_or ℚ k with h | h <;> rw [h] <;> push_cast <;> field_simp <;>
    first | linear_combination hz' | linear_combination -hz'

lemma blockRes_int_right (n k : ℕ) (hk : k ≤ n) : ∃ z : ℤ, blockRes n n k = z := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [blockRes_eq _ _ _ hk, Nat.add_sub_cancel_left]
  have h4 : (DF d : ℚ) ≠ 0 := by exact_mod_cast (DF_pos d).ne'
  have hprod : ∏ j ∈ range (k + d), (2 * (((k + d : ℕ) : ℤ) - k + j : ℚ) + 1)
      = (DF (d + (k + d)) : ℚ) / DF d := by
    rw [eq_div_iff h4, mul_comm, ← prod_odd_shift]
    congr 1
    exact prod_congr rfl fun j _ => by push_cast; ring
  rw [hprod]
  obtain ⟨z, hz⟩ := dvd_right k d
  have hz' : ((2 ^ (k + d) * DF (d + (k + d)) : ℕ) : ℚ)
      = ((Nat.factorial k * Nat.factorial d * DF d * z : ℕ) : ℚ) := by rw [hz]
  push_cast at hz'
  have h1 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have h2 : (Nat.factorial d : ℚ) ≠ 0 := by positivity
  rcases neg_one_pow_eq_or ℚ k with h | h
  · refine ⟨z, ?_⟩
    rw [h]; push_cast; field_simp; linear_combination hz'
  · refine ⟨-z, ?_⟩
    rw [h]; push_cast; field_simp; linear_combination -hz'

lemma blockRes_int_left (n k : ℕ) (hk : k ≤ n) : ∃ z : ℤ, blockRes n (-(n : ℤ)) k = z := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [blockRes_eq _ _ _ hk, Nat.add_sub_cancel_left]
  have h4 : (DF k : ℚ) ≠ 0 := by exact_mod_cast (DF_pos k).ne'
  have hprod : ∏ j ∈ range (k + d), (2 * (((-((k + d : ℕ) : ℤ) : ℤ) : ℚ) - k + j) + 1)
      = ((-1) ^ (k + d) * (DF (k + (k + d)) : ℚ)) / DF k := by
    rw [← prod_range_reflect (fun j => 2 * (((-((k + d : ℕ) : ℤ) : ℤ) : ℚ) - k + j) + 1) (k + d)]
    have hc : (-1 : ℚ) ^ (k + d) = ∏ _x ∈ range (k + d), (-1 : ℚ) := by simp
    rw [eq_div_iff h4, ← prod_odd_shift k (k + d), hc, mul_left_comm, ← prod_mul_distrib, mul_comm]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.1 hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hprod, show k + (k + d) = (k + d) + k by ring]
  obtain ⟨z, hz⟩ := dvd_left k d
  have hz' : ((2 ^ (k + d) * DF ((k + d) + k) : ℕ) : ℚ)
      = ((Nat.factorial k * Nat.factorial d * DF k * z : ℕ) : ℚ) := by rw [hz]
  push_cast at hz'
  have h1 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have h2 : (Nat.factorial d : ℚ) ≠ 0 := by positivity
  rcases neg_one_pow_eq_or ℚ k with h | h <;> rcases neg_one_pow_eq_or ℚ (k + d) with h' | h'
  · exact ⟨z, by rw [h, h']; push_cast; field_simp; first | linear_combination hz' | linear_combination -hz'⟩
  · exact ⟨-z, by rw [h, h']; push_cast; field_simp; first | linear_combination hz' | linear_combination -hz'⟩
  · exact ⟨-z, by rw [h, h']; push_cast; field_simp; first | linear_combination hz' | linear_combination -hz'⟩
  · exact ⟨z, by rw [h, h']; push_cast; field_simp; first | linear_combination hz' | linear_combination -hz'⟩

/-- The three shifted blocks are simple fractions with integer residues. -/
lemma block_simple (n : ℕ) (b : ℤ) (hb : b = -(n : ℤ) ∨ b = 0 ∨ b = n) : Simple n (block n b) := by
  have hint : ∀ k ∈ range (n + 1), ∃ z : ℤ, blockRes n b k = z := by
    intro k hk
    have hk' := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rcases hb with rfl | rfl | rfl
    · exact blockRes_int_left n k hk'
    · exact blockRes_int_mid n k hk'
    · exact blockRes_int_right n k hk'
  choose! e he using hint
  refine ⟨e, fun t ht => ?_⟩
  rw [block_eq_sum n b t ht]
  exact sum_congr rfl fun k hk => by rw [he k hk]

/-- `B_0(t) = n! / ∏_{j≤n} (t+j)`. -/
noncomputable def block0 (n : ℕ) (t : ℚ) : ℚ :=
  (Nat.factorial n : ℚ) / ∏ j ∈ range (n + 1), (t + j)

/-- `B_0 = Σ_k (-1)^k C(n,k) / (t+k)`. -/
lemma block0_simple (n : ℕ) : Simple n (block0 n) := by
  refine ⟨fun k => (-1) ^ k * Nat.choose n k, fun t ht => ?_⟩
  have := residue_expansion (C (Nat.factorial n : ℚ)) (by simp) t ht
  simp only [eval_C] at this
  rw [block0, this]
  refine sum_congr rfl fun k hk => ?_
  have hk' := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [prod_erase_sub n k hk']
  congr 1
  have hc : (Nat.factorial n : ℚ) = Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk').symm
  rw [hc]
  push_cast
  have h1 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have h2 : (Nat.factorial (n - k) : ℚ) ≠ 0 := by positivity
  rcases neg_one_pow_eq_or ℚ k with h | h <;> rw [h] <;> field_simp

lemma Simple.rep_one {n : ℕ} {g : ℚ → ℚ} (hg : Simple n g) : Rep n 1 g := by
  obtain ⟨e, he⟩ := hg
  refine ⟨fun i k => if i = 0 then (e k : ℚ) else 0, fun i hi k _ => ?_, fun t ht => ?_⟩
  · have : i = 0 := by simpa using hi
    subst this
    exact ⟨e k, by simp⟩
  · rw [he t ht]
    simp [pfSum]

lemma Rep.mul_simple' {n σ : ℕ} {f g : ℚ → ℚ} (hf : Rep n σ f) (hg : Simple n g) :
    Rep n (σ + 1) (fun t => f t * g t) := by
  obtain ⟨e, he⟩ := hg
  refine (hf.mul_simple 0 e).congr fun t ht => ?_
  rw [he t ht]
  simp

/-- `(2t+n) · g` for a simple `g` is an integer constant plus a simple fraction. -/
lemma Simple.linear_mul {n : ℕ} {g : ℚ → ℚ} (hg : Simple n g) :
    ∃ (c : ℤ) (e : ℕ → ℤ), ∀ t, NonPole n t →
      (2 * t + n) * g t = c + ∑ j ∈ range (n + 1), (e j : ℚ) / (t + j) := by
  obtain ⟨e, he⟩ := hg
  refine ⟨2 * ∑ j ∈ range (n + 1), e j, fun j => e j * ((n : ℤ) - 2 * j), fun t ht => ?_⟩
  rw [he t ht, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have := ht j hj
  field_simp
  ring

lemma Rep.mul_linear_simple {n σ : ℕ} {f g : ℚ → ℚ} (hf : Rep n σ f) (hg : Simple n g) :
    Rep n (σ + 1) (fun t => f t * ((2 * t + n) * g t)) := by
  obtain ⟨c, e, he⟩ := hg.linear_mul
  refine (hf.mul_simple c e).congr fun t ht => ?_
  rw [he t ht]

/-! ### `R_n` as a function and its block factorization -/

/-- `R_n(t) = 2^{6n} (n!)^{s-3} (2t+n) ∏_{j=1}^{3n} (t-n+j-½) / ∏_{j=0}^{n} (t+j)^s`. -/
noncomputable def Rfun (s n : ℕ) (t : ℚ) : ℚ :=
  2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * (2 * t + n)
    * (∏ j ∈ range (3 * n), (t - n + (j + 1) - 1 / 2)) / ∏ j ∈ range (n + 1), (t + j) ^ s

lemma prod_nonpole_ne_zero {n : ℕ} {t : ℚ} (ht : NonPole n t) :
    ∏ j ∈ range (n + 1), (t + (j : ℚ)) ≠ 0 :=
  prod_ne_zero_iff.2 fun j hj => ht j hj

/-- The block factorization, away from poles. -/
lemma Rfun_eq_blocks {s : ℕ} (hs : 3 ≤ s) (n : ℕ) (t : ℚ) (ht : NonPole n t) :
    Rfun s n t = block n 0 t * ((2 * t + n) * block n (-(n : ℤ)) t) * block n n t
      * (block0 n t) ^ (s - 3) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
  simp only [Rfun, block, block0, Nat.add_sub_cancel]
  rw [prod_pow]
  set P := ∏ j ∈ range (n + 1), (t + (j : ℚ)) with hPdef
  have hP : P ≠ 0 := prod_nonpole_ne_zero ht
  rw [show 3 * n = n + n + n by ring, prod_range_add, prod_range_add, pow_add P,
    show 6 * n = 2 * n + 2 * n + 2 * n by ring, pow_add, pow_add]
  have e1 : ∏ j ∈ range n, (t - n + (j + 1 : ℚ) - 1 / 2) = ∏ j ∈ range n, (t + ((-(n : ℤ) : ℤ) : ℚ) + j + 1 / 2) :=
    prod_congr rfl fun j _ => by push_cast; ring
  have e2 : ∏ j ∈ range n, (t - n + ((n + j : ℕ) + 1 : ℚ) - 1 / 2) = ∏ j ∈ range n, (t + ((0 : ℤ) : ℚ) + j + 1 / 2) :=
    prod_congr rfl fun j _ => by push_cast; ring
  have e3 : ∏ j ∈ range n, (t - n + ((n + n + j : ℕ) + 1 : ℚ) - 1 / 2) = ∏ j ∈ range n, (t + ((n : ℤ) : ℚ) + j + 1 / 2) :=
    prod_congr rfl fun j _ => by push_cast; ring
  rw [e1, e2, e3, div_pow]
  field_simp

/-- **`R_n` is a level-`s` representation** with `d_n^{s-1-i}`-integral coefficients. -/
theorem rep_Rfun {s : ℕ} (hs : 3 ≤ s) (n : ℕ) : Rep n s (Rfun s n) := by
  have h1 : Rep n 1 (block n 0) := (block_simple n 0 (Or.inr (Or.inl rfl))).rep_one
  have h2 : Rep n 2 (fun t => block n 0 t * ((2 * t + n) * block n (-(n : ℤ)) t)) :=
    h1.mul_linear_simple (block_simple n _ (Or.inl rfl))
  have h3 : Rep n 3 (fun t => block n 0 t * ((2 * t + n) * block n (-(n : ℤ)) t) * block n n t) :=
    h2.mul_simple' (block_simple n n (Or.inr (Or.inr rfl)))
  have h4 : ∀ m, Rep n (3 + m) (fun t =>
      block n 0 t * ((2 * t + n) * block n (-(n : ℤ)) t) * block n n t * (block0 n t) ^ m) := by
    intro m
    induction m with
    | zero => simpa using h3
    | succ m ih =>
      have := ih.mul_simple' (block0_simple n)
      refine this.congr fun t _ => ?_
      rw [pow_succ]; ring
  have := h4 (s - 3)
  rw [show 3 + (s - 3) = s by omega] at this
  exact this.congr fun t ht => (Rfun_eq_blocks hs n t ht).symm

end LeanFormalizations.DirichletBeta
