/-
# N3 — nonvanishing: `r_n < 0` (**the crux**)

`r_n` is a nonzero *number*, and nothing about the ledger proves that; classically it comes from
a positive `s`-fold Beta integral

    |r_n| = 2^{6n} (3n+1)!/n!³ · ∫_{[0,1]^s} (1 - T) ∏_j t_j^{n-½}(1-t_j)^n / (1+T)^{3n+2} dt > 0.

**This file proves it without any integral**, by the discrete shadow of that argument
(`CompleteMonotone.lean`).  Writing `Rval s n u = C_n · c_u · M_u` with

    B_u = n! / ∏_{j=0}^{n} (u + n + ½ + j),   M_u = B_u^s,   c_u = C(3n+1+u, u) + C(3n+u, u-1),

the sequence `B` is strictly completely monotone (its iterated differences have a closed form),
hence so is `M = B^s` (discrete Leibniz), and the alternating binomial sums
`N_j(u) = Σ_m (-1)^m C(m+j, m) M_{u+m}` satisfy the Pascal recursion
`N_{j+1}(u) + N_{j+1}(u+1) = N_j(u)`, so each is the alternating resolvent of the previous and
stays strictly completely monotone.  Finally `Σ_u (-1)^u c_u M_u = N_{3n+1}(0) - N_{3n+1}(1) > 0`
and `r_n = -C_n · (that)` for even `n`.

The sign convention `r_n = -C_n·∫` was verified numerically before this proof was written
(`papers/catalan-beta-validate.py`, part (c)); the kernel now confirms it.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Rational
import LeanFormalizations.NumberTheory.DirichletBeta.CompleteMonotone

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-! ### The reciprocal product `1/∏_{j<m}(u + a + j)` is strictly completely monotone -/

/-- `invProd a m u = 1 / ∏_{j < m} (u + a + j)`. -/
noncomputable def invProd (a : ℝ) (m : ℕ) : ℕ → ℝ := fun u => (∏ j ∈ range m, ((u : ℝ) + a + j))⁻¹

lemma prod_shift_pos {a : ℝ} (ha : 0 < a) (m u : ℕ) : 0 < ∏ j ∈ range m, ((u : ℝ) + a + j) :=
  Finset.prod_pos fun j _ => by positivity

lemma fd_invProd {a : ℝ} (ha : 0 < a) (m : ℕ) : fd (invProd a m) = (m : ℝ) • invProd a (m + 1) := by
  funext u
  simp only [fd_apply, invProd, Pi.smul_apply, smul_eq_mul]
  have hP := prod_shift_pos ha m u
  have hQ := prod_shift_pos ha m (u + 1)
  have h1 : ∏ j ∈ range (m + 1), ((u : ℝ) + a + j) = (∏ j ∈ range m, ((u : ℝ) + a + j)) * (u + a + m) := by
    rw [prod_range_succ]
  have h2 : ∏ j ∈ range (m + 1), ((u : ℝ) + a + j) = (∏ j ∈ range m, (((u + 1 : ℕ) : ℝ) + a + j)) * (u + a) := by
    rw [prod_range_succ']
    push_cast
    simp only [Nat.cast_zero, add_zero]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    ring
  rw [h1]
  have hua : (0 : ℝ) < u + a := by positivity
  have hQ' : ∏ j ∈ range m, (((u + 1 : ℕ) : ℝ) + a + j)
      = (∏ j ∈ range m, ((u : ℝ) + a + j)) * (u + a + m) / (u + a) := by
    rw [← h1, h2]; field_simp
  rw [hQ']
  field_simp
  ring

lemma fd_iter_invProd {a : ℝ} (ha : 0 < a) (m k : ℕ) :
    fd^[k] (invProd a m) = (∏ i ∈ range k, ((m : ℝ) + i)) • invProd a (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, fd_invProd ha, fd_iter_smul, ih, smul_smul]
    have hprod : ∏ i ∈ range (k + 1), ((m : ℝ) + i)
        = (m : ℝ) * ∏ i ∈ range k, (((m + 1 : ℕ) : ℝ) + i) := by
      rw [prod_range_succ']
      push_cast
      simp only [Nat.cast_zero, add_zero]
      rw [mul_comm]
      congr 1
      exact prod_congr rfl fun i _ => by ring
    have hidx : m + (k + 1) = m + 1 + k := by ring
    rw [hprod, hidx]

lemma strictCM_invProd {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) : StrictCM (invProd a m) := by
  intro k u
  rw [fd_iter_invProd ha, Pi.smul_apply, smul_eq_mul, invProd]
  refine mul_pos (Finset.prod_pos fun i _ => ?_) (inv_pos.2 (prod_shift_pos ha _ _))
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

/-! ### The sequences `B`, `M`, `c` and the factorization of `Rval` -/

/-- `B_u = n! / ∏_{j=0}^{n} (u + n + ½ + j)`, in the shape of `Rval`'s denominator. -/
noncomputable def Bseq (n : ℕ) : ℕ → ℝ := fun u =>
  (Nat.factorial n : ℝ) / ∏ j ∈ range (n + 1), ((2 * ((n : ℝ) + 1 + u + j) - 1) / 2)

/-- `M_u = B_u^s`. -/
noncomputable def Mseq (s n : ℕ) : ℕ → ℝ := Bseq n ^ s

lemma Mseq_apply (s n u : ℕ) : Mseq s n u = Bseq n u ^ s := rfl

lemma Bseq_eq (n : ℕ) : Bseq n = (Nat.factorial n : ℝ) • invProd ((n : ℝ) + 1 / 2) (n + 1) := by
  funext u
  simp only [Bseq, invProd, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  congr 2
  refine prod_congr rfl fun j _ => ?_
  ring

lemma strictCM_Bseq (n : ℕ) : StrictCM (Bseq n) := by
  rw [Bseq_eq]
  exact (strictCM_invProd (by positivity) (by omega)).smul (by positivity)

lemma strictCM_Mseq {s : ℕ} (hs : 1 ≤ s) (n : ℕ) : StrictCM (Mseq s n) :=
  (strictCM_Bseq n).pow hs

lemma Mseq_pos {s : ℕ} (hs : 3 ≤ s) (n u : ℕ) : 0 < Mseq s n u :=
  (strictCM_Mseq (by omega : 1 ≤ s) n).pos u

lemma Mseq_nonneg {s : ℕ} (hs : 3 ≤ s) (n u : ℕ) : 0 ≤ Mseq s n u := (Mseq_pos hs n u).le

/-- `C_n = 2^{6n} (3n+1)! / (n!)^3`. -/
noncomputable def Cn (n : ℕ) : ℝ :=
  2 ^ (6 * n) * (Nat.factorial (3 * n + 1) : ℝ) / (Nat.factorial n : ℝ) ^ 3

/-- `c_u = (3n+1+2u) (u+3n)! / (u! (3n+1)!)`. -/
noncomputable def cseq (n : ℕ) : ℕ → ℝ := fun u =>
  ((3 * n + 1 + 2 * u : ℕ) : ℝ) * (Nat.factorial (u + 3 * n) : ℝ)
    / ((Nat.factorial u : ℝ) * (Nat.factorial (3 * n + 1) : ℝ))

lemma Cn_pos (n : ℕ) : 0 < Cn n := by unfold Cn; positivity

lemma cseq_pos (n u : ℕ) : 0 < cseq n u := by unfold cseq; positivity

/-- The factorization `Rval s n u = C_n · c_u · M_u` (for `s ≥ 3`). -/
lemma Rval_eq_factor {s : ℕ} (hs : 3 ≤ s) (n u : ℕ) :
    ((Rval s n u : ℚ) : ℝ) = Cn n * cseq n u * Mseq s n u := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
  simp only [Rval, Cn, cseq, Mseq_apply, Bseq, Nat.add_sub_cancel]
  push_cast
  have hP : (0 : ℝ) < ∏ j ∈ range (n + 1), ((2 * ((n : ℝ) + 1 + u + j) - 1) / 2) := by
    refine Finset.prod_pos fun j _ => ?_
    have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) < 2 * ((n : ℝ) + 1 + u + j) - 1 := by linarith
    positivity
  rw [Finset.prod_pow, div_pow, pow_add]
  field_simp
  ring

lemma cseq_zero (n : ℕ) : cseq n 0 = 1 := by
  simp only [cseq, Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero, add_zero, zero_add]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

lemma cseq_succ (n m : ℕ) :
    cseq n (m + 1) = (Nat.choose (3 * n + 2 + m) (m + 1) : ℝ) + (Nat.choose (3 * n + 1 + m) m : ℝ) := by
  rw [Nat.cast_choose ℝ (by omega : m + 1 ≤ 3 * n + 2 + m),
    Nat.cast_choose ℝ (by omega : m ≤ 3 * n + 1 + m),
    show 3 * n + 2 + m - (m + 1) = 3 * n + 1 by omega,
    show 3 * n + 1 + m - m = 3 * n + 1 by omega]
  simp only [cseq]
  have h1 : Nat.factorial (3 * n + 2 + m) = (3 * n + 2 + m) * Nat.factorial (3 * n + 1 + m) := by
    rw [show 3 * n + 2 + m = (3 * n + 1 + m) + 1 by ring, Nat.factorial_succ]
  have h2 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
  have h3 : m + 1 + 3 * n = 3 * n + 1 + m := by ring
  rw [h1, h2, h3]
  push_cast
  field_simp
  ring

/-- `c_u ≥ C(3n+1+u, u)`. -/
lemma choose_le_cseq (n u : ℕ) : (Nat.choose (3 * n + 1 + u) u : ℝ) ≤ cseq n u := by
  cases u with
  | zero => simp [cseq_zero]
  | succ m =>
    rw [cseq_succ, show 3 * n + 1 + (m + 1) = 3 * n + 2 + m by ring]
    have : (0 : ℝ) ≤ (Nat.choose (3 * n + 1 + m) m : ℝ) := Nat.cast_nonneg _
    linarith

/-! ### Weighted summability, inherited from `summable_Rval` -/

/-- `Σ_m c_m M_m` converges. -/
lemma summable_cseq_mul_Mseq {s n : ℕ} (hs : 3 ≤ s) :
    Summable (fun m => cseq n m * Mseq s n m) := by
  have h := (summable_Rval (n := n) hs).mul_left (Cn n)⁻¹
  refine h.congr fun m => ?_
  rw [Rval_eq_factor hs]
  field_simp [(Cn_pos n).ne']

/-- Weighted summability `Σ_m C(m+j, m) M_m < ∞` for `j ≤ 3n+1`. -/
lemma summable_choose_mul_Mseq {s n : ℕ} (hs : 3 ≤ s) {j : ℕ} (hj : j ≤ 3 * n + 1) :
    Summable (fun m => (Nat.choose (m + j) m : ℝ) * Mseq s n m) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (summable_cseq_mul_Mseq (n := n) hs)
  · exact mul_nonneg (Nat.cast_nonneg _) (Mseq_nonneg hs n m)
  · refine mul_le_mul_of_nonneg_right ?_ (Mseq_nonneg hs n m)
    refine le_trans ?_ (choose_le_cseq n m)
    exact_mod_cast Nat.choose_le_choose m (by omega : m + j ≤ 3 * n + 1 + m)

lemma summable_Mseq {s n : ℕ} (hs : 3 ≤ s) : Summable (Mseq s n) := by
  have := summable_choose_mul_Mseq (n := n) hs (j := 0) (by omega)
  simpa using this

/-! ### The alternating binomial sums `N_j` -/

/-- `N_j(u) = Σ_m (-1)^m C(m+j, m) M_{u+m}`. -/
noncomputable def Nseq (s n j : ℕ) : ℕ → ℝ := fun u =>
  ∑' m, (-1 : ℝ) ^ m * (Nat.choose (m + j) m : ℝ) * Mseq s n (u + m)

lemma choose_add_le_choose_add (u m j : ℕ) :
    Nat.choose (m + j) m ≤ Nat.choose (u + m + j) (u + m) := by
  rw [Nat.choose_symm_add, Nat.choose_symm_add]
  exact Nat.choose_le_choose j (by omega)

lemma summable_Nseq_term {s n : ℕ} (hs : 3 ≤ s) {j : ℕ} (hj : j ≤ 3 * n + 1) (u : ℕ) :
    Summable (fun m => (-1 : ℝ) ^ m * (Nat.choose (m + j) m : ℝ) * Mseq s n (u + m)) := by
  have h : Summable (fun m => (Nat.choose (u + m + j) (u + m) : ℝ) * Mseq s n (u + m)) := by
    have := (summable_nat_add_iff u).2 (summable_choose_mul_Mseq (n := n) hs hj)
    refine this.congr fun m => ?_
    simp only [add_comm m u]
  refine Summable.of_norm_bounded h fun m => ?_
  have hM := (Mseq_nonneg hs n (u + m))
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hM]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast choose_add_le_choose_add u m j) hM

/-- The Pascal recursion `N_{j+1}(u) + N_{j+1}(u+1) = N_j(u)`. -/
lemma Nseq_rec {s n : ℕ} (hs : 3 ≤ s) {j : ℕ} (hj : j + 1 ≤ 3 * n + 1) (u : ℕ) :
    Nseq s n (j + 1) u + Nseq s n (j + 1) (u + 1) = Nseq s n j u := by
  simp only [Nseq]
  rw [(summable_Nseq_term hs hj u).tsum_eq_zero_add,
    (summable_Nseq_term hs (by omega) u).tsum_eq_zero_add, add_assoc]
  simp only [pow_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_zero]
  congr 1
  rw [← ((summable_nat_add_iff 1).2 (summable_Nseq_term hs (by omega) u)).tsum_add
    (summable_Nseq_term hs (by omega) (u + 1))]
  refine tsum_congr fun m => ?_
  have hp : (Nat.choose (m + 1 + (j + 1)) (m + 1) : ℝ)
      = Nat.choose (m + (j + 1)) m + Nat.choose (m + 1 + j) (m + 1) := by
    rw [show m + 1 + (j + 1) = (m + j + 1) + 1 by ring, Nat.choose_succ_succ',
      show m + (j + 1) = m + j + 1 by ring, show m + 1 + j = m + j + 1 by ring]
    push_cast; ring
  rw [hp, show u + 1 + m = u + (m + 1) by ring]
  ring

/-- `N_j → 0`: it is bounded by a tail of the convergent weighted series. -/
lemma Nseq_tendsto {s n : ℕ} (hs : 3 ≤ s) {j : ℕ} (hj : j ≤ 3 * n + 1) :
    Tendsto (Nseq s n j) atTop (𝓝 0) := by
  set g : ℕ → ℝ := fun m => (Nat.choose (m + j) m : ℝ) * Mseq s n m with hg
  have hgs : Summable g := summable_choose_mul_Mseq hs hj
  have hg0 : ∀ m, 0 ≤ g m := fun m =>
    mul_nonneg (Nat.cast_nonneg _) (Mseq_nonneg hs n m)
  refine squeeze_zero_norm (fun u => ?_) (tendsto_sum_nat_add g)
  simp only [Nseq]
  refine (norm_tsum_le_tsum_norm (summable_Nseq_term hs hj u).norm).trans ?_
  refine (summable_Nseq_term hs hj u).norm.tsum_le_tsum (fun m => ?_)
    ((summable_nat_add_iff u).2 hgs)
  have hM := (Mseq_nonneg hs n (u + m))
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hM, hg]
  simp only [add_comm m u]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast choose_add_le_choose_add u m j) hM

lemma Nseq_zero_eq_alt {s n : ℕ} : Nseq s n 0 = alt (Mseq s n) := by
  funext u
  simp [Nseq, alt]

/-- **The engine.**  Every `N_j`, `j ≤ 3n+1`, is strictly completely monotone (and summable). -/
theorem Nseq_strictCM {s n : ℕ} (hs : 3 ≤ s) :
    ∀ j, j ≤ 3 * n + 1 → StrictCM (Nseq s n j) ∧ Summable (Nseq s n j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hM := strictCM_Mseq (by omega : 1 ≤ s) n
    have hMs := summable_Mseq (n := n) hs
    rw [Nseq_zero_eq_alt]
    refine ⟨hM.alt hMs, ?_⟩
    exact Summable.of_nonneg_of_le (fun u => ((hM.alt hMs).pos u).le)
      (fun u => alt_le hMs hM.antitone u) hMs
  | succ j ih =>
    intro hj
    obtain ⟨hcm, hsum⟩ := ih (by omega)
    have heq : Nseq s n (j + 1) = alt (Nseq s n j) :=
      alt_of_recurrence (Nseq_rec hs hj) (Nseq_tendsto hs hj) hsum
    have hcm' : StrictCM (Nseq s n (j + 1)) := by rw [heq]; exact hcm.alt hsum
    refine ⟨hcm', ?_⟩
    refine Summable.of_nonneg_of_le (fun u => (hcm'.pos u).le) (fun u => ?_) hsum
    have := Nseq_rec hs hj u
    have := hcm'.pos (u + 1)
    linarith

/-- `Σ_u (-1)^u c_u M_u = N_{3n+1}(0) - N_{3n+1}(1)`. -/
lemma tsum_alt_cseq {s n : ℕ} (hs : 3 ≤ s) :
    ∑' u, (-1 : ℝ) ^ u * (cseq n u * Mseq s n u)
      = Nseq s n (3 * n + 1) 0 - Nseq s n (3 * n + 1) 1 := by
  have hsum : Summable (fun u => (-1 : ℝ) ^ u * (cseq n u * Mseq s n u)) := by
    refine Summable.of_norm_bounded (summable_cseq_mul_Mseq (n := n) hs) fun u => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_of_nonneg]
    exact mul_nonneg (cseq_pos n u).le (Mseq_nonneg hs n u)
  rw [hsum.tsum_eq_zero_add]
  simp only [Nseq]
  rw [(summable_Nseq_term hs le_rfl 0).tsum_eq_zero_add]
  simp only [pow_zero, cseq_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add,
    add_zero]
  rw [add_sub_assoc]
  congr 1
  have h1 : Summable (fun b : ℕ => (-1 : ℝ) ^ (b + 1)
      * (Nat.choose (b + 1 + (3 * n + 1)) (b + 1) : ℝ) * Mseq s n (b + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_Nseq_term (n := n) hs le_rfl 0)).congr fun b => by simp
  have h2 : Summable (fun m : ℕ => (-1 : ℝ) ^ m
      * (Nat.choose (m + (3 * n + 1)) m : ℝ) * Mseq s n (1 + m)) :=
    summable_Nseq_term hs le_rfl 1
  rw [← h1.tsum_sub h2]
  refine tsum_congr fun m => ?_
  rw [cseq_succ, show m + 1 + (3 * n + 1) = 3 * n + 2 + m by ring,
    show m + (3 * n + 1) = 3 * n + 1 + m by ring, show 1 + m = m + 1 by ring]
  ring

/-- **N3 (the crux).**  For odd `s ≥ 3` and even `n`, the linear form is strictly negative.
The leading term `u = 0` carries the sign `(-1)^{n+1} = -1` and dominates. -/
theorem rForm_neg {s n : ℕ} (hs : 3 ≤ s) (_hodd : Odd s) (hn : Even n) : rForm s n < 0 := by
  have hterm : ∀ u : ℕ, (-1 : ℝ) ^ (n + u + 1) * (Rval s n u : ℝ)
      = -(Cn n * ((-1 : ℝ) ^ u * (cseq n u * Mseq s n u))) := by
    intro u
    rw [Rval_eq_factor hs, pow_succ, pow_add, hn.neg_one_pow]
    ring
  unfold rForm
  simp_rw [hterm]
  rw [tsum_neg, tsum_mul_left, tsum_alt_cseq hs]
  have h := (Nseq_strictCM (n := n) hs (3 * n + 1) le_rfl).1 1 0
  simp only [Function.iterate_one, fd_apply, zero_add] at h
  have := Cn_pos n
  nlinarith

/-- **Nonvanishing** — what the ledger consumes. -/
theorem rForm_ne_zero {s n : ℕ} (hs : 3 ≤ s) (hodd : Odd s) (hn : Even n) : rForm s n ≠ 0 :=
  ne_of_lt (rForm_neg hs hodd hn)

end LeanFormalizations.DirichletBeta
