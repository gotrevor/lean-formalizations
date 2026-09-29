/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Champernowne's constant is transcendental (Mahler 1937), via Roth

`C₁₀ = 0.123456789101112…`, i.e. `∑ n / 10^{L(n)}`, where `L(n)` is the number of digits of
`1, 2, …, n` written in a row, so `n` occupies the digits ending at position `L(n)`.

## Route (phase 18)

Let `N = L(10^{k−1} − 1)` be the number of digits used by the `(k−1)`-digit numbers, and let
`a = 10^{k−1}`, `x = 10^{−k}`.  The `k`-digit block `a, a+1, a+2, …` is the start of
`∑_{j ≥ 0} (a + j) x^{j+1} = a x/(1−x) + x²/(1−x)²`, a rational with denominator dividing
`(10^k − 1)²`.  So `p_k/q_k := C_N + 10^{−N}·(that rational)`, with `C_N` the first `N` digits, has
`q_k ∣ 10^N (10^k − 1)²` and agrees with `C` until the `k`-digit block runs out, at digit about
`N + 9k·10^{k−1}`.  Numerically (`scripts/champernowne-approx.py`), `−log|C − p_k/q_k| / log q_k`
is `16.2, 15.0, 13.4` for `k = 2, 3, 4`, decreasing to Amou's irrationality measure `10` (1991).
Anything above `2 + δ` for infinitely many distinct `p_k/q_k` contradicts `Roth1955`.

Leaves: the tail identity (a finite geometric-arithmetic sum plus a tail bound), the denominator
bound, the error bound `|C − p_k/q_k| ≤ q_k^{−3}` (say) for `k ≥ 2`, and distinctness of the
`p_k/q_k`.  Note that Roth's set uses `r.den` in lowest terms, which is at most `q_k`, so the
bound only improves.  Normality of `C₁₀` belongs in `normal-numbers`.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.NumberTheory.Diophantine.StephanEdges

namespace LeanFormalizations.Champernowne

open LeanFormalizations.Literature

/-- Total number of decimal digits of `1, 2, …, n`. -/
def digitsUpTo (n : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 n, (Nat.digits 10 m).length

/-- **Champernowne's constant** `0.123456789101112…`: the integer `n` is written so that its
last digit is decimal place `digitsUpTo n`. -/
noncomputable def champernowne : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 10 ^ digitsUpTo (n + 1)


/-! ## Leaf 1: the digit-counting function `digitsUpTo` -/

lemma digitsUpTo_succ (n : ℕ) :
    digitsUpTo (n + 1) = digitsUpTo n + (Nat.digits 10 (n + 1)).length := by
  unfold digitsUpTo
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- A number with `10 ^ m ≤ n < 10 ^ (m+1)` has exactly `m + 1` decimal digits. -/
lemma digits_len_of_mem_block {m n : ℕ} (h₁ : 10 ^ m ≤ n) (h₂ : n < 10 ^ (m + 1)) :
    (Nat.digits 10 n).length = m + 1 := by
  have hp : 0 < 10 ^ m := pow_pos (by norm_num) m
  have hn : n ≠ 0 := by omega
  rw [Nat.length_digits 10 n (by norm_num) hn, Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂]

/-- `N m` = number of decimal digits used by all of `1, 2, …, 10 ^ m − 1`. -/
abbrev blockStart (m : ℕ) : ℕ := digitsUpTo (10 ^ m - 1)

/-- Inside the block of `(m+1)`-digit numbers, `digitsUpTo` is arithmetic with step `m + 1`. -/
lemma digitsUpTo_block (m : ℕ) : ∀ j : ℕ, j < 9 * 10 ^ m →
    digitsUpTo (10 ^ m + j) = blockStart m + (m + 1) * (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h1 : (1:ℕ) ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have : 10 ^ m + 0 = (10 ^ m - 1) + 1 := by omega
    rw [this, digitsUpTo_succ]
    have : (10 ^ m - 1) + 1 = 10 ^ m := by omega
    rw [this, digits_len_of_mem_block (le_refl _) (by
      have : (10:ℕ) ^ m * 1 < 10 ^ m * 10 := by
        have := Nat.one_le_pow m 10 (by norm_num); omega
      simpa [pow_succ] using this)]
    ring
  | succ j ih =>
    intro hj
    have hj' : j < 9 * 10 ^ m := by omega
    have heq : 10 ^ m + (j + 1) = (10 ^ m + j) + 1 := by ring
    rw [heq, digitsUpTo_succ, ih hj']
    have hlen : (Nat.digits 10 (10 ^ m + j + 1)).length = m + 1 := by
      refine digits_len_of_mem_block (by omega) ?_
      have : (10:ℕ) ^ (m+1) = 10 ^ m * 10 := by ring
      omega
    rw [hlen]; ring


lemma blockStart_succ (m : ℕ) :
    blockStart (m + 1) = blockStart m + (m + 1) * (9 * 10 ^ m) := by
  have h1 : (1:ℕ) ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have h : (10:ℕ) ^ (m + 1) - 1 = 10 ^ m + (9 * 10 ^ m - 1) := by
    have : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
    omega
  rw [show blockStart (m+1) = digitsUpTo (10 ^ (m+1) - 1) from rfl, h,
    digitsUpTo_block m (9 * 10 ^ m - 1) (by omega)]
  congr 2
  omega

/-! ## Leaf 2: term bounds, summability, tail estimates -/

/-- The `n`-th summand of Champernowne's constant. -/
noncomputable def cterm (n : ℕ) : ℝ := (n : ℝ) / 10 ^ digitsUpTo n

lemma champernowne_eq_tsum : champernowne = ∑' n : ℕ, cterm (n + 1) := rfl

lemma one_le_digits_len {n : ℕ} (hn : n ≠ 0) : 1 ≤ (Nat.digits 10 n).length := by
  cases h : Nat.digits 10 n with
  | nil => exact absurd (Nat.digits_eq_nil_iff_eq_zero.mp h) hn
  | cons a l => simp

lemma digitsUpTo_add_le (M : ℕ) : ∀ i : ℕ, digitsUpTo M + i ≤ digitsUpTo (M + i) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : M + (i + 1) = M + i + 1 := by omega
    rw [e]
    have := one_le_digits_len (n := M + i + 1) (by omega)
    have h := digitsUpTo_succ (M + i)
    omega

@[simp] lemma digitsUpTo_zero : digitsUpTo 0 = 0 := by simp [digitsUpTo]

lemma le_digitsUpTo (n : ℕ) : n ≤ digitsUpTo n := by
  simpa using digitsUpTo_add_le 0 n

lemma cterm_nonneg (n : ℕ) : 0 ≤ cterm n := by
  unfold cterm; positivity

/-- The key size bound: the `(n+1)`-st term is below `10 ^ (−digitsUpTo n)`. -/
lemma cterm_succ_lt (n : ℕ) : cterm (n + 1) < 1 / 10 ^ digitsUpTo n := by
  have hlt : (n + 1 : ℕ) < 10 ^ (Nat.digits 10 (n + 1)).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have hlt' : ((n + 1 : ℕ) : ℝ) < 10 ^ (Nat.digits 10 (n + 1)).length := by
    exact_mod_cast hlt
  unfold cterm
  rw [digitsUpTo_succ, pow_add]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 : (0:ℝ) < 10 ^ digitsUpTo n := by positivity
  nlinarith [hlt', h1]

lemma summable_cterm : Summable fun n : ℕ => cterm (n + 1) := by
  apply Summable.of_nonneg_of_le (fun n => cterm_nonneg _) (fun n => (cterm_succ_lt n).le)
  have : ∀ n : ℕ, (1:ℝ) / 10 ^ digitsUpTo n ≤ (1/10 : ℝ) ^ n := by
    intro n
    rw [div_pow, one_pow, one_div, one_div, inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (le_digitsUpTo n)
  exact Summable.of_nonneg_of_le (fun n => by positivity) this
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- Shifted summability: the tail starting at `K + 1`. -/
lemma summable_cterm_shift (K : ℕ) : Summable fun i : ℕ => cterm (K + 1 + i) := by
  exact ((summable_nat_add_iff K).mpr summable_cterm).congr (fun i => by congr 1; omega)

/-- The tail of Champernowne's series past `K`. -/
noncomputable def ctail (K : ℕ) : ℝ := ∑' i : ℕ, cterm (K + 1 + i)

lemma ctail_nonneg (K : ℕ) : 0 ≤ ctail K :=
  tsum_nonneg fun i => cterm_nonneg _

lemma ctail_pos (K : ℕ) : 0 < ctail K := by
  refine lt_of_lt_of_le ?_ ((summable_cterm_shift K).le_tsum 0 (fun i _ => cterm_nonneg _))
  have : cterm (K + 1 + 0) = ((K+1:ℕ):ℝ) / 10 ^ digitsUpTo (K+1+0) := rfl
  rw [this]
  positivity

lemma ctail_le (K : ℕ) : ctail K ≤ (10/9) * (1 / 10 ^ digitsUpTo K) := by
  have hb : ∀ i : ℕ, cterm (K + 1 + i) ≤ (1 / 10 ^ digitsUpTo K) * (1/10 : ℝ) ^ i := by
    intro i
    have h1 : cterm (K + i + 1) < 1 / 10 ^ digitsUpTo (K + i) := cterm_succ_lt _
    have h2 : digitsUpTo K + i ≤ digitsUpTo (K + i) := digitsUpTo_add_le K i
    have h3 : (1:ℝ) / 10 ^ digitsUpTo (K + i) ≤ 1 / 10 ^ (digitsUpTo K + i) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) h2
    have : cterm (K + 1 + i) = cterm (K + i + 1) := by ring_nf
    rw [this]
    calc cterm (K + i + 1) ≤ 1 / 10 ^ (digitsUpTo K + i) := le_trans h1.le h3
      _ = (1 / 10 ^ digitsUpTo K) * (1/10 : ℝ) ^ i := by
          rw [pow_add, div_pow, one_pow]; field_simp
  have hs : Summable fun i : ℕ => (1 / 10 ^ digitsUpTo K : ℝ) * (1/10 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  show (∑' i : ℕ, cterm (K + 1 + i)) ≤ _
  refine le_trans ((summable_cterm_shift K).tsum_le_tsum hb hs) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num),
    show ((1:ℝ) - 1/10)⁻¹ = 10/9 by norm_num]
  ring_nf
  exact le_refl _

lemma ctail_succ (K : ℕ) : ctail K = cterm (K + 1) + ctail (K + 1) := by
  show (∑' i : ℕ, cterm (K + 1 + i)) = _
  rw [(summable_cterm_shift K).tsum_eq_zero_add]
  congr 1
  exact tsum_congr fun i => by congr 1; omega


/-! ## Leaf 3: partial sums are explicit rationals, and the block split -/

/-- The integer formed by writing `1, 2, …, K` in a row. -/
def prefixNum : ℕ → ℕ
  | 0 => 0
  | K + 1 => prefixNum K * 10 ^ (Nat.digits 10 (K + 1)).length + (K + 1)

/-- The partial sum of Champernowne's series. -/
noncomputable def cpartial (K : ℕ) : ℝ := ∑ i ∈ Finset.range K, cterm (i + 1)

lemma cpartial_eq (K : ℕ) : cpartial K = (prefixNum K : ℝ) / 10 ^ digitsUpTo K := by
  induction K with
  | zero => simp [cpartial, prefixNum]
  | succ K ih =>
    rw [cpartial, Finset.sum_range_succ, ← cpartial, ih, prefixNum, digitsUpTo_succ]
    have h1 : (0:ℝ) < 10 ^ digitsUpTo K := by positivity
    have h2 : (0:ℝ) < 10 ^ (Nat.digits 10 (K + 1)).length := by positivity
    unfold cterm
    rw [digitsUpTo_succ]
    push_cast
    rw [pow_add]
    field_simp

lemma champ_split (K : ℕ) : champernowne = cpartial K + ctail K := by
  have h := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => cterm (n + 1)) K summable_cterm
  rw [champernowne_eq_tsum, ← h]
  congr 1
  exact tsum_congr fun i => by congr 1; omega

/-- The `j`-th term of the geometric-arithmetic series continuing the `(m+1)`-digit block. -/
noncomputable def gser (m j : ℕ) : ℝ :=
  ((10 ^ m + j : ℕ) : ℝ) / 10 ^ (blockStart m + (m + 1) * (j + 1))

lemma cterm_eq_gser {m i : ℕ} (hi : i < 9 * 10 ^ m) : cterm (10 ^ m + i) = gser m i := by
  unfold cterm gser
  rw [digitsUpTo_block m i hi]

lemma hasSum_gser (m : ℕ) :
    HasSum (gser m)
      (((10:ℝ) ^ m * (10 ^ (m + 1) - 1) + 1) / (10 ^ blockStart m * (10 ^ (m + 1) - 1) ^ 2)) := by
  set T : ℝ := (10:ℝ) ^ (m + 1) with hTdef
  have hT10 : (10:ℝ) ≤ T := by
    rw [hTdef]; calc (10:ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (m+1) := by apply pow_le_pow_right₀ (by norm_num); omega
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : T - 1 ≠ 0 := by intro h; linarith [h ▸ (by linarith : (9:ℝ) ≤ T - 1)]
  set y : ℝ := T⁻¹ with hy
  have hy1 : |y| < 1 := by
    rw [hy, abs_of_pos (by positivity)]
    rw [inv_lt_one_iff₀]; right; linarith
  have h1 : HasSum (fun j : ℕ => y ^ j) (1 - y)⁻¹ :=
    hasSum_geometric_of_abs_lt_one hy1
  have h2 : HasSum (fun j : ℕ => (j : ℝ) * y ^ j) (y / (1 - y) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by simpa using hy1)
  have h3 := ((h1.mul_left ((10:ℝ) ^ m)).add h2).mul_left
    (1 / ((10:ℝ) ^ blockStart m * T))
  have hval : (1 / ((10:ℝ) ^ blockStart m * T)) *
      ((10:ℝ) ^ m * (1 - y)⁻¹ + y / (1 - y) ^ 2) =
      ((10:ℝ) ^ m * (T - 1) + 1) / (10 ^ blockStart m * (T - 1) ^ 2) := by
    rw [hy]
    have h10 : ((10:ℝ) ^ blockStart m) ≠ 0 := by positivity
    field_simp
  rw [hval] at h3
  refine h3.congr_fun fun j => ?_
  have hT0' : T ≠ 0 := ne_of_gt hT0
  have hpow : (10:ℝ) ^ (blockStart m + (m + 1) * (j + 1))
      = 10 ^ blockStart m * T * T ^ j := by
    rw [hTdef, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  unfold gser
  rw [hpow, hy, inv_pow]
  push_cast
  field_simp

lemma summable_gser (m : ℕ) : Summable (gser m) := (hasSum_gser m).summable

/-- The tail of the continued block series past its `9·10^m` genuine terms. -/
noncomputable def gtail (m : ℕ) : ℝ := ∑' j : ℕ, gser m (9 * 10 ^ m + j)

lemma gser_block_sum (m : ℕ) :
    ∑ i ∈ Finset.range (9 * 10 ^ m), gser m i =
      (((10:ℝ) ^ m * (10 ^ (m + 1) - 1) + 1) /
        (10 ^ blockStart m * (10 ^ (m + 1) - 1) ^ 2)) - gtail m := by
  have h := Summable.sum_add_tsum_nat_add (f := gser m) (9 * 10 ^ m) (summable_gser m)
  rw [(hasSum_gser m).tsum_eq] at h
  unfold gtail
  have : (∑' j : ℕ, gser m (9 * 10 ^ m + j)) = ∑' j : ℕ, gser m (j + 9 * 10 ^ m) :=
    tsum_congr fun j => by congr 1; omega
  rw [this]
  linarith


/-! ## Leaf 4: the master identity `C − p_m/q_m = ctail − gtail` -/

lemma ctail_block (m : ℕ) :
    ctail (10 ^ m - 1) =
      (∑ i ∈ Finset.range (9 * 10 ^ m), cterm (10 ^ m + i)) + ctail (10 ^ (m + 1) - 1) := by
  have ha : (1:ℕ) ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hpow : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
  have hs : Summable (fun i : ℕ => cterm (10 ^ m + i)) :=
    (summable_cterm_shift (10 ^ m - 1)).congr (fun i => by congr 1; omega)
  have h := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => cterm (10 ^ m + i)) (9 * 10 ^ m) hs
  have e1 : ctail (10 ^ m - 1) = ∑' i : ℕ, cterm (10 ^ m + i) :=
    tsum_congr fun i => by congr 1; omega
  have e2 : ctail (10 ^ (m + 1) - 1) = ∑' i : ℕ, cterm (10 ^ m + (i + 9 * 10 ^ m)) :=
    tsum_congr fun i => by congr 1; omega
  rw [e1, e2, ← h]

lemma champ_sub_approx (m : ℕ) :
    champernowne - (cpartial (10 ^ m - 1) +
        ((10:ℝ) ^ m * (10 ^ (m + 1) - 1) + 1) /
          (10 ^ blockStart m * (10 ^ (m + 1) - 1) ^ 2))
      = ctail (10 ^ (m + 1) - 1) - gtail m := by
  have hblk : ∑ i ∈ Finset.range (9 * 10 ^ m), cterm (10 ^ m + i)
      = ∑ i ∈ Finset.range (9 * 10 ^ m), gser m i :=
    Finset.sum_congr rfl fun i hi => cterm_eq_gser (Finset.mem_range.mp hi)
  have h := champ_split (10 ^ m - 1)
  rw [ctail_block m, hblk, gser_block_sum m] at h
  linarith

/-! ### The approximation as an explicit rational -/

/-- Numerator of the `m`-th block approximation. -/
def champNum (m : ℕ) : ℕ :=
  prefixNum (10 ^ m - 1) * (10 ^ (m + 1) - 1) ^ 2 + 10 ^ m * (10 ^ (m + 1) - 1) + 1

/-- Denominator of the `m`-th block approximation: `10^N · (10^{m+1} − 1)²`. -/
def champDen (m : ℕ) : ℕ := 10 ^ blockStart m * (10 ^ (m + 1) - 1) ^ 2

lemma champDen_pos (m : ℕ) : 0 < champDen m := by
  have h1 : (1:ℕ) ≤ 10 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h9 : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
  have ha : (1:ℕ) ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have : 0 < 10 ^ (m + 1) - 1 := by omega
  unfold champDen
  positivity

/-- The `m`-th block approximation to Champernowne's constant. -/
noncomputable def champApprox (m : ℕ) : ℚ := (champNum m : ℚ) / (champDen m : ℚ)

lemma champApprox_cast (m : ℕ) :
    ((champApprox m : ℚ) : ℝ) = cpartial (10 ^ m - 1) +
      ((10:ℝ) ^ m * (10 ^ (m + 1) - 1) + 1) /
        (10 ^ blockStart m * (10 ^ (m + 1) - 1) ^ 2) := by
  have h1 : (1:ℕ) ≤ 10 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hA : ((10:ℝ) ^ (m + 1) - 1) ≠ 0 := by
    have : (10:ℝ) ≤ 10 ^ (m + 1) := by
      calc (10:ℝ) = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (m + 1) := by apply pow_le_pow_right₀ (by norm_num); omega
    intro h; linarith
  have hB : ((10:ℝ) ^ blockStart m) ≠ 0 := by positivity
  rw [cpartial_eq]
  unfold champApprox champNum champDen
  push_cast [Nat.cast_sub h1]
  rw [show digitsUpTo (10 ^ m - 1) = blockStart m from rfl]
  field_simp
  ring

/-- The denominator of the reduced rational divides the explicit `champDen`. -/
lemma champApprox_den_dvd (m : ℕ) : (champApprox m).den ∣ champDen m := by
  have h := Rat.den_dvd (champNum m : ℤ) (champDen m : ℤ)
  have e : ((champNum m : ℤ) : ℚ) / ((champDen m : ℤ) : ℚ) = champApprox m := by
    unfold champApprox; push_cast; ring
  rw [Rat.divInt_eq_div, e] at h
  exact_mod_cast h


/-! ## Leaf 5: numeric bounds on the two tails -/

lemma gser_nonneg (m j : ℕ) : 0 ≤ gser m j := by unfold gser; positivity

lemma summable_gtail (m : ℕ) : Summable fun j : ℕ => gser m (9 * 10 ^ m + j) :=
  ((summable_nat_add_iff (9 * 10 ^ m)).mpr (summable_gser m)).congr
    (fun j => by congr 1; omega)

lemma gser_first (m : ℕ) : gser m (9 * 10 ^ m) = 1 / 10 ^ blockStart (m + 1) := by
  have hnum : (10:ℕ) ^ m + 9 * 10 ^ m = 10 ^ (m + 1) := by ring
  have hexp : blockStart m + (m + 1) * (9 * 10 ^ m + 1) = blockStart (m + 1) + (m + 1) := by
    rw [blockStart_succ]; ring
  unfold gser
  rw [hnum, hexp, pow_add]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

lemma gtail_ge (m : ℕ) : 1 / 10 ^ blockStart (m + 1) ≤ gtail m := by
  have h := (summable_gtail m).le_tsum 0 (fun j _ => gser_nonneg _ _)
  rw [← gser_first m]
  simpa [gtail] using h

/-- `∑' j, (j+1) r^j = (1−r)⁻²` for `0 ≤ r < 1`; the instance we need is `r = 1/10`. -/
lemma tsum_succ_mul_geometric_tenth :
    ∑' j : ℕ, ((j : ℝ) + 1) * (1/10 : ℝ) ^ j = 100 / 81 := by
  have h1 : HasSum (fun j : ℕ => (1/10 : ℝ) ^ j) (1 - 1/10)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have h2 : HasSum (fun j : ℕ => (j : ℝ) * (1/10 : ℝ) ^ j) ((1/10 : ℝ) / (1 - 1/10) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)
  have h3 := h2.add h1
  have : ((1/10 : ℝ) / (1 - 1/10) ^ 2 + (1 - 1/10)⁻¹) = 100 / 81 := by norm_num
  rw [this] at h3
  exact (h3.congr_fun fun j => by ring).tsum_eq

lemma gtail_le (m : ℕ) : gtail m ≤ 2 * (1 / 10 ^ blockStart (m + 1)) := by
  have hT : (10:ℝ) ≤ 10 ^ (m + 1) := by
    calc (10:ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (m + 1) := by apply pow_le_pow_right₀ (by norm_num); omega
  have key : ∀ j : ℕ, gser m (9 * 10 ^ m + j) ≤
      (1 / 10 ^ blockStart (m + 1)) * (((j : ℝ) + 1) * (1/10 : ℝ) ^ j) := by
    intro j
    have hnum : (10:ℕ) ^ m + (9 * 10 ^ m + j) = 10 ^ (m + 1) + j := by ring
    have hexp : blockStart m + (m + 1) * (9 * 10 ^ m + j + 1)
        = blockStart (m + 1) + (m + 1) + (m + 1) * j := by rw [blockStart_succ]; ring
    have hc : (((10 ^ (m + 1) + j : ℕ)) : ℝ) = (10:ℝ) ^ (m + 1) + (j : ℝ) := by push_cast; ring
    have hden : (10:ℝ) ^ (blockStart (m + 1) + (m + 1) + (m + 1) * j)
        = 10 ^ blockStart (m + 1) * 10 ^ (m + 1) * ((10:ℝ) ^ (m + 1)) ^ j := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    unfold gser
    rw [hnum, hexp, hc, hden]
    set X : ℝ := (10:ℝ) ^ (m + 1) with hXdef
    set P : ℝ := (10:ℝ) ^ blockStart (m + 1) with hPdef
    have hX : (10:ℝ) ≤ X := hT
    have hP : (0:ℝ) < P := by rw [hPdef]; positivity
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hXj : (0:ℝ) < X ^ j := by positivity
    have hZ : (0:ℝ) < (10:ℝ) ^ j := by positivity
    have hZY : (10:ℝ) ^ j ≤ X ^ j := pow_le_pow_left₀ (by norm_num) hX j
    have hR : (1 / P) * (((j : ℝ) + 1) * (1/10 : ℝ) ^ j) = ((j : ℝ) + 1) / (P * 10 ^ j) := by
      rw [div_pow, one_pow]; field_simp
    rw [hR, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (X + (j : ℝ)) * (P * 10 ^ j) ≤ (((j : ℝ) + 1) * X) * (P * 10 ^ j) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [hX, hj]
      _ ≤ (((j : ℝ) + 1) * X) * (P * X ^ j) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hZY hP.le
      _ = ((j : ℝ) + 1) * (P * X * X ^ j) := by ring
  have hs : Summable fun j : ℕ =>
      (1 / 10 ^ blockStart (m + 1) : ℝ) * (((j : ℝ) + 1) * (1/10 : ℝ) ^ j) := by
    have h1 : Summable (fun j : ℕ => (j : ℝ) * (1/10 : ℝ) ^ j) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/10:ℝ))
        (by rw [Real.norm_eq_abs]; norm_num)).summable
    have h2 : Summable (fun j : ℕ => (1/10 : ℝ) ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact ((h1.add h2).congr (fun j => by ring)).mul_left _
  have hle := (summable_gtail m).tsum_le_tsum key hs
  rw [tsum_mul_left, tsum_succ_mul_geometric_tenth] at hle
  have hB : (0:ℝ) < 1 / 10 ^ blockStart (m + 1) := by positivity
  calc gtail m ≤ 1 / 10 ^ blockStart (m + 1) * (100 / 81) := hle
    _ ≤ 2 * (1 / 10 ^ blockStart (m + 1)) := by linarith

lemma digitsUpTo_pow (m : ℕ) : digitsUpTo (10 ^ (m + 1)) = blockStart (m + 1) + (m + 2) := by
  have h := digitsUpTo_block (m + 1) 0 (by positivity)
  simpa using h

lemma ctail_block_le (m : ℕ) :
    ctail (10 ^ (m + 1) - 1) ≤ (1/5) * (1 / 10 ^ blockStart (m + 1)) := by
  have h1 : (1:ℕ) ≤ 10 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hK : 10 ^ (m + 1) - 1 + 1 = 10 ^ (m + 1) := by omega
  have hsucc := ctail_succ (10 ^ (m + 1) - 1)
  rw [hK] at hsucc
  have hterm : cterm (10 ^ (m + 1)) = (1/10) * (1 / 10 ^ blockStart (m + 1)) := by
    unfold cterm
    rw [digitsUpTo_pow m]
    have hc : (((10:ℕ) ^ (m + 1) : ℕ) : ℝ) = (10:ℝ) ^ (m + 1) := by push_cast; ring
    rw [hc, show blockStart (m + 1) + (m + 2) = blockStart (m + 1) + 1 + (m + 1) by omega,
      pow_add, pow_add]
    have hb : (0:ℝ) < 10 ^ blockStart (m + 1) := by positivity
    have hx : (0:ℝ) < (10:ℝ) ^ (m + 1) := by positivity
    field_simp
    ring
  have htail : ctail (10 ^ (m + 1)) ≤ (10/9) * (1 / 10 ^ digitsUpTo (10 ^ (m + 1))) :=
    ctail_le _
  have hmono : (1:ℝ) / 10 ^ digitsUpTo (10 ^ (m + 1)) ≤
      (1/100) * (1 / 10 ^ blockStart (m + 1)) := by
    rw [digitsUpTo_pow m, show blockStart (m + 1) + (m + 2) = blockStart (m + 1) + 2 + m by omega,
      pow_add, pow_add]
    have hb : (0:ℝ) < 10 ^ blockStart (m + 1) := by positivity
    have e : (1:ℝ) / (10 ^ blockStart (m + 1) * 10 ^ 2 * 10 ^ m)
        = (1/100) * (1 / 10 ^ blockStart (m + 1)) * (1 / 10 ^ m) := by
      field_simp; ring
    rw [e]
    have h10 : (1:ℝ) / 10 ^ m ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    nlinarith [h10, (by positivity : (0:ℝ) < (1/100 : ℝ) * (1 / 10 ^ blockStart (m + 1)))]
  have hbpos : (0:ℝ) < 1 / 10 ^ blockStart (m + 1) := by positivity
  rw [hsucc, hterm]
  linarith [htail, hmono, hbpos]

/-- Sanity anchor for the definition: the first eleven digits are `12345678910`. -/
theorem champernowne_prefix :
    ⌊champernowne * 10 ^ 11⌋ = 12345678910 := by
  sorry

/-- Champernowne's constant is irrational (unconditional). -/
theorem irrational_champernowne : Irrational champernowne := by
  sorry

/-- **Mahler (1937)**: Champernowne's constant is transcendental, from Roth's theorem. -/
theorem transcendental_champernowne (hR : Roth1955) : Transcendental ℚ champernowne := by
  sorry

/-- The same, from Stephan's machine-checked Ridout theorem (`roth1955_of_stephan`). -/
theorem transcendental_champernowne_of_stephan (h : Stephan2026Ridout) :
    Transcendental ℚ champernowne :=
  transcendental_champernowne (Diophantine.roth1955_of_stephan h)

end LeanFormalizations.Champernowne
