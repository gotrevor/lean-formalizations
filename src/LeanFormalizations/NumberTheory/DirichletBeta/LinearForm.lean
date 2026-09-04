/-
# N2 — the decomposition: `d_n^s · r_n` is an integer combination of `1, β(2), β(4), …, β(s-1)`

The arithmetic heart.  Partial fractions of `R_n`,

    R_n(t) = Σ_{i=1}^{s} Σ_{k=0}^{n} a_{i,k} / (t+k)^i,

give `r_n = Σ_{i even, 2 ≤ i ≤ s-1} A_i β(i) + A_0` with `A_i = 2^i Σ_k (-1)^{k-1} a_{i,k}`.  Two
facts do the work:

* **integrality** (SIGMA Lemma 1): `d_n^{s-i} a_{i,k} ∈ ℤ`, where `d_n = lcm(1,…,n)`;
* **odd vanishing**: `R_n(-t-n) = R_n(t)` for odd `s`, which kills `A_i` for odd `i`.

The frozen statement below asks only for what the ledger actually consumes: **some** integer
vector `A` with `d_n^s · r_n = A_0 + Σ_i A_i β(2i)`.  That is implied by the finer
`d_n^{s-i} A_i ∈ ℤ` (multiply by `d_n^i`), and it is strictly easier to prove, so it does not
commit the treadmill to a particular partial-fraction route.

✅ Validated numerically (`papers/catalan-beta-validate.py`) at `(n,s) ∈ {(2,5),(4,5),(2,7),(4,7),(6,7)}`:
`d_n^{s-i} a_{i,k} ∈ ℤ`, the odd `A_i` vanish, the decomposition reproduces `r_n`, and every
`d_n^{s-i} A_i`, `d_n^s A_0` has denominator `1`.  **Hypotheses `Odd s`, `Even n` are exactly the
range validated** — do not weaken them without a fresh probe (the Phase 3 `E1` lesson).
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Beta
import LeanFormalizations.NumberTheory.DirichletBeta.Rational
import LeanFormalizations.NumberTheory.DirichletBeta.Blocks
import LeanFormalizations.NumberTheory.DirichletBeta.Symmetry
import LeanFormalizations.NumberTheory.DirichletBeta.PartialSums

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- `d_n = lcm(1, …, n)`, as in `Mathlib.NumberTheory.Chebyshev`. -/
noncomputable abbrev dn (n : ℕ) : ℕ := Nat.lcmUpto n

/-- The half-integers `w + ½ - m` are never poles. -/
lemma nonPole_half (m w : ℕ) : NonPole (m + m) ((w : ℚ) + 1 / 2 - m) := by
  intro k _ h
  have h' : ((2 * w + 2 * k + 1 : ℕ) : ℚ) = ((2 * m : ℕ) : ℚ) := by push_cast; linarith
  have := Nat.cast_injective h'
  omega

/-- Odd-index reindexing: if `f` vanishes at even indices, `Σ_{i<2h+1} f i = Σ_{j=1}^{h} f (2j-1)`. -/
lemma sum_range_odd_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : ∀ i, Even i → f i = 0) :
    ∀ h : ℕ, ∑ i ∈ range (2 * h + 1), f i = ∑ j ∈ Icc 1 h, f (2 * j - 1) := by
  intro h
  induction h with
  | zero => simp [hf 0 ⟨0, rfl⟩]
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_Icc_succ_top (by omega), hf (2 * h + 1 + 1) ⟨h + 1, by ring⟩, add_zero,
      show 2 * (h + 1) - 1 = 2 * h + 1 by omega]

/-- **N2 (the decomposition).**  For odd `s ≥ 3` and even `n`, `d_n^s · r_n` is a ℤ-linear
combination of `1` and the even beta values `β(2), β(4), …, β(s-1)`.

The `β` indices are `2i` for `1 ≤ i ≤ (s-1)/2`; at `s = 21` that is `β(2), β(4), …, β(20)`. -/
theorem exists_int_combination {s n : ℕ} (hs : 3 ≤ s) (hodd : Odd s) (hn : Even n) :
    ∃ A : ℕ → ℤ,
      ((dn n : ℝ)) ^ s * rForm s n
        = (A 0 : ℝ) + ∑ i ∈ Icc 1 ((s - 1) / 2), (A i : ℝ) * dirichletBeta (2 * i) := by
  obtain ⟨m, rfl⟩ := hn
  set n := m + m with hn_def
  have hn : Even n := ⟨m, rfl⟩
  -- the symmetrized representation
  obtain ⟨b, hbint, hbsym, hbrep⟩ := (rep_Rfun hs n).symmetrize hodd hn
  choose! zb hzb using hbint
  -- the limits `L_q`
  have hLex : ∀ q : ℕ, ∃ L : ℝ, 1 ≤ q → Tendsto (Eps q) atTop (𝓝 L) := by
    intro q
    by_cases hq : 1 ≤ q
    · obtain ⟨L, hL⟩ := exists_tendsto_Eps hq
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose L hL using hLex
  -- the per-term limits
  have hFex : ∀ i ∈ range s, ∀ k ∈ range (n + 1), ∃ F : ℚ,
      (∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ (i + 1) * F = 2 * z) ∧
      Tendsto (Tps (i + 1) ((k : ℝ) - m + 1 / 2)) atTop
        (𝓝 ((-1) ^ (k + m) * 2 ^ (i + 1) * L (i + 1) + F)) := by
    intro i _ k hk
    have hk' := mem_range.1 hk
    have hL' := hL (i + 1) (by omega)
    by_cases hkm : m ≤ k
    · obtain ⟨F, hF, hT⟩ := tendsto_Tps_pos (by omega) hL' n (k - m) (by omega)
      refine ⟨F, hF, ?_⟩
      rw [Nat.cast_sub hkm] at hT
      have : (-1 : ℝ) ^ (k - m) = (-1) ^ (k + m) := by
        rw [neg_one_pow_eq_pow_mod_two (n := k - m), neg_one_pow_eq_pow_mod_two (n := k + m)]
        congr 1; omega
      rw [this] at hT
      exact hT.congr fun W => by rw [show (k : ℝ) - m + 1 / 2 = (k : ℝ) - m + 1 / 2 from rfl]
    · obtain ⟨F, hF, hT⟩ := tendsto_Tps_neg (by omega) hL' n (m - k) (by omega)
      refine ⟨F, hF, ?_⟩
      rw [Nat.cast_sub (by omega)] at hT
      have : (-1 : ℝ) ^ (m - k) = (-1) ^ (k + m) := by
        rw [neg_one_pow_eq_pow_mod_two (n := m - k), neg_one_pow_eq_pow_mod_two (n := k + m)]
        congr 1; omega
      rw [this] at hT
      exact hT.congr fun W => by rw [show (1 / 2 : ℝ) - ((m : ℝ) - k) = (k : ℝ) - m + 1 / 2 by ring]
  choose! F hF using hFex
  -- the partial sums
  set PS : ℕ → ℝ := fun W => ∑ w ∈ range W,
    (-1 : ℝ) ^ (w + m + 1) * ((Rfun s n ((w : ℚ) + 1 / 2 - m) : ℚ) : ℝ) with hPS
  -- (i) `PS → rForm`
  have hPS_lim : Tendsto PS atTop (𝓝 (rForm s n)) := by
    have hsum : Summable (fun u : ℕ => (-1 : ℝ) ^ (n + u + 1) * (Rval s n u : ℝ)) := by
      refine Summable.of_norm_bounded (summable_Rval (n := n) hs) fun u => ?_
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact le_of_eq (Real.norm_of_nonneg (by exact_mod_cast (Rval_pos s n u).le))
    have h1 := hsum.hasSum.tendsto_sum_nat
    rw [← tendsto_add_atTop_iff_nat (3 * m)]
    refine h1.congr fun U => ?_
    simp only [hPS]
    rw [show U + 3 * m = 3 * m + U by ring, sum_range_add]
    have hz : ∑ w ∈ range (3 * m), (-1 : ℝ) ^ (w + m + 1) * ((Rfun s n ((w : ℚ) + 1 / 2 - m) : ℚ) : ℝ) = 0 := by
      refine sum_eq_zero fun w hw => ?_
      rw [Rfun_vanish s m w (mem_range.1 hw)]; simp
    rw [hz, zero_add]
    refine sum_congr rfl fun u _ => ?_
    rw [Rval_eq_Rfun]
    have hsgn : (-1 : ℝ) ^ (n + u + 1) = (-1) ^ (3 * m + u + m + 1) := by
      rw [neg_one_pow_eq_pow_mod_two (n := n + u + 1),
        neg_one_pow_eq_pow_mod_two (n := 3 * m + u + m + 1)]
      congr 1; omega
    rw [hsgn]
    congr 3
    rw [hn_def]; push_cast; ring
  -- (ii) `PS W` expanded through the partial fractions
  have hPS_eq : ∀ W, PS W = ∑ k ∈ range (n + 1), ∑ i ∈ range s,
      ((b i k : ℝ) * (-1) ^ (m + 1)) * Tps (i + 1) ((k : ℝ) - m + 1 / 2) W := by
    intro W
    simp only [hPS]
    have hrw : ∀ w ∈ range W, (-1 : ℝ) ^ (w + m + 1) * ((Rfun s n ((w : ℚ) + 1 / 2 - m) : ℚ) : ℝ)
        = ∑ k ∈ range (n + 1), ∑ i ∈ range s,
            ((b i k : ℝ) * (-1) ^ (m + 1)) * ((-1) ^ w / ((w : ℝ) + ((k : ℝ) - m + 1 / 2)) ^ (i + 1)) := by
      intro w _
      rw [hbrep _ (nonPole_half m w)]
      simp only [pfSum]
      push_cast
      simp only [mul_sum]
      refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
      rw [show ((w : ℝ) + 1 / 2 - m + k) = (w : ℝ) + ((k : ℝ) - m + 1 / 2) by ring, pow_add,
        pow_add (-1 : ℝ) w m]
      ring
    rw [sum_congr rfl hrw, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    simp only [Tps, mul_sum]
  -- (iii) the limit of the expansion
  have hlim2 : Tendsto (fun W => ∑ k ∈ range (n + 1), ∑ i ∈ range s,
      ((b i k : ℝ) * (-1) ^ (m + 1)) * Tps (i + 1) ((k : ℝ) - m + 1 / 2) W) atTop
      (𝓝 (∑ k ∈ range (n + 1), ∑ i ∈ range s,
        ((b i k : ℝ) * (-1) ^ (m + 1)) * ((-1) ^ (k + m) * 2 ^ (i + 1) * L (i + 1) + F i k))) := by
    refine tendsto_finsetSum _ fun k hk => tendsto_finsetSum _ fun i hi => ?_
    exact ((hF i hi k hk).2).const_mul _
  have hEq : rForm s n = ∑ k ∈ range (n + 1), ∑ i ∈ range s,
      ((b i k : ℝ) * (-1) ^ (m + 1)) * ((-1) ^ (k + m) * 2 ^ (i + 1) * L (i + 1) + F i k) :=
    tendsto_nhds_unique hPS_lim (hlim2.congr fun W => (hPS_eq W).symm)
  -- regroup: `rForm = Σ_i Atil i · L (i+1) + C0`
  set Atil : ℕ → ℚ := fun i => 2 ^ (i + 1) * ∑ k ∈ range (n + 1), (-1) ^ (k + 1) * b i k with hAtil
  set C0 : ℚ := ∑ k ∈ range (n + 1), ∑ i ∈ range s, b i k * (-1) ^ (m + 1) * F i k with hC0
  have hEq2 : rForm s n = ∑ i ∈ range s, (Atil i : ℝ) * L (i + 1) + (C0 : ℝ) := by
    rw [hEq, hAtil, hC0]
    push_cast
    simp only [mul_add, sum_add_distrib]
    congr 1
    · rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun k _ => ?_
      have hsgn : (-1 : ℝ) ^ (m + 1) * (-1) ^ (k + m) = (-1) ^ (k + 1) := by
        rw [← pow_add, neg_one_pow_eq_pow_mod_two (n := m + 1 + (k + m)),
          neg_one_pow_eq_pow_mod_two (n := k + 1)]
        congr 1; omega
      linear_combination ((b i k : ℝ) * 2 ^ (i + 1) * L (i + 1)) * hsgn
  -- vanishing of the odd-`L` coefficients
  have hAtil0 : ∀ i, Even i → Atil i = 0 := by
    intro i hi
    simp only [hAtil]
    rw [sum_sign_symCoef_eq_zero hn b hbsym hi, mul_zero]
  -- integrality of `d^s Atil i`
  have hAint : ∀ i ∈ range s, ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ s * Atil i = z := by
    intro i hi
    have hi' := mem_range.1 hi
    refine ⟨2 ^ i * (Nat.lcmUpto n : ℤ) ^ (i + 1) * ∑ k ∈ range (n + 1), (-1) ^ (k + 1) * zb i k, ?_⟩
    simp only [hAtil]
    push_cast
    simp only [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hpow : (Nat.lcmUpto n : ℚ) ^ s = (Nat.lcmUpto n : ℚ) ^ (s - 1 - i) * (Nat.lcmUpto n : ℚ) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    linear_combination (2 ^ i * (Nat.lcmUpto n : ℚ) ^ (i + 1) * (-1 : ℚ) ^ (k + 1)) * hzb i hi k hk
  choose! zA hzA using hAint
  -- integrality of `d^s C0`
  have hCint : ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ s * C0 = z := by
    choose! zF hzF using fun i hi k hk => (hF i hi k hk).1
    refine ⟨∑ k ∈ range (n + 1), ∑ i ∈ range s, (-1) ^ (m + 1) * zb i k * zF i k, ?_⟩
    simp only [hC0]
    push_cast
    simp only [mul_sum]
    refine sum_congr rfl fun k hk => sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have hpow : (Nat.lcmUpto n : ℚ) ^ s = (Nat.lcmUpto n : ℚ) ^ (s - 1 - i) * (Nat.lcmUpto n : ℚ) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    linear_combination ((-1 : ℚ) ^ (m + 1) * (Nat.lcmUpto n : ℚ) ^ (i + 1) * F i k / 2) * hzb i hi k hk
      + ((-1 : ℚ) ^ (m + 1) * zb i k / 2) * hzF i hi k hk
  obtain ⟨zC, hzC⟩ := hCint
  -- assemble
  obtain ⟨h, rfl⟩ := hodd
  have hh : (2 * h + 1 - 1) / 2 = h := by omega
  refine ⟨fun j => if j = 0 then zC else zA (2 * j - 1), ?_⟩
  simp only [if_true, hh]
  rw [hEq2, mul_add, mul_sum]
  have hcast : (((Nat.lcmUpto n : ℚ) ^ (2 * h + 1) * C0 : ℚ) : ℝ) = (zC : ℝ) := by rw [hzC, Rat.cast_intCast]
  push_cast at hcast
  rw [show (dn n : ℝ) = (Nat.lcmUpto n : ℝ) from rfl, hcast, add_comm]
  congr 1
  rw [sum_range_odd_eq (fun i => (Nat.lcmUpto n : ℝ) ^ (2 * h + 1) * ((Atil i : ℝ) * L (i + 1)))
    (fun i hi => by rw [hAtil0 i hi]; simp) h]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_Icc.1 hj
  have hne : j ≠ 0 := by omega
  simp only [hne, if_false]
  have hmem : 2 * j - 1 ∈ range (2 * h + 1) := mem_range.2 (by omega)
  have hcastA : (((Nat.lcmUpto n : ℚ) ^ (2 * h + 1) * Atil (2 * j - 1) : ℚ) : ℝ) = (zA (2 * j - 1) : ℝ) := by
    rw [hzA _ hmem, Rat.cast_intCast]
  push_cast at hcastA
  rw [← mul_assoc, hcastA, show 2 * j - 1 + 1 = 2 * j by omega]
  congr 1
  exact tendsto_nhds_unique (hL (2 * j) (by omega)) (tendsto_Eps_beta (by omega))

end LeanFormalizations.DirichletBeta
