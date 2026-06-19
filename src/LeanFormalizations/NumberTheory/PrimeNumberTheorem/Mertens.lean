/-
# Mertens' First Theorem  `∑_{n ≤ N} Λ(n)/n = log N + O(1)`

The classical first theorem of Mertens, in von Mangoldt form: the weighted prime-power sum
`∑_{n ≤ N} Λ(n)/n` differs from `log N` by a bounded amount.  This is **absent from mathlib**, and is
an immediate consequence of the repo's keystone Chebyshev identity
`∑_{d ≤ N} Λ(d)·⌊N/d⌋ = log(N!)` (`sum_vonMangoldt_mul_floor_div`) together with Stirling's formula
and Chebyshev's elementary upper bound `ψ(x) ≤ (log 4 + 4)·x`.

**Idea.**  Write `S(N) = ∑_{d ≤ N} Λ(d)/d`.  Then
`N·S(N) − log(N!) = ∑_{d ≤ N} Λ(d)·(N/d − ⌊N/d⌋) ∈ [0, ∑_{d ≤ N} Λ(d)] = [0, ψ(N)]`,
so `log(N!) ≤ N·S(N) ≤ log(N!) + ψ(N)`.  Stirling pins `log(N!) = N·log N − N + O(log N)` and
Chebyshev pins `ψ(N) = O(N)`, hence `S(N) = log N + O(1)`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.PrimeGap

namespace LeanFormalizations.Mertens

open Finset Filter Asymptotics
open scoped ArithmeticFunction
open LeanFormalizations.NoThreeInLine

/-- `S(N) := ∑_{d ≤ N} Λ(d)/d`, the von Mangoldt weighted sum of Mertens' first theorem. -/
noncomputable def vonMangoldtSumDiv (N : ℕ) : ℝ := ∑ d ∈ Finset.Ioc 0 N, Λ d / (d : ℝ)

/-- `N·S(N) = ∑_{d ≤ N} Λ(d)·(N/d)` (real division). -/
lemma natCast_mul_vonMangoldtSumDiv (N : ℕ) :
    (N : ℝ) * vonMangoldtSumDiv N = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N : ℝ) / d) := by
  rw [vonMangoldtSumDiv, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  simp only [div_eq_mul_inv]; ring

/-- `ψ(N) = ∑_{d ≤ N} Λ(d)` for a natural argument. -/
lemma psi_natCast_eq_sum (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ∑ d ∈ Finset.Ioc 0 N, Λ d := by
  rw [show Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Ioc 0 ⌊(N : ℝ)⌋₊, Λ n from rfl, Nat.floor_natCast]

/-- The keystone sandwich: `0 ≤ N·S(N) − log(N!) ≤ ψ(N)`. -/
lemma sandwich (N : ℕ) :
    Real.log (Nat.factorial N) ≤ (N : ℝ) * vonMangoldtSumDiv N ∧
      (N : ℝ) * vonMangoldtSumDiv N ≤ Real.log (Nat.factorial N) + Chebyshev.psi (N : ℝ) := by
  have hdiff : (N : ℝ) * vonMangoldtSumDiv N - Real.log (Nat.factorial N)
      = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    rw [natCast_mul_vonMangoldtSumDiv, ← sum_vonMangoldt_mul_floor_div N,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  -- each summand lies in `[0, Λ d]`
  have hterm_nonneg : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    intro d _
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
      (by linarith [Nat.cast_div_le (m := N) (n := d) (α := ℝ)])
  have hterm_le : ∀ d ∈ Finset.Ioc 0 N, Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) ≤ Λ d := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := hd.1
    have hfac : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
      have hnat : N < d * (N / d + 1) := by
        have h1 := Nat.div_add_mod N d
        have h2 := Nat.mod_lt N hd0
        nlinarith [h1, h2]
      have hcast : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
        have := (Nat.cast_lt (α := ℝ)).mpr hnat
        push_cast at this ⊢
        linarith [this]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hdiv : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hdR]; nlinarith [hcast]
      linarith [hdiv]
    calc Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))
        ≤ Λ d * 1 := by
          apply mul_le_mul_of_nonneg_left hfac ArithmeticFunction.vonMangoldt_nonneg
      _ = Λ d := mul_one _
  constructor
  · have : 0 ≤ (N : ℝ) * vonMangoldtSumDiv N - Real.log (Nat.factorial N) := by
      rw [hdiff]; exact Finset.sum_nonneg hterm_nonneg
    linarith
  · have : (N : ℝ) * vonMangoldtSumDiv N - Real.log (Nat.factorial N)
        ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d := by
      rw [hdiff]; exact Finset.sum_le_sum hterm_le
    rw [psi_natCast_eq_sum]; linarith

/-- **Mertens' first theorem (explicit bound).** For every `N ≥ 1`,
`|∑_{d ≤ N} Λ(d)/d − log N| ≤ log 4 + 5`. -/
theorem abs_vonMangoldtSumDiv_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |vonMangoldtSumDiv N - Real.log N| ≤ Real.log 4 + 5 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : N ≠ 0 := by omega
  set S := vonMangoldtSumDiv N with hSdef
  set L := Real.log (Nat.factorial N) with hLdef
  obtain ⟨hlo, hhi⟩ := sandwich N
  rw [← hSdef, ← hLdef] at hlo hhi
  -- numeric facts about `log`
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogNle : Real.log N ≤ (N : ℝ) - 1 := Real.log_le_sub_one_of_pos hN0
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2pi : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlog2N : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by positivity)
  -- Stirling lower / upper on `log(N!)`
  have hStir := Stirling.le_log_factorial_stirling hNne
  have hFacUp := log_factorial_le (m := N) hNne
  rw [← hLdef] at hStir hFacUp
  -- `N·log N − N ≤ L ≤ N·log N`
  have hLlo : (N : ℝ) * Real.log N - N ≤ L := by nlinarith [hStir, hlogN0, hlog2pi]
  have hLhi : L ≤ (N : ℝ) * Real.log N := by
    rw [hlog2N] at hFacUp; nlinarith [hFacUp, hlogNle, hlog2, hN0]
  -- Chebyshev upper bound on `ψ`
  have hpsi : Chebyshev.psi (N : ℝ) ≤ (Real.log 4 + 4) * N :=
    Chebyshev.psi_le_const_mul_self (le_of_lt hN0)
  -- assemble: `log N − 1 ≤ S ≤ log N + (log 4 + 4)`
  have hStep1 : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * S := by nlinarith [hlo, hLlo]
  have hSlo : Real.log N - 1 ≤ S := le_of_mul_le_mul_left hStep1 hN0
  have hStep2 : (N : ℝ) * S ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith [hhi, hLhi, hpsi]
  have hShi : S ≤ Real.log N + (Real.log 4 + 4) := le_of_mul_le_mul_left hStep2 hN0
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **Mertens' first theorem.** `∑_{n ≤ N} Λ(n)/n = log N + O(1)` as `N → ∞`. -/
theorem mertens_first :
    (fun N : ℕ ↦ vonMangoldtSumDiv N - Real.log N) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 5, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact abs_vonMangoldtSumDiv_sub_log_le hN

end LeanFormalizations.Mertens
