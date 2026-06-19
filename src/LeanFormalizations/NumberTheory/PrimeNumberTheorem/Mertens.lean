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

/-- **The von Mangoldt sum diverges.** `∑_{n ≤ N} Λ(n)/n → ∞` — a quantitative (rate `log N`)
strengthening of the infinitude of primes, immediate from `mertens_first`. -/
theorem vonMangoldtSumDiv_tendsto_atTop :
    Tendsto vonMangoldtSumDiv atTop atTop := by
  have key : ∀ᶠ N : ℕ in atTop, Real.log N - (Real.log 4 + 5) ≤ vonMangoldtSumDiv N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := abs_vonMangoldtSumDiv_sub_log_le hN
    rw [abs_le] at h; linarith [h.1]
  have hg : Tendsto (fun N : ℕ ↦ Real.log N - (Real.log 4 + 5)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-(Real.log 4 + 5))
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono' atTop key hg

/-- `log x ≤ 2·√x` for `x ≥ 0` (from `log √x ≤ √x − 1`). -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hx] at h1
    linarith [hs.le]

/-- **`∑ log n / n²` converges.** Comparison with `2/n^{3/2}` (a convergent `p`-series, `p = 3/2 > 1`)
via `log n ≤ 2√n`.  The linchpin for the prime-power tail bound of the prime form below. -/
lemma summable_log_div_sq :
    Summable (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ 2) := by
  have hg : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    have h := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2
    simpa [mul_one_div] using h
  refine Summable.of_nonneg_of_le ?_ ?_ hg
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog := log_le_two_mul_sqrt (x := (n : ℝ)) hnpos.le
      rw [Real.sqrt_eq_rpow] at hlog
      have h2 : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast (n : ℝ) 2]; norm_num
      have heq : 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 = 2 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [h2, mul_div_assoc, ← Real.rpow_sub hnpos,
          show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num, Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
      calc Real.log n / (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by gcongr
        _ = 2 / (n : ℝ) ^ (3 / 2 : ℝ) := heq

/-- `P(N) := ∑_{p ≤ N, p prime} (log p)/p`, the prime sum of Mertens' first theorem (prime form). -/
noncomputable def primeSumDiv (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p / (p : ℝ)

/-- The von Mangoldt sum minus the prime sum is the **proper-prime-power tail**
`∑_{d ≤ N, ¬prime} Λ(d)/d` (the `¬prime` terms with `Λ ≠ 0` are exactly the `p^k`, `k ≥ 2`). -/
lemma vonMangoldtSumDiv_sub_primeSumDiv (N : ℕ) :
    vonMangoldtSumDiv N - primeSumDiv N
      = ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / (d : ℝ) := by
  have hsplit : vonMangoldtSumDiv N
      = (∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / (d : ℝ))
        + ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / (d : ℝ) := by
    rw [vonMangoldtSumDiv]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : (∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / (d : ℝ)) = primeSumDiv N := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hsplit, hprime]; ring

/-- **Upper half of Mertens' first theorem, prime form.** `∑_{p ≤ N} (log p)/p ≤ log N + (log 4 + 5)`
for `N ≥ 1` — immediate, since the proper-prime-power tail dropped is `≥ 0`.  (The matching lower bound
needs the tail to be `O(1)`; see the follow-up note below.) -/
theorem primeSumDiv_le {N : ℕ} (hN : 1 ≤ N) :
    primeSumDiv N ≤ Real.log N + (Real.log 4 + 5) := by
  have htail : 0 ≤ ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hd := vonMangoldtSumDiv_sub_primeSumDiv N
  have hvm := abs_vonMangoldtSumDiv_sub_log_le hN
  rw [abs_le] at hvm
  linarith [hvm.2, hd, htail]

/-!
## Follow-up: the prime form `∑_{p ≤ x} (log p)/p = log x + O(1)`

The recognizable form of Mertens' first theorem sums only over primes.  It differs from
`vonMangoldtSumDiv` by the *proper prime-power tail*
`∑_{p^k ≤ N, k ≥ 2} (log p)/p^k`, which is bounded by the convergent series
`∑_p (log p)/(p(p−1)) ≤ 2 ∑_p (log p)/p²`.  Establishing that bound requires reindexing the tail as
a double sum over `(p, k ≥ 2)` and summing the geometric series in `k` (no pointwise majorant over
all `n` works — the tail converges only by the sparsity of prime powers, while `∑ Λ(n)/n` itself
diverges).  The convergent majorant `2·∑_b (log b)/b²` is **already secured** by `summable_log_div_sq`
above; what remains is purely the regrouping: an injection `proper-prime-power d ↦ (minFac d, exponent)`
into `Icc 2 N ×ˢ Icc 2 N`, the per-base geometric bound
`∑_{k≥2} (log p)/p^k ≤ 2(log p)/p²`, and `Finset.sum_image`/`sum_le_tsum`.  Then
`∑_{p ≤ N} (log p)/p = vonMangoldtSumDiv N − tail(N) = log N + O(1)`.  Left for a dedicated lap.
-/

end LeanFormalizations.Mertens
