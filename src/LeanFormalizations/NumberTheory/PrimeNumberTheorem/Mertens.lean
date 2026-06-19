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

/-- `∑_{p ≤ N} (log p)/p ≥ 0`. -/
lemma primeSumDiv_nonneg (N : ℕ) : 0 ≤ primeSumDiv N := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)) (by positivity)

/-- **The prime sum has order `log N`.** `∑_{p ≤ N} (log p)/p = O(log N)` — the right order of
magnitude (upper bound), from `primeSumDiv_le` and nonnegativity.  (The sharp `log N + O(1)` needs the
tail to be `O(1)`; see the follow-up note.) -/
theorem primeSumDiv_isBigO_log :
    primeSumDiv =O[atTop] (fun N : ℕ ↦ Real.log N) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop (Real.log 4 + 5)] with N hN hbig
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primeSumDiv_nonneg N), abs_of_nonneg hlogN0]
  linarith [primeSumDiv_le hN, hbig]

/-!
## The prime form `∑_{p ≤ x} (log p)/p = log x + O(1)`

The recognizable form of Mertens' first theorem sums only over primes.  It differs from
`vonMangoldtSumDiv` by the *proper prime-power tail* `∑_{p^k ≤ N, k ≥ 2} (log p)/p^k`, which we now
bound by the convergent constant `2·∑_b (log b)/b²` (secured by `summable_log_div_sq`).  The regrouping
injects each proper prime power `d ↦ (minFac d, exponent)` into `Icc 2 N ×ˢ Icc 2 N`, sums the
geometric series in the exponent, and compares the base sum to the `tsum`.  No pointwise majorant over
all `n` works — the tail converges only by the sparsity of prime powers, while `∑ Λ(n)/n` diverges.
-/

/-- Geometric tail from exponent `2`: `∑_{k=2}^N r^k ≤ 2·r²` for `0 ≤ r ≤ ½`.  (The `r²` factor — not
available from the full geometric series — is what makes the prime-power tail converge.) -/
private lemma sum_geom_Icc_two_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, r ^ k ≤ 2 * r ^ 2 := by
  have hr1 : r < 1 := by linarith
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hsum : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
  have hinj : Set.InjOn (fun k => k - 2) (↑(Finset.Icc 2 N) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    simp only at hab
    omega
  have hinner : ∑ k ∈ Finset.Icc 2 N, r ^ (k - 2) ≤ (1 - r)⁻¹ := by
    have he : ∑ k ∈ Finset.Icc 2 N, r ^ (k - 2)
        = ∑ j ∈ (Finset.Icc 2 N).image (fun k => k - 2), r ^ j :=
      (Finset.sum_image hinj).symm
    rw [he, ← tsum_geometric_of_lt_one hr0 hr1]
    exact hsum.sum_le_tsum _ (fun j _ => by positivity)
  have hfac : ∑ k ∈ Finset.Icc 2 N, r ^ k = r ^ 2 * ∑ k ∈ Finset.Icc 2 N, r ^ (k - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    rw [← pow_add]; congr 1; omega
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    have h1 : (1 : ℝ) ≤ 2 * (1 - r) := by linarith
    calc (1 - r)⁻¹ = 1 * (1 - r)⁻¹ := (one_mul _).symm
      _ ≤ (2 * (1 - r)) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hr1'), mul_one]
  rw [hfac]
  calc r ^ 2 * ∑ k ∈ Finset.Icc 2 N, r ^ (k - 2)
      ≤ r ^ 2 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg r)
    _ = 2 * r ^ 2 := by ring

/-- Per-base bound: `∑_{k=2}^N (log p)/p^k ≤ 2(log p)/p²` for `2 ≤ p`. -/
private lemma sum_logp_div_pow_le {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, Real.log p / (p : ℝ) ^ k ≤ 2 * Real.log p / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hrhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    have hc : (p : ℝ)⁻¹ * (p : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hppos)
    nlinarith [hc, mul_nonneg hr0 (show (0 : ℝ) ≤ (p : ℝ) - 2 by linarith)]
  have hgeom := sum_geom_Icc_two_le hr0 hrhalf N
  have hrw : ∑ k ∈ Finset.Icc 2 N, Real.log p / (p : ℝ) ^ k
      = Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  calc Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k
      ≤ Real.log p * (2 * ((p : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hgeom hlogp
    _ = 2 * Real.log p / (p : ℝ) ^ 2 := by rw [inv_pow]; ring

/-- **The proper-prime-power tail is bounded by a constant.**
`∑_{d ≤ N, ¬prime} Λ(d)/d ≤ 2·∑'_b (log b)/b²`.  This is the heart of the prime form: it isolates the
`O(1)` gap between `vonMangoldtSumDiv` and `primeSumDiv`. -/
theorem vonMangoldtSumDiv_sub_primeSumDiv_le (N : ℕ) :
    vonMangoldtSumDiv N - primeSumDiv N ≤ 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 := by
  classical
  rw [vonMangoldtSumDiv_sub_primeSumDiv N]
  set T := (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d) with hT
  set G : ℕ × ℕ → ℝ := fun q => Real.log q.1 / (q.1 : ℝ) ^ q.2 with hG
  set φ : ℕ → ℕ × ℕ := fun d => (d.minFac, d.factorization d.minFac) with hφ
  -- Step A: restrict the tail to prime powers (the `¬IsPrimePow` terms have `Λ = 0`).
  have hAfilter : ∑ d ∈ T.filter IsPrimePow, Λ d / (d : ℝ) = ∑ d ∈ T, Λ d / (d : ℝ) := by
    apply Finset.sum_filter_of_ne
    intro d _ hne
    by_contra hnp
    refine hne ?_
    show Λ d / (d : ℝ) = 0
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, zero_div]
  rw [← hAfilter]
  set PP := T.filter IsPrimePow with hPP
  -- membership facts
  have hmem : ∀ d ∈ PP, IsPrimePow d ∧ ¬ Nat.Prime d ∧ d ≤ N ∧ 0 < d := by
    intro d hd
    simp only [hPP, hT, Finset.mem_filter, Finset.mem_Ioc] at hd
    exact ⟨hd.2, hd.1.2, hd.1.1.2, hd.1.1.1⟩
  -- reconstruction: `minFac d ^ exponent = d`, base prime, exponent ≥ 2
  have hfacts : ∀ d ∈ PP, Nat.Prime d.minFac ∧ 2 ≤ d.factorization d.minFac ∧
      d.minFac ^ (d.factorization d.minFac) = d := by
    intro d hd
    obtain ⟨hpp, hnp, _, _⟩ := hmem d hd
    have hd1 : d ≠ 1 := by have := hpp.one_lt; omega
    have hpprime : Nat.Prime d.minFac := Nat.minFac_prime hd1
    have hrec : d.minFac ^ (d.factorization d.minFac) = d := hpp.minFac_pow_factorization_eq
    refine ⟨hpprime, ?_, hrec⟩
    by_contra hlt
    push_neg at hlt
    have hd2 : 2 ≤ d := hpp.two_le
    have hk01 : d.factorization d.minFac = 0 ∨ d.factorization d.minFac = 1 := by omega
    rcases hk01 with h0 | h1
    · rw [h0, pow_zero] at hrec; omega
    · rw [h1, pow_one] at hrec; exact hnp (hrec ▸ hpprime)
  -- each tail term equals `G (φ d)`
  have hCval : ∀ d ∈ PP, Λ d / (d : ℝ) = G (φ d) := by
    intro d hd
    obtain ⟨_, _, hrec⟩ := hfacts d hd
    obtain ⟨hpp, _, _, _⟩ := hmem d hd
    have hΛ : Λ d = Real.log (d.minFac) := by
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
    have hcast : ((d.minFac : ℝ)) ^ (d.factorization d.minFac) = (d : ℝ) := by
      rw [← Nat.cast_pow, hrec]
    simp only [hG, hφ]
    rw [hΛ, hcast]
  -- the injection lands in `Icc 2 N ×ˢ Icc 2 N`
  have hImg : PP.image φ ⊆ Finset.Icc 2 N ×ˢ Finset.Icc 2 N := by
    rw [Finset.image_subset_iff]
    intro d hd
    obtain ⟨hpprime, hk2, hrec⟩ := hfacts d hd
    obtain ⟨_, _, hdN, hd0⟩ := hmem d hd
    have hpN : d.minFac ≤ N := le_trans (Nat.minFac_le hd0) hdN
    have hkN : d.factorization d.minFac ≤ N := by
      have h2k : 2 ^ (d.factorization d.minFac) ≤ d :=
        le_trans (Nat.pow_le_pow_left hpprime.two_le _) (le_of_eq hrec)
      have hlt : d.factorization d.minFac < 2 ^ (d.factorization d.minFac) := Nat.lt_two_pow_self
      omega
    simp only [hφ, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hpprime.two_le, hpN⟩, hk2, hkN⟩
  -- `φ` is injective on `PP` (via the reconstruction)
  have hinj : Set.InjOn φ (↑PP : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨_, _, hreca⟩ := hfacts a ha
    obtain ⟨_, _, hrecb⟩ := hfacts b hb
    simp only [hφ, Prod.mk.injEq] at hab
    calc a = a.minFac ^ (a.factorization a.minFac) := hreca.symm
      _ = b.minFac ^ (b.factorization b.minFac) := by rw [hab.2, hab.1]
      _ = b := hrecb
  -- assemble: tail = ∑ G(φ d) = ∑_image G ≤ ∑_box G = ∑∑ ≤ ∑ 2logp/p² ≤ 2·tsum
  have hsummable := summable_log_div_sq
  calc ∑ d ∈ PP, Λ d / (d : ℝ)
      = ∑ d ∈ PP, G (φ d) := Finset.sum_congr rfl hCval
    _ = ∑ q ∈ PP.image φ, G q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ Finset.Icc 2 N ×ˢ Finset.Icc 2 N, G q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hImg
        intro q hq _
        simp only [Finset.mem_product, Finset.mem_Icc] at hq
        simp only [hG]
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast le_trans (by norm_num) hq.1.1))
          (by positivity)
    _ = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, G (p, k) := by rw [Finset.sum_product]
    _ ≤ ∑ p ∈ Finset.Icc 2 N, 2 * Real.log p / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_Icc] at hp
        simp only [hG]
        exact sum_logp_div_pow_le hp.1 N
    _ = 2 * ∑ p ∈ Finset.Icc 2 N, Real.log p / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine hsummable.sum_le_tsum _ (fun b _ => ?_)
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp
        · exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hb)) (by positivity)

/-- The proper-prime-power tail is nonnegative. -/
theorem vonMangoldtSumDiv_sub_primeSumDiv_nonneg (N : ℕ) :
    0 ≤ vonMangoldtSumDiv N - primeSumDiv N := by
  rw [vonMangoldtSumDiv_sub_primeSumDiv N]
  exact Finset.sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- **Mertens' first theorem, prime form (explicit bound).** For every `N ≥ 1`,
`|∑_{p ≤ N} (log p)/p − log N| ≤ (log 4 + 5) + 2·∑'_b (log b)/b²`. -/
theorem abs_primeSumDiv_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |primeSumDiv N - Real.log N| ≤ (Real.log 4 + 5) + 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 := by
  have hvm := abs_vonMangoldtSumDiv_sub_log_le hN
  rw [abs_le] at hvm ⊢
  have hlo := vonMangoldtSumDiv_sub_primeSumDiv_nonneg N
  have hhi := vonMangoldtSumDiv_sub_primeSumDiv_le N
  constructor <;> linarith [hvm.1, hvm.2]

/-- **Mertens' first theorem, prime form.** `∑_{p ≤ N} (log p)/p = log N + O(1)` as `N → ∞`. -/
theorem mertens_first_prime :
    (fun N : ℕ ↦ primeSumDiv N - Real.log N) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  -- the tail `vonMangoldtSumDiv − primeSumDiv` is bounded, hence `O(1)`
  have htail : (fun N : ℕ ↦ vonMangoldtSumDiv N - primeSumDiv N) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2, ?_⟩
    filter_upwards with N
    rw [Real.norm_eq_abs, norm_one, mul_one,
      abs_of_nonneg (vonMangoldtSumDiv_sub_primeSumDiv_nonneg N)]
    exact vonMangoldtSumDiv_sub_primeSumDiv_le N
  have heq : (fun N : ℕ ↦ primeSumDiv N - Real.log N)
      = (fun N ↦ (vonMangoldtSumDiv N - Real.log N) - (vonMangoldtSumDiv N - primeSumDiv N)) := by
    funext N; ring
  rw [heq]
  exact mertens_first.sub htail

/-- `(1 : ℝ)` is `o(log N)` as `N → ∞` (since `log N → ∞`).  Bridge for the `~ log` capstones. -/
private lemma one_isLittleO_log :
    (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ Real.log N) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine (Asymptotics.isLittleO_one_left_iff ℝ).mpr ?_
  simp only [Real.norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp hlog

/-- **The prime sum is asymptotic to `log`.** `∑_{p ≤ N} (log p)/p ~ log N` — the multiplicative form
of Mertens' first theorem, immediate from the `O(1)` bound. -/
theorem primeSumDiv_isEquivalent_log :
    primeSumDiv ~[atTop] (fun N : ℕ ↦ Real.log N) :=
  mertens_first_prime.trans_isLittleO one_isLittleO_log

/-- **The von Mangoldt sum is asymptotic to `log`.** `∑_{n ≤ N} Λ(n)/n ~ log N`. -/
theorem vonMangoldtSumDiv_isEquivalent_log :
    vonMangoldtSumDiv ~[atTop] (fun N : ℕ ↦ Real.log N) :=
  mertens_first.trans_isLittleO one_isLittleO_log

/-!
## Toward Mertens' second theorem `∑_{p ≤ x} 1/p = log log x + O(1)`

The recipe (next lap): apply mathlib's continuous Abel summation `sum_mul_eq_sub_integral_mul` with
coefficients `c(n) = [n prime]·(log n)/n` (so `c(n)·(1/log n) = [n prime]/n`, summing to `∑_{p≤x} 1/p`)
and weight `f(t) = 1/log t`.  The partial sums `∑_{n≤t} c(n) = primeSumDiv ⌊t⌋ = log t + O(1)` (proved
above), so the integral term splits into the `log log x` main term `∫ 1/(t log t)` plus a convergent
`O(1)` remainder.  The `log log` primitive is the irreducible analytic input — proved here.
-/

/-- `d/dt log(log t) = 1/(t·log t)` for `t > 1`.  The antiderivative behind the `log log x` main term
of Mertens' second theorem. -/
lemma hasDerivAt_log_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s ↦ Real.log (Real.log s)) (Real.log t * t)⁻¹ t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h : HasDerivAt (fun s ↦ Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
    (Real.hasDerivAt_log hlog).comp t (Real.hasDerivAt_log ht0)
  rwa [← mul_inv] at h

open MeasureTheory in
/-- **`∫_a^b 1/(t·log t) dt = log(log b) − log(log a)`** for `1 < a ≤ b`.  The primitive underlying the
`log log x` main term of Mertens' second theorem `∑_{p ≤ x} 1/p = log log x + O(1)`. -/
lemma integral_inv_log_mul {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t * t)⁻¹ = Real.log (Real.log b) - Real.log (Real.log a) := by
  have hsub : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s ↦ Real.log (Real.log s)) (Real.log t * t)⁻¹ t := by
    intro t ht
    rw [hsub, Set.mem_Icc] at ht
    exact hasDerivAt_log_log (by linarith [ht.1])
  have hcont : ContinuousOn (fun t ↦ (Real.log t * t)⁻¹) (Set.uIcc a b) := by
    rw [hsub]
    apply ContinuousOn.inv₀
    · exact (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).mul continuousOn_id
    · exact fun t ht => ne_of_gt (mul_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])) (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- `d/dt (1/log t) = −1/(t·(log t)²)` for `t > 1`.  The weight derivative for the Abel-summation
derivation of Mertens' second theorem (weight `f(t) = 1/log t`). -/
lemma hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s ↦ (Real.log s)⁻¹) (-(t * (Real.log t) ^ 2)⁻¹) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h := (Real.hasDerivAt_log ht0).inv hlog
  convert h using 1
  rw [div_eq_mul_inv, mul_inv]
  ring

open MeasureTheory in
/-- `∫_a^b 1/(t·(log t)²) dt = 1/log a − 1/log b` for `1 < a ≤ b`.  Bounds the **convergent remainder**
`∫ r(t)/(t log²t)` (with `|r| ≤ C`) of Mertens' second theorem by `C/log a`, uniformly in `b` — the key
fact that the remainder is `O(1)`. -/
lemma integral_inv_mul_sq_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t * (Real.log t) ^ 2)⁻¹ = (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hsub : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s ↦ -(Real.log s)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
    intro t ht
    rw [hsub, Set.mem_Icc] at ht
    simpa using (hasDerivAt_inv_log (by linarith [ht.1])).neg
  have hcont : ContinuousOn (fun t ↦ (t * (Real.log t) ^ 2)⁻¹) (Set.uIcc a b) := by
    rw [hsub]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).pow 2)
    · exact fun t ht => ne_of_gt (mul_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])
        (pow_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])) 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

/-- Abel-summation coefficient for Mertens' second theorem: `c(n) = [n prime]·(log n)/n`. -/
noncomputable def primeLogDivCoeff (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

@[simp] lemma primeLogDivCoeff_zero : primeLogDivCoeff 0 = 0 := by simp [primeLogDivCoeff]

@[simp] lemma primeLogDivCoeff_one : primeLogDivCoeff 1 = 0 := by simp [primeLogDivCoeff]

/-- The **prime reciprocal sum** `∑_{p ≤ N} 1/p` — the subject of Mertens' second theorem. -/
noncomputable def primeRecipSum (N : ℕ) : ℝ := ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (p : ℝ)⁻¹

/-- Bridge: the coefficient partial sum is exactly `primeSumDiv`. `∑_{k≤N} c(k) = ∑_{p≤N}(log p)/p`. -/
lemma sum_primeLogDivCoeff_eq (N : ℕ) :
    ∑ k ∈ Finset.Icc 0 N, primeLogDivCoeff k = primeSumDiv N := by
  have hset : (Finset.Icc 0 N).filter Nat.Prime = (Finset.Ioc 0 N).filter Nat.Prime := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    exact ⟨fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.pos, h⟩, hp⟩, fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨Nat.zero_le _, h⟩, hp⟩⟩
  simp only [primeLogDivCoeff]
  rw [← Finset.sum_filter, hset, primeSumDiv]

/-- Bridge: weighting the coefficient by `1/log k` yields the prime reciprocal sum.
`∑_{k≤N} (1/log k)·c(k) = ∑_{p≤N} 1/p`. -/
lemma sum_inv_log_mul_primeLogDivCoeff_eq (N : ℕ) :
    ∑ k ∈ Finset.Icc 0 N, (Real.log k)⁻¹ * primeLogDivCoeff k = primeRecipSum N := by
  have hset : (Finset.Icc 0 N).filter Nat.Prime = (Finset.Ioc 0 N).filter Nat.Prime := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    exact ⟨fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.pos, h⟩, hp⟩, fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨Nat.zero_le _, h⟩, hp⟩⟩
  simp only [primeLogDivCoeff, mul_ite, mul_zero]
  rw [← Finset.sum_filter, hset, primeRecipSum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  have hlog : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.2.one_lt))
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul]

open MeasureTheory in
/-- **Abel-summation identity for the prime reciprocal sum** (toward Mertens' second theorem). For
every `N`,
`∑_{p≤N} 1/p = (∑_{p≤N}(log p)/p)/log N + ∫_2^N (∑_{p≤⌊t⌋}(log p)/p)/(t·(log t)²) dt`.
With `∑_{p≤x}(log p)/p = log x + O(1)` (`mertens_first_prime`) this reduces Mertens' 2nd to the
integral estimate `∫_2^N (log t + O(1))/(t log²t) = log log N + O(1)`. -/
theorem mertens_second_identity (N : ℕ) :
    primeRecipSum N
      = primeSumDiv N / Real.log N
        + ∫ t in Set.Ioc (2 : ℝ) (N : ℝ), primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
  have hderiv_eq : ∀ t : ℝ, 1 < t →
      deriv (fun s => (Real.log s)⁻¹) t = -(t * (Real.log t) ^ 2)⁻¹ :=
    fun t ht => (hasDerivAt_inv_log ht).deriv
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), DifferentiableAt ℝ (fun s => (Real.log s)⁻¹) t := by
    intro t ht; rw [Set.mem_Icc] at ht
    exact (hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv (fun s => (Real.log s)⁻¹)) (Set.Icc (2 : ℝ) (N : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => -(t * (Real.log t) ^ 2)⁻¹) (Set.Icc (2 : ℝ) N) := by
      apply ContinuousOn.neg; apply ContinuousOn.inv₀
      · exact continuousOn_id.mul ((Real.continuousOn_log.mono
          (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).pow 2)
      · exact fun t ht => ne_of_gt (mul_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])
          (pow_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])) 2))
    refine (hcont.integrableOn_compact isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht; rw [Set.mem_Icc] at ht
    exact (hderiv_eq t (by linarith [ht.1])).symm
  have habel := sum_mul_eq_sub_integral_mul₁ primeLogDivCoeff (f := fun s => (Real.log s)⁻¹)
    primeLogDivCoeff_zero primeLogDivCoeff_one (N : ℝ) hdiff hint
  rw [Nat.floor_natCast] at habel
  simp only [sum_inv_log_mul_primeLogDivCoeff_eq, sum_primeLogDivCoeff_eq] at habel
  have heq_int : ∫ t in Set.Ioc (2 : ℝ) (N : ℝ),
        deriv (fun s => (Real.log s)⁻¹) t * primeSumDiv ⌊t⌋₊
      = - ∫ t in Set.Ioc (2 : ℝ) (N : ℝ), primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht; rw [Set.mem_Ioc] at ht
    simp only []
    rw [hderiv_eq t (by linarith [ht.1]), div_eq_mul_inv]; ring
  rw [heq_int] at habel
  rw [habel]; ring

/-- The first term of the Abel identity tends to `1`:  `(∑_{p≤N}(log p)/p)/log N → 1`.  (Immediate from
`primeSumDiv ~ log`.)  So in `mertens_second_identity` the boundary term contributes `1 + o(1)`, and
Mertens' second theorem reduces to the integral term `∫_2^N primeSumDiv ⌊t⌋ /(t log²t) = log log N + O(1)`. -/
theorem primeSumDiv_div_log_tendsto_one :
    Tendsto (fun N : ℕ ↦ primeSumDiv N / Real.log N) atTop (nhds 1) := by
  have hv : ∀ᶠ N : ℕ in atTop, Real.log N ≠ 0 := by
    have h : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [h.eventually_gt_atTop 0] with N hN using ne_of_gt hN
  exact (isEquivalent_iff_tendsto_one hv).mp primeSumDiv_isEquivalent_log

/-- Floor-vs-continuous `log` gap: `log t − log ⌊t⌋₊ ≤ log(3/2)` for `t ≥ 2` (since `2 ≤ ⌊t⌋₊ ≤ t <
⌊t⌋₊+1`).  The genuinely-new estimate controlling the Mertens-2nd remainder integrand. -/
lemma log_sub_log_floor_le {t : ℝ} (ht : 2 ≤ t) :
    Real.log t - Real.log ⌊t⌋₊ ≤ Real.log (3 / 2) := by
  have htpos : (0 : ℝ) < t := by linarith
  have hfloor_ge : (2 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hfloorR : (2 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor_ge
  have hfloorpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  rw [← Real.log_div (ne_of_gt htpos) (ne_of_gt hfloorpos)]
  apply Real.log_le_log (div_pos htpos hfloorpos)
  rw [div_le_iff₀ hfloorpos]
  nlinarith [hlt, hfloorR]

/-- **Uniform bound on the Mertens-2nd remainder numerator.** For `t ≥ 2`,
`|primeSumDiv ⌊t⌋₊ − log t| ≤ (log4+5) + 2∑'_b(log b)/b² + log(3/2)` — a constant, independent of `t`.
With `integral_inv_mul_sq_log` this makes the remainder integral `O(1)`. -/
lemma abs_primeSumDiv_floor_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |primeSumDiv ⌊t⌋₊ - Real.log t|
      ≤ ((Real.log 4 + 5) + 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2) + Real.log (3 / 2) := by
  have hfloor2 : (2 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hfloor1 : (1 : ℕ) ≤ ⌊t⌋₊ := by omega
  have hfloorRpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by
    have : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor1
    linarith
  have h1 := abs_primeSumDiv_sub_log_le hfloor1
  have h2 := log_sub_log_floor_le ht
  have h3 : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t := Real.log_le_log hfloorRpos (Nat.floor_le (by linarith))
  calc |primeSumDiv ⌊t⌋₊ - Real.log t|
      ≤ |primeSumDiv ⌊t⌋₊ - Real.log ⌊t⌋₊| + |Real.log ⌊t⌋₊ - Real.log t| := abs_sub_le _ _ _
    _ ≤ ((Real.log 4 + 5) + 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2) + Real.log (3 / 2) := by
        have hb2 : |Real.log (⌊t⌋₊ : ℝ) - Real.log t| ≤ Real.log (3 / 2) := by
          rw [abs_of_nonpos (by linarith [h3])]; linarith [h2]
        linarith [h1, hb2]

open MeasureTheory in
/-- The Mertens-2nd integrand `primeSumDiv ⌊t⌋₊ /(t (log t)²)` is integrable on `[2,N]`.  (The
step-function `∑_{k≤⌊t⌋} c k` times the continuous weight, via mathlib's `integrableOn_mul_sum_Icc`.) -/
lemma integrableOn_primeSumDiv_floor_div (N : ℕ) :
    IntegrableOn (fun t ↦ primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2)) (Set.Icc (2 : ℝ) N) := by
  have hcont : ContinuousOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Set.Icc (2 : ℝ) N) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).pow 2)
    · exact fun t ht => ne_of_gt (mul_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])
        (pow_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])) 2))
  have hg : IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Set.Icc (2 : ℝ) N) :=
    hcont.integrableOn_compact isCompact_Icc
  have h := integrableOn_mul_sum_Icc (m := 0) primeLogDivCoeff (a := (2 : ℝ)) (b := (N : ℝ))
    (by norm_num) hg
  refine h.congr_fun ?_ measurableSet_Icc
  intro t _
  simp only []
  rw [sum_primeLogDivCoeff_eq]; ring

open MeasureTheory intervalIntegral in
/-- **Mertens' second theorem.** `∑_{p ≤ N} 1/p = log log N + O(1)` as `N → ∞` — **absent from mathlib**.
Assembled from `mertens_second_identity` (Abel summation) + the `log log N` main integral
(`integral_inv_log_mul`) + the `O(1)` remainder (`abs_primeSumDiv_floor_sub_log_le` with
`integral_inv_mul_sq_log`). -/
theorem mertens_second :
    (fun N : ℕ ↦ primeRecipSum N - Real.log (Real.log N)) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  have hC₀nn : (0 : ℝ) ≤ (Real.log 4 + 5) + 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ Real.log 4 + 5 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
    have h2 : (0 : ℝ) ≤ ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 := by
      apply tsum_nonneg; intro b
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      · exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hb)) (by positivity)
    linarith
  set C₀ : ℝ := (Real.log 4 + 5) + 2 * ∑' b : ℕ, Real.log b / (b : ℝ) ^ 2 with hC₀def
  have hlog32 : (0 : ℝ) ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  set Cr : ℝ := C₀ + Real.log (3 / 2) with hCrdef
  have hCrnn : (0 : ℝ) ≤ Cr := by rw [hCrdef]; linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨(1 + C₀ / Real.log 2) + Cr / Real.log 2 + |Real.log (Real.log 2)|, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [Real.norm_eq_abs, norm_one, mul_one]
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ N := by omega
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlogNpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le hlog2pos hlogN2
  -- integrabilities (the step-function integrand, the continuous weight, and the bound integrand)
  have hI1 : IntervalIntegrable (fun t ↦ primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2)) volume 2 N :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hNR).mpr (integrableOn_primeSumDiv_floor_div N)
  have hcont2 : ContinuousOn (fun t : ℝ ↦ (Real.log t * t)⁻¹) (Set.uIcc 2 N) := by
    rw [Set.uIcc_of_le hNR]
    apply ContinuousOn.inv₀
    · exact (Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).mul continuousOn_id
    · exact fun t ht => ne_of_gt (mul_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))
        (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))
  have hI2 : IntervalIntegrable (fun t ↦ (Real.log t * t)⁻¹) volume 2 N := hcont2.intervalIntegrable
  have hcontInv : ContinuousOn (fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹) (Set.uIcc 2 N) := by
    rw [Set.uIcc_of_le hNR]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (by simp only [Set.mem_Icc] at ht; linarith [ht.1]))).pow 2)
    · exact fun t ht => ne_of_gt (mul_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])
        (pow_pos (Real.log_pos (by simp only [Set.mem_Icc] at ht; linarith [ht.1])) 2))
  have hIg : IntervalIntegrable (fun t ↦ Cr * (t * (Real.log t) ^ 2)⁻¹) volume 2 N :=
    (hcontInv.const_smul Cr).intervalIntegrable
  -- the main integral (log log) and the identity in interval form
  have hJ : ∫ t in (2 : ℝ)..N, (Real.log t * t)⁻¹ = Real.log (Real.log N) - Real.log (Real.log 2) :=
    integral_inv_log_mul (by norm_num) hNR
  have hidI : primeRecipSum N
      = primeSumDiv N / Real.log N + ∫ t in (2 : ℝ)..N, primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
    rw [mertens_second_identity N, ← integral_of_le hNR]
  -- pointwise bound for the remainder integrand on `Ι 2 N`
  have h_ae : ∀ᵐ t ∂(volume.restrict (Set.uIoc (2 : ℝ) N)),
      ‖primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) - (Real.log t * t)⁻¹‖ ≤ Cr * (t * (Real.log t) ^ 2)⁻¹ := by
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ (fun t ht => ?_))
    rw [Set.uIoc_of_le hNR, Set.mem_Ioc] at ht
    have htt : (1 : ℝ) < t := by linarith [ht.1]
    have htpos : (0 : ℝ) < t := by linarith
    have hlogtpos : (0 : ℝ) < Real.log t := Real.log_pos htt
    have hden : (0 : ℝ) < t * (Real.log t) ^ 2 := mul_pos htpos (pow_pos hlogtpos 2)
    have heq : primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) - (Real.log t * t)⁻¹
        = (primeSumDiv ⌊t⌋₊ - Real.log t) / (t * (Real.log t) ^ 2) := by
      field_simp
    have hb := abs_primeSumDiv_floor_sub_log_le (le_of_lt ht.1)
    rw [← hC₀def, ← hCrdef] at hb
    rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hden, ← div_eq_mul_inv]
    gcongr
  -- assemble: primeRecipSum N − log log N = primeSumDiv N/log N + R − log log 2
  have hkey : primeRecipSum N - Real.log (Real.log N)
      = primeSumDiv N / Real.log N
        + (∫ t in (2 : ℝ)..N, (primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) - (Real.log t * t)⁻¹))
        - Real.log (Real.log 2) := by
    have hf1 : (∫ t in (2 : ℝ)..N, primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2))
        = (∫ t in (2 : ℝ)..N, (primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) - (Real.log t * t)⁻¹))
          + ∫ t in (2 : ℝ)..N, (Real.log t * t)⁻¹ := by
      rw [integral_sub hI1 hI2]; ring
    rw [hidI, hf1, hJ]; ring
  -- bound the remainder `R`
  have hRbound : |∫ t in (2 : ℝ)..N,
      (primeSumDiv ⌊t⌋₊ / (t * (Real.log t) ^ 2) - (Real.log t * t)⁻¹)| ≤ Cr / Real.log 2 := by
    have hnorm := norm_integral_le_abs_of_norm_le h_ae hIg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_mul_sq_log (by norm_num) hNR] at hnorm
    have hinvle : (Real.log N)⁻¹ ≤ (Real.log 2)⁻¹ := by
      have h := _root_.one_div_le_one_div_of_le hlog2pos hlogN2
      rwa [one_div, one_div] at h
    have hpos : 0 ≤ Cr * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) := mul_nonneg hCrnn (by linarith)
    rw [abs_of_nonneg hpos] at hnorm
    have htail : Cr * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) ≤ Cr / Real.log 2 := by
      have h0 : 0 ≤ Cr * (Real.log N)⁻¹ := mul_nonneg hCrnn (by positivity)
      rw [mul_sub, div_eq_mul_inv]; linarith
    linarith
  -- the boundary term is bounded
  have hps := abs_primeSumDiv_sub_log_le hN1
  rw [← hC₀def] at hps
  have hquot : primeSumDiv N / Real.log N ≤ 1 + C₀ / Real.log 2 := by
    rw [div_le_iff₀ hlogNpos]
    have hle : primeSumDiv N ≤ Real.log N + C₀ := by rw [abs_le] at hps; linarith [hps.2]
    have haux : C₀ ≤ C₀ / Real.log 2 * Real.log N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]; nlinarith [hC₀nn, hlogN2]
    nlinarith [hle, haux]
  have hquot0 : 0 ≤ primeSumDiv N / Real.log N := div_nonneg (primeSumDiv_nonneg N) hlogNpos.le
  have habsquot : |primeSumDiv N / Real.log N| ≤ 1 + C₀ / Real.log 2 := by
    rw [abs_of_nonneg hquot0]; exact hquot
  -- conclude
  rw [hkey]
  have e1 := abs_le.mp habsquot
  have e2 := abs_le.mp hRbound
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [e1.1, e2.1, le_abs_self (Real.log (Real.log 2))]
  · linarith [e1.2, e2.2, neg_le_abs (Real.log (Real.log 2))]

end LeanFormalizations.Mertens
