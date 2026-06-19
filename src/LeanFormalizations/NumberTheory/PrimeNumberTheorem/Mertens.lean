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

end LeanFormalizations.Mertens
