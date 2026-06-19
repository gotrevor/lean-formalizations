/-
# Dirichlet's Divisor Problem  `∑_{n ≤ N} d(n) = N·log N + (2γ−1)·N + O(√N)`

The classical leading asymptotic for the summatory divisor function `D(N) = ∑_{n ≤ N} d(n)`,
where `d(n) = σ₀(n)` is the number of divisors of `n`.  Dirichlet (1849) proved, via the
*hyperbola method*, the sharp two-term expansion with error `O(√N)` — strictly better than the
trivial `O(N)` from the divisor-switching identity alone.  **This is absent from mathlib**, which
records only the `O(N)` identity `∑_{n ≤ N} σ₀(n) = ∑_{n ≤ N} ⌊N/n⌋`
(`ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div`) with an explicit
`--TODO: Dirichlet hyperbola method to get sums of length sqrt N`.

**Idea (Dirichlet hyperbola method).**  Count lattice points under the hyperbola `ab ≤ N`.
With `K = ⌊√N⌋`, every pair `(a,b)` with `ab ≤ N` has `a ≤ K` or `b ≤ K` (else `ab ≥ (K+1)² > N`),
and inclusion–exclusion over `{a ≤ K}`, `{b ≤ K}` (using `a,b ≤ K ⟹ ab ≤ K² ≤ N`) gives the
**hyperbola identity** `D(N) = 2·∑_{a ≤ K} ⌊N/a⌋ − K²`.  Then `⌊N/a⌋ = N/a + O(1)` summed over
`a ≤ K` turns `∑_{a ≤ K} ⌊N/a⌋` into `N·H_K + O(√N)`, the harmonic number `H_K = log K + γ + O(1/K)`
pins the constant, and `K² = N + O(√N)` finishes:
`D(N) = 2N(½log N + γ) − N + O(√N) = N log N + (2γ−1)N + O(√N)`.

The harmonic estimate `|H_n − log n − γ| ≤ 1/n` comes from squeezing `γ` between mathlib's two
monotone Euler–Mascheroni sequences (`harmonic n − log(n+1) < γ < harmonic n − log n`).
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace LeanFormalizations.DirichletDivisor

open Finset Filter Asymptotics Real
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ### The harmonic number error term `|H_n − log n − γ| ≤ 1/n` -/

/-- **Sharp harmonic-number estimate.** For `n ≥ 1`,
`0 ≤ harmonic n − log n − γ ≤ 1/n`.  Squeeze `γ` between the increasing sequence
`harmonic n − log(n+1)` and the decreasing sequence `harmonic n − log n` (mathlib's
`eulerMascheroniSeq`/`eulerMascheroniSeq'`), then `log(n+1) − log n = log(1+1/n) ≤ 1/n`. -/
theorem harmonic_sub_log_sub_gamma_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (harmonic n : ℝ) - Real.log n - eulerMascheroniConstant ∧
      (harmonic n : ℝ) - Real.log n - eulerMascheroniConstant ≤ 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- lower: γ < harmonic n − log n
  have h1 : eulerMascheroniConstant < (harmonic n : ℝ) - Real.log n := by
    have := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    rwa [eulerMascheroniSeq', if_neg (by omega)] at this
  -- upper: harmonic n − log(n+1) < γ
  have h2 : (harmonic n : ℝ) - Real.log (n + 1) < eulerMascheroniConstant :=
    eulerMascheroniSeq_lt_eulerMascheroniConstant n
  -- log(n+1) − log n ≤ 1/n
  have hlog : Real.log (n + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hrw : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
    rw [hrw]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
    linarith
  exact ⟨by linarith, by linarith⟩

/-- `|harmonic n − log n − γ| ≤ 1/n` for `n ≥ 1`. -/
theorem abs_harmonic_sub_log_sub_gamma_le {n : ℕ} (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - eulerMascheroniConstant| ≤ 1 / n := by
  obtain ⟨hlo, hhi⟩ := harmonic_sub_log_sub_gamma_bounds hn
  have hnn : (0 : ℝ) ≤ 1 / n := by positivity
  rw [abs_le]; exact ⟨by linarith, hhi⟩

/-! ### The hyperbola identity (combinatorial crux) -/

/-- **Dirichlet hyperbola identity.**  `∑_{a=1}^{N} ⌊N/a⌋ + ⌊√N⌋² = 2·∑_{a=1}^{⌊√N⌋} ⌊N/a⌋`.
The lattice-point count `#{(a,b) : a,b ≥ 1, ab ≤ N} = ∑_{a≤N} ⌊N/a⌋` split by inclusion–exclusion
over `{a ≤ ⌊√N⌋}`, `{b ≤ ⌊√N⌋}`. -/
theorem hyperbola_identity (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, N / a) + (Nat.sqrt N) ^ 2
      = 2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), N / a := by
  set K := Nat.sqrt N with hKdef
  have hKleN : K ≤ N := Nat.sqrt_le_self N
  have hK2leN : K * K ≤ N := by rw [hKdef]; exact Nat.sqrt_le N
  have hlt : N < (K + 1) * (K + 1) := by
    have h := Nat.lt_succ_sqrt N; rw [← hKdef] at h; simpa [Nat.succ_eq_add_one] using h
  -- counting lemma: #{x ∈ [1,N] : m·x ≤ N} = ⌊N/m⌋  (m ≥ 1)
  have hcount : ∀ m, 1 ≤ m → ((Finset.Icc 1 N).filter (fun x => m * x ≤ N)).card = N / m := by
    intro m hm
    have hset : (Finset.Icc 1 N).filter (fun x => m * x ≤ N) = Finset.Icc 1 (N / m) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hx1, _⟩, hmx⟩
        exact ⟨hx1, (Nat.le_div_iff_mul_le (by omega)).mpr (by rwa [mul_comm] at hmx)⟩
      · rintro ⟨hx1, hxd⟩
        have hmx : m * x ≤ N := by
          rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hxd
        exact ⟨⟨hx1, le_trans hxd (Nat.div_le_self N m)⟩, hmx⟩
    rw [hset, Nat.card_Icc]; exact Nat.add_sub_cancel _ _
  -- the restriction `(Icc 1 N).filter (· ≤ K) = Icc 1 K`
  have hsetK : (Finset.Icc 1 N).filter (· ≤ K) = Finset.Icc 1 K := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hKleN⟩, h2⟩
  -- the lattice sets
  set P := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N) with hPdef
  set A := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N ∧ p.1 ≤ K) with hAdef
  set B := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N ∧ p.2 ≤ K) with hBdef
  -- #P = ∑_{a≤N} ⌊N/a⌋
  have hP : P.card = ∑ a ∈ Finset.Icc 1 N, N / a := by
    rw [hPdef, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    rw [← Finset.card_filter]; exact hcount a ha.1
  -- #A = ∑_{a≤K} ⌊N/a⌋
  have hA : A.card = ∑ a ∈ Finset.Icc 1 K, N / a := by
    rw [hAdef, Finset.card_filter, Finset.sum_product]
    dsimp only
    have step : ∀ a ∈ Finset.Icc 1 N,
        (∑ b ∈ Finset.Icc 1 N, ite (a * b ≤ N ∧ a ≤ K) 1 0) = ite (a ≤ K) (N / a) 0 := by
      intro a ha; rw [Finset.mem_Icc] at ha
      by_cases haK : a ≤ K
      · simp only [haK, and_true, if_true]
        rw [← Finset.card_filter]; exact hcount a ha.1
      · simp [haK]
    rw [Finset.sum_congr rfl step, ← Finset.sum_filter, hsetK]
  -- #B = ∑_{a≤K} ⌊N/a⌋  (count by the second coordinate)
  have hB : B.card = ∑ a ∈ Finset.Icc 1 K, N / a := by
    rw [hBdef, Finset.card_filter, Finset.sum_product_right]
    dsimp only
    have step : ∀ b ∈ Finset.Icc 1 N,
        (∑ a ∈ Finset.Icc 1 N, ite (a * b ≤ N ∧ b ≤ K) 1 0) = ite (b ≤ K) (N / b) 0 := by
      intro b hb; rw [Finset.mem_Icc] at hb
      by_cases hbK : b ≤ K
      · simp only [hbK, and_true, if_true]
        rw [← Finset.card_filter]
        have hcomm : (Finset.Icc 1 N).filter (fun a => a * b ≤ N)
            = (Finset.Icc 1 N).filter (fun x => b * x ≤ N) := by
          apply Finset.filter_congr
          intro a _
          exact ⟨fun h => by rwa [Nat.mul_comm] at h, fun h => by rwa [Nat.mul_comm] at h⟩
        rw [hcomm]
        exact hcount b hb.1
      · simp [hbK]
    rw [Finset.sum_congr rfl step, ← Finset.sum_filter, hsetK]
  -- #(A ∩ B) = K²
  have hAB : (A ∩ B).card = K ^ 2 := by
    have hAiB : A ∩ B = Finset.Icc 1 K ×ˢ Finset.Icc 1 K := by
      rw [hAdef, hBdef]
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, hb1, _⟩, _, haK⟩, _, _, hbK⟩
        exact ⟨⟨ha1, haK⟩, hb1, hbK⟩
      · rintro ⟨⟨ha1, haK⟩, hb1, hbK⟩
        have haN : p.1 ≤ N := le_trans haK hKleN
        have hbN : p.2 ≤ N := le_trans hbK hKleN
        have hab : p.1 * p.2 ≤ N := le_trans (Nat.mul_le_mul haK hbK) hK2leN
        exact ⟨⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hab, haK⟩, ⟨⟨ha1, haN⟩, hb1, hbN⟩, hab, hbK⟩
    rw [hAiB, Finset.card_product, Nat.card_Icc]
    have : K + 1 - 1 = K := by omega
    rw [this]; ring
  -- A ∪ B = P  (every lattice point has a coordinate ≤ K)
  have hAuB : A ∪ B = P := by
    rw [hAdef, hBdef, hPdef]
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro (⟨h, hab, _⟩ | ⟨h, hab, _⟩) <;> exact ⟨h, hab⟩
    · rintro ⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hab⟩
      by_cases h1 : p.1 ≤ K
      · exact Or.inl ⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hab, h1⟩
      · push_neg at h1
        refine Or.inr ⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hab, ?_⟩
        by_contra h2; push_neg at h2
        have : (K + 1) * (K + 1) ≤ p.1 * p.2 := Nat.mul_le_mul (by omega) (by omega)
        omega
  -- combine via inclusion–exclusion
  have hcomb := Finset.card_union_add_card_inter A B
  rw [hAuB, hP, hAB, hA, hB] at hcomb
  rw [two_mul]; exact hcomb

/-! ### The floor-sum decomposition -/

/-- `∑_{a=1}^{K} ⌊N/a⌋ = N·(∑_{a=1}^{K} 1/a) − F` with the fractional defect
`F = ∑_{a=1}^{K} (N/a − ⌊N/a⌋) ∈ [0, K]`. -/
theorem sum_floor_div_eq (N K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, ((N / a : ℕ) : ℝ)
      = (N : ℝ) * (∑ a ∈ Finset.Icc 1 K, (a : ℝ)⁻¹)
        - ∑ a ∈ Finset.Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [div_eq_mul_inv]; ring

/-- The fractional defect `F` lies in `[0, K]`. -/
theorem sum_frac_bounds (N K : ℕ) :
    0 ≤ ∑ a ∈ Finset.Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ)) ∧
      ∑ a ∈ Finset.Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ)) ≤ K := by
  constructor
  · refine Finset.sum_nonneg (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    have : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := Nat.cast_div_le
    linarith
  · calc ∑ a ∈ Finset.Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ))
        ≤ ∑ _a ∈ Finset.Icc 1 K, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [Finset.mem_Icc] at ha
          have hub : N ≤ (N / a + 1) * a := by
            have h := Nat.div_add_mod N a
            have hm : N % a < a := Nat.mod_lt N (by omega)
            nlinarith [h, hm]
          have hpa : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
          have : (N : ℝ) / a ≤ ((N / a : ℕ) : ℝ) + 1 := by
            rw [div_le_iff₀ hpa]
            calc (N : ℝ) ≤ (((N / a + 1) * a : ℕ) : ℝ) := by exact_mod_cast hub
              _ = (((N / a : ℕ) : ℝ) + 1) * a := by push_cast; ring
          linarith
      _ = K := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-- `∑_{a=1}^{K} 1/a = harmonic K` (cast to `ℝ`). -/
theorem sum_inv_eq_harmonic (K : ℕ) :
    (∑ a ∈ Finset.Icc 1 K, (a : ℝ)⁻¹) = (harmonic K : ℝ) := by
  rw [harmonic_eq_sum_Icc]; push_cast; rfl

/-! ### The Dirichlet divisor asymptotic -/

set_option maxHeartbeats 1000000 in
/-- **Dirichlet's divisor problem, explicit error form.** For `N ≥ 4`,
`|∑_{n=1}^{N} d(n) − (N·log N + (2γ−1)·N)| ≤ 12·√N`. -/
theorem abs_sum_sigma0_sub_le {N : ℕ} (hN : 4 ≤ N) :
    |(∑ n ∈ Finset.Ioc 0 N, ((σ 0 n : ℝ)))
        - ((N : ℝ) * Real.log N + (2 * eulerMascheroniConstant - 1) * N)|
      ≤ 12 * Real.sqrt N := by
  set K := Nat.sqrt N with hKdef
  have hK2leN : K ^ 2 ≤ N := Nat.sqrt_le' N
  have hNltK1 : N < (K + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hK1 : 1 ≤ K := by rw [hKdef, Nat.le_sqrt']; nlinarith [hN]
  -- index-set conversions
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  -- real shorthands
  have hKRpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set sN : ℝ := Real.sqrt N with hsN
  have hsNpos : 0 < sN := Real.sqrt_pos.mpr hNRpos
  have hsqsN : sN ^ 2 = (N : ℝ) := Real.sq_sqrt hNRpos.le
  have hsqrt_ge2 : 2 ≤ sN := by
    rw [hsN, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  -- K ≤ √N
  have hKR_le : (K : ℝ) ≤ sN := by
    rw [hsN]; refine Real.le_sqrt_of_sq_le ?_
    calc (K : ℝ) ^ 2 = ((K ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) := by exact_mod_cast hK2leN
  -- √N < K + 1
  have hsqrt_lt : sN < (K : ℝ) + 1 := by
    rw [hsN, Real.sqrt_lt' (by positivity)]
    calc (N : ℝ) < (((K + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNltK1
      _ = ((K : ℝ) + 1) ^ 2 := by push_cast; ring
  -- √N < 2K
  have hsqrt_lt_2K : sN < 2 * K := by nlinarith [hsqrt_lt, hsqrt_ge2]
  -- N − K² ∈ [0, 2K]  (real)
  have hNsubK2_le : (N : ℝ) - (K : ℝ) ^ 2 ≤ 2 * K := by
    have hN' : N ≤ K ^ 2 + 2 * K := by nlinarith [hNltK1]
    have : (N : ℝ) ≤ ((K ^ 2 + 2 * K : ℕ) : ℝ) := by exact_mod_cast hN'
    push_cast at this; nlinarith [this]
  have hNsubK2_nonneg : 0 ≤ (N : ℝ) - (K : ℝ) ^ 2 := by
    have : ((K ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK2leN
    push_cast at this; nlinarith [this]
  -- the divisor sum equals the asymmetric floor sum
  have hD1 : ∑ n ∈ Finset.Ioc 0 N, ((σ 0 n : ℝ)) = ∑ a ∈ Finset.Icc 1 N, ((N / a : ℕ) : ℝ) := by
    have key := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N
    rw [← Nat.cast_sum, key, Nat.cast_sum, hIoc]
  -- hyperbola identity in ℝ:  D = 2·S − K²
  have hHyp : (∑ a ∈ Finset.Icc 1 N, ((N / a : ℕ) : ℝ)) + (K : ℝ) ^ 2
      = 2 * ∑ a ∈ Finset.Icc 1 K, ((N / a : ℕ) : ℝ) := by
    have h := hyperbola_identity N
    rw [← hKdef] at h
    calc (∑ a ∈ Finset.Icc 1 N, ((N / a : ℕ) : ℝ)) + (K : ℝ) ^ 2
        = (((∑ a ∈ Finset.Icc 1 N, N / a) + K ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ = ((2 * ∑ a ∈ Finset.Icc 1 K, N / a : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * ∑ a ∈ Finset.Icc 1 K, ((N / a : ℕ) : ℝ) := by push_cast; ring
  -- the head sum:  S = N·H_K − F
  set S : ℝ := ∑ a ∈ Finset.Icc 1 K, ((N / a : ℕ) : ℝ) with hS
  set HK : ℝ := (harmonic K : ℝ) with hHK
  set F : ℝ := ∑ a ∈ Finset.Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ)) with hF
  have hSeq : S = (N : ℝ) * HK - F := by
    rw [hS, sum_floor_div_eq N K, sum_inv_eq_harmonic, ← hHK, ← hF]
  obtain ⟨hF0, hFK⟩ := sum_frac_bounds N K
  rw [← hF] at hF0 hFK
  -- harmonic estimate
  have hHKbound : |HK - Real.log K - eulerMascheroniConstant| ≤ 1 / K :=
    abs_harmonic_sub_log_sub_gamma_le hK1
  set e : ℝ := HK - Real.log K - eulerMascheroniConstant with he
  have heHK : HK = Real.log K + eulerMascheroniConstant + e := by rw [he]; ring
  have hebound : |e| ≤ 1 / K := hHKbound
  -- log lower/upper
  have hlog_lb : 2 * Real.log K ≤ Real.log N := by
    have h1 : Real.log ((K : ℝ) ^ 2) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by
        calc (K : ℝ) ^ 2 = ((K ^ 2 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (N : ℝ) := by exact_mod_cast hK2leN)
    rwa [Real.log_pow] at h1
    -- log (K^2) = 2 * log K
  have hlog_ub : Real.log N - 2 * Real.log K ≤ 2 / K := by
    have hdiv : Real.log N - 2 * Real.log K = Real.log ((N : ℝ) / (K : ℝ) ^ 2) := by
      rw [Real.log_div hNRpos.ne' (by positivity), Real.log_pow]; ring
    rw [hdiv]
    have hpos : (0 : ℝ) < (N : ℝ) / (K : ℝ) ^ 2 := by positivity
    have h1 : Real.log ((N : ℝ) / (K : ℝ) ^ 2) ≤ (N : ℝ) / (K : ℝ) ^ 2 - 1 :=
      Real.log_le_sub_one_of_pos hpos
    have h2 : (N : ℝ) / (K : ℝ) ^ 2 - 1 ≤ 2 / K := by
      rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hNsubK2_le, hKRpos]
    linarith
  -- assemble D and the error
  have hD : (∑ n ∈ Finset.Ioc 0 N, ((σ 0 n : ℝ)))
      = 2 * (N : ℝ) * HK - 2 * F - (K : ℝ) ^ 2 := by
    rw [hD1]; have : (∑ a ∈ Finset.Icc 1 N, ((N / a : ℕ) : ℝ)) = 2 * S - (K : ℝ) ^ 2 := by
      linarith [hHyp]
    rw [this, hSeq]; ring
  -- error expression
  have herr : (∑ n ∈ Finset.Ioc 0 N, ((σ 0 n : ℝ)))
        - ((N : ℝ) * Real.log N + (2 * eulerMascheroniConstant - 1) * N)
      = ((N : ℝ) * (2 * Real.log K) - (N : ℝ) * Real.log N) + 2 * (N : ℝ) * e
        - 2 * F + ((N : ℝ) - (K : ℝ) ^ 2) := by
    rw [hD, heHK]; ring
  rw [herr]
  -- bound each piece
  have hb1 : |(N : ℝ) * (2 * Real.log K) - (N : ℝ) * Real.log N| ≤ 2 * (N : ℝ) / K := by
    have hpos2NK : (0 : ℝ) ≤ 2 * (N : ℝ) / K := by positivity
    have hupper : (N : ℝ) * Real.log N - (N : ℝ) * (2 * Real.log K) ≤ 2 * (N : ℝ) / K := by
      have h := mul_le_mul_of_nonneg_left hlog_ub hNRpos.le
      rw [show 2 * (N : ℝ) / K = (N : ℝ) * (2 / K) by ring]; nlinarith [h]
    have hlower : 0 ≤ (N : ℝ) * Real.log N - (N : ℝ) * (2 * Real.log K) := by
      have h := mul_nonneg hNRpos.le (by linarith [hlog_lb] : (0:ℝ) ≤ Real.log N - 2 * Real.log K)
      nlinarith [h]
    rw [abs_le]; exact ⟨by linarith [hupper], by linarith [hlower, hpos2NK]⟩
  have hb2 : |2 * (N : ℝ) * e| ≤ 2 * (N : ℝ) / K := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hNRpos]
    calc 2 * (N : ℝ) * |e| ≤ 2 * (N : ℝ) * (1 / K) :=
          by nlinarith [hebound, hNRpos.le, abs_nonneg e]
      _ = 2 * (N : ℝ) / K := by ring
  have hb3 : |2 * F| ≤ 2 * (K : ℝ) := by
    rw [abs_of_nonneg (by linarith [hF0])]; linarith [hFK]
  have hb4 : |(N : ℝ) - (K : ℝ) ^ 2| ≤ 2 * (K : ℝ) := by
    rw [abs_of_nonneg hNsubK2_nonneg]; exact hNsubK2_le
  -- combine via triangle inequality
  have key4 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
    intro a b c d
    calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ (|a + b| + |c|) + |d| := by linarith [abs_add_le (a + b) c]
      _ ≤ ((|a| + |b|) + |c|) + |d| := by linarith [abs_add_le a b]
  have h2NK : 2 * (N : ℝ) / K ≤ 4 * sN := by
    rw [div_le_iff₀ hKRpos]; nlinarith [hsqrt_lt_2K, hsNpos, hsqsN]
  have hsplit : ((N : ℝ) * (2 * Real.log K) - (N : ℝ) * Real.log N) + 2 * (N : ℝ) * e
        - 2 * F + ((N : ℝ) - (K : ℝ) ^ 2)
      = ((N : ℝ) * (2 * Real.log K) - (N : ℝ) * Real.log N) + (2 * (N : ℝ) * e)
        + (-(2 * F)) + ((N : ℝ) - (K : ℝ) ^ 2) := by ring
  rw [hsplit]
  refine (key4 _ _ _ _).trans ?_
  rw [abs_neg]
  linarith [hb1, hb2, hb3, hb4, h2NK, hKR_le]

/-- **Dirichlet's divisor problem (asymptotic form).**
`∑_{n ≤ N} d(n) − (N·log N + (2γ−1)·N) = O(√N)` as `N → ∞`. -/
theorem sum_sigma0_isBigO_sqrt :
    (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, ((σ 0 n : ℝ)))
        - ((N : ℝ) * Real.log N + (2 * eulerMascheroniConstant - 1) * N))
      =O[atTop] (fun N : ℕ => Real.sqrt N) := by
  refine IsBigO.of_bound 12 ?_
  filter_upwards [eventually_ge_atTop 4] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_sum_sigma0_sub_le hN

end LeanFormalizations.DirichletDivisor
