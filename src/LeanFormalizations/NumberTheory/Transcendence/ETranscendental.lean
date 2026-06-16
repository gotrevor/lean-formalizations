/-
# Transcendence of `e` — chipping the Lindemann–Weierstrass wall

This file attacks **Hermite's 1873 theorem** that `e = Real.exp 1` is transcendental
over `ℚ`, building directly on the *analytic* part of Lindemann–Weierstrass already
in mathlib:

  `LindemannWeierstrass.exp_polynomial_approx`
  (`Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`).

Transcendence of `e` is the **accessible frontier** of the Lindemann–Weierstrass
wall cited by `HermiteLindemann.hermite_lindemann`: it needs *no* symmetric-function
machinery, because the relevant polynomial `∏_{k=1}^m (X - k)` already has its roots
at the ordinary integers `1,…,m`. (The full `hermite_lindemann` for `π` additionally
needs symmetric functions over the Galois conjugates of `iπ` — the genuinely missing
mathlib infrastructure. Transcendence of `e` is exactly the `α = 1` instance of
`hermite_lindemann` and the natural first prerequisite to discharge.)

## Status — COMPLETE, fully axiom-clean

`e_transcendental : Transcendental ℚ (Real.exp 1)` is **proved end-to-end**;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `sorry`, no custom
axiom). This *discharges* the `α = 1` instance of `HermiteLindemann.hermite_lindemann`.

* `exists_intPoly_aeval_eq_zero` — the algebraic reduction (denominator-clearing via
  `IsFractionRing` + factor out the `X`-power using `e ≠ 0`).
* `tendsto_const_mul_pow_div_factorial`, `exists_prime_smallness`,
  `hermitePoly_eval_zero_ne`, `hermitePoly_aroots` — analytic decay + prime selection
  (roadmap step 2) and the Hermite polynomial's value/roots data (roadmap step 1).
* `no_intPoly_aeval_eq_zero` — the full Hermite assembly (roadmap step 3): the integer
  `N`, its `‖(N:ℂ)‖ < 1` bound, and `mod p` nonvanishing.
* `e_transcendental` — the headline.

The remaining frontier (general `hermite_lindemann`, hence `π`) needs symmetric
functions over the Galois conjugates of the algebraic exponents — the conjugate-product
extension of this same `exp_polynomial_approx` assembly. See `PENDING_WORK.md`.

## The Hermite assembly (roadmap for `no_intPoly_aeval_eq_zero`)

Let `q : ℤ[X]`, `q.coeff 0 ≠ 0`, and suppose `aeval e q = 0`, i.e.
`∑_{k=0}^{m} a_k e^k = 0` with `a_k = q.coeff k`, `a_0 ≠ 0`, `m = q.natDegree`.

1. Set `f = ∏_{k=1}^{m} (X - C k) : ℤ[X]`, with `f.eval 0 = (-1)^m m! ≠ 0` and
   complex roots exactly `{1,…,m}`. Apply `exp_polynomial_approx f` to get `c`.
2. For a prime `p` with `p > (f.eval 0).natAbs`, `p > |a_0|`, and
   `(∑_{k}|a_k|) · c^p/(p-1)! < 1`, obtain `n` (`p ∤ n`) and `gp : ℤ[X]` with, for
   each `k ∈ {1,…,m}`:  `‖n·e^k - p·gp(k)‖ ≤ c^p/(p-1)!`.
3. Multiply `∑ a_k e^k = 0` by `n`; replace `n·e^k = p·gp(k) + ε_k`. The integer
   `N := a_0·n + p·∑_{k=1}^m a_k·gp(k)` satisfies `‖(N:ℂ)‖ ≤ (∑|a_k|)·c^p/(p-1)! < 1`,
   so `N = 0`; but `N ≡ a_0·n (mod p)` with `p ∤ a_0·n`, so `N ≠ 0`. Contradiction.
-/
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Order.Floor

open Polynomial Filter Finset
open scoped Nat Topology

namespace LeanFormalizations.Transcendence

/-- **Algebraic reduction (proved).** If `e = Real.exp 1` is algebraic over `ℚ`, there
is a nonzero *integer* polynomial annihilating `e` whose **constant term is nonzero**.

Two steps: (i) `e` algebraic over `ℚ` ⟹ algebraic over `ℤ` (clearing denominators via
`IsFractionRing.isAlgebraic_iff`); (ii) factor out the largest power of `X` from the
integer annihilator (`exists_eq_pow_rootMultiplicity_mul_and_not_dvd` at `0`) — the
cofactor `q` has `q.coeff 0 ≠ 0` and still annihilates `e` because `e ≠ 0`. -/
theorem exists_intPoly_aeval_eq_zero (h : IsAlgebraic ℚ (Real.exp 1)) :
    ∃ q : ℤ[X], q.coeff 0 ≠ 0 ∧ aeval (Real.exp 1) q = 0 := by
  have hz : IsAlgebraic ℤ (Real.exp 1) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h
  obtain ⟨p, hp0, hp⟩ := hz
  obtain ⟨q, hq_eq, hq_ndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 (0 : ℤ)
  rw [map_zero, sub_zero] at hq_eq hq_ndvd
  have hcoeff : q.coeff 0 ≠ 0 := fun hc => hq_ndvd (X_dvd_iff.mpr hc)
  refine ⟨q, hcoeff, ?_⟩
  have hpow : aeval (Real.exp 1) p
      = (Real.exp 1) ^ (p.rootMultiplicity 0) * aeval (Real.exp 1) q := by
    conv_lhs => rw [hq_eq]
    rw [map_mul, map_pow, aeval_X]
  rw [hpow] at hp
  rcases mul_eq_zero.mp hp with h1 | h2
  · exact absurd h1 (pow_ne_zero _ (Real.exp_ne_zero 1))
  · exact h2

/-! ### Infrastructure for the analytic crux (proved, axiom-clean)

Three portable building blocks for the Hermite assembly: the analytic limit
`B·c^p/(p-1)! → 0`, the prime-selection corollary it yields (step 2 of the roadmap),
and that the Hermite polynomial `∏_{k=1}^m (X − k)` has nonzero value at `0` (step 1,
the hypothesis `exp_polynomial_approx` requires). -/

/-- `B · c^p / (p-1)! → 0` as `p → ∞`: the analytic decay driving Hermite's bound.
Reindex `tendsto_pow_div_factorial_atTop` (`c^n/n! → 0`) by `p ↦ p-1`. -/
theorem tendsto_const_mul_pow_div_factorial (c B : ℝ) :
    Tendsto (fun p : ℕ => B * (c ^ p / (p - 1)!)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => c ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop c
  have h1 : Tendsto (fun j : ℕ => c ^ (j + 1) / j ! : ℕ → ℝ) atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => c * (c ^ j / j !) : ℕ → ℝ) atTop (𝓝 (c * 0)) := h0.const_mul c
    rw [mul_zero] at this
    refine this.congr (fun j => ?_); rw [pow_succ]; ring
  have h2 : Tendsto (fun p : ℕ => c ^ p / (p - 1)! : ℕ → ℝ) atTop (𝓝 0) := by
    refine (h1.comp (tendsto_sub_atTop_nat 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with p hp
    simp only [Function.comp_apply]; rw [Nat.sub_add_cancel hp]
  have := h2.const_mul B; rw [mul_zero] at this; exact this

/-- **Prime selection** (roadmap step 2): a prime `p` exceeding any bound `M` with the
Hermite smallness `B · c^p/(p-1)! < 1`. From the decay above + infinitude of primes. -/
theorem exists_prime_smallness (c B : ℝ) (M : ℕ) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ B * (c ^ p / (p - 1)!) < 1 := by
  have hev : ∀ᶠ p : ℕ in atTop, B * (c ^ p / (p - 1)!) < 1 :=
    (tendsto_const_mul_pow_div_factorial c B).eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max N (M + 1))
  exact ⟨p, hp_prime,
    lt_of_lt_of_le (Nat.lt_succ_self M) (le_trans (le_max_right _ _) hp_ge),
    hN p (le_trans (le_max_left _ _) hp_ge)⟩

/-- **The Hermite polynomial value at 0** (roadmap step 1): `∏_{k=1}^m (X − k)` does not
vanish at `0`, so `exp_polynomial_approx` applies to it. -/
theorem hermitePoly_eval_zero_ne (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, (X - C (k : ℤ))).eval 0 ≠ 0 := by
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  rw [eval_sub, eval_X, eval_C]
  simp only [Finset.mem_Icc] at hk
  have : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk.1)
  simpa using this

/-- **The Hermite polynomial's complex roots** (roadmap step 1): the roots of
`∏_{k=1}^m (X − k)` over `ℂ` are exactly the integers `1,…,m` (as a multiset, each
with multiplicity one). Lets the per-root bound from `exp_polynomial_approx` be
re-summed over `k = 1,…,m`. -/
theorem hermitePoly_aroots (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, (X - C (k : ℤ))).aroots ℂ
      = (Finset.Icc 1 m).val.map (fun k : ℕ => (k : ℂ)) := by
  rw [Polynomial.aroots_def, Polynomial.map_prod]
  have hcongr : ∀ k ∈ Finset.Icc 1 m,
      (X - C (k : ℤ)).map (algebraMap ℤ ℂ) = X - C ((k : ℕ) : ℂ) := by intro k _; simp
  rw [Finset.prod_congr rfl hcongr, Finset.prod_eq_multiset_prod]
  have key := roots_multiset_prod_X_sub_C ((Finset.Icc 1 m).val.map (fun k : ℕ => (k : ℂ)))
  rw [Multiset.map_map] at key
  exact key

/-- **Hermite's contradiction** (proved). No nonzero integer polynomial with nonzero
constant term annihilates `e`.

The assembly of `LindemannWeierstrass.exp_polynomial_approx` into a nonzero integer of
absolute value `< 1`: build the integer `N := a₀·n + p·∑ aₖ·gp(k)`; the analytic
estimates (re-summed over `hermitePoly_aroots`) give `‖(N:ℂ)‖ ≤ B·c^p/(p-1)! < 1` so
`N = 0`, while `N ≡ a₀·n (mod p)` with `p ∤ a₀·n` gives `N ≠ 0` — contradiction. -/
theorem no_intPoly_aeval_eq_zero (q : ℤ[X]) (hq0 : q.coeff 0 ≠ 0) :
    aeval (Real.exp 1) q ≠ 0 := by
  intro hrel
  set m := q.natDegree with hm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `q` is a nonzero constant: `aeval e q = q.coeff 0 ≠ 0`.
    rw [aeval_eq_sum_range, ← hm, hm0] at hrel
    simp only [zero_add, range_one, sum_singleton, pow_zero, zsmul_eq_mul, mul_one] at hrel
    exact hq0 (by exact_mod_cast hrel)
  -- The Hermite polynomial `f = ∏_{k=1}^m (X - k)` and its approximation data.
  set f : ℤ[X] := ∏ k ∈ Finset.Icc 1 m, (X - C (k : ℤ)) with hfdef
  have hf0 : f.eval 0 ≠ 0 := hermitePoly_eval_zero_ne m
  set a₀ : ℤ := q.coeff 0 with ha0
  set B : ℝ := ∑ k ∈ Finset.Icc 1 m, (|q.coeff k| : ℝ) with hB
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  obtain ⟨p, hp_prime, hp_gt, hp_small⟩ :=
    exists_prime_smallness c B (max (f.eval 0).natAbs a₀.natAbs)
  have hp_f : (f.eval 0).natAbs < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_a0 : a₀.natAbs < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  obtain ⟨n, hpn, gp, hgp_deg, hgp_bound⟩ := hc p hp_f hp_prime
  -- Per-root estimate re-expressed over `k = 1,…,m` (via `hermitePoly_aroots`).
  have hbound : ∀ k ∈ Finset.Icc 1 m,
      ‖(n : ℂ) * Complex.exp k - (p : ℂ) * aeval ((k : ℕ) : ℂ) gp‖ ≤ c ^ p / (p - 1)! := by
    intro k hk
    have hroot : ((k : ℕ) : ℂ) ∈ f.aroots ℂ := by
      rw [hfdef, hermitePoly_aroots]
      exact Multiset.mem_map_of_mem _ (Finset.mem_val.mpr hk)
    have hb := hgp_bound hroot
    rwa [zsmul_eq_mul, nsmul_eq_mul] at hb
  -- The annihilating relation, transported to `ℂ` and split off the `k = 0` term.
  have hcrel : ∑ k ∈ range (m + 1), (q.coeff k : ℂ) * Complex.exp k = 0 := by
    have hbridge : ∀ k : ℕ, Complex.exp (k : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ k := by
      intro k; rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; norm_num
    have hreal : ∑ k ∈ range (m + 1), (q.coeff k : ℝ) * (Real.exp 1) ^ k = 0 := by
      rw [← hrel, aeval_eq_sum_range, ← hm]
      exact Finset.sum_congr rfl (fun k _ => by rw [zsmul_eq_mul])
    have hcast : ((∑ k ∈ range (m + 1), (q.coeff k : ℝ) * (Real.exp 1) ^ k : ℝ) : ℂ) = 0 := by
      rw [hreal]; simp
    rw [Complex.ofReal_sum] at hcast
    rw [← hcast]
    exact Finset.sum_congr rfl (fun k _ => by rw [hbridge k]; push_cast; ring)
  have hsplit : (a₀ : ℂ) + ∑ k ∈ Icc 1 m, (q.coeff k : ℂ) * Complex.exp k = 0 := by
    rw [show range (m + 1) = insert 0 (Icc 1 m) from by
          ext x; simp only [mem_range, mem_insert, mem_Icc]; omega,
        Finset.sum_insert (by simp)] at hcrel
    simpa using hcrel
  -- The crucial integer `N := a₀·n + p·∑ aₖ·gp(k)`.
  set N : ℤ := a₀ * n + (p : ℤ) * ∑ k ∈ Finset.Icc 1 m, q.coeff k * gp.eval (k : ℤ) with hNdef
  have hNcast : (N : ℂ) =
      - ∑ k ∈ Finset.Icc 1 m,
          (q.coeff k : ℂ) * ((n : ℂ) * Complex.exp k - (p : ℂ) * aeval ((k : ℕ) : ℂ) gp) := by
    have haeval : ∀ k : ℕ, aeval ((k : ℕ) : ℂ) gp = ((gp.eval (k : ℤ) : ℤ) : ℂ) := by
      intro k
      have hh : ((k : ℕ) : ℂ) = algebraMap ℤ ℂ (k : ℤ) := by push_cast; ring
      rw [hh, aeval_algebraMap_apply]; simp [aeval_def]
    have e1 : ∀ k ∈ Icc 1 m,
        (q.coeff k : ℂ) * ((n : ℂ) * Complex.exp k - (p : ℂ) * aeval ((k : ℕ) : ℂ) gp)
        = (n : ℂ) * ((q.coeff k : ℂ) * Complex.exp k)
          - (p : ℂ) * ((q.coeff k : ℂ) * ((gp.eval (k : ℤ) : ℤ) : ℂ)) := by
      intro k _; rw [haeval k]; ring
    rw [hNdef, Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    linear_combination (n : ℂ) * hsplit
  -- `‖N‖ < 1` (analytic bound) forces `N = 0`…
  have hNzero : N = 0 := by
    have hnorm : ‖(N : ℂ)‖ < 1 := by
      rw [hNcast, norm_neg]
      calc ‖∑ k ∈ Finset.Icc 1 m,
              (q.coeff k : ℂ) * ((n : ℂ) * Complex.exp k - (p : ℂ) * aeval ((k : ℕ) : ℂ) gp)‖
          ≤ ∑ k ∈ Finset.Icc 1 m,
              ‖(q.coeff k : ℂ) * ((n : ℂ) * Complex.exp k - (p : ℂ) * aeval ((k : ℕ) : ℂ) gp)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 m, (|q.coeff k| : ℝ) * (c ^ p / (p - 1)!) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [norm_mul, Complex.norm_intCast]
            exact mul_le_mul_of_nonneg_left (hbound k hk) (by positivity)
        _ = B * (c ^ p / (p - 1)!) := by rw [hB, Finset.sum_mul]
        _ < 1 := hp_small
    rw [Complex.norm_intCast] at hnorm
    have hN1 : |N| < 1 := by exact_mod_cast hnorm
    exact Int.abs_lt_one_iff.mp hN1
  -- …while `p ∤ N` (since `N ≡ a₀·n (mod p)`, `p ∤ a₀·n`) forces `N ≠ 0`. Contradiction.
  have hNne : N ≠ 0 := by
    have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
    have hpa0 : ¬ (p : ℤ) ∣ a₀ := by
      intro hd
      have hpos : 0 < |a₀| := abs_pos.mpr hq0
      have hle : (p : ℤ) ≤ |a₀| := Int.le_of_dvd hpos ((dvd_abs _ _).mpr hd)
      rw [Int.abs_eq_natAbs] at hle
      omega
    have hdvd_prod : ¬ (p : ℤ) ∣ a₀ * n := fun h => (hp_prime_int.dvd_mul.mp h).elim hpa0 hpn
    intro hN0
    apply hdvd_prod
    have he : a₀ * n = -((p : ℤ) * ∑ k ∈ Finset.Icc 1 m, q.coeff k * gp.eval (k : ℤ)) := by
      rw [hNdef] at hN0; linarith [hN0]
    rw [he]
    exact (Dvd.intro _ rfl).neg_right
  exact hNne hNzero

/-- **Transcendence of `e`** over `ℚ` (Hermite, 1873) — fully machine-checked.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. -/
theorem e_transcendental : Transcendental ℚ (Real.exp 1) := by
  intro h
  obtain ⟨q, hq0, hq⟩ := exists_intPoly_aeval_eq_zero h
  exact no_intPoly_aeval_eq_zero q hq0 hq

end LeanFormalizations.Transcendence
