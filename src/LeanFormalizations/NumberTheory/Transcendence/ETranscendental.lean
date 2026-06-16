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

## Status (this lap)

* `exists_intPoly_aeval_eq_zero` — **proved, axiom-clean**: the algebraic reduction.
  If `e` is algebraic over `ℚ` then a *nonzero integer* polynomial with *nonzero
  constant term* annihilates `e` (clear denominators via `IsFractionRing`, then
  factor out the largest power of `X` using `e ≠ 0`).
* `no_intPoly_aeval_eq_zero` — **isolated analytic crux (disclosed `sorry`)**: no such
  polynomial can annihilate `e`. This is the Hermite assembly of `exp_polynomial_approx`
  and is the single remaining hard step. Roadmap in its docstring.
* `e_transcendental` — the headline, proved *modulo* the crux.

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

open Polynomial Filter
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

/-- **Hermite's contradiction — the isolated analytic crux** (disclosed `sorry`).
No nonzero integer polynomial with nonzero constant term annihilates `e`.

This is the assembly of `LindemannWeierstrass.exp_polynomial_approx` into a nonzero
integer of absolute value `< 1`; see the file header for the full roadmap. It is the
single remaining hard step in the transcendence of `e`, and the concrete
prerequisite being chipped toward `HermiteLindemann.hermite_lindemann`. -/
theorem no_intPoly_aeval_eq_zero (q : ℤ[X]) (hq0 : q.coeff 0 ≠ 0) :
    aeval (Real.exp 1) q ≠ 0 := by
  sorry

/-- **Transcendence of `e`** over `ℚ` (Hermite, 1873), modulo the isolated analytic
crux `no_intPoly_aeval_eq_zero`. The algebraic reduction is machine-checked. -/
theorem e_transcendental : Transcendental ℚ (Real.exp 1) := by
  intro h
  obtain ⟨q, hq0, hq⟩ := exists_intPoly_aeval_eq_zero h
  exact no_intPoly_aeval_eq_zero q hq0 hq

end LeanFormalizations.Transcendence
