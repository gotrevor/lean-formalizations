/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #249, #251, #1049: three dyadic-tail routes, walked and closed (2026-10-05)

The three problems ask whether these numbers are irrational:

* #249: `∑ φ(n) / 2^n`;
* #251: `∑ p_n / 2^n`;
* #1049 (Chowla): `∑ 1 / (t^n − 1)` for rational `t > 1`, with `t = 3/2` the first open case.

One mechanism was invented for each and killed the same day.  Each death matches a barrier that
William Cook (Plectis, `wcook04/plectis-erdos` at `605b273`) had posted independently on the
erdosproblems.com threads.  The `Maze.lean` rows anchor on the declarations below.

The common frame: if `x = ∑ a_n 2^(-n)` is rational with odd denominator part `q`, every scaled
tail `V_N = q · ∑_{k ≥ 1} a_(N+k) 2^(-k)` is a positive integer, and
`V_(N+M) = 2^M V_N − q ∑_{i ≤ M} a_(N+i) 2^(M−i)`.
-/

namespace LeanFormalizations.ErdosDyadic

open Filter

/-- The `n`th prime, zero-indexed (`p 0 = 2`). -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap `g n = p (n + 1) − p n`. -/
noncomputable abbrev g (n : ℕ) : ℕ := p (n + 1) - p n

/-! ## #249: CRT forcing of `2`-adic valuations (route M1) -/

/-- **`φ = μ ∗ id` at `x = 1/2`** (williamwkcook, erdosproblems #249 thread, 2026-09-11).  Believed
(~99%): `∑ φ(m) x^m = ∑_d μ(d) x^d / (1 − x^d)²`, and `2^d/(2^d − 1)² = 1/(2^d − 1) + 1/(2^d − 1)²`
with `∑_d μ(d) / (2^d − 1) = 1/2`.  So any proof for #249 must use Möbius arithmetic.  Replacing
`μ` by a free `{−1, 0, 1}` sequence reaches rationals, because the terms are `≍ 2^(-d)`. -/
theorem totient_dyadic_eq_moebius :
    ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n =
      ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / ((2 : ℝ) ^ n - 1) ^ 2 + 1 / 2 := by
  sorry

/-- **Route M1 (Erdős's `d(n)` template applied to `φ`).**  If `2^i ∣ φ(N + i)` for `1 ≤ i ≤ M`, then
`2^M ∣ V_(N+M)`, while `0 < V_(N+M) ≤ q (N + M + 2)` since `φ(m) ≤ m`.  The route closes #249 if, for
every constant `C` and start `N₀`, such a block exists with `C (N + M + 2) < 2^M`. -/
def TotientForcingRoute : Prop :=
  ∀ C N₀ : ℕ, ∃ M N : ℕ, N₀ ≤ N ∧ C * (N + M + 2) < 2 ^ M ∧
    ∀ i ∈ Finset.Icc 1 M, 2 ^ i ∣ Nat.totient (N + i)

/-- **The bit-count barrier (believed ~85%).**  `2^i ∣ φ(m)` has density about
`log log m / 2^(i−1)` once `i` exceeds `log₂ log log m`, so a block of length `M` costs about
`M²/2` bits of conditions.  The route needs `N < 2^M`, i.e. only `log₂ N ≈ M` bits are available.
The expected number of `N < 2^M` with such a block is about `2^(M − M²/2 + O(M log log M))`,
which is summable in `M`.  Control: for `d(n)` the coefficients are polylogarithmic, so `M ≈ log log N`
suffices and the count passes, which matches Erdős 1948.  For unbounded `φ` it fails.  Cook's
#249 note proves the bounded variants `φ(n) mod m` and says the unbounded series is outside
that method. -/
theorem not_totientForcingRoute : ¬ TotientForcingRoute := by
  sorry

/-! ## #251: windows of controlled gaps (route M2) -/

/-- **Gap reduction** (Tao, erdosproblems #251 thread, 2025-10-07).  Believed (~99%): summation by
parts on `p_n = 2 + ∑_(i<n) g_i`.  So #251 is the irrationality of the gap series. -/
theorem primes_dyadic_eq_two_add_gaps :
    ∑' n, (p n : ℝ) / 2 ^ (n + 1) = 2 + ∑' n, (g n : ℝ) / 2 ^ (n + 1) := by
  sorry

/-- **Cook 2026, Proposition 1.1 (a weaker form).**  Sparse, slowly growing corrections to the
prime gaps make the dyadic gap series rational.  The corrections are eventually divisible by every
fixed `q`, so the perturbed partial sums keep every eventual congruence of `p_n`.  The source also
puts the support on a set of upper Banach density zero and keeps `m`-gap block statistics for
`m = o(log log X)`; those clauses are dropped here, so this is weaker than the source.

W. Cook, *Erdős Problem 251: prime-gap dyadic series*, `wcook04/plectis-erdos` at `605b273`,
`paper/251/erdos-251-prime-gap-dyadic-series.pdf`, Prop. 1.1 (unrefereed). -/
def Cook2026GapPerturbation : Prop :=
  ∀ ε > (0 : ℝ), ∃ e : ℕ → ℕ,
    (∀ᶠ n in atTop, (e n : ℝ) ≤ Real.log (n + 3) ^ ε) ∧
    (∀ q : ℕ, 0 < q → ∀ᶠ n in atTop, q ∣ e n) ∧
    ∃ r : ℚ, ∑' n, ((g n + e n : ℕ) : ℝ) / 2 ^ (n + 1) = r

/-! ## #1049 at `t = 3/2`: `3`-adic forcing (route M3) -/

/-- The Lambert series of #1049, `F(t) = ∑_(n ≥ 1) 1 / (t^n − 1)`. -/
noncomputable def lambertF (t : ℝ) : ℝ := ∑' n : ℕ, 1 / (t ^ (n + 1) - 1)

/-- **Cook 2026, from Zudilin 2004 (a weaker form).**  For coprime `a > b ≥ 1` with
`log b / log a < θ* = 0.40568…`, `F(a/b)` is irrational.  The constant `0.4056 < θ*` makes this
weaker than the source.  `b = 1` is Erdős 1948.

W. Cook, *Erdős Problem 1049: rational-base Lambert series*, `wcook04/plectis-erdos` at `605b273`,
`paper/1049/erdos-1049-rational-base-lambert.pdf` (unrefereed); W. Zudilin, *Heine's basic
transform and a permutation group for q-harmonic series*, Acta Arith. 111 (2004). -/
def Cook2026RationalBase : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → b < a → 1 ≤ b →
    Real.log b / Real.log a < 0.4056 → Irrational (lambertF ((a : ℝ) / b))

/-- **`t = 3/2` lies outside every known rational-base region.**  `log 2 / log 3 > 1/2`, beyond
Cook's `0.4056` (and Bundschuh–Väänänen's `0.3987`).  Route M3 (force `3^i ∣ τ(N + i)` and use
integrality of `W_N = s · 2^N · T_N`) dies because the `2^N` scale swamps any forced `3^M`.  This
is the Mahler `3/2` wall. -/
theorem three_halves_outside_cook_region : ¬ (Real.log 2 / Real.log 3 < 0.4056) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < 2 * Real.log 2 := by
    have h : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [not_lt, le_div_iff₀ h3]
  linarith

/-! ## #267: lacunary Fibonacci reciprocals (superseded, 2026-10-05) -/

/-- **Snyder 2026 (Erdős #267, every `c > 1`).**  If `n` is positive, strictly increasing and
`n (k + 1) ≥ c · n k` for some `c > 1`, then `∑ 1 / F_(n_k)` is irrational.  Badea 1993 had
`c ≥ 2`; Nguyen 2022 (ANT 16) has transcendence for `c > 2`, which is sharp because
`∑ 1/F_(2^k) = (7 − √5)/2`.

C. Snyder (GPT 5.6, custom harness), proof claim on erdosproblems.com/forum/thread/267,
2026-07-15, bundle `erdos-267-solution.zip` from starfleetmath.com: theorem
`Research.erdos_problem_267`, 27,673-line `Erdos267Standalone.lean`.  **Independently kernel-checked
here 2026-10-05** against Mathlib `fabf563` (Lean v4.31.0, a CoW clone of `~/.lake-base/4.31.0`).
The build passed and the axioms are `[propext, Classical.choice, Quot.sound]`.  The statement
matches formal-conjectures `erdos_267` up to real versus rational `c`, which are equivalent.  Not
`require`d yet; the route to that is a fork plus a pinned `require`. -/
def Snyder2026Erdos267 : Prop :=
  ∀ n : ℕ → ℕ, (∀ k, 0 < n k) → StrictMono n →
    (∃ c : ℝ, 1 < c ∧ ∀ k, c * (n k : ℝ) ≤ n (k + 1)) →
    Irrational (∑' k, (Nat.fib (n k) : ℝ)⁻¹)

-- The tiling identity and the algebraicity conjecture moved to `LacunaryFib/` (phase LF1).

end LeanFormalizations.ErdosDyadic
