/-
# Prime-gap input to the HJSW lower bound — sharpening the general-`N` constant

The HJSW construction `shearSel p` gives `3(p−1)` no-three-collinear points inside `[0,2p)²`, so for
any prime `p` with `2p ≤ N` we get `3(p−1) ≤ maxNoThreeInLine N`
(`maxNoThreeInLine_ge_of_two_mul_prime_le`, the *prime-gap interface*). The general-`N` lower constant
is therefore exactly `3/2 · (largest prime ≤ N/2)/(N/2)` — pinned by **how close to `N/2` we can
guarantee a prime**:

* **Bertrand** (`Nat.exists_prime_lt_and_le_two_mul`, in mathlib): a prime in `(N/4, N/2]` ⟹ constant
  `3/4` (`maxNoThreeInLine_ge_three_quarters`).
* **Nagura 1952** (`nagura_prime` below): a prime in `(n, 6n/5]` for `n ≥ 25` ⟹ constant `5/4`
  (`maxNoThreeInLine_ge_five_fourths`).
* **PNT-strength gaps** (prime in `((1−ε)N/2, N/2]`): the full `3/2 − o(1)`, matching `hjsw_lower_bound`
  at the natural sizes `N = 2p` for *all* large `N`.

`nagura_prime` is the **active frontier crux** of this thread: it is *proven mathematics* (Nagura
1952), so it is honest 🟡 debt, not an open conjecture — but mathlib lacks the prerequisite (a
Chebyshev **lower** bound `c·x ≤ θ x`; it has only the upper bound `theta_le_log4_mul_x` and the
primorial bound `primorial_le_four_pow`). It is left as a disclosed `sorry` and is the cross-lap
target; the payoff `maxNoThreeInLine_ge_five_fourths` is wired and ready. See `PENDING_WORK.md` for the
central-binomial attack plan. The repo's **headline** theorems (`hjsw_lower_bound`,
`maxNoThreeInLine_bounds`, …) do not depend on this file and remain axiom-clean.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Statement
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace LeanFormalizations.NoThreeInLine

/-! ### Towards the missing prerequisite: a Chebyshev lower bound

Nagura's product argument needs a *lower* bound on `∏_{p ≤ m} p` (Chebyshev `θ`), which mathlib
lacks. The ℕ-level foundation is `lcm(1,…,2n) ≥ 4ⁿ / n` (`four_pow_lt_mul_lcm`): the central binomial
divides `lcm(1,…,2n)` (every prime power dividing `C(2n,n)` is `≤ 2n`), and `4ⁿ < n·C(2n,n)`. This is
the ℕ analogue of `ψ(2n) ≥ n·log 4 − log n`; combined with `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
it would yield the `θ` lower bound feeding Nagura. These bricks are axiom-clean.

The remaining (well-scoped) bridge to a real `ψ` lower bound is the single identity
`Real.log ((Icc 1 N).lcm id) = Chebyshev.ψ N`: apply
`ArithmeticFunction.vonMangoldt_sum` (`∑_{d ∣ m} Λ d = log m`) at `m = lcm(1..N)`, then match the
nonzero (prime-power) terms — a prime power `q` divides `lcm(1..N)` iff `q ≤ N` (via the Finset-lcm
`p`-adic valuation), so the divisor-sum and the `n ≤ N` sum carry the same `Λ` terms. -/

open Finset in
/-- **The central binomial divides `lcm(1,…,2n)`.** Every prime power `pᵏ ∥ C(2n,n)` satisfies
`pᵏ ≤ 2n` (`Nat.pow_factorization_choose_le`), so `pᵏ ∈ [1,2n]` and divides the lcm; as `C(2n,n)` is
the product of these prime powers it divides the lcm too. -/
theorem centralBinom_dvd_lcm_Icc {n : ℕ} (hn : 0 < n) :
    Nat.centralBinom n ∣ (Finset.Icc 1 (2 * n)).lcm id := by
  have h2n : 0 < 2 * n := by omega
  have hC : Nat.centralBinom n ≠ 0 := (Nat.centralBinom_pos n).ne'
  have hL : (Finset.Icc 1 (2 * n)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨a, ha, ha0⟩
    rw [Finset.mem_Icc] at ha
    simp only [id_eq] at ha0; omega
  rw [← Nat.factorization_le_iff_dvd hC hL, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · set k := (Nat.centralBinom n).factorization p with hk
    have hple : p ^ k ≤ 2 * n := by
      have := Nat.pow_factorization_choose_le (n := 2 * n) (k := n) (p := p) h2n
      rwa [← Nat.centralBinom, ← hk] at this
    have hmem : p ^ k ∈ Finset.Icc 1 (2 * n) :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, hple⟩
    have hdvd : p ^ k ∣ (Finset.Icc 1 (2 * n)).lcm id := by
      simpa using Finset.dvd_lcm (f := id) hmem
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hL).mp hdvd
  · rw [Nat.factorization_eq_zero_of_non_prime _ hp]; exact Nat.zero_le _

/-- **ℕ Chebyshev lower bound.** `4ⁿ < n · lcm(1,…,2n)` for `n ≥ 4` — the integer form of
`ψ(2n) ≳ n·log 4`, and the foundation for a `θ` lower bound (the ingredient Nagura needs that mathlib
is missing). Proof: `4ⁿ < n·C(2n,n)` (`Nat.four_pow_lt_mul_centralBinom`) and `C(2n,n) ≤ lcm(1,…,2n)`
(`centralBinom_dvd_lcm_Icc`). -/
theorem four_pow_lt_mul_lcm {n : ℕ} (hn : 4 ≤ n) :
    4 ^ n < n * (Finset.Icc 1 (2 * n)).lcm id := by
  have hdvd := centralBinom_dvd_lcm_Icc (n := n) (by omega)
  have hL0 : 0 < (Finset.Icc 1 (2 * n)).lcm id :=
    Nat.pos_of_ne_zero (by
      rw [Ne, Finset.lcm_eq_zero_iff]; rintro ⟨a, ha, ha0⟩
      rw [Finset.mem_Icc] at ha; simp only [id_eq] at ha0; omega)
  calc 4 ^ n < n * Nat.centralBinom n := Nat.four_pow_lt_mul_centralBinom n hn
    _ ≤ n * (Finset.Icc 1 (2 * n)).lcm id :=
        Nat.mul_le_mul_left n (Nat.le_of_dvd hL0 hdvd)

/-- The `p`-adic valuation of a `Finset.lcm` of nonzero naturals is the `sup` of the valuations.
(Reusable; mathlib has `Nat.factorization_lcm` only for pairs.) -/
theorem factorization_finset_lcm {p : ℕ} {s : Finset ℕ} (hs : ∀ m ∈ s, m ≠ 0) :
    ((s.lcm id).factorization p) = s.sup (fun m => m.factorization p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ m ∈ s, m ≠ 0 := fun m hm => hs m (Finset.mem_insert_of_mem hm)
    have hlcm0 : s.lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; rintro ⟨b, hb, hb0⟩; exact hs' b hb (by simpa using hb0)
    rw [Finset.lcm_insert, Finset.sup_insert, ← ih hs']
    have := Nat.factorization_lcm (a := a) (b := s.lcm id) ha0 hlcm0
    simp only [id_eq]
    rw [show GCDMonoid.lcm a (s.lcm id) = Nat.lcm a (s.lcm id) from rfl, this,
      Finsupp.sup_apply]

/-- For a prime power `pᵏ` (`k≥1`): `pᵏ ∣ lcm(1,…,N) ⟺ pᵏ ≤ N`. The crux of the
`log(lcm(1..N)) = ψ N` bridge: the prime-power divisors of `lcm(1..N)` are exactly the prime powers
`≤ N`. -/
theorem primePow_dvd_lcm_Icc_iff {p k N : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p ^ k ∣ (Finset.Icc 1 N).lcm id ↔ p ^ k ≤ N := by
  have hge1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have hL0 : (Finset.Icc 1 N).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; rintro ⟨b, hb, hb0⟩
    rw [Finset.mem_Icc] at hb; simp only [id_eq] at hb0; omega
  constructor
  · intro hdvd
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hL0,
      factorization_finset_lcm (fun m hm => by rw [Finset.mem_Icc] at hm; omega)] at hdvd
    have hne : (Finset.Icc 1 N).Nonempty := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exfalso; rw [hN] at hdvd; simp at hdvd; omega
      · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
    obtain ⟨m, hm, hmsup⟩ := Finset.exists_mem_eq_sup _ hne (fun m => m.factorization p)
    rw [hmsup] at hdvd
    rw [Finset.mem_Icc] at hm
    have hmdvd : p ^ k ∣ m := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mpr hdvd
    exact le_trans (Nat.le_of_dvd (by omega) hmdvd) hm.2
  · intro hle
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hge1, hle⟩)

open scoped ArithmeticFunction in
/-- **The von Mangoldt ↔ lcm bridge.** `log(lcm(1,…,N)) = ψ N` (Chebyshev's `ψ`). Both sides sum
`log p` over prime powers `pᵏ ≤ N`: the LHS via `vonMangoldt_sum` over the divisors of `lcm(1..N)`,
whose prime-power divisors are exactly the prime powers `≤ N` (`primePow_dvd_lcm_Icc_iff`). This is the
final link turning the ℕ bound `four_pow_lt_mul_lcm` into a real Chebyshev `ψ` lower bound. -/
theorem log_lcm_Icc_eq_psi (N : ℕ) :
    Real.log (((Finset.Icc 1 N).lcm id : ℕ) : ℝ) = Chebyshev.psi N := by
  classical
  have hL0 : (Finset.Icc 1 N).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; rintro ⟨b, hb, hb0⟩
    rw [Finset.mem_Icc] at hb; simp only [id_eq] at hb0; omega
  rw [← ArithmeticFunction.vonMangoldt_sum, Chebyshev.psi, Nat.floor_natCast]
  have key : ((Finset.Icc 1 N).lcm id).divisors.filter (fun d => IsPrimePow d)
      = (Finset.Ioc 0 N).filter (fun d => IsPrimePow d) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hqL, _⟩, hpp⟩
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp
      exact ⟨⟨pow_pos (Nat.prime_iff.mpr hp).pos k,
        (primePow_dvd_lcm_Icc_iff (Nat.prime_iff.mpr hp) hk).mp hqL⟩, ⟨p, k, hp, hk, rfl⟩⟩
    · rintro ⟨⟨_, hqN⟩, hpp⟩
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp
      exact ⟨⟨(primePow_dvd_lcm_Icc_iff (Nat.prime_iff.mpr hp) hk).mpr hqN, hL0⟩,
        ⟨p, k, hp, hk, rfl⟩⟩
  have hLsum : ∑ d ∈ ((Finset.Icc 1 N).lcm id).divisors, Λ d
      = ∑ d ∈ ((Finset.Icc 1 N).lcm id).divisors.filter (fun d => IsPrimePow d), Λ d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxnf
    rw [Finset.mem_filter, not_and] at hxnf
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg (hxnf hx)]
  have hNsum : ∑ n ∈ Finset.Ioc 0 N, Λ n
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun d => IsPrimePow d), Λ n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxnf
    rw [Finset.mem_filter, not_and] at hxnf
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg (hxnf hx)]
  rw [hLsum, hNsum, key]

/-- **Chebyshev `ψ` lower bound.** `n·log 4 − log n < ψ(2n)` for `n ≥ 4` — a genuine lower bound on
the Chebyshev function (mathlib has only upper bounds), via `four_pow_lt_mul_lcm` and the
`log_lcm_Icc_eq_psi` bridge. The ingredient Nagura needs that mathlib is missing. -/
theorem psi_lower {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n < Chebyshev.psi (2 * n) := by
  have h := four_pow_lt_mul_lcm (n := n) hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hlcm0 : (0 : ℝ) < ((Finset.Icc 1 (2 * n)).lcm id : ℕ) := by
    have hne : (Finset.Icc 1 (2 * n)).lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; rintro ⟨b, hb, hb0⟩
      rw [Finset.mem_Icc] at hb; simp only [id_eq] at hb0; omega
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hcast : (4 : ℝ) ^ n < (n : ℝ) * ((Finset.Icc 1 (2 * n)).lcm id : ℕ) := by exact_mod_cast h
  have hlog : Real.log ((4 : ℝ) ^ n) < Real.log ((n : ℝ) * ((Finset.Icc 1 (2 * n)).lcm id : ℕ)) :=
    Real.log_lt_log (by positivity) hcast
  rw [Real.log_pow, Real.log_mul hn0.ne' hlcm0.ne', log_lcm_Icc_eq_psi (2 * n)] at hlog
  push_cast at hlog ⊢
  linarith [hlog]

/-- **Nagura's theorem (1952).** For every `n ≥ 25` there is a prime `p` in the interval `(n, 6n/5]`
(i.e. `n < p` and `5p ≤ 6n`). This sharpens Bertrand's postulate (`p ≤ 2n`) to ratio `6/5`.

**Status: disclosed `sorry` — the active frontier crux of the HJSW general-`N` thread.** This is a
*theorem* (proven by Nagura in 1952), not a conjecture; it is 🟡 debt, formalizable but gated on
infrastructure mathlib does not yet provide.

**Attack plan** (mirrors mathlib's `Nat.exists_prime_lt_and_le_two_mul`, sharpened):
* Lower bound on the central binomial: `4^n ≤ n · C(2n,n)` (`Nat.four_pow_lt_mul_centralBinom`).
* If there were **no** prime in `(n, 6n/5]`, the primes `> n` dividing `C(2n,n)` lie in `(6n/5, 2n]`,
  so by `centralBinom_factorization_small`-style bounds plus `primorial_le_four_pow` the coefficient is
  bounded above by `(2n)^√(2n) · 4^(6n/5) · (contribution of (6n/5,2n])`.
* The missing ingredient vs. Bertrand: one must *lower-bound* the prime mass in `(6n/5, 2n]` — i.e. a
  Chebyshev lower bound `θ(x) ≥ c·x` (equivalently `ψ(x) ≥ log C(2n,n) ≥ n·log 4 − log n` via
  `C(2n,n) ≤ ∏_{p^k ≤ 2n} p = exp(ψ(2n))`). mathlib has the upper Chebyshev bound only.
* Small `n ∈ [25, N₀)` are discharged by an explicit descending prime list (as in Bertrand's small
  cases). Submitted to Aristotle as a self-contained job. -/
theorem nagura_prime {n : ℕ} (hn : 25 ≤ n) : ∃ p, p.Prime ∧ n < p ∧ 5 * p ≤ 6 * n := by
  sorry

/-- **HJSW general-`N` lower bound at constant `5/4`** (conditional on `nagura_prime`). For `N ≥ 60`,
applying Nagura at `n = ⌊5N/12⌋` yields a prime `p ∈ (⌊5N/12⌋, N/2]`, whose sheared construction gives
`3(p−1) ≥ 3⌊5N/12⌋ ≈ 5N/4` points. This is the `5/4` rung between Bertrand's `3/4`
(`maxNoThreeInLine_ge_three_quarters`) and the conjectural `3/2 − o(1)`.

The conclusion is stated in the exact floor form `3·⌊5N/12⌋` (asymptotically `5N/4`), paralleling the
`3·⌊N/4⌋ = 3·⌊3N/12⌋` form of the Bertrand bound: the improvement `3/12 → 5/12` of the inner
coefficient is the constant `3/4 → 5/4`. -/
theorem maxNoThreeInLine_ge_five_fourths {N : ℕ} (hN : 60 ≤ N) :
    3 * (5 * N / 12) ≤ maxNoThreeInLine N := by
  obtain ⟨p, hp, hlo, hhi⟩ := nagura_prime (n := 5 * N / 12) (by omega)
  have h2p : 2 * p ≤ N := by omega
  have := maxNoThreeInLine_ge_of_two_mul_prime_le hp h2p
  omega

end LeanFormalizations.NoThreeInLine
