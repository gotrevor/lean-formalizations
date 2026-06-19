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
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Real.Pi.Bounds

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

/-- **Chebyshev `θ` lower bound.** `n·log 4 − log n − 2√(2n)·log(2n) < θ(2n)` for `n ≥ 4` — combine
`psi_lower` with mathlib's `abs_psi_sub_theta_le_sqrt_mul_log` (`|ψ−θ| ≤ 2√x·log x`). The main term is
`n·log 4 ≈ 1.386 n` with a lower-order `√` correction, so `θ(2n) ≳ (log 4)·n`: the genuine `θ` lower
bound that Nagura's product argument needs and that mathlib was missing. -/
theorem theta_lower {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n - 2 * Real.sqrt (2 * n) * Real.log (2 * n)
      < Chebyshev.theta (2 * n) := by
  have hpsi := psi_lower hn
  have h1 : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
  have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log h1
  rw [abs_le] at habs
  push_cast at hpsi habs ⊢
  linarith [habs.2]

/-! ### Chebyshev's `T`-function: the keystone of the *refined* lower bound

The elementary central-binomial lower bound (`psi_lower`/`theta_lower`) caps at constant `log 4 / 2 ≈
0.69` — provably too weak for any prime-gap ratio `< 2` (a careful central-binomial split needs the
*upper* constant pushed below `log 4` AND the *lower* constant above `log 4 / 2`; the crude pair gives
exactly Bertrand). Chebyshev's sharper bounds (`ψ(x) ≳ 0.92 x`, `θ(x) ≲ 1.11 x`) come from the
summatory function `T(n) = ∑_{d ≤ n} Λ(d)⌊n/d⌋ = log(n!)` and its linear combination at shifts
`1, 1/2, 1/3, 1/5, 1/30`. The identity below is that keystone — mathlib has neither it nor any refined
Chebyshev bound. From it the `2,3,5,30` combination yields a lower constant `≈ 0.92`, enough (via the
central-binomial split) for a prime in `(n, c·n]` with `c < 2`, hence a general-`N` no-three-in-line
constant strictly above Bertrand's `3/4`. -/

open scoped ArithmeticFunction in
open Finset in
/-- **Chebyshev's summatory identity** `∑_{d=1}^{n} Λ(d)·⌊n/d⌋ = log(n!)`. Double-counting:
`⌊n/d⌋` is the number of multiples of `d` in `[1,n]`, so `∑_d Λ(d)·#{k≤n : d∣k}` reindexes to
`∑_{k≤n} ∑_{d∣k} Λ(d) = ∑_{k≤n} log k = log(n!)` (`vonMangoldt_sum` + `log_prod`). The keystone of the
refined Chebyshev bounds; absent from mathlib. -/
theorem sum_vonMangoldt_mul_floor_div (n : ℕ) :
    ∑ d ∈ Finset.Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ) = Real.log (Nat.factorial n : ℝ) := by
  classical
  have hIoc : Finset.Ioc 0 n = Finset.Ico 1 (n + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  -- `log(n!) = ∑_{k ∈ (0,n]} log k`
  have hfact : (Nat.factorial n : ℝ) = ∏ k ∈ Finset.Ioc 0 n, (k : ℝ) := by
    rw [hIoc, ← Nat.cast_prod]; exact_mod_cast (Finset.prod_Ico_id_eq_factorial n).symm
  have hlogfact : Real.log (Nat.factorial n : ℝ) = ∑ k ∈ Finset.Ioc 0 n, Real.log (k : ℝ) := by
    rw [hfact, Real.log_prod]
    intro k hk; rw [Finset.mem_Ioc] at hk
    exact_mod_cast hk.1.ne'
  rw [hlogfact]
  -- each `log k = ∑_{d ∣ k} Λ d`, and `divisors k = {d ∈ (0,n] : d ∣ k}` for `k ∈ (0,n]`
  have hlog : ∀ k ∈ Finset.Ioc 0 n,
      Real.log (k : ℝ) = ∑ d ∈ (Finset.Ioc 0 n).filter (· ∣ k), Λ d := by
    intro k hk; rw [Finset.mem_Ioc] at hk
    rw [← ArithmeticFunction.vonMangoldt_sum (n := k)]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hdk, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdk hk.1, (Nat.le_of_dvd hk.1 hdk).trans hk.2⟩, hdk⟩
    · rintro ⟨_, hdk⟩; exact ⟨hdk, hk.1.ne'⟩
  rw [Finset.sum_congr rfl hlog]
  -- swap the order of summation
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  -- inner sum is constant `Λ d` over the `(n/d)` multiples of `d`
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

/-- **Chebyshev's floor combination is `0` or `1`.** For every `n`,
`⌊n⌋ − ⌊n/2⌋ − ⌊n/3⌋ − ⌊n/5⌋ + ⌊n/30⌋ ∈ {0,1}` (stated additively to dodge ℕ truncated subtraction).
Writing `n = 30q + r`, the `q`-coefficient `30 − 15 − 10 − 6 + 1 = 0` cancels, so the combination
depends only on `r = n mod 30` and is checked by `decide` over the 30 residues. This is the
sign-control that turns `T(n) = log(n!)` (`sum_vonMangoldt_mul_floor_div`) into the refined Chebyshev
`ψ` bound: `f(n) := T(n) − T(⌊n/2⌋) − T(⌊n/3⌋) − T(⌊n/5⌋) + T(⌊n/30⌋) = ∑_d Λ(d)·g(n/d)` with
`g ∈ {0,1}`, giving `ψ(n) − ψ(n/6) ≤ f(n) ≤ ψ(n)` and hence the lower constant `≈ 0.92`. -/
theorem floor_comb_bounds (n : ℕ) :
    n / 2 + n / 3 + n / 5 ≤ n + n / 30 ∧ n + n / 30 ≤ n / 2 + n / 3 + n / 5 + 1 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 30 ∧ n = 30 * q + r :=
    ⟨n / 30, n % 30, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 30).symm⟩
  have e2 : (30 * q + r) / 2 = 15 * q + r / 2 := by
    rw [show 30 * q + r = r % 2 + (15 * q + r / 2) * 2 by omega]; rw [Nat.add_mul_div_right _ _ (by norm_num)]
    omega
  have e3 : (30 * q + r) / 3 = 10 * q + r / 3 := by
    rw [show 30 * q + r = r % 3 + (10 * q + r / 3) * 3 by omega]; rw [Nat.add_mul_div_right _ _ (by norm_num)]
    omega
  have e5 : (30 * q + r) / 5 = 6 * q + r / 5 := by
    rw [show 30 * q + r = r % 5 + (6 * q + r / 5) * 5 by omega]; rw [Nat.add_mul_div_right _ _ (by norm_num)]
    omega
  have e30 : (30 * q + r) / 30 = q + r / 30 := by
    rw [show 30 * q + r = r % 30 + (q + r / 30) * 30 by omega]; rw [Nat.add_mul_div_right _ _ (by norm_num)]
    omega
  rw [e2, e3, e5, e30]
  have hres : r / 2 + r / 3 + r / 5 ≤ r + r / 30 ∧ r + r / 30 ≤ r / 2 + r / 3 + r / 5 + 1 := by
    interval_cases r <;> decide
  omega

open scoped ArithmeticFunction in
/-- `log(⌊n/k⌋!) = ∑_{d ≤ n} Λ(d)·⌊n/(k·d)⌋` for `k ≥ 1` — the keystone
(`sum_vonMangoldt_mul_floor_div`) at `⌊n/k⌋`, re-indexed over the common range `(0,n]` (the extra
terms `d > n/k` vanish since `⌊n/(k·d)⌋ = ⌊⌊n/k⌋/d⌋ = 0`). Lets the five shifts of Chebyshev's `T`
share one index set. -/
theorem logFactorial_div_eq_sum (n k : ℕ) (hk : 0 < k) :
    Real.log (Nat.factorial (n / k)) = ∑ d ∈ Finset.Ioc 0 n, Λ d * ((n / (k * d) : ℕ) : ℝ) := by
  rw [← sum_vonMangoldt_mul_floor_div (n / k)]
  rw [Finset.sum_congr rfl (fun d _ => by rw [Nat.div_div_eq_div_mul] :
    ∀ d ∈ Finset.Ioc 0 (n / k), Λ d * (((n / k) / d : ℕ) : ℝ) = Λ d * ((n / (k * d) : ℕ) : ℝ))]
  refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right (Nat.div_le_self n k)) (fun d hd hd' => ?_)
  rw [Finset.mem_Ioc] at hd
  simp only [Finset.mem_Ioc, not_and, not_le] at hd'
  have : n / (k * d) = 0 := by
    rw [← Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt (hd' hd.1)
  rw [this]; simp

open scoped ArithmeticFunction in
open Finset in
/-- **Chebyshev's `T`-combination is `∑ Λ(d)·g(n/d)`** with `g ∈ {0,1}`. The five log-factorials
combine (over the common range `(0,n]`, via `logFactorial_div_eq_sum`) into a single `Λ`-weighted sum
whose `d`-th coefficient is the floor combination `g(n/d) = ⌊n/d⌋−⌊n/2d⌋−⌊n/3d⌋−⌊n/5d⌋+⌊n/30d⌋`
(using `⌊n/(k d)⌋ = ⌊(n/d)/k⌋`). -/
theorem logFactorial_comb_eq (n : ℕ) :
    Real.log (Nat.factorial n) - Real.log (Nat.factorial (n / 2)) - Real.log (Nat.factorial (n / 3))
        - Real.log (Nat.factorial (n / 5)) + Real.log (Nat.factorial (n / 30))
      = ∑ d ∈ Ioc 0 n, Λ d * (((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ) - ((n / (3 * d) : ℕ) : ℝ)
          - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ)) := by
  have h1 : Real.log (Nat.factorial n) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ) :=
    (sum_vonMangoldt_mul_floor_div n).symm
  rw [h1, logFactorial_div_eq_sum n 2 (by norm_num), logFactorial_div_eq_sum n 3 (by norm_num),
    logFactorial_div_eq_sum n 5 (by norm_num), logFactorial_div_eq_sum n 30 (by norm_num),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => by ring)

open scoped ArithmeticFunction in
open Finset in
/-- **Refined Chebyshev `ψ` lower bound (combinatorial half).** The `T`-combination is `≤ ψ(n)`:
each coefficient `g(n/d) ∈ {0,1}` (`floor_comb_bounds`) and `Λ ≥ 0`, so the `Λ`-weighted sum is at
most `∑_{d ≤ n} Λ(d) = ψ(n)`. Combined with the Stirling lower bound on the left-hand combination of
`log(⌊n/k⌋!)` (`≈ 0.9213·n`), this yields `ψ(n) ≳ 0.92 n` — strictly beating the elementary
`log 4 / 2 ≈ 0.69` and the route to a prime gap of ratio `< 2`. -/
theorem logFactorial_comb_le_psi (n : ℕ) :
    Real.log (Nat.factorial n) - Real.log (Nat.factorial (n / 2)) - Real.log (Nat.factorial (n / 3))
        - Real.log (Nat.factorial (n / 5)) + Real.log (Nat.factorial (n / 30))
      ≤ Chebyshev.psi n := by
  rw [logFactorial_comb_eq, Chebyshev.psi, Nat.floor_natCast]
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  have hbr : ((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ) - ((n / (3 * d) : ℕ) : ℝ)
      - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ) ≤ 1 := by
    have hb := floor_comb_bounds (n / d)
    have e2 : n / d / 2 = n / (2 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e3 : n / d / 3 = n / (3 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e5 : n / d / 5 = n / (5 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e30 : n / d / 30 = n / (30 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [e2, e3, e5, e30] at hb
    have := hb.2
    push_cast
    rw [← Nat.cast_le (α := ℝ)] at this
    push_cast at this
    linarith
  calc Λ d * _ ≤ Λ d * 1 := by exact mul_le_mul_of_nonneg_left hbr hΛ
    _ = Λ d := mul_one _

/-- **Chebyshev's floor combination is `≥ 1` on `[1,5]`.** For `1 ≤ m < 6`,
`⌊m/2⌋+⌊m/3⌋+⌊m/5⌋+1 ≤ m+⌊m/30⌋` (additive form of `g(m) ≥ 1`). Checked by `decide` over `m ∈ {1,…,5}`
(`⌊m/30⌋ = 0` there, so `g(m) = m − ⌊m/2⌋ − ⌊m/3⌋ − ⌊m/5⌋ = 1`). This is the sign-control for the
*lower* combinatorial bound `ψ(n) − ψ(⌊n/6⌋) ≤ f(n)`: for `⌊n/6⌋ < d ≤ n` one has `⌊n/d⌋ ∈ [1,5]`,
so the `d`-th coefficient of `f(n)` is `≥ 1`. -/
theorem floor_comb_ge_one (m : ℕ) (h1 : 1 ≤ m) (h6 : m < 6) :
    m / 2 + m / 3 + m / 5 + 1 ≤ m + m / 30 := by
  interval_cases m <;> decide

open scoped ArithmeticFunction in
open Finset in
/-- **Refined Chebyshev `ψ` *upper* step (combinatorial half).** `ψ(n) − ψ(⌊n/6⌋) ≤ f(n)`. The
`T`-combination `f(n) = ∑_d Λ(d)·g(⌊n/d⌋)` has all coefficients `g ≥ 0` (`floor_comb_bounds`), and for
`⌊n/6⌋ < d ≤ n` (where `⌊n/d⌋ ∈ [1,5]`) the coefficient is `≥ 1` (`floor_comb_ge_one`). Dropping the
nonnegative terms outside `(⌊n/6⌋, n]` and bounding the rest below by `Λ(d)·1` gives
`∑_{⌊n/6⌋ < d ≤ n} Λ(d) = ψ(n) − ψ(⌊n/6⌋) ≤ f(n)`. Combined with the analytic upper bound
`logFactorial_comb_upper` (`f(n) ≤ A·n + O(log n)`) this is the dual *upper* recurrence whose iterate
gives `ψ(n) ≲ (6/5)A·n`. -/
theorem logFactorial_comb_ge_psi_sub {n : ℕ} :
    Chebyshev.psi (n : ℝ) - Chebyshev.psi ((n / 6 : ℕ) : ℝ)
      ≤ Real.log (Nat.factorial n) - Real.log (Nat.factorial (n / 2))
          - Real.log (Nat.factorial (n / 3)) - Real.log (Nat.factorial (n / 5))
          + Real.log (Nat.factorial (n / 30)) := by
  rw [logFactorial_comb_eq]
  set m := n / 6 with hmdef
  have hmn : m ≤ n := by rw [hmdef]; omega
  have hψ : Chebyshev.psi (n : ℝ) - Chebyshev.psi ((m : ℕ) : ℝ)
      = ∑ d ∈ Finset.Ioc m n, Λ d := by
    rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast]
    have hunion : Finset.Ioc 0 n = Finset.Ioc 0 m ∪ Finset.Ioc m n :=
      (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) hmn).symm
    rw [hunion, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl m))]
    ring
  rw [hψ]
  have hstepA : ∑ d ∈ Finset.Ioc m n, Λ d
      ≤ ∑ d ∈ Finset.Ioc m n, Λ d * (((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ)
          - ((n / (3 * d) : ℕ) : ℝ) - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rw [Finset.mem_Ioc] at hd
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hd0 : 0 < d := by omega
    have hge1 : 1 ≤ n / d := Nat.one_le_div_iff hd0 |>.mpr hd.2
    have hle5 : n / d < 6 := by
      rw [Nat.div_lt_iff_lt_mul hd0]
      have : n < 6 * (m + 1) := by rw [hmdef]; omega
      omega
    have hcoef : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ) - ((n / (3 * d) : ℕ) : ℝ)
        - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ) := by
      have hb := floor_comb_ge_one (n / d) hge1 hle5
      have e2 : n / d / 2 = n / (2 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
      have e3 : n / d / 3 = n / (3 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
      have e5 : n / d / 5 = n / (5 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
      have e30 : n / d / 30 = n / (30 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
      rw [e2, e3, e5, e30] at hb
      rw [← Nat.cast_le (α := ℝ)] at hb
      push_cast at hb
      linarith
    calc Λ d = Λ d * 1 := (mul_one _).symm
      _ ≤ Λ d * _ := mul_le_mul_of_nonneg_left hcoef hΛ
  have hstepB : ∑ d ∈ Finset.Ioc m n, Λ d * (((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ)
          - ((n / (3 * d) : ℕ) : ℝ) - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ))
      ≤ ∑ d ∈ Finset.Ioc 0 n, Λ d * (((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ)
          - ((n / (3 * d) : ℕ) : ℝ) - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (by omega)) ?_
    intro d _ _
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hc0 := floor_comb_bounds (n / d)
    have e2 : n / d / 2 = n / (2 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e3 : n / d / 3 = n / (3 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e5 : n / d / 5 = n / (5 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have e30 : n / d / 30 = n / (30 * d) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [e2, e3, e5, e30] at hc0
    have hcoef : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) - ((n / (2 * d) : ℕ) : ℝ) - ((n / (3 * d) : ℕ) : ℝ)
        - ((n / (5 * d) : ℕ) : ℝ) + ((n / (30 * d) : ℕ) : ℝ) := by
      have := hc0.1
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast at this
      linarith
    exact mul_nonneg hΛ hcoef
  linarith [hstepA, hstepB]

/-- **Explicit Stirling *upper* bound on `log(m!)`** for `m ≥ 1`:
`log(m!) ≤ m·log m − m + log(2m)/2 + 1 − log 2 / 2`. mathlib has only the matching *lower* bound
(`Stirling.le_log_factorial_stirling`); this is the missing companion, derived from
`log_stirlingSeq_formula` and the fact that `log ∘ stirlingSeq` is antitone with maximum
`log(stirlingSeq 1) = 1 − log 2 / 2`. Needed (with the lower bound) to pin the leading constant of
Chebyshev's `T`-combination. -/
theorem log_factorial_le {m : ℕ} (hm : m ≠ 0) :
    Real.log (Nat.factorial m) ≤ m * Real.log m - m + Real.log (2 * m) / 2 + 1 - Real.log 2 / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hform := Stirling.log_stirlingSeq_formula (j + 1)
  have hanti : Real.log (Stirling.stirlingSeq (j + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
    Stirling.log_stirlingSeq'_antitone (Nat.zero_le j)
  have hs1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by norm_num)]
  have hpos : (0 : ℝ) < (↑(j + 1) : ℝ) := by positivity
  have hlogdiv : (↑(j + 1) : ℝ) * Real.log ((↑(j + 1) : ℝ) / Real.exp 1)
      = (↑(j + 1) : ℝ) * Real.log (↑(j + 1) : ℝ) - (↑(j + 1) : ℝ) := by
    rw [Real.log_div hpos.ne' (Real.exp_pos 1).ne', Real.log_exp]; ring
  rw [hs1] at hanti
  rw [hlogdiv] at hform
  linarith [hform, hanti]

/-- `log 3 > 1.09`, via the `log(1−x)` Taylor remainder (`abs_log_sub_add_sum_range_le`) at `x = 1/3`
(so `log(2/3) = log 2 − log 3`) plus `Real.log_two_gt_d9`. mathlib pins only `log 2` numerically. -/
theorem log_three_gt : (1.09 : ℝ) < Real.log 3 := by
  have hx : |(1 / 3 : ℝ)| < 1 := by rw [abs_of_pos] <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  have hl2 := Real.log_two_gt_d9
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.1, h.2, hl2]

/-- `log 5 > 1.6`, via the same series at `x = 1/5` (`log(4/5) = log 4 − log 5 = 2 log 2 − log 5`). -/
theorem log_five_gt : (1.6 : ℝ) < Real.log 5 := by
  have hx : |(1 / 5 : ℝ)| < 1 := by rw [abs_of_pos] <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  have hl2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num), hlog4,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.1, h.2, hl2]

/-- **Chebyshev's constant `A > 0.91`.** `A := (7/15)·log2 + (3/10)·log3 + (1/6)·log5 ≈ 0.9213` is the
leading coefficient of the `2,3,5,30` `T`-combination (`A = ½log2+⅓log3+⅕log5−1/30·log30`, simplified
using `log30 = log2+log3+log5`). The bound `A > 0.91` (from `log_three_gt`, `log_five_gt`,
`log_two_gt_d9`) is what makes the refined Chebyshev lower bound `ψ(n) ≳ 0.91 n` strictly beat the
elementary `log4/2 ≈ 0.69`. -/
theorem chebyshev_const_gt :
    (0.91 : ℝ) < (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5 := by
  have h2 := Real.log_two_gt_d9
  have h3 := log_three_gt
  have h5 := log_five_gt
  linarith [h2, h3, h5]

/-- **Leading-term identity for Chebyshev's `T`-combination.** The continuous (un-floored) main terms
of `T(x) − T(x/2) − T(x/3) − T(x/5) + T(x/30)` collapse to exactly `A·x`: the `x·log x` terms cancel
(coeffs `1−½−⅓−⅕+1/30 = 0`) and `∑±(x/k)log k = A·x` with `A = (7/15)log2+(3/10)log3+(1/6)log5`
(`chebyshev_const_gt`). This is the algebraic core of the analytic half of `ψ(n) ≳ A·n`; what remains
is bounding the floor/Stirling corrections (each `O(log n)`) around it. -/
theorem logFactorial_leading_identity {x : ℝ} (hx : 0 < x) :
    x * Real.log x - (x / 2) * Real.log (x / 2) - (x / 3) * Real.log (x / 3)
        - (x / 5) * Real.log (x / 5) + (x / 30) * Real.log (x / 30)
      = x * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5) := by
  rw [Real.log_div hx.ne' (by norm_num), Real.log_div hx.ne' (by norm_num),
    Real.log_div hx.ne' (by norm_num), Real.log_div hx.ne' (by norm_num)]
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [h30]; ring

/-- `t ↦ t·log t` is monotone on `[1,∞)`: `m·log m ≤ x·log x` for `1 ≤ m ≤ x`. The bridge from the
*floored* terms `⌊n/k⌋·log⌊n/k⌋` (what the Stirling bounds produce) to the *continuous*
`(n/k)·log(n/k)` (what `logFactorial_leading_identity` cancels) in the analytic-half assembly. -/
theorem mul_log_le_mul_log {m x : ℝ} (h1 : 1 ≤ m) (hmx : m ≤ x) :
    m * Real.log m ≤ x * Real.log x := by
  have h := Real.log_mul_self_monotoneOn (Set.mem_setOf_eq ▸ h1)
    (Set.mem_setOf_eq ▸ le_trans h1 hmx) hmx
  simpa [mul_comm] using h

/-- **Per-term upper bound for the subtracted log-factorials** (continuous form). For `1 ≤ k ≤ n`,
`log(⌊n/k⌋!) ≤ (n/k)·log(n/k) − ⌊n/k⌋ + log(2n)/2 + 1 − log2/2`: `log_factorial_le` at `m=⌊n/k⌋`,
then the floored `m·log m` is raised to the continuous `(n/k)·log(n/k)` via `mul_log_le_mul_log`, and
`log(2⌊n/k⌋) ≤ log(2n)`. Used on the `k∈{2,3,5}` terms of `f(n)`. -/
theorem log_factorial_div_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.log (Nat.factorial (n / k))
      ≤ ((n : ℝ) / k) * Real.log ((n : ℝ) / k) - ((n / k : ℕ) : ℝ)
        + Real.log (2 * n) / 2 + 1 - Real.log 2 / 2 := by
  have hm1 : 1 ≤ n / k := (Nat.one_le_div_iff (by omega)).mpr hkn
  have hub := log_factorial_le (m := n / k) (by omega)
  have hmono : ((n / k : ℕ) : ℝ) * Real.log ((n / k : ℕ) : ℝ)
      ≤ ((n : ℝ) / k) * Real.log ((n : ℝ) / k) :=
    mul_log_le_mul_log (by exact_mod_cast hm1) Nat.cast_div_le
  have hlog2 : Real.log (2 * ((n / k : ℕ) : ℝ)) ≤ Real.log (2 * (n : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n k
    linarith
  linarith [hub, hmono, hlog2]

/-- **Secant bound for `t·log t`** (convexity): `b·log b − a·log a ≤ (b−a)(log b + 1)` for
`0 < a ≤ b`. Algebraic proof: `b log b − a log a = (b−a)log b + a·log(b/a)` and `a·log(b/a) ≤ b−a`
(from `log y ≤ y−1`). Bounds the `O(log n)` floor slop on the `+⌊n/30⌋` term (the hard *lower*
direction) in the `f(n)` lower bound. -/
theorem mul_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b * Real.log b - a * Real.log a ≤ (b - a) * (Real.log b + 1) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hlog : a * Real.log (b / a) ≤ b - a := by
    have h := Real.log_le_sub_one_of_pos (x := b / a) (by positivity)
    have hba : a * (b / a) = b := by field_simp
    nlinarith [h, ha.le]
  have hsplit : b * Real.log b - a * Real.log a
      = (b - a) * Real.log b + a * Real.log (b / a) := by
    rw [Real.log_div hb.ne' ha.ne']; ring
  have hexp : (b - a) * (Real.log b + 1) = (b - a) * Real.log b + (b - a) := by ring
  rw [hsplit, hexp]; linarith [hlog]

/-- **Per-term lower bound for the added log-factorial** (continuous form). For `1 ≤ k ≤ n`,
`(n/k)·log(n/k) − n/k − log(n/k) − 1 ≤ log(⌊n/k⌋!)`: Stirling's lower bound at `m=⌊n/k⌋` (drop the
nonnegative `log m/2 + log(2π)/2`), then lower the floored `⌊n/k⌋·log⌊n/k⌋` to the continuous
`(n/k)·log(n/k)` via the secant bound `mul_log_sub_le` (slop `≤ log(n/k)+1`). Used on the `+⌊n/30⌋`
term of `f(n)`. -/
theorem log_factorial_div_ge {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) / k) * Real.log ((n : ℝ) / k) - (n : ℝ) / k - Real.log ((n : ℝ) / k) - 1
      ≤ Real.log (Nat.factorial (n / k)) := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hm1 : 1 ≤ n / k := (Nat.one_le_div_iff (by omega)).mpr hkn
  have hca : (1 : ℝ) ≤ ((n / k : ℕ) : ℝ) := by exact_mod_cast hm1
  have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
  have h1le : (1 : ℝ) ≤ (n : ℝ) / k := (one_le_div hkpos).mpr (by exact_mod_cast hkn)
  have hlogpos : 0 ≤ Real.log ((n : ℝ) / k) := Real.log_nonneg h1le
  have hlb := Stirling.le_log_factorial_stirling (n := n / k) (by omega)
  have hloghalf : 0 ≤ Real.log ((n / k : ℕ) : ℝ) / 2 := by positivity
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have := Real.log_nonneg this; linarith
  have hsec := mul_log_sub_le (a := ((n / k : ℕ) : ℝ)) (b := (n : ℝ) / k) (by linarith) hle
  have hfrac : (n : ℝ) / k - ((n / k : ℕ) : ℝ) ≤ 1 := by
    have h1 : n < (n / k + 1) * k := by
      have e := Nat.div_add_mod n k
      have m := Nat.mod_lt n (show 0 < k by omega)
      nlinarith [e, m]
    have h2 : (n : ℝ) ≤ (((n / k : ℕ) : ℝ) + 1) * k := by exact_mod_cast h1.le
    have h3 : (n : ℝ) / k ≤ ((n / k : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hkpos]; linarith [h2]
    linarith [h3]
  have hprod : ((n : ℝ) / k - ((n / k : ℕ) : ℝ)) * (Real.log ((n : ℝ) / k) + 1)
      ≤ 1 * (Real.log ((n : ℝ) / k) + 1) :=
    mul_le_mul_of_nonneg_right hfrac (by linarith)
  linarith [hlb, hsec, hprod, hle, hloghalf, hlog2pi]

/-- **Lower bound on Chebyshev's `T`-combination `f(n) ≥ A·n − (O(log n) error)`.** Assembles the five
per-term Stirling bounds (`Stirling.le_log_factorial_stirling` at `n`; `log_factorial_div_le` for
`k=2,3,5`; `log_factorial_div_ge` for `k=30`) via the leading identity `logFactorial_leading_identity`
(which collapses the continuous `(n/k)·log(n/k)` combination to `A·n`) and the floor slop
(`−n+⌊n/2⌋+⌊n/3⌋+⌊n/5⌋−n/30 ≥ −3`, the linear-in-`n` part being `0`). The trailing `log`/constant terms
are a genuine `O(log n)` error. This is the analytic half of `ψ(n) ≳ A·n`. -/
theorem logFactorial_comb_lower {n : ℕ} (hn : 30 ≤ n) :
    (n : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5)
        + Real.log n / 2 + Real.log (2 * Real.pi) / 2 - 3 * Real.log (2 * n) / 2
        + 3 * Real.log 2 / 2 - Real.log ((n : ℝ) / 30) - 7
      ≤ Real.log (Nat.factorial n) - Real.log (Nat.factorial (n / 2))
          - Real.log (Nat.factorial (n / 3)) - Real.log (Nat.factorial (n / 5))
          + Real.log (Nat.factorial (n / 30)) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hS := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hU2 := log_factorial_div_le (n := n) (k := 2) (by norm_num) (by omega)
  have hU3 := log_factorial_div_le (n := n) (k := 3) (by norm_num) (by omega)
  have hU5 := log_factorial_div_le (n := n) (k := 5) (by norm_num) (by omega)
  have hL30 := log_factorial_div_ge (n := n) (k := 30) (by norm_num) (by omega)
  have hID := logFactorial_leading_identity (x := (n : ℝ)) hnpos
  -- floor slop: ⌊n/k⌋ ≥ n/k − 1
  have fge : ∀ k : ℕ, 1 ≤ k → (n : ℝ) / k - 1 ≤ ((n / k : ℕ) : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by positivity
    have h1 : n < (n / k + 1) * k := by
      have e := Nat.div_add_mod n k; have m := Nat.mod_lt n (show 0 < k by omega); nlinarith [e, m]
    have h2 : (n : ℝ) ≤ (((n / k : ℕ) : ℝ) + 1) * k := by exact_mod_cast h1.le
    have h3 : (n : ℝ) / k ≤ ((n / k : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hkpos]; linarith [h2]
    linarith [h3]
  have f2 := fge 2 (by norm_num)
  have f3 := fge 3 (by norm_num)
  have f5 := fge 5 (by norm_num)
  norm_num at hU2 hU3 hU5 hL30 hID f2 f3 f5 hS ⊢
  linarith [hS, hU2, hU3, hU5, hL30, hID, f2, f3, f5]

/-- **Upper bound on Chebyshev's `T`-combination `f(n) ≤ A·n + (O(log n) error)`.** The mirror of
`logFactorial_comb_lower`: upper-bound `log(n!)` and `log(⌊n/30⌋!)` by Stirling's *upper* bound
(`log_factorial_le`, `log_factorial_div_le`) and lower-bound the subtracted `log(⌊n/k⌋!)` (`k=2,3,5`)
by Stirling's *lower* bound (`log_factorial_div_ge`). The continuous `(n/k)·log(n/k)` combination again
collapses to `A·n` (`logFactorial_leading_identity`); the linear-in-`n` part vanishes and only the
`⌊n/30⌋` floor slop (`≤ 1`) and the `O(log n)` corrections survive. This is the analytic half of the
dual *upper* Chebyshev estimate `ψ(n) − ψ(⌊n/6⌋) ≤ A·n + O(log n)`, whose geometric iterate gives
`ψ(n) ≲ (6/5)A·n` — the missing ingredient to lower the prime-gap ratio `8/5 → 6/5`. -/
theorem logFactorial_comb_upper {n : ℕ} (hn : 30 ≤ n) :
    Real.log (Nat.factorial n) - Real.log (Nat.factorial (n / 2))
        - Real.log (Nat.factorial (n / 3)) - Real.log (Nat.factorial (n / 5))
        + Real.log (Nat.factorial (n / 30))
      ≤ (n : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5)
        + 4 * Real.log n - Real.log 30 + 6 := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hSu := log_factorial_le (m := n) (by omega)
  have hL2 := log_factorial_div_ge (n := n) (k := 2) (by norm_num) (by omega)
  have hL3 := log_factorial_div_ge (n := n) (k := 3) (by norm_num) (by omega)
  have hL5 := log_factorial_div_ge (n := n) (k := 5) (by norm_num) (by omega)
  have hU30 := log_factorial_div_le (n := n) (k := 30) (by norm_num) (by omega)
  have hID := logFactorial_leading_identity (x := (n : ℝ)) hnpos
  have f30 : (n : ℝ) / 30 - 1 ≤ ((n / 30 : ℕ) : ℝ) := by
    have hkpos : (0 : ℝ) < 30 := by norm_num
    have h1 : n < (n / 30 + 1) * 30 := by
      have e := Nat.div_add_mod n 30; have m := Nat.mod_lt n (show 0 < 30 by norm_num); nlinarith [e, m]
    have h2 : (n : ℝ) ≤ (((n / 30 : ℕ) : ℝ) + 1) * 30 := by exact_mod_cast h1.le
    have h3 : (n : ℝ) / 30 ≤ ((n / 30 : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hkpos]; linarith [h2]
    linarith [h3]
  have e2 : Real.log ((n : ℝ) / 2) = Real.log n - Real.log 2 := Real.log_div hnpos.ne' (by norm_num)
  have e3 : Real.log ((n : ℝ) / 3) = Real.log n - Real.log 3 := Real.log_div hnpos.ne' (by norm_num)
  have e5 : Real.log ((n : ℝ) / 5) = Real.log n - Real.log 5 := Real.log_div hnpos.ne' (by norm_num)
  have e30 : Real.log ((n : ℝ) / 30) = Real.log n - Real.log 30 := Real.log_div hnpos.ne' (by norm_num)
  have e2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hnpos.ne'
  have e30s : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  norm_num at hSu hL2 hL3 hL5 hU30 hID f30 e2 e3 e5 e30 e2n e30s ⊢
  linarith [hSu, hL2, hL3, hL5, hU30, hID, f30, e2, e3, e5, e30, e2n, e30s]

/-- **Refined Chebyshev `ψ` lower bound** (the capstone). For `n ≥ 30`,
`A·n + O(log n) ≤ ψ(n)` with leading constant `A = (7/15)log2+(3/10)log3+(1/6)log5 > 0.91`
(`chebyshev_const_gt`) — **strictly beating** the elementary `log4/2 ≈ 0.69` (`psi_lower`/`theta_lower`)
that mathlib's central-binomial argument caps at. Immediate from the combinatorial half
`logFactorial_comb_le_psi` (`f(n) ≤ ψ(n)`) and the analytic half `logFactorial_comb_lower`
(`A·n + O(log n) ≤ f(n)`). This is the bound mathlib entirely lacks and the *only* route to a
no-three-in-line general-`N` constant past Bertrand's `3/4`. Remaining downstream: the dual upper
iterate `ψ(n) ≲ (6/5)A·n`, then the central-binomial split for a prime in `(n, c·n]`, `c < 2`. -/
theorem psi_refined_lower {n : ℕ} (hn : 30 ≤ n) :
    (n : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5)
        + Real.log n / 2 + Real.log (2 * Real.pi) / 2 - 3 * Real.log (2 * n) / 2
        + 3 * Real.log 2 / 2 - Real.log ((n : ℝ) / 30) - 7
      ≤ Chebyshev.psi n :=
  le_trans (logFactorial_comb_lower hn) (logFactorial_comb_le_psi n)

/-- **Refined Chebyshev `ψ` *upper* recurrence step.** For `n ≥ 30`,
`ψ(n) − ψ(⌊n/6⌋) ≤ A·n + 4·log n − log 30 + 6` with `A = (7/15)log2+(3/10)log3+(1/6)log5`. Chains the
combinatorial lower bound `logFactorial_comb_ge_psi_sub` (`ψ(n) − ψ(⌊n/6⌋) ≤ f(n)`) with the analytic
upper bound `logFactorial_comb_upper` (`f(n) ≤ A·n + O(log n)`). Telescoping this 6-fold recurrence
(strong induction, `ψ(⌊n/6^k⌋) = 0` once `n/6^k < 2`) yields `ψ(n) ≤ (6/5)A·n + O(log² n)` — the dual
*upper* Chebyshev bound, which lowers the prime-gap ratio from `8/5` toward Nagura's `6/5` and the
no-three-in-line constant from `15/16` toward `5/4`. -/
theorem psi_refined_upper_step {n : ℕ} (hn : 30 ≤ n) :
    Chebyshev.psi (n : ℝ) - Chebyshev.psi ((n / 6 : ℕ) : ℝ)
      ≤ (n : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5)
        + 4 * Real.log n - Real.log 30 + 6 :=
  le_trans logFactorial_comb_ge_psi_sub (logFactorial_comb_upper hn)

/-- **Refined Chebyshev `θ` lower bound.** For `n ≥ 30`,
`A·n − 4·√n·log n − 9 ≤ θ(n)` with `A = (7/15)log2+(3/10)log3+(1/6)log5 > 0.91`. Combines the
capstone `psi_refined_lower` (`ψ(n) ≥ A·n + O(log n)`) with `abs_psi_sub_theta_le_sqrt_mul_log`
(`θ ≥ ψ − 2√n·log n`); the `O(log n)` corrections are folded into the clean `−4√n·log n − 9` error
(using `log n ≤ √n·log n` and `log(2π)/2 + log 30 − 7 ≥ −9`). This is the genuine refined `θ` lower
bound — leading constant `0.92` rather than the elementary `log4/2 ≈ 0.69` (`theta_lower`) — and is the
lower half of the two-sided `θ` estimate feeding the sub-`2` prime gap. -/
theorem theta_refined_lower {n : ℕ} (hn : 30 ≤ n) :
    (n : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5)
        - 4 * Real.sqrt n * Real.log n - 9
      ≤ Chebyshev.theta n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hp := psi_refined_lower hn
  have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hn1
  rw [abs_le] at habs
  -- algebraic simplifications of the ψ-error logarithms
  have h2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) (by positivity)
  have hn30 : Real.log ((n : ℝ) / 30) = Real.log n - Real.log 30 :=
    Real.log_div (by positivity) (by norm_num)
  -- side facts to fold O(log n) into −4√n·log n − 9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hsq : Real.log n ≤ Real.sqrt n * Real.log n := by nlinarith [hlogn, hsqrt1]
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact Real.log_nonneg this
  have hlog30 : 0 ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  rw [h2n, hn30] at hp
  linarith [hp, habs.2, hsq, hlog2pi, hlog30]

/-- **`√z·log z` is small relative to `z`.** For `z ≥ 2⁴⁰`, `√z·log z ≤ (40·log2/2²⁰)·z`. Proof:
`log z/√z` is antitone on `[e², ∞)` (`Real.log_div_sqrt_antitoneOn`), so on `z ≥ 2⁴⁰` it is at most
its value `(40·log2)/2²⁰` at `2⁴⁰` (where `√(2⁴⁰) = 2²⁰` and `log(2⁴⁰) = 40·log2`); multiply through by
`z = √z·√z`. The coefficient `40·log2/2²⁰ ≈ 2.6·10⁻⁵` is *driven below* any fixed positive margin by
the threshold `2⁴⁰`, which is exactly what lets the `√·log` error in the two-sided `θ` estimate be
dominated by the linear gap `((8/5)A − log4)·n` — the engine of the sub-`2` prime gap. -/
theorem sqrt_log_small (z : ℝ) (hz : (2 : ℝ) ^ 40 ≤ z) :
    Real.sqrt z * Real.log z ≤ (40 * Real.log 2 / 2 ^ 20) * z := by
  have hzpos : (0 : ℝ) < z := lt_of_lt_of_le (by positivity) hz
  have he2le8 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [he, h, hp]
  have he2 : Real.exp 2 ≤ (2 : ℝ) ^ 40 := le_trans he2le8 (by norm_num)
  have hanti := Real.log_div_sqrt_antitoneOn (he2) (le_trans he2 hz) hz
  have hsqrt40 : Real.sqrt ((2 : ℝ) ^ 40) = 2 ^ 20 := by
    rw [show ((2 : ℝ) ^ 40) = ((2 : ℝ) ^ 20) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog40 : Real.log ((2 : ℝ) ^ 40) = 40 * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  simp only at hanti
  rw [hsqrt40, hlog40] at hanti
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hzpos
  rw [div_le_iff₀ hsz] at hanti
  have hmss : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hzpos.le
  have hstep : Real.sqrt z * Real.log z
      ≤ Real.sqrt z * ((40 * Real.log 2 / 2 ^ 20) * Real.sqrt z) :=
    mul_le_mul_of_nonneg_left hanti hsz.le
  have heq : Real.sqrt z * ((40 * Real.log 2 / 2 ^ 20) * Real.sqrt z)
      = (40 * Real.log 2 / 2 ^ 20) * (Real.sqrt z * Real.sqrt z) := by ring
  rw [hmss] at heq
  linarith [hstep, heq]

/-- **Prime in `(n, 8n/5]`** for `n ≥ 5·2³⁷` — a sub-`2` prime gap, *unconditional and axiom-clean*.
This is the first prime-gap ratio below Bertrand's `2` reached in this development, and it is the lever
that pushes the no-three-in-line general-`N` constant strictly above Bertrand's `3/4`
(`maxNoThreeInLine_ge_fifteen_sixteenths`).

**Proof (two-sided Chebyshev `θ`).** By contradiction: if no prime lies in `(n, M]` with `M = ⌊8n/5⌋`,
then `θ(M) = θ(n)` (the prime-filtered sums over `(0,M]` and `(0,n]` coincide). But the **refined**
lower bound gives `θ(M) ≥ A·M − 4√M·log M − 9 ≥ (8/5)A·n − O(√n log n)` with `A > 0.91`, so
`(8/5)A > 1.456`, while mathlib's elementary upper bound gives `θ(n) ≤ (log4)·n < 1.3863·n`. The gap
`((8/5)A − log4)·n ≈ 0.07·n` beats the `√·log` error (`sqrt_log_small`, with `M ≥ 2⁴⁰`) once
`n ≥ 5·2³⁷`, contradicting `θ(M) = θ(n)`. The threshold is large but explicit — no asymptotic
hand-waving — and only the leading *constant* (not the gap ratio) is sacrificed versus Nagura's `6/5`.

The genuinely Chebyshev-strength input (`theta_refined_lower`, hence `psi_refined_lower`) is what
mathlib lacked; the elementary `theta_lower` (`≈ 0.69·x`) provably cannot reach any ratio `< 2`. -/
theorem exists_prime_in_eight_fifths {n : ℕ} (hn : 5 * 2 ^ 37 ≤ n) :
    ∃ p, p.Prime ∧ n < p ∧ 5 * p ≤ 8 * n := by
  by_contra hcon
  push_neg at hcon
  have hprime : ∀ p, p.Prime → n < p → 8 * n < 5 * p := by
    intro p hp hnp; have := hcon p hp hnp; omega
  set M := 8 * n / 5 with hMdef
  have hnM : n ≤ M := by rw [hMdef]; omega
  have h5M : 5 * M ≤ 8 * n := by rw [hMdef]; omega
  have h8n : 8 * n < 5 * (M + 1) := by rw [hMdef]; omega
  -- no prime in `(n, M]` ⟹ `θ(M) = θ(n)`
  have hθeq : Chebyshev.theta ((M : ℕ) : ℝ) = Chebyshev.theta (n : ℝ) := by
    rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpM⟩, hpp⟩
      refine ⟨⟨hp0, ?_⟩, hpp⟩
      by_contra hpn
      push_neg at hpn
      have hgt := hprime p hpp hpn
      have : 5 * p ≤ 8 * n := le_trans (by omega) h5M
      omega
    · rintro ⟨⟨hp0, hpn⟩, hpp⟩
      exact ⟨⟨hp0, le_trans hpn hnM⟩, hpp⟩
  have hM30 : 30 ≤ M := by omega
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hnR : (5 * 2 ^ 37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `M ≥ 2⁴⁰`, `8n/5 − 1 ≤ M ≤ 8n/5`
  have hM2_40 : (2 : ℝ) ^ 40 ≤ (M : ℝ) := by
    have hN : (2 : ℕ) ^ 40 ≤ M := by
      rw [hMdef, Nat.le_div_iff_mul_le (by norm_num)]; omega
    calc (2 : ℝ) ^ 40 = ((2 ^ 40 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (M : ℝ) := by exact_mod_cast hN
  have hMub : (M : ℝ) ≤ 8 * (n : ℝ) / 5 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (5 * M : ℝ) ≤ 8 * n := by exact_mod_cast h5M
    linarith
  have hMlo : 8 * (n : ℝ) / 5 - 1 ≤ (M : ℝ) := by
    rw [div_sub_one (by norm_num), div_le_iff₀ (by norm_num)]
    have : (8 * n : ℝ) < 5 * (M + 1) := by exact_mod_cast h8n
    linarith
  -- the two `θ` bounds
  have hθlow := theta_refined_lower hM30
  have hθup := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity)
  -- numeric `log`/`A` facts
  have hlog2 := Real.log_two_lt_d9
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA := chebyshev_const_gt
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- dominate the `√·log` error
  have hsl := sqrt_log_small (M : ℝ) hM2_40
  have hcnn : (0 : ℝ) ≤ 40 * Real.log 2 / 2 ^ 20 := by positivity
  have hprod : (40 * Real.log 2 / 2 ^ 20) * (M : ℝ)
      ≤ (40 * Real.log 2 / 2 ^ 20) * (8 * (n : ℝ) / 5) :=
    mul_le_mul_of_nonneg_left hMub hcnn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h3 : 4 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) ≤ 0.0002 * (n : ℝ) := by
    nlinarith [hsl, hprod, hlog2, hlog2nn, hn0]
  -- `M·A ≥ 0.91·M` (drops the transcendental `A` from the linear program)
  have hAM : 0.91 * (M : ℝ)
      ≤ (M : ℝ) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5) := by
    nlinarith [hA, hMnn]
  have hnbig : (200 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hnR
  have hlog4num : Real.log 4 ≤ 1.3862944 := by rw [hlog4]; linarith [hlog2]
  have hub : Real.log 4 * (n : ℝ) ≤ 1.3862944 * (n : ℝ) := mul_le_mul_of_nonneg_right hlog4num hn0
  rw [hθeq] at hθlow
  linarith [hθlow, hθup, h3, hAM, hMlo, hub, hnbig]

/-- **HJSW general-`N` lower bound at constant `15/16`** (unconditional, axiom-clean). For `N ≥ 2⁴¹`,
the sub-`2` prime gap `exists_prime_in_eight_fifths` at `n = ⌊5N/16⌋` yields a prime
`p ∈ (⌊5N/16⌋, N/2]`, whose sheared construction gives `3(p−1) ≥ 3⌊5N/16⌋ ≈ 15N/16` points. This is
the **first unconditional improvement on Bertrand's `3/4`** (`maxNoThreeInLine_ge_three_quarters`,
`3·⌊N/4⌋ = 3·⌊4N/16⌋`) for the general-`N` no-three-in-line constant: `4/16 → 5/16`, i.e. `3/4 → 15/16`,
driven purely by the refined Chebyshev bound `θ(x) ≳ 0.92x` that this file builds. The threshold `2⁴¹`
is large but explicit (no `o(1)`); pushing the constant toward Nagura's `5/4` only needs the dual
upper iterate `θ(x) ≲ (6/5)A·x`, lowering the gap ratio from `8/5` toward `6/5`. -/
theorem maxNoThreeInLine_ge_fifteen_sixteenths {N : ℕ} (hN : 2 ^ 41 ≤ N) :
    3 * (5 * N / 16) ≤ maxNoThreeInLine N := by
  have hn : 5 * 2 ^ 37 ≤ 5 * N / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  obtain ⟨p, hp, hlo, hhi⟩ := exists_prime_in_eight_fifths (n := 5 * N / 16) hn
  have h2p : 2 * p ≤ N := by omega
  have := maxNoThreeInLine_ge_of_two_mul_prime_le hp h2p
  omega

/-- **Nagura's theorem (1952).** For every `n ≥ 25` there is a prime `p` in the interval `(n, 6n/5]`
(i.e. `n < p` and `5p ≤ 6n`). This sharpens Bertrand's postulate (`p ≤ 2n`) to ratio `6/5`.

**Status: disclosed `sorry` — the active frontier crux of the HJSW general-`N` thread.** This is a
*theorem* (proven by Nagura in 1952), not a conjecture; it is 🟡 debt, formalizable but gated on
infrastructure mathlib does not yet provide.

**Attack plan** (mirrors mathlib's `Nat.exists_prime_lt_and_le_two_mul`, sharpened). The Chebyshev
lower-bound infrastructure above (`psi_lower`/`theta_lower`) is the elementary part; what remains is
the *precise* numerical inequality.
* `4^n ≤ n · C(2n,n)` (`Nat.four_pow_lt_mul_centralBinom`); split `C(2n,n)`'s factorization keeping the
  `(6n/5, 2n]` primes (sharpen `centralBinom_factorization_small`/`centralBinom_le_of_no_bertrand_prime`).
* ⚠️ DEFINITIVE (computed): the *crude* elementary constants are **insufficient** for ratio `6/5` —
  with `theta_lower` (`θ(x) ≳ (log4/2)x`) the bound is `C(2n,n) ≤ (2n)^√(2n)·4^(31n/15)`, and
  `31/15 ≈ 2.07 > 1`, so it does NOT contradict `4ⁿ ≤ n·C(2n,n)`. (`log4/2 ≈ 0.69` is the best
  *elementary* `θ` constant; the true `θ(x)~x` needs PNT.) Nagura needs the precise *tuned* inequality
  — the analogue of `bertrand_main_inequality` re-derived for `6/5`, valid `n ≥ N₀`, with
  `n ∈ [25, N₀)` by `decide`. That analytic computation is the genuine remaining content.
* Submitted to Aristotle (`1644a603`). -/
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
