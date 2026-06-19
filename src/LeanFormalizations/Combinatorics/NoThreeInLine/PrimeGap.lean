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
