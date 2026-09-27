/-
# Mills' theorem, conditional on primes between consecutive cubes

W. H. Mills, *A prime-representing function*, Bull. Amer. Math. Soc. **53** (1947), 604:
there is a real `A > 1` with `⌊A^(3^n)⌋` prime for every `n ≥ 1`.

Mills' proof has two halves:

* an **analytic input**: for all sufficiently large `n` there is a prime strictly between `n³`
  and `(n+1)³` (Ingham 1937; explicitly for `n ≥ exp(exp(33.3))`, Dudek 2016);
* an **elementary nested-interval construction** turning that input into `A`.

This file does the second half, with the analytic input as an explicit hypothesis
`PrimeBetweenCubesFrom N`.  Nothing here proves Ingham's theorem, so the headline
`exists_mills_of_primeBetweenCubes` is **conditional**.

## Faithfulness

`IsMills` and `IsMinMills` are copied verbatim from google-deepmind/formal-conjectures,
`FormalConjectures/Wikipedia/Mills.lean` (`Mills.IsMills`, `Mills.IsMinMills`), so a
discharge of the hypothesis closes their `Mills.exists'` and `Mills.exists_least` as stated.

## Proof plan (the construction)

Pick a prime `p₀ ≥ max N 2` (`Nat.exists_infinite_primes`) and define `p (k+1)` as a prime
strictly between `(p k)³` and `(p k + 1)³` (the hypothesis, applied at `p k ≥ N`).  Then:

1. `(p k + 1)³ − 1 = p k · ((p k)² + 3 p k + 3)` is composite, so `p (k+1) + 1 < (p k + 1)³`.
2. `u k = (p k) ^ (3⁻ᵏ)` is monotone, `v k = (p k + 1) ^ (3⁻ᵏ)` is strictly antitone, and
   `u k < v k`.
3. `A = ⨆ k, u k` satisfies `p k ≤ A^(3^k) < p k + 1`, so `⌊A^(3^k)⌋₊ = p k`.
4. Re-index: `IsMills` quantifies over `n : ℕ+` with exponent `3^n`, so use `A` built from a
   sequence whose `k = 0` term is chosen so that the `n ≥ 1` terms are the primes.  (Either
   start the chain at `p 0` and take `A := ⨆ k, u k` with `⌊A^(3^n)⌋₊ = p n`, `n ≥ 1`, or
   shift; `A > 1` because `A ≥ u 0 = p 0 ≥ 2`.)

The **least** Mills number (`exists_least_of_exists`) is unconditional given one Mills number:
each constraint `⌊A^(3^n)⌋₊ = p` cuts out a left-closed interval `[p^(3⁻ⁿ), (p+1)^(3⁻ⁿ))`,
so the set `{A > 1 | IsMills A}` is closed under limits of antitone sequences, and it is
bounded below by `2^(1/3)`.  Take the infimum and show it is attained.
-/
import Mathlib

namespace LeanFormalizations.Mills

/-- **Verbatim from formal-conjectures** `Mills.IsMills`: `⌊A^(3^n)⌋₊` is prime for every
positive `n`. -/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/-- **Verbatim from formal-conjectures** `Mills.IsMinMills`: `A` is the least Mills number. -/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/-- The analytic input to Mills' theorem: from `N` on, every gap between consecutive cubes
contains a prime.  True for some `N` by Ingham (1937); Dudek (2016) makes `N` explicit. -/
def PrimeBetweenCubesFrom (N : ℕ) : Prop :=
  ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

/-- Step 1 of the plan: a prime below `(n+1)³` is at most `(n+1)³ − 2`, because
`(n+1)³ − 1 = n (n² + 3n + 3)` is composite for `n ≥ 2`. -/
theorem prime_add_one_lt_cube {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hlt : p < (n + 1) ^ 3) :
    p + 1 < (n + 1) ^ 3 := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with h | h
  · exact h
  exfalso
  have hfac : p = n * (n ^ 2 + 3 * n + 3) := by nlinarith [h, sq_nonneg n]
  have hdvd : n ∣ p := ⟨_, hfac⟩
  rcases (hp.eq_one_or_self_of_dvd n hdvd) with h1 | h2
  · omega
  · nlinarith [hfac, h2]


/-! ## The construction

With the analytic input in hand the construction is the same nested-interval engine as
Wright's, but for `f x = x³` the `n`-fold iterate is just `x ^ (3^n)`, so no iteration
helper is needed: the inverse interval endpoints are literal `rpow`s `x ^ (3^k)⁻¹.
-/

section Construction

variable {N : ℕ} (h : PrimeBetweenCubesFrom N)

/-- One step of the prime chain: a prime strictly between `m³` and `(m+1)³`, with the
strict upper bound `· + 1 < (m+1)³` supplied by `prime_add_one_lt_cube`. -/
private noncomputable def cubeStep (m : ℕ) : ℕ := if hm : N ≤ m then (h m hm).choose else 2

include h in
private lemma cubeStep_spec {m : ℕ} (hm : N ≤ m) (hm2 : 2 ≤ m) :
    (cubeStep h m).Prime ∧ m ^ 3 < cubeStep h m ∧ cubeStep h m + 1 < (m + 1) ^ 3 := by
  have hs := (h m hm).choose_spec
  have he : cubeStep h m = (h m hm).choose := by rw [cubeStep, dif_pos hm]
  rw [he]
  exact ⟨hs.1, hs.2.1, prime_add_one_lt_cube hm2 hs.1 hs.2.2⟩

/-- The prime chain `p 0 < p 1 < …`, each strictly between the cubes of the previous. -/
private noncomputable def cubeSeq : ℕ → ℕ
  | 0 => (Nat.exists_infinite_primes (max N 2)).choose
  | k + 1 => cubeStep h (cubeSeq k)

include h in
private lemma cubeSeq_spec (k : ℕ) : (cubeSeq h k).Prime ∧ max N 2 ≤ cubeSeq h k := by
  induction k with
  | zero =>
      have := (Nat.exists_infinite_primes (max N 2)).choose_spec
      exact ⟨this.2, this.1⟩
  | succ k ih =>
      obtain ⟨hp, hge⟩ := ih
      have hN : N ≤ cubeSeq h k := le_trans (le_max_left _ _) hge
      have h2 : 2 ≤ cubeSeq h k := le_trans (le_max_right _ _) hge
      obtain ⟨hq, hlo, _⟩ := cubeStep_spec h hN h2
      refine ⟨hq, ?_⟩
      have : cubeSeq h k ≤ (cubeSeq h k) ^ 3 := Nat.le_self_pow (by norm_num) _
      show max N 2 ≤ cubeStep h (cubeSeq h k)
      omega

include h in
private lemma cubeSeq_lower (k : ℕ) : (cubeSeq h k) ^ 3 < cubeSeq h (k + 1) := by
  obtain ⟨_, hge⟩ := cubeSeq_spec h k
  exact (cubeStep_spec h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.1

include h in
private lemma cubeSeq_upper (k : ℕ) : cubeSeq h (k + 1) + 1 < (cubeSeq h k + 1) ^ 3 := by
  obtain ⟨_, hge⟩ := cubeSeq_spec h k
  exact (cubeStep_spec h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.2

/-- Left endpoints of the nested intervals in `A`-space. -/
private noncomputable def mu (k : ℕ) : ℝ := (cubeSeq h k : ℝ) ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹
/-- Right endpoints of the nested intervals in `A`-space. -/
private noncomputable def nu (k : ℕ) : ℝ := ((cubeSeq h k : ℝ) + 1) ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹

private lemma exp_pos (k : ℕ) : (0:ℝ) < ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹ := by positivity

/-- `(x³) ^ (3^(k+1))⁻¹ = x ^ (3^k)⁻¹`: cubing eats one level of the root. -/
private lemma cube_root_step {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (3:ℕ)) ^ ((((3:ℕ) ^ (k+1) : ℕ) : ℝ))⁻¹ = x ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
  congr 1
  have h3 : ((3:ℕ) : ℝ) ≠ 0 := by norm_num
  have hk : (((3:ℕ) ^ k : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

include h in
private lemma mu_lt_succ (k : ℕ) : mu h k < mu h (k + 1) := by
  have hbase : (0:ℝ) ≤ ((cubeSeq h k : ℝ)) ^ (3:ℕ) := by positivity
  have hlt : ((cubeSeq h k : ℝ)) ^ (3:ℕ) < (cubeSeq h (k+1) : ℝ) := by
    have := cubeSeq_lower h k; exact_mod_cast this
  have := Real.rpow_lt_rpow hbase hlt (exp_pos (k+1))
  rwa [cube_root_step (by positivity) k] at this

include h in
private lemma nu_succ_lt (k : ℕ) : nu h (k + 1) < nu h k := by
  have hbase : (0:ℝ) ≤ (cubeSeq h (k+1) : ℝ) + 1 := by positivity
  have hlt : (cubeSeq h (k+1) : ℝ) + 1 < ((cubeSeq h k : ℝ) + 1) ^ (3:ℕ) := by
    have := cubeSeq_upper h k
    have hc : ((cubeSeq h (k+1) + 1 : ℕ) : ℝ) < (((cubeSeq h k + 1) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc; linarith
  have := Real.rpow_lt_rpow hbase hlt (exp_pos (k+1))
  rwa [cube_root_step (by positivity) k] at this

include h in
private lemma mu_lt_nu (k : ℕ) : mu h k < nu h k :=
  Real.rpow_lt_rpow (by positivity) (by linarith) (exp_pos k)

include h in
private lemma mu_le_nu (m k : ℕ) : mu h m ≤ nu h k := by
  have hmono : Monotone (mu h) := monotone_nat_of_le_succ fun n => (mu_lt_succ h n).le
  have hanti : Antitone (nu h) := antitone_nat_of_succ_le fun n => (nu_succ_lt h n).le
  rcases le_total m k with hmk | hmk
  · exact le_trans (hmono hmk) (mu_lt_nu h k).le
  · exact le_trans (mu_lt_nu h m).le (hanti hmk)

include h in
private lemma mu_bddAbove : BddAbove (Set.range (mu h)) :=
  ⟨nu h 0, by rintro _ ⟨m, rfl⟩; exact mu_le_nu h m 0⟩

include h in
private lemma pow_mu (k : ℕ) : (mu h k) ^ ((3:ℕ) ^ k) = (cubeSeq h k : ℝ) :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

include h in
private lemma pow_nu (k : ℕ) : (nu h k) ^ ((3:ℕ) ^ k) = (cubeSeq h k : ℝ) + 1 :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

include h in
private lemma floor_pow_iSup (k : ℕ) :
    ⌊(⨆ n, mu h n) ^ ((3:ℕ) ^ k)⌋₊ = cubeSeq h k := by
  set A : ℝ := ⨆ n, mu h n with hA
  have hlo : mu h k < A := lt_of_lt_of_le (mu_lt_succ h k) (le_ciSup (mu_bddAbove h) (k+1))
  have hhi : A < nu h k :=
    lt_of_le_of_lt (ciSup_le fun m => mu_le_nu h m (k+1)) (nu_succ_lt h k)
  have hmupos : (0:ℝ) ≤ mu h k := by unfold mu; positivity
  have h1 : (cubeSeq h k : ℝ) < A ^ ((3:ℕ) ^ k) := by
    rw [← pow_mu h k]; exact pow_lt_pow_left₀ hlo hmupos (by positivity)
  have h2 : A ^ ((3:ℕ) ^ k) < (cubeSeq h k : ℝ) + 1 := by
    rw [← pow_nu h k]; exact pow_lt_pow_left₀ hhi (le_of_lt (lt_of_le_of_lt hmupos hlo)) (by positivity)
  have hnn : (0:ℝ) ≤ A ^ ((3:ℕ) ^ k) := le_trans (Nat.cast_nonneg _) h1.le
  rw [Nat.floor_eq_iff hnn]
  exact ⟨h1.le, h2⟩

end Construction

/-- **Mills' theorem, conditional on primes between consecutive cubes.** -/
theorem exists_mills_of_primeBetweenCubes {N : ℕ} (h : PrimeBetweenCubesFrom N) :
    ∃ A > 1, IsMills A := by
  refine ⟨⨆ n, mu h n, ?_, fun n => ?_⟩
  · have h0 : mu h 0 = (cubeSeq h 0 : ℝ) := by
      simp [mu]
    have hge : (2:ℝ) ≤ mu h 0 := by
      rw [h0]
      exact_mod_cast le_trans (le_max_right N 2) (cubeSeq_spec h 0).2
    have := le_ciSup (mu_bddAbove h) 0
    linarith
  · rw [floor_pow_iSup h (n : ℕ)]
    exact (cubeSeq_spec h (n : ℕ)).1.prime

/-- **The least Mills number exists** as soon as one Mills number does.  Unconditional. -/
theorem exists_least_of_exists (h : ∃ A > 1, IsMills A) : ∃ A, IsMinMills A := by
  set S : Set ℝ := {x | x > 1 ∧ IsMills x} with hS
  obtain ⟨A₀, hA₀1, hA₀⟩ := h
  have hne : S.Nonempty := ⟨A₀, hA₀1, hA₀⟩
  -- every Mills number is at least `5/4`, since `⌊A³⌋₊` is prime, hence `A³ ≥ 2`
  have hlb : ∀ x ∈ S, (5/4 : ℝ) ≤ x := by
    rintro x ⟨hx1, hx⟩
    have hp := hx 1
    have hcube : ((2:ℕ) : ℝ) ≤ x ^ (3 ^ ((1 : ℕ+) : ℕ)) := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast (Nat.prime_iff.mpr hp).two_le
    norm_num at hcube
    by_contra hcon
    push Not at hcon
    have hc3 : x ^ 3 < (5/4 : ℝ) ^ 3 := pow_lt_pow_left₀ hcon (by linarith) (by norm_num)
    norm_num at hc3
    linarith
  have hbdd : BddBelow S := ⟨5/4, hlb⟩
  set m : ℝ := sInf S with hm
  have hmlb : (5/4 : ℝ) ≤ m := le_csInf hne hlb
  have hm1 : m > 1 := by linarith
  have hmpos : (0:ℝ) ≤ m := by linarith
  refine ⟨m, ⟨hm1, fun n => ?_⟩, fun x hx => csInf_le hbdd hx⟩
  -- fix `n`; the floor of `m ^ (3^n)` is already the prime attached to any `A ∈ S`
  -- close enough to `m` from above
  set k : ℕ := 3 ^ ((n : ℕ)) with hk
  set q : ℕ := ⌊m ^ k⌋₊ with hq
  have hqle : (q : ℝ) ≤ m ^ k := Nat.floor_le (by positivity)
  have hqlt : m ^ k < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  -- `{x | x ^ k < q + 1}` is open and contains `m`
  have hopen : IsOpen {x : ℝ | x ^ k < (q : ℝ) + 1} :=
    isOpen_lt (continuous_pow k) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen m hqlt
  obtain ⟨A, hAS, hAlt⟩ := exists_lt_of_csInf_lt hne (show m < m + δ by linarith)
  have hmA : m ≤ A := csInf_le hbdd hAS
  have hAmem : A ∈ {x : ℝ | x ^ k < (q : ℝ) + 1} := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hAup : A ^ k < (q : ℝ) + 1 := hAmem
  have hAlo : (q : ℝ) ≤ A ^ k :=
    le_trans hqle (pow_le_pow_left₀ hmpos hmA k)
  have hfl : ⌊A ^ k⌋₊ = q := by
    rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg q) hAlo)]
    exact ⟨hAlo, hAup⟩
  have := hAS.2 n
  rw [← hk, hfl] at this
  exact this

/-- **Mills' constant exists, conditional on primes between consecutive cubes.** -/
theorem exists_least_of_primeBetweenCubes {N : ℕ} (h : PrimeBetweenCubesFrom N) :
    ∃ A, IsMinMills A :=
  exists_least_of_exists (exists_mills_of_primeBetweenCubes h)

end LeanFormalizations.Mills
