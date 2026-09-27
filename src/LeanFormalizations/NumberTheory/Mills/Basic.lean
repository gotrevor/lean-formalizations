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

/-- The chain started at a *chosen* `m₀`: `m₀`, then a prime strictly between the cubes of the
previous term, forever.  Only the terms of index `≥ 1` are prime; `m₀` itself need only satisfy
`max N 2 ≤ m₀`.  Letting `m₀` be chosen is exactly what makes the resulting Mills number
bounded *above* (by `m₀ + 1`), which the original `Nat.exists_infinite_primes` start did not. -/
private noncomputable def cubeSeq (m₀ : ℕ) : ℕ → ℕ
  | 0 => m₀
  | k + 1 => cubeStep h (cubeSeq m₀ k)

variable {m₀ : ℕ} (hm₀ : max N 2 ≤ m₀)

include h hm₀ in
private lemma cubeSeq_ge (k : ℕ) : max N 2 ≤ cubeSeq h m₀ k := by
  induction k with
  | zero => exact hm₀
  | succ k ih =>
      have hN : N ≤ cubeSeq h m₀ k := le_trans (le_max_left _ _) ih
      have h2 : 2 ≤ cubeSeq h m₀ k := le_trans (le_max_right _ _) ih
      obtain ⟨hq, hlo, _⟩ := cubeStep_spec h hN h2
      have : cubeSeq h m₀ k ≤ (cubeSeq h m₀ k) ^ 3 := Nat.le_self_pow (by norm_num) _
      show max N 2 ≤ cubeStep h (cubeSeq h m₀ k)
      omega

include h hm₀ in
private lemma cubeSeq_prime_succ (k : ℕ) : (cubeSeq h m₀ (k + 1)).Prime := by
  have ih := cubeSeq_ge h hm₀ k
  exact (cubeStep_spec h (le_trans (le_max_left _ _) ih) (le_trans (le_max_right _ _) ih)).1

include h hm₀ in
private lemma cubeSeq_prime (hp : m₀.Prime) (k : ℕ) : (cubeSeq h m₀ k).Prime := by
  cases k with
  | zero => exact hp
  | succ k => exact cubeSeq_prime_succ h hm₀ k

include h hm₀ in
private lemma cubeSeq_lower (k : ℕ) : (cubeSeq h m₀ k) ^ 3 < cubeSeq h m₀ (k + 1) := by
  have hge := cubeSeq_ge h hm₀ k
  exact (cubeStep_spec h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.1

include h hm₀ in
private lemma cubeSeq_upper (k : ℕ) : cubeSeq h m₀ (k + 1) + 1 < (cubeSeq h m₀ k + 1) ^ 3 := by
  have hge := cubeSeq_ge h hm₀ k
  exact (cubeStep_spec h (le_trans (le_max_left _ _) hge) (le_trans (le_max_right _ _) hge)).2.2

/-- Left endpoints of the nested intervals in `A`-space. -/
private noncomputable def mu (m₀ k : ℕ) : ℝ :=
  (cubeSeq h m₀ k : ℝ) ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹
/-- Right endpoints of the nested intervals in `A`-space. -/
private noncomputable def nu (m₀ k : ℕ) : ℝ :=
  ((cubeSeq h m₀ k : ℝ) + 1) ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹

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

include h hm₀ in
private lemma mu_lt_succ (k : ℕ) : mu h m₀ k < mu h m₀ (k + 1) := by
  have hbase : (0:ℝ) ≤ ((cubeSeq h m₀ k : ℝ)) ^ (3:ℕ) := by positivity
  have hlt : ((cubeSeq h m₀ k : ℝ)) ^ (3:ℕ) < (cubeSeq h m₀ (k+1) : ℝ) := by
    have := cubeSeq_lower h hm₀ k; exact_mod_cast this
  have := Real.rpow_lt_rpow hbase hlt (exp_pos (k+1))
  rwa [cube_root_step (by positivity) k] at this

include h hm₀ in
private lemma nu_succ_lt (k : ℕ) : nu h m₀ (k + 1) < nu h m₀ k := by
  have hbase : (0:ℝ) ≤ (cubeSeq h m₀ (k+1) : ℝ) + 1 := by positivity
  have hlt : (cubeSeq h m₀ (k+1) : ℝ) + 1 < ((cubeSeq h m₀ k : ℝ) + 1) ^ (3:ℕ) := by
    have := cubeSeq_upper h hm₀ k
    have hc : ((cubeSeq h m₀ (k+1) + 1 : ℕ) : ℝ) < (((cubeSeq h m₀ k + 1) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc; linarith
  have := Real.rpow_lt_rpow hbase hlt (exp_pos (k+1))
  rwa [cube_root_step (by positivity) k] at this

include h in
private lemma mu_lt_nu (k : ℕ) : mu h m₀ k < nu h m₀ k :=
  Real.rpow_lt_rpow (by positivity) (by linarith) (exp_pos k)

include h hm₀ in
private lemma mu_le_nu (m k : ℕ) : mu h m₀ m ≤ nu h m₀ k := by
  have hmono : Monotone (mu h m₀) := monotone_nat_of_le_succ fun n => (mu_lt_succ h hm₀ n).le
  have hanti : Antitone (nu h m₀) := antitone_nat_of_succ_le fun n => (nu_succ_lt h hm₀ n).le
  rcases le_total m k with hmk | hmk
  · exact le_trans (hmono hmk) (mu_lt_nu h k).le
  · exact le_trans (mu_lt_nu h m).le (hanti hmk)

include h hm₀ in
private lemma mu_bddAbove : BddAbove (Set.range (mu h m₀)) :=
  ⟨nu h m₀ 0, by rintro _ ⟨m, rfl⟩; exact mu_le_nu h hm₀ m 0⟩

include h in
private lemma pow_mu (k : ℕ) : (mu h m₀ k) ^ ((3:ℕ) ^ k) = (cubeSeq h m₀ k : ℝ) :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

include h in
private lemma pow_nu (k : ℕ) : (nu h m₀ k) ^ ((3:ℕ) ^ k) = (cubeSeq h m₀ k : ℝ) + 1 :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

include h hm₀ in
private lemma floor_pow_iSup (k : ℕ) :
    ⌊(⨆ n, mu h m₀ n) ^ ((3:ℕ) ^ k)⌋₊ = cubeSeq h m₀ k := by
  set A : ℝ := ⨆ n, mu h m₀ n with hA
  have hlo : mu h m₀ k < A :=
    lt_of_lt_of_le (mu_lt_succ h hm₀ k) (le_ciSup (mu_bddAbove h hm₀) (k+1))
  have hhi : A < nu h m₀ k :=
    lt_of_le_of_lt (ciSup_le fun m => mu_le_nu h hm₀ m (k+1)) (nu_succ_lt h hm₀ k)
  have hmupos : (0:ℝ) ≤ mu h m₀ k := by unfold mu; positivity
  have h1 : (cubeSeq h m₀ k : ℝ) < A ^ ((3:ℕ) ^ k) := by
    rw [← pow_mu h k]; exact pow_lt_pow_left₀ hlo hmupos (by positivity)
  have h2 : A ^ ((3:ℕ) ^ k) < (cubeSeq h m₀ k : ℝ) + 1 := by
    rw [← pow_nu h k]
    exact pow_lt_pow_left₀ hhi (le_of_lt (lt_of_le_of_lt hmupos hlo)) (by positivity)
  have hnn : (0:ℝ) ≤ A ^ ((3:ℕ) ^ k) := le_trans (Nat.cast_nonneg _) h1.le
  rw [Nat.floor_eq_iff hnn]
  exact ⟨h1.le, h2⟩

include h hm₀ in
/-- The built Mills number lies below `m₀ + 1`: the `k = 0` interval is `[m₀, m₀ + 1)`. -/
private lemma iSup_mu_lt : (⨆ n, mu h m₀ n) < (m₀ : ℝ) + 1 := by
  have h0 : nu h m₀ 0 = (m₀ : ℝ) + 1 := by
    simp [nu, cubeSeq]
  have := lt_of_le_of_lt (ciSup_le fun m => mu_le_nu h hm₀ m 1) (nu_succ_lt h hm₀ 0)
  rwa [h0] at this

include h hm₀ in
private lemma le_iSup_mu : (m₀ : ℝ) ≤ ⨆ n, mu h m₀ n := by
  have h0 : mu h m₀ 0 = (m₀ : ℝ) := by simp [mu, cubeSeq]
  have := le_ciSup (mu_bddAbove h hm₀) 0
  rwa [h0] at this

end Construction

/-- **Mills' theorem with an explicit upper bound**, conditional on primes between consecutive
cubes: starting the chain at any `m₀ ≥ max N 2` gives a Mills number in `[m₀, m₀ + 1)`. -/
theorem exists_mills_lt_of_primeBetweenCubes {N m₀ : ℕ} (h : PrimeBetweenCubesFrom N)
    (hm₀ : max N 2 ≤ m₀) : ∃ A, 1 < A ∧ IsMills A ∧ A < (m₀ : ℝ) + 1 := by
  have h2 : (2:ℝ) ≤ (m₀ : ℝ) := by
    exact_mod_cast le_trans (le_max_right N 2) hm₀
  refine ⟨⨆ n, mu h m₀ n, ?_, fun n => ?_, iSup_mu_lt h hm₀⟩
  · have := le_iSup_mu h hm₀; linarith
  · obtain ⟨k, hk⟩ : ∃ k, ((n : ℕ)) = k + 1 := ⟨(n : ℕ) - 1, by have h : 0 < (n : ℕ) := n.2; omega⟩
    rw [hk, floor_pow_iSup h hm₀ (k + 1)]
    exact (cubeSeq_prime_succ h hm₀ k).prime

/-- **Mills' theorem, conditional on primes between consecutive cubes.** -/
theorem exists_mills_of_primeBetweenCubes {N : ℕ} (h : PrimeBetweenCubesFrom N) :
    ∃ A > 1, IsMills A := by
  obtain ⟨A, hA1, hA, -⟩ := exists_mills_lt_of_primeBetweenCubes h (le_refl (max N 2))
  exact ⟨A, hA1, hA⟩

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


/-- **Mills' theorem with a cube-root-scale upper bound.**  Starting the chain at a chosen
*prime* `m₀ ≥ max N 2` and taking the cube root of the resulting number shifts the indexing by
one: the digit at `n = 1` is `m₀` itself, so `A³ < m₀ + 1`.  This is the form that gives an
explicit bound of the right order of magnitude (`A ≈ m₀^(1/3)`). -/
theorem exists_mills_cube_lt_of_primeBetweenCubes {N m₀ : ℕ} (h : PrimeBetweenCubesFrom N)
    (hp : m₀.Prime) (hm₀ : max N 2 ≤ m₀) :
    ∃ A, 1 < A ∧ IsMills A ∧ A ^ 3 < (m₀ : ℝ) + 1 := by
  have h2 : (2:ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast le_trans (le_max_right N 2) hm₀
  set B : ℝ := ⨆ n, mu h m₀ n with hB
  have hBlo : (m₀ : ℝ) ≤ B := le_iSup_mu h hm₀
  have hBhi : B < (m₀ : ℝ) + 1 := iSup_mu_lt h hm₀
  have hB0 : (0:ℝ) ≤ B := by linarith
  refine ⟨B ^ ((((3:ℕ)) : ℝ))⁻¹, ?_, ?_, ?_⟩
  · -- `A > 1` because `A³ = B ≥ 2`
    have hcube : (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ (3:ℕ) = B :=
      Real.rpow_inv_natCast_pow hB0 (by norm_num)
    have hA0 : (0:ℝ) ≤ B ^ ((((3:ℕ)) : ℝ))⁻¹ := Real.rpow_nonneg hB0 _
    by_contra hcon
    push Not at hcon
    have : (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ (3:ℕ) ≤ 1 := pow_le_one₀ hA0 hcon
    rw [hcube] at this
    linarith
  · intro n
    obtain ⟨k, hk⟩ : ∃ k, ((n : ℕ)) = k + 1 := ⟨(n : ℕ) - 1, by have h : 0 < (n : ℕ) := n.2; omega⟩
    have hcube : (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ (3:ℕ) = B :=
      Real.rpow_inv_natCast_pow hB0 (by norm_num)
    have hstep : (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ ((3:ℕ) ^ ((n : ℕ))) = B ^ ((3:ℕ) ^ k) := by
      rw [hk, pow_succ, mul_comm, pow_mul, hcube]
    rw [hstep, floor_pow_iSup h hm₀ k]
    exact (cubeSeq_prime h hm₀ hp k).prime
  · have hcube : (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ (3:ℕ) = B :=
      Real.rpow_inv_natCast_pow hB0 (by norm_num)
    rw [show (3:ℕ) = ((3:ℕ)) from rfl] at hcube
    calc (B ^ ((((3:ℕ)) : ℝ))⁻¹) ^ 3 = B := hcube
      _ < (m₀ : ℝ) + 1 := hBhi

end LeanFormalizations.Mills
