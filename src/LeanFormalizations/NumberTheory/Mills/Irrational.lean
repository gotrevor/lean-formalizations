/-
# Mills' constant is irrational (Saito 2024), from three literature inputs

K. Saito, *Mills' constant is irrational*, Mathematika **71** (2025), no. 3, e70027,
arXiv:2404.19461.  Local-only full text (gitignored): `papers/saito-2024-mills-irrational.{pdf,txt}`.

Saito's theorem is stated for general exponent sequences `(c_k)`; here `c_k = 3` throughout
(so `C_k = 3^k`, `b = 3`, `I_b = ℕ`, `B = 3`), which is all formal-conjectures'
`Mills.irrational` needs.  Inputs, each a hypothesis (`Literature/Primes.lean`):

* `BakerHarmanPintz2001` — primes in `[x, x + x^(21/40)]`, with a count (Saito Thm 2.1).
  Only `1/2 ≤ θ < 2/3` is used (`θ_b = 1 − θ − 1/3 > 0`, and `3θ ≤ 2` in (3.11)).
* `Matomaki2007` — few intervals with too few primes (Saito Thm 3.7).
* `Mahler1957` — powers of a non-integer rational stay away from integers (Saito Thm 2.5).

## Route (Saito §2–§3, specialised to `c = 3`)

1. `primeBetweenCubes_of_BHP`: BHP puts a prime in `[n³, n³ + n^(63/40)] ⊂ (n³, (n+1)³)` for
   large `n`, so Mills numbers exist (`exists_mills_of_primeBetweenCubes`, already proved), and
   so a least one does (`exists_least_of_exists`).
2. **Lemma 3.5**: `p_k³ ≤ p_{k+1} < (p_k + 1)³ − 1` for `p_k = ⌊ξ^(3^k)⌋₊` (`ξ` any Mills number).
3. **Lemma 3.8** (from Matomäki): if `[X, X + X^η]` has `≥ d₂ X^η / log X` primes then some prime
   `q` in it has `[q³, q³ + q²]` holding `≥ d₁ q² / log q³` primes.
4. **Lemma 3.6** (minimality): for large `k`, `p_{k+1} ≤ p_k³ + p_k^(3θ)`; otherwise Matomäki's
   construction (a chain `q_m` built with Lemma 3.8, by induction) yields a Mills number `< ξ`.
5. **Lemma 3.9**: hence `|ξ^(3^k) − p_k| ≤ e^(−γ 3^k)` for some `γ > 0` and all large `k`.
6. **Conclusion**: if `ξ = a/b` then `ξ^(3^k)` is never an integer (else `p_{k+1} = p_k³`), so
   `ξ` is a non-integer rational `> 1`, and Mahler with `ε := γ`, `n := 3^k` contradicts 5.
-/
import LeanFormalizations.NumberTheory.Mills.Basic
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.Mills.Schoenfeld

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- Baker–Harman–Pintz puts a prime in every large cube gap (any `θ < 2/3` would do). -/
theorem primeBetweenCubes_of_BHP (h : BakerHarmanPintz2001) :
    ∃ N, PrimeBetweenCubesFrom N := by
  obtain ⟨d₀, hd₀, X, hX⟩ := h
  refine ⟨max 2 (⌈X⌉₊ + 1), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn2r : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hnX : X ≤ (n:ℝ) := by
    have h1 : ⌈X⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hc : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast (show ⌈X⌉₊ ≤ n by omega)
    linarith
  set x : ℝ := (n:ℝ) ^ (3:ℕ) with hx
  have hx8 : (8:ℝ) ≤ x := by
    have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 2 by norm_num) hn2r 3
    rw [hx]; norm_num at h; linarith
  have hxn : (n:ℝ) ≤ x := by
    have h : (n:ℝ) ^ (1:ℕ) ≤ (n:ℝ) ^ (3:ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [pow_one] at h; rw [hx]; linarith
  have hx1 : (1:ℝ) < x := by linarith
  have hcount := hX x (le_trans hnX hxn)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  -- the interval `[x, x + x^(21/40)]` sits inside `(n³, (n+1)³)`
  have hsmall : x ^ ((21:ℝ) / 40) ≤ (n:ℝ) ^ (2:ℕ) := by
    have h1 : x ^ ((21:ℝ) / 40) ≤ x ^ ((2:ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have h2 : x ^ ((2:ℝ) / 3) = (n:ℝ) ^ (2:ℕ) := by
      rw [hx, ← Real.rpow_natCast (n:ℝ) 3, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (n:ℝ) 2]
      norm_num
    linarith
  -- a prime in the interval
  have hcpos : 0 < primesIn x (x + x ^ ((21:ℝ) / 40)) := by
    rcases Nat.eq_zero_or_pos (primesIn x (x + x ^ ((21:ℝ) / 40))) with h0 | h0
    · rw [h0] at hcount
      have : (0:ℝ) < d₀ * x ^ ((21:ℝ) / 40) / Real.log x :=
        div_pos (mul_pos hd₀ (Real.rpow_pos_of_pos (by linarith) _)) hlogx
      norm_num at hcount
      linarith
    · exact h0
  unfold primesIn at hcpos
  obtain ⟨p, hpmem⟩ := Finset.card_pos.1 hcpos
  simp only [Finset.mem_filter, Finset.mem_Icc] at hpmem
  obtain ⟨⟨hplo, hphi⟩, hp⟩ := hpmem
  -- `⌈n³⌉₊ = n³`
  have hceil : ⌈x⌉₊ = n ^ 3 := by
    rw [hx, show ((n:ℝ)) ^ (3:ℕ) = ((n ^ 3 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [hceil] at hplo
  refine ⟨p, hp, ?_, ?_⟩
  · -- `n³` itself is not prime
    refine lt_of_le_of_ne hplo ?_
    intro hEq
    rw [← hEq] at hp
    have hdvd : n ∣ n ^ 3 := dvd_pow_self n (by norm_num)
    rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | h1
    · omega
    · have hlt3 : n ^ 1 < n ^ 3 := Nat.pow_lt_pow_right hn2 (by norm_num)
      rw [pow_one, ← h1] at hlt3
      exact absurd hlt3 (lt_irrefl _)
  · -- `p ≤ n³ + n² < (n+1)³`
    have hpr : (p : ℝ) ≤ x + x ^ ((21:ℝ) / 40) := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast hphi
    have hlt : (p : ℝ) < (((n + 1) ^ 3 : ℕ) : ℝ) := by
      push_cast
      rw [hx] at hpr
      nlinarith [hsmall, hn2r]
    exact_mod_cast hlt

/-- Mills' theorem from Baker–Harman–Pintz. -/
theorem exists_mills_of_BHP (h : BakerHarmanPintz2001) : ∃ A > 1, IsMills A :=
  let ⟨_, hN⟩ := primeBetweenCubes_of_BHP h
  exists_mills_of_primeBetweenCubes hN

/-! ### The digit sequence of a Mills number (Saito §3, `c ≡ 3`)

`mdigit A k = ⌊A^(3^(k+1))⌋₊` is Saito's `p_{k+1}` (his index starts at 1).  With `c_k = 3`
throughout, `C_k = 3^k`, `b = 3`, `I_b = ℕ`, `θ = 21/40` and `θ_b = 1 − θ − 1/3 = 17/120 > 0`.
-/

/-- The digits of a Mills number: `mdigit A k = ⌊A^(3^(k+1))⌋₊`, so `mdigit A 0 = ⌊A³⌋₊`. -/
noncomputable def mdigit (A : ℝ) (k : ℕ) : ℕ := ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊

theorem mdigit_prime {A : ℝ} (hA : IsMills A) (k : ℕ) : (mdigit A k).Prime := by
  have := hA ⟨k + 1, by omega⟩
  simpa [mdigit] using Nat.prime_iff.2 this

theorem mdigit_two_le {A : ℝ} (hA : IsMills A) (k : ℕ) : 2 ≤ mdigit A k :=
  (mdigit_prime hA k).two_le

theorem mdigit_le_pow {A : ℝ} (hA0 : 0 ≤ A) (k : ℕ) :
    (mdigit A k : ℝ) ≤ A ^ ((3:ℕ) ^ (k + 1)) := Nat.floor_le (by positivity)

theorem pow_lt_mdigit_add_one (A : ℝ) (k : ℕ) :
    A ^ ((3:ℕ) ^ (k + 1)) < (mdigit A k : ℝ) + 1 := Nat.lt_floor_add_one _

theorem pow_succ_eq_cube (A : ℝ) (k : ℕ) :
    A ^ ((3:ℕ) ^ (k + 1 + 1)) = (A ^ ((3:ℕ) ^ (k + 1))) ^ (3:ℕ) := by
  rw [show (3:ℕ) ^ (k + 1 + 1) = (3:ℕ) ^ (k + 1) * 3 by ring, pow_mul]

/-- **Saito Lemma 3.5**, lower half: `p_k³ < p_{k+1}` (equality is impossible, a cube of a
prime `≥ 2` is not prime). -/
theorem mdigit_cube_lt {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) (k : ℕ) :
    (mdigit A k) ^ 3 < mdigit A (k + 1) := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hcube : ((mdigit A k ^ 3 : ℕ) : ℝ) ≤ A ^ ((3:ℕ) ^ (k + 1 + 1)) := by
    rw [pow_succ_eq_cube]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (mdigit_le_pow hA0 k) 3
  have hfloor : mdigit A k ^ 3 ≤ mdigit A (k + 1) := Nat.le_floor hcube
  refine lt_of_le_of_ne hfloor ?_
  intro hEq
  have hp := mdigit_prime hA (k + 1)
  rw [← hEq] at hp
  have h2c := mdigit_two_le hA k
  rcases hp.eq_one_or_self_of_dvd (mdigit A k) (dvd_pow_self _ (by norm_num)) with h | h
  · omega
  · have hlt : (mdigit A k) ^ 1 < (mdigit A k) ^ 3 := Nat.pow_lt_pow_right h2c (by norm_num)
    rw [pow_one, ← h] at hlt
    exact absurd hlt (lt_irrefl _)

/-- **Saito Lemma 3.5**, upper half: `p_{k+1} < (p_k + 1)³ − 1`. -/
theorem mdigit_succ_lt {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) (k : ℕ) :
    mdigit A (k + 1) + 1 < (mdigit A k + 1) ^ 3 := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hup : A ^ ((3:ℕ) ^ (k + 1 + 1)) < (((mdigit A k + 1) ^ 3 : ℕ) : ℝ) := by
    rw [pow_succ_eq_cube]
    push_cast
    exact pow_lt_pow_left₀ (pow_lt_mdigit_add_one A k) (by positivity) (by norm_num)
  exact prime_add_one_lt_cube (mdigit_two_le hA k) (mdigit_prime hA (k + 1))
    ((Nat.floor_lt (by positivity)).2 hup)

/-- The digits grow at least like a tower: `p_1^(3^k) ≤ p_{k+1}`.  This is Saito (3.20). -/
theorem mdigit_pow_le {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) (k : ℕ) :
    (mdigit A 0) ^ ((3:ℕ) ^ k) ≤ mdigit A k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : (mdigit A 0) ^ ((3:ℕ) ^ (k + 1)) = ((mdigit A 0) ^ ((3:ℕ) ^ k)) ^ 3 := by
        rw [← pow_mul, show (3:ℕ) ^ k * 3 = (3:ℕ) ^ (k + 1) by ring]
      rw [h1]
      exact le_trans (Nat.pow_le_pow_left ih 3) (mdigit_cube_lt hA1 hA k).le

/-! ### The crux: Saito Lemma 3.6

The one genuinely deep obligation left.  Minimality of `ξ` plus Matomäki's Theorem 3.7 forbid
the gap `p_{k+1} − p_k³` from exceeding `p_k^(3θ) = p_k^(63/40)` for large `k`.

Saito's proof (§3, after Theorem 3.7): suppose `p_{k+1} > p_k³ + p_k^(63/40)` for arbitrarily
large `k`.  Fix such a `k`.  Baker–Harman–Pintz at `x = p_k³` says `[p_k³, p_k³ + p_k^(63/40)]`
has `≥ d₀ p_k^(63/40) / log p_k³` primes, so **Lemma 3.8** (below) hands us a prime `q_{k+1}` in
that interval whose own interval `[q³, q³ + q²]` is again prime-rich; iterating gives an
infinite chain `q_m` with `q_m³ ≤ q_{m+1} ≤ q_m³ + q_m²`, hence (glued to `p_1, …, p_k`) a Mills
number `w` whose `(k+1)`-st digit is `q_{k+1} ≤ p_k³ + p_k^(63/40) < p_{k+1}`, so `w < ξ` —
contradicting minimality.

The two named pieces this splits into are `Rich`/`saito_lemma38` and `rich_chain`. -/

/-- Matomäki's richness condition at a prime `q` (Saito (3.14) with `c ≡ 3`): the interval
`[q³, q³ + q²]` contains at least `d₁ q² / log q³` primes. -/
def Rich (d₁ : ℝ) (q : ℕ) : Prop :=
  d₁ * (q:ℝ) ^ 2 / Real.log ((q:ℝ) ^ 3) ≤ (primesIn ((q:ℝ) ^ 3) ((q:ℝ) ^ 3 + (q:ℝ) ^ 2) : ℝ)

/-- **Saito Lemma 3.8**, specialised to `c = 3`, `E = 3`, `ε = 1/4`.  A prime-rich interval
`[X, X + X^η]` (`η ∈ [1/2, 3/4]`) contains a prime `q` whose cube-interval `[q³, q³ + q²]` is
itself prime-rich.

Proof (Saito §3): if every prime `q ∈ [X, X + X^η]` had few primes in `[q³, q³ + q²]`, those
intervals — pairwise disjoint, since `q' ≥ q + 1` forces `q'³ ≥ q³ + 3q² + 3q + 1 > q³ + q²` —
would be more than the `D (X³)^(2/3 − 2/3) = D X^(1 − 3/3)` that Matomäki's Theorem 3.7 allows
inside `[X³, 2X³]`, because `d₂ X^η / log X − D X^(1 − 3/3) > 0` for large `X` (Saito (3.7)).

**OPEN.**  Needs the `Finset`-level disjointness bookkeeping to instantiate `Matomaki2007`. -/
theorem cube_rpow_two_thirds {q : ℝ} (hq : 0 < q) :
    (q ^ (3:ℕ)) ^ ((2:ℝ)/3) = q ^ (2:ℕ) := by
  rw [← Real.rpow_natCast q 3, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q 2]
  norm_num

theorem saito_lemma38 (hM : Matomaki2007) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ d₁ < 1 ∧ ∀ d₂ > (0:ℝ), ∃ X₀ : ℝ, ∀ X ≥ X₀,
      ∀ η ∈ Set.Icc (1/2 : ℝ) (3/4),
        d₂ * X ^ η / Real.log X ≤ (primesIn X (X + X ^ η) : ℝ) →
        ∃ q : ℕ, q.Prime ∧ X ≤ (q:ℝ) ∧ (q:ℝ) ≤ X + X ^ η ∧ Rich d₁ q := by
  obtain ⟨d₁, D, hd₁0, hd₁1, hD, Xm, hmat⟩ := hM
  refine ⟨d₁, hd₁0, hd₁1, fun d₂ hd₂ => ?_⟩
  refine ⟨max ((10:ℝ) ^ (4:ℕ)) (max Xm ((2 * D / d₂) ^ (4:ℕ) + 1)), fun X hX η hη hcount => ?_⟩
  have hX4 : (10:ℝ) ^ (4:ℕ) ≤ X := le_trans (le_max_left _ _) hX
  have hX10000 : (10000:ℝ) ≤ X := by norm_num at hX4; linarith
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hXpos : (0:ℝ) < X := by linarith
  have hXm : Xm ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXc : (2 * D / d₂) ^ (4:ℕ) < X := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
    linarith
  by_contra hcon
  push Not at hcon
  -- the window sits inside `[X, (11/10) X]`
  have hX14 : (10:ℝ) ≤ X ^ ((1:ℝ)/4) := by
    have h1 : ((10:ℝ) ^ (4:ℕ)) ^ ((1:ℝ)/4) = 10 := by
      rw [← Real.rpow_natCast (10:ℝ) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (10:ℝ) = ((10:ℝ) ^ (4:ℕ)) ^ ((1:ℝ)/4) := h1.symm
      _ ≤ X ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by positivity) hX4 (by norm_num)
  have hsplit : X ^ ((3:ℝ)/4) * X ^ ((1:ℝ)/4) = X := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hp34 : (0:ℝ) < X ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos hXpos _
  have hX34 : X ^ ((3:ℝ)/4) ≤ X / 10 := by nlinarith [hsplit, hX14, hp34]
  have hηle : X ^ η ≤ X ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by exact_mod_cast hη.2)
  have hwin : X + X ^ η ≤ 11/10 * X := by linarith
  have hXX : (2:ℝ) * X ^ (2:ℕ) ≤ X ^ (3:ℕ) := by nlinarith [hX10000, sq_nonneg X]
  -- the primes in the window
  set R : Finset ℕ := (Finset.Icc ⌈X⌉₊ ⌊X + X ^ η⌋₊).filter Nat.Prime with hR
  have hRcard : (R.card : ℝ) = (primesIn X (X + X ^ η) : ℝ) := by rw [hR, primesIn]
  have hmem : ∀ q ∈ R, q.Prime ∧ X ≤ (q:ℝ) ∧ (q:ℝ) ≤ X + X ^ η := by
    intro q hq
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, hp⟩ := hq
    refine ⟨hp, le_trans (Nat.le_ceil X) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))⟩
  -- transport to `Finset ℝ` of cubes
  set S : Finset ℝ := R.image (fun q : ℕ => (q:ℝ) ^ (3:ℕ)) with hS
  have hinj : Set.InjOn (fun q : ℕ => (q:ℝ) ^ (3:ℕ)) R := by
    intro q _ q' _ h
    simp only at h
    have hn : q ^ 3 = q' ^ 3 := by
      have : ((q ^ 3 : ℕ) : ℝ) = ((q' ^ 3 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact Nat.pow_left_injective (by norm_num) hn
  have hScard : S.card = R.card := Finset.card_image_of_injOn hinj
  have hSmem : ∀ n ∈ S, ∃ q ∈ R, (q:ℝ) ^ (3:ℕ) = n := by
    intro n hn
    rw [hS, Finset.mem_image] at hn
    obtain ⟨q, hqR, hqn⟩ := hn
    exact ⟨q, hqR, hqn⟩
  -- Matomäki's three hypotheses
  have hbound : ∀ n ∈ S, X ^ (3:ℕ) ≤ n ∧ n + n ^ ((2:ℝ)/3) ≤ 2 * X ^ (3:ℕ) := by
    intro n hn
    obtain ⟨q, hqR, rfl⟩ := hSmem n hn
    obtain ⟨hp, hXq, hqX⟩ := hmem q hqR
    have hq0 : (0:ℝ) < (q:ℝ) := by linarith
    rw [cube_rpow_two_thirds hq0]
    refine ⟨pow_le_pow_left₀ (by linarith) hXq 3, ?_⟩
    have hq11 : (q:ℝ) ≤ 11/10 * X := le_trans hqX hwin
    have h3 : (q:ℝ) ^ (3:ℕ) ≤ (11/10 * X) ^ (3:ℕ) := pow_le_pow_left₀ hq0.le hq11 3
    have h2 : (q:ℝ) ^ (2:ℕ) ≤ (11/10 * X) ^ (2:ℕ) := pow_le_pow_left₀ hq0.le hq11 2
    have e3 : (11/10 * X) ^ (3:ℕ) = 1331/1000 * X ^ (3:ℕ) := by ring
    have e2 : (11/10 * X) ^ (2:ℕ) = 121/100 * X ^ (2:ℕ) := by ring
    rw [e3] at h3; rw [e2] at h2
    have hX3pos : (0:ℝ) < X ^ (3:ℕ) := by positivity
    linarith
  have hdisj : (S : Set ℝ).PairwiseDisjoint (fun n => Set.Icc n (n + n ^ ((2:ℝ)/3))) := by
    have key : ∀ u v : ℕ, u ∈ R → v ∈ R → u < v →
        Disjoint (Set.Icc ((u:ℝ) ^ (3:ℕ)) ((u:ℝ) ^ (3:ℕ) + ((u:ℝ) ^ (3:ℕ)) ^ ((2:ℝ)/3)))
          (Set.Icc ((v:ℝ) ^ (3:ℕ)) ((v:ℝ) ^ (3:ℕ) + ((v:ℝ) ^ (3:ℕ)) ^ ((2:ℝ)/3))) := by
      intro u v huR hvR huv
      obtain ⟨hup, hXu, _⟩ := hmem u huR
      obtain ⟨hvp, hXv, _⟩ := hmem v hvR
      have hu0 : (0:ℝ) < (u:ℝ) := by linarith
      have hv0 : (0:ℝ) < (v:ℝ) := by linarith
      rw [cube_rpow_two_thirds hu0, cube_rpow_two_thirds hv0, Set.disjoint_left]
      intro x hx hx'
      have huv1 : (u:ℝ) + 1 ≤ (v:ℝ) := by exact_mod_cast (by omega : u + 1 ≤ v)
      have hgap : (u:ℝ) ^ (3:ℕ) + (u:ℝ) ^ (2:ℕ) < (v:ℝ) ^ (3:ℕ) := by
        have : ((u:ℝ) + 1) ^ (3:ℕ) ≤ (v:ℝ) ^ (3:ℕ) := pow_le_pow_left₀ (by linarith) huv1 3
        nlinarith [this, hu0]
      linarith [hx.2, hx'.1]
    intro a ha b hb hab
    rw [hS] at ha hb
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨u, huR, rfl⟩ := ha
    obtain ⟨v, hvR, rfl⟩ := hb
    have hne : u ≠ v := by
      intro h; rw [h] at hab; exact hab rfl
    rcases lt_or_gt_of_ne hne with h | h
    · exact key u v huR hvR h
    · exact (key v u hvR huR h).symm
  have hpoorS : ∀ n ∈ S,
      (primesIn n (n + n ^ ((2:ℝ)/3)) : ℝ) ≤ d₁ * n ^ ((2:ℝ)/3) / Real.log n := by
    intro n hn
    obtain ⟨q, hqR, rfl⟩ := hSmem n hn
    obtain ⟨hp, hXq, hqX⟩ := hmem q hqR
    have hq0 : (0:ℝ) < (q:ℝ) := by linarith
    rw [cube_rpow_two_thirds hq0]
    have hnr := hcon q hp hXq hqX
    unfold Rich at hnr
    exact le_of_lt (not_le.1 hnr)
  -- Matomäki caps the count by `D`
  have hXcube : Xm ≤ X ^ (3:ℕ) := by nlinarith [hX1, hXm]
  have hfin := hmat (X ^ (3:ℕ)) hXcube ((2:ℝ)/3) (by constructor <;> norm_num) S hbound hdisj
    hpoorS
  rw [show (2:ℝ)/3 - (2:ℝ)/3 = 0 by norm_num, Real.rpow_zero, mul_one, hScard] at hfin
  -- but the hypothesis forces it above `D`
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log X < 2 * X ^ ((1:ℝ)/4) := log_lt_two_rpow hX1
  have hηge : X ^ ((1:ℝ)/2) ≤ X ^ η :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by exact_mod_cast hη.1)
  have hsplit2 : X ^ ((1:ℝ)/2) = X ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hc0 : (0:ℝ) < 2 * D / d₂ := by positivity
  have hc4 : 2 * D / d₂ < X ^ ((1:ℝ)/4) := by
    have h1 : ((2 * D / d₂) ^ (4:ℕ)) ^ ((1:ℝ)/4) = 2 * D / d₂ := by
      rw [← Real.rpow_natCast (2 * D / d₂) 4, ← Real.rpow_mul hc0.le]
      norm_num
    calc 2 * D / d₂ = ((2 * D / d₂) ^ (4:ℕ)) ^ ((1:ℝ)/4) := h1.symm
      _ < X ^ ((1:ℝ)/4) := Real.rpow_lt_rpow (by positivity) hXc (by norm_num)
  have h14pos : (0:ℝ) < X ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hXpos _
  have h2D : 2 * D ≤ d₂ * X ^ ((1:ℝ)/4) := by
    rw [div_lt_iff₀ hd₂] at hc4
    linarith
  have hbig : D < d₂ * X ^ η / Real.log X := by
    rw [lt_div_iff₀ hlogpos]
    calc D * Real.log X < D * (2 * X ^ ((1:ℝ)/4)) := mul_lt_mul_of_pos_left hlog hD
      _ ≤ d₂ * X ^ ((1:ℝ)/2) := by rw [hsplit2]; nlinarith [h2D, h14pos]
      _ ≤ d₂ * X ^ η := mul_le_mul_of_nonneg_left hηge hd₂.le
  rw [← hRcard] at hcount
  linarith [hcount, hfin, hbig]

/-- **Saito Lemma 3.6** (specialised to `c ≡ 3`) — THE CRUX.  See the section docstring.

**OPEN.**  Route: `saito_lemma38` + the `rich_chain` induction + `Chain.exists_shifted_of_chain`
glued to `p_1, …, p_k`, then minimality of `A`. -/
theorem saito_lemma36 (hB : BakerHarmanPintz2001) (hM : Matomaki2007) {A : ℝ}
    (hA : IsMinMills A) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (mdigit A (k + 1) : ℝ) ≤ (mdigit A k : ℝ) ^ (3:ℕ) + (mdigit A k : ℝ) ^ ((63:ℝ)/40) := by
  sorry

/-! ### Saito Lemma 3.9 and the Mahler contradiction -/

/-- **Saito (3.19)**, one step: from `p_{k+1} ≤ p_k³ + p_k^(63/40)` the real `A^(3^(k+1))` sits
within `2 / p_k^(17/40)` of `p_k`.  The cube-root expansion is replaced by the elementary
`(1 + t)³ ≥ 1 + 3t`, with the slack `6 > 2` absorbing the `+1` from the floor. -/
theorem mdigit_dist_le {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) {k : ℕ}
    (h : (mdigit A (k + 1) : ℝ) ≤ (mdigit A k : ℝ) ^ (3:ℕ) + (mdigit A k : ℝ) ^ ((63:ℝ)/40)) :
    A ^ ((3:ℕ) ^ (k + 1)) - (mdigit A k : ℝ) ≤ 2 / (mdigit A k : ℝ) ^ ((17:ℝ)/40) := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  set u : ℝ := (mdigit A k : ℝ) with hu
  have hu2 : (2:ℝ) ≤ u := by rw [hu]; exact_mod_cast mdigit_two_le hA k
  have hup : (0:ℝ) < u := by linarith
  set y : ℝ := A ^ ((3:ℕ) ^ (k + 1)) with hy
  have hone : (1:ℝ) ≤ u ^ ((63:ℝ)/40) := Real.one_le_rpow (by linarith) (by norm_num)
  have hcube : y ^ (3:ℕ) ≤ u ^ (3:ℕ) + 2 * u ^ ((63:ℝ)/40) := by
    have h1 : y ^ (3:ℕ) < (mdigit A (k + 1) : ℝ) + 1 := by
      rw [hy, ← pow_succ_eq_cube]
      exact pow_lt_mdigit_add_one A (k + 1)
    linarith
  -- the elementary expansion
  have hpos57 : (0:ℝ) < u ^ ((57:ℝ)/40) := Real.rpow_pos_of_pos hup _
  have hpos17 : (0:ℝ) < u ^ ((17:ℝ)/40) := Real.rpow_pos_of_pos hup _
  have keyA : u ^ ((57:ℝ)/40) = u * u ^ ((17:ℝ)/40) := by
    rw [show ((57:ℝ)/40) = 1 + (17:ℝ)/40 by norm_num, Real.rpow_add hup, Real.rpow_one]
  have keyB : u ^ (3:ℕ) = u ^ ((63:ℝ)/40) * u ^ ((57:ℝ)/40) := by
    rw [← Real.rpow_add hup, show (63:ℝ)/40 + (57:ℝ)/40 = ((3:ℕ):ℝ) by norm_num,
      Real.rpow_natCast]
  set t : ℝ := 2 / u ^ ((57:ℝ)/40) with ht
  have ht0 : (0:ℝ) < t := by rw [ht]; positivity
  have e1 : u * (1 + t) = u + 2 / u ^ ((17:ℝ)/40) := by
    rw [ht, keyA]
    field_simp
  have e2 : u ^ (3:ℕ) * (3 * t) = 6 * u ^ ((63:ℝ)/40) := by
    rw [ht]
    nth_rewrite 1 [keyB]
    field_simp
    ring
  by_contra hcon
  push Not at hcon
  have hylt : u * (1 + t) < y := by rw [e1]; linarith
  have hu3 : (0:ℝ) ≤ u * (1 + t) := by positivity
  have hcubelt : (u * (1 + t)) ^ (3:ℕ) < y ^ (3:ℕ) := pow_lt_pow_left₀ hylt hu3 (by norm_num)
  have hexp : u ^ (3:ℕ) * (1 + 3 * t) ≤ (u * (1 + t)) ^ (3:ℕ) := by
    have h13 : (1:ℝ) + 3 * t ≤ (1 + t) ^ (3:ℕ) := by nlinarith [ht0, sq_nonneg t]
    have : u ^ (3:ℕ) * (1 + 3 * t) ≤ u ^ (3:ℕ) * (1 + t) ^ (3:ℕ) := by
      exact mul_le_mul_of_nonneg_left h13 (by positivity)
    calc u ^ (3:ℕ) * (1 + 3 * t) ≤ u ^ (3:ℕ) * (1 + t) ^ (3:ℕ) := this
      _ = (u * (1 + t)) ^ (3:ℕ) := by ring
  have : u ^ (3:ℕ) + 6 * u ^ ((63:ℝ)/40) ≤ u ^ (3:ℕ) + 2 * u ^ ((63:ℝ)/40) := by
    calc u ^ (3:ℕ) + 6 * u ^ ((63:ℝ)/40) = u ^ (3:ℕ) * (1 + 3 * t) := by rw [← e2]; ring
      _ ≤ (u * (1 + t)) ^ (3:ℕ) := hexp
      _ ≤ y ^ (3:ℕ) := hcubelt.le
      _ ≤ u ^ (3:ℕ) + 2 * u ^ ((63:ℝ)/40) := hcube
  have hpos63 : (0:ℝ) < u ^ ((63:ℝ)/40) := Real.rpow_pos_of_pos hup _
  linarith

/-- **Saito Lemma 3.9**: the digits approximate `A^(3^(k+1))` exponentially well. -/
theorem saito_lemma39 {A : ℝ} (hA1 : 1 < A) (hA : IsMills A)
    (h36 : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (mdigit A (k + 1) : ℝ) ≤ (mdigit A k : ℝ) ^ (3:ℕ) + (mdigit A k : ℝ) ^ ((63:ℝ)/40)) :
    ∃ γ > (0:ℝ), ∃ k₁ : ℕ, ∀ k ≥ k₁,
      |A ^ ((3:ℕ) ^ (k + 1)) - (mdigit A k : ℝ)| ≤ Real.exp (-(γ * ((3:ℕ) ^ (k + 1) : ℕ))) := by
  obtain ⟨k₀, h36⟩ := h36
  have hA0 : (0:ℝ) ≤ A := by linarith
  set p : ℕ := mdigit A 0 with hp
  have hp2 : 2 ≤ p := mdigit_two_le hA 0
  have hp2r : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  set L : ℝ := Real.log (p:ℝ) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hp2r
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
  refine ⟨(17/240) * L, by positivity, max k₀ 2, fun k hk => ?_⟩
  have hk0 : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  set u : ℝ := (mdigit A k : ℝ) with hu
  have hu2 : (2:ℝ) ≤ u := by rw [hu]; exact_mod_cast mdigit_two_le hA k
  have hupos : (0:ℝ) < u := by linarith
  -- the two-sided bound
  have hlo : (0:ℝ) ≤ A ^ ((3:ℕ) ^ (k + 1)) - u := by
    rw [hu]; linarith [mdigit_le_pow hA0 k]
  have hhi : A ^ ((3:ℕ) ^ (k + 1)) - u ≤ 2 / u ^ ((17:ℝ)/40) := mdigit_dist_le hA1 hA (h36 k hk0)
  rw [abs_of_nonneg hlo]
  -- tower growth turns `u^(17/40)` into `exp((17/40) 3^k L)`
  have htow : ((p ^ ((3:ℕ) ^ k) : ℕ) : ℝ) ≤ u := by
    rw [hu]; exact_mod_cast mdigit_pow_le hA1 hA k
  have hpow : ((p ^ ((3:ℕ) ^ k) : ℕ) : ℝ) ^ ((17:ℝ)/40)
      = Real.exp ((17/40) * ((3:ℕ) ^ k : ℕ) * L) := by
    push_cast
    rw [← Real.rpow_natCast (p:ℝ) ((3:ℕ) ^ k), ← Real.rpow_mul (by linarith),
      Real.rpow_def_of_pos (by linarith), hL]
    congr 1
    push_cast
    ring
  have hmono : ((p ^ ((3:ℕ) ^ k) : ℕ) : ℝ) ^ ((17:ℝ)/40) ≤ u ^ ((17:ℝ)/40) :=
    Real.rpow_le_rpow (by positivity) htow (by norm_num)
  have hdiv : 2 / u ^ ((17:ℝ)/40) ≤ 2 / Real.exp ((17/40) * ((3:ℕ) ^ k : ℕ) * L) := by
    rw [← hpow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hmono
  -- and `2 ≤ exp((17/80) 3^k L)` once `k ≥ 2`
  have h3k : (9:ℝ) ≤ ((3:ℕ) ^ k : ℕ) := by
    have : (3:ℕ) ^ 2 ≤ (3:ℕ) ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    calc (9:ℝ) = (((3:ℕ) ^ 2 : ℕ) : ℝ) := by norm_num
      _ ≤ _ := by exact_mod_cast this
  have hslack : Real.log 2 ≤ (17/80) * ((3:ℕ) ^ k : ℕ) * L := by
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    nlinarith [hL2, hLpos, h3k, Real.log_pos (show (1:ℝ) < 2 by norm_num)]
  have h2le : (2:ℝ) ≤ Real.exp ((17/80) * ((3:ℕ) ^ k : ℕ) * L) := by
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.2 hslack
  have hgoal : 2 / Real.exp ((17/40) * ((3:ℕ) ^ k : ℕ) * L)
      ≤ Real.exp (-((17/240) * L * ((3:ℕ) ^ (k + 1) : ℕ))) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    have harg : -((17/240) * L * ((3:ℕ) ^ (k + 1) : ℕ)) + (17/40) * ((3:ℕ) ^ k : ℕ) * L
        = (17/80) * ((3:ℕ) ^ k : ℕ) * L := by
      have h3 : (((3:ℕ) ^ (k + 1) : ℕ) : ℝ) = 3 * (((3:ℕ) ^ k : ℕ) : ℝ) := by
        push_cast; ring
      rw [h3]; ring
    rw [harg]
    exact h2le
  linarith [hdiv, hhi, hgoal]

/-- A Mills number is never an integer: `⌊A^(3^(k+2))⌋₊` would be the cube of `⌊A^(3^(k+1))⌋₊`,
which is not prime. -/
theorem mills_not_intCast {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) (m : ℤ) : A ≠ (m : ℝ) := by
  intro hAm
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hm1 : (1:ℤ) < m := by exact_mod_cast hAm ▸ hA1
  have hm0 : (0:ℤ) ≤ m := by omega
  set n : ℕ := m.toNat with hn
  have hmn : (m : ℝ) = (n : ℝ) := by rw [hn]; exact_mod_cast (Int.toNat_of_nonneg hm0).symm
  have hAn : A = (n : ℝ) := by rw [hAm, hmn]
  -- every `A^(3^j)` is the natural number `n^(3^j)`, so the floor is exact
  have hfl : ∀ j : ℕ, mdigit A j = n ^ ((3:ℕ) ^ (j + 1)) := by
    intro j
    rw [mdigit, hAn, show ((n:ℝ)) ^ ((3:ℕ) ^ (j + 1)) = ((n ^ ((3:ℕ) ^ (j + 1)) : ℕ) : ℝ) by
      push_cast; ring, Nat.floor_natCast]
  have hc := mdigit_cube_lt hA1 hA 0
  rw [hfl 0, hfl 1, ← pow_mul, show (3:ℕ) ^ (0 + 1) * 3 = (3:ℕ) ^ (1 + 1) by norm_num] at hc
  exact absurd hc (lt_irrefl _)

/-- **Saito (2024)**: the least Mills number is irrational, from Baker–Harman–Pintz,
Matomäki and Mahler.  Matches formal-conjectures `Mills.irrational` plus the three inputs. -/
theorem irrational (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hMa : Mahler1957)
    {A : ℝ} (hA : IsMinMills A) : Irrational A := by
  obtain ⟨⟨hA1, hAm⟩, hAmin⟩ := hA
  rintro ⟨r, hr⟩
  have hA0 : (0:ℝ) ≤ A := by linarith
  -- `A` is a rational `> 1` which is not an integer
  have hr1 : 1 < r := by
    have : ((1:ℚ) : ℝ) < ((r : ℚ) : ℝ) := by rw [hr]; exact_mod_cast hA1
    exact_mod_cast this
  have hden : r.den ≠ 1 := by
    intro h1
    have hnum : ((r.num : ℚ) : ℝ) = A := by rw [(Rat.den_eq_one_iff r).1 h1, hr]
    exact mills_not_intCast hA1 hAm r.num (by rw [← hnum]; push_cast; ring)
  -- Saito Lemma 3.9 and Mahler collide
  obtain ⟨γ, hγ, k₁, h39⟩ := saito_lemma39 hA1 hAm (saito_lemma36 hB hM ⟨⟨hA1, hAm⟩, hAmin⟩)
  obtain ⟨n₀, hMah⟩ := hMa r hr1 hden γ hγ
  -- pick `k` with `3^(k+1) ≥ n₀` and `k ≥ k₁`
  obtain ⟨k, hk1, hkn⟩ : ∃ k : ℕ, k₁ ≤ k ∧ n₀ ≤ (3:ℕ) ^ (k + 1) := by
    refine ⟨max k₁ n₀, le_max_left _ _, ?_⟩
    exact le_trans (le_trans (le_max_right k₁ n₀) (Nat.le_succ _)) (Nat.lt_pow_self (by norm_num)).le
  set N : ℕ := (3:ℕ) ^ (k + 1) with hN
  have hsmall := h39 k hk1
  have hbig := hMah N hkn
  rw [hr] at hbig
  have hround : |A ^ N - ((round (A ^ N) : ℤ) : ℝ)| ≤ |A ^ N - ((mdigit A k : ℤ) : ℝ)| :=
    round_le _ _
  have hcast : (((mdigit A k : ℤ)) : ℝ) = (mdigit A k : ℝ) := by push_cast; ring
  rw [hcast] at hround
  have : Real.exp (-(γ * N)) < Real.exp (-(γ * N)) := by
    calc Real.exp (-(γ * N)) < |A ^ N - ((round (A ^ N) : ℤ) : ℝ)| := by
          simpa [hN] using hbig
      _ ≤ |A ^ N - (mdigit A k : ℝ)| := hround
      _ ≤ Real.exp (-(γ * ((3:ℕ) ^ (k + 1) : ℕ))) := hsmall
      _ = Real.exp (-(γ * N)) := by rw [hN]
  exact absurd this (lt_irrefl _)

end LeanFormalizations.Mills
