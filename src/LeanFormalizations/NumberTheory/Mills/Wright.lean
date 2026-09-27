/-
# Wright's prime-representing power tower

E. M. Wright, *A prime-representing function*, Amer. Math. Monthly **58** (1951), 616–618:
there is a real `ω` such that, with `g 0 = ω` and `g (n+1) = 2 ^ g n`,
`⌊g n⌋` is prime for every `n ≥ 1`.  (`ω ≈ 1.9287800`, OEIS A086238.)

Unlike Mills' theorem this is **unconditional from Bertrand's postulate**
(`Nat.exists_prime_lt_and_le_two_mul`), which mathlib already has.

## Proof plan

Build primes `q 1 < q 2 < …` with `2 ^ q k < q (k+1) < 2 ^ (q k + 1)`: Bertrand at
`m = 2 ^ q k` gives a prime in `(m, 2m]`, and `2m = 2^(q k + 1)` is not prime once
`q k ≥ 1`, so the upper inequality is strict.  Pull the intervals back through the tower:
`log₂` applied `k` times to `[q k, q k + 1)` gives nested intervals `[a k, b k)` in `ω`-space
(`a` monotone, `b` antitone — this is where `2 ^ q k < q (k+1)` and `q (k+1) + 1 ≤ 2^(q k + 1)`
are used).  Take `ω := ⨆ k, a k`; then `q k ≤ tower ω k < q k + 1`.  Commit a helper for the
inverse tower (`iterate Real.logb 2`) and its monotonicity before the limit argument.
-/
import Mathlib

namespace LeanFormalizations.Mills

/-- The power tower `2^2^…^2^ω` with `n` twos. -/
noncomputable def tower (ω : ℝ) : ℕ → ℝ
  | 0 => ω
  | n + 1 => (2 : ℝ) ^ tower ω n


/-! ## The inverse tower and the nested-interval engine -/

open Real

/-- `invtower x n` is the real `ω` with `tower ω n = x`: apply `logb 2` `n` times. -/
noncomputable def invtower : ℝ → ℕ → ℝ
  | x, 0 => x
  | x, n + 1 => invtower (Real.logb 2 x) n

@[simp] lemma invtower_zero (x : ℝ) : invtower x 0 = x := rfl

lemma invtower_succ (x : ℝ) (n : ℕ) :
    invtower x (n + 1) = invtower (Real.logb 2 x) n := rfl

lemma one_le_tower_one (n : ℕ) : 1 ≤ tower 1 n := by
  induction n with
  | zero => simp [tower]
  | succ n ih =>
      have : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ tower 1 n :=
        Real.rpow_le_rpow_left_iff (x := 2) (by norm_num) |>.2 (by linarith)
      simpa [tower] using this

lemma tower_one_pos (n : ℕ) : 0 < tower 1 n := lt_of_lt_of_le one_pos (one_le_tower_one n)

/-- The base-2 logarithm turns the tower bound `tower 1 (n+1) < x` into `tower 1 n < logb 2 x`. -/
lemma tower_lt_logb {n : ℕ} {x : ℝ} (h : tower 1 (n + 1) < x) :
    tower 1 n < Real.logb 2 x := by
  have hx : 0 < x := lt_trans (tower_one_pos _) h
  have hb : (1 : ℝ) < 2 := by norm_num
  have : (2 : ℝ) ^ tower 1 n < (2 : ℝ) ^ Real.logb 2 x := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) hx]
    simpa [tower] using h
  exact (Real.rpow_lt_rpow_left_iff hb).1 this

lemma lt_logb_two_iff {c x : ℝ} (hx : 0 < x) :
    c < Real.logb 2 x ↔ (2 : ℝ) ^ c < x := by
  constructor
  · intro h
    calc (2:ℝ) ^ c < (2:ℝ) ^ Real.logb 2 x :=
          (Real.rpow_lt_rpow_left_iff (by norm_num)).2 h
      _ = x := Real.rpow_logb (by norm_num) (by norm_num) hx
  · intro h
    have : (2:ℝ) ^ c < (2:ℝ) ^ Real.logb 2 x := by
      rwa [Real.rpow_logb (by norm_num) (by norm_num) hx]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).1 this

/-- `invtower` really inverts `tower`, as soon as `x` clears the `n`-th tower of twos. -/
lemma tower_invtower : ∀ (n : ℕ) (x : ℝ), tower 1 n < x → tower (invtower x n) n = x := by
  intro n
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
      intro x hx
      have hx0 : 0 < x := lt_trans (tower_one_pos _) hx
      have hlog : tower 1 n < Real.logb 2 x := tower_lt_logb hx
      have := ih _ hlog
      rw [invtower_succ]
      show (2 : ℝ) ^ tower (invtower (Real.logb 2 x) n) n = x
      rw [this, Real.rpow_logb (by norm_num) (by norm_num) hx0]

lemma invtower_lt_invtower : ∀ (n : ℕ) (x y : ℝ), tower 1 n < x → x < y →
    invtower x n < invtower y n := by
  intro n
  induction n with
  | zero => intro x y _ h; exact h
  | succ n ih =>
      intro x y hx hxy
      have hx0 : 0 < x := lt_trans (tower_one_pos _) hx
      have hlx : tower 1 n < Real.logb 2 x := tower_lt_logb hx
      have : Real.logb 2 x < Real.logb 2 y := Real.logb_lt_logb (by norm_num) hx0 hxy
      simpa [invtower_succ] using ih _ _ hlx this

/-- `tower · n` is strictly monotone in the seed. -/
lemma tower_strictMono (n : ℕ) : StrictMono (fun ω : ℝ => tower ω n) := by
  induction n with
  | zero => intro a b h; exact h
  | succ n ih =>
      intro a b h
      have := ih h
      simpa [tower] using (Real.rpow_lt_rpow_left_iff (x := 2) (by norm_num)).2 this

/-! ## The Bertrand step -/

/-- From a prime `q ≥ 2`, Bertrand's postulate applied at `2^q - 1` yields a prime `p` with
`2^q < p` **and** the strict upper bound `p + 1 < 2^(q+1)`.  Applying Bertrand one below `2^q`
is what buys the strictness: it is needed to keep the nested intervals from degenerating. -/
lemma wright_step {q : ℕ} (hq : 2 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ 2 ^ q < p ∧ p + 1 < 2 ^ (q + 1) := by
  have hM : 4 ≤ 2 ^ q := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ q - 1) (by omega)
  have hne : p ≠ 2 ^ q := by
    intro h
    have hpow : ¬ (Nat.Prime (2 ^ q)) := by
      intro hP
      rcases (hP.eq_one_or_self_of_dvd 2 (dvd_pow_self 2 (by omega))) with h1 | h2
      · omega
      · omega
    exact hpow (h ▸ hp)
  refine ⟨p, hp, by omega, ?_⟩
  have : 2 ^ (q + 1) = 2 * 2 ^ q := by ring
  omega

/-- The prime sequence: `2, p₁, p₂, …` with `2 ^ qseq n < qseq (n+1)` and
`qseq (n+1) + 1 < 2 ^ (qseq n + 1)`. -/
noncomputable def nextWrightPrime (q : ℕ) : ℕ :=
  if h : 2 ≤ q then (wright_step h).choose else 2

noncomputable def qseq : ℕ → ℕ
  | 0 => 2
  | n + 1 => nextWrightPrime (qseq n)

lemma qseq_prime : ∀ n, (qseq n).Prime := by
  intro n
  induction n with
  | zero => exact Nat.prime_two
  | succ n ih =>
      have h2 : 2 ≤ qseq n := ih.two_le
      show (nextWrightPrime (qseq n)).Prime
      rw [nextWrightPrime, dif_pos h2]
      exact (wright_step h2).choose_spec.1

lemma qseq_two_le (n : ℕ) : 2 ≤ qseq n := (qseq_prime n).two_le

lemma qseq_lower (n : ℕ) : 2 ^ qseq n < qseq (n + 1) := by
  have h2 : 2 ≤ qseq n := qseq_two_le n
  show 2 ^ qseq n < nextWrightPrime (qseq n)
  rw [nextWrightPrime, dif_pos h2]
  exact (wright_step h2).choose_spec.2.1

lemma qseq_upper (n : ℕ) : qseq (n + 1) + 1 < 2 ^ (qseq n + 1) := by
  have h2 : 2 ≤ qseq n := qseq_two_le n
  show nextWrightPrime (qseq n) + 1 < 2 ^ (qseq n + 1)
  rw [nextWrightPrime, dif_pos h2]
  exact (wright_step h2).choose_spec.2.2

/-! ## The nested intervals -/

lemma tower_one_lt_qseq (n : ℕ) : tower 1 n < (qseq n : ℝ) := by
  induction n with
  | zero => simp [tower]; exact_mod_cast (by norm_num : (1:ℝ) < 2)
  | succ n ih =>
      have h1 : (2:ℝ) ^ tower 1 n < (2:ℝ) ^ ((qseq n : ℕ) : ℝ) :=
        (Real.rpow_lt_rpow_left_iff (by norm_num)).2 ih
      have h2 : (2:ℝ) ^ ((qseq n : ℕ) : ℝ) = ((2 ^ qseq n : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; ring
      have h3 : ((2 ^ qseq n : ℕ) : ℝ) < (qseq (n+1) : ℝ) := by
        exact_mod_cast qseq_lower n
      calc tower 1 (n+1) = (2:ℝ) ^ tower 1 n := rfl
        _ < (2:ℝ) ^ ((qseq n : ℕ) : ℝ) := h1
        _ = ((2 ^ qseq n : ℕ) : ℝ) := h2
        _ < (qseq (n+1) : ℝ) := h3

noncomputable def wa (n : ℕ) : ℝ := invtower (qseq n : ℝ) n
noncomputable def wb (n : ℕ) : ℝ := invtower ((qseq n : ℝ) + 1) n

lemma wa_lt_wb (n : ℕ) : wa n < wb n :=
  invtower_lt_invtower n _ _ (tower_one_lt_qseq n) (by linarith)

lemma wa_lt_succ (n : ℕ) : wa n < wa (n + 1) := by
  have hpos : (0:ℝ) < (qseq (n+1) : ℝ) := lt_trans (tower_one_pos _) (tower_one_lt_qseq _)
  have key : ((qseq n : ℕ) : ℝ) < Real.logb 2 ((qseq (n+1) : ℕ) : ℝ) := by
    rw [lt_logb_two_iff hpos, Real.rpow_natCast]
    exact_mod_cast qseq_lower n
  have := invtower_lt_invtower n ((qseq n : ℕ) : ℝ) (Real.logb 2 ((qseq (n+1) : ℕ) : ℝ))
    (tower_one_lt_qseq n) key
  simpa [wa, invtower_succ] using this

lemma wb_succ_lt (n : ℕ) : wb (n + 1) < wb n := by
  have hpos : (0:ℝ) < (qseq (n+1) : ℝ) + 1 := by
    have := tower_one_pos (n+1); have := tower_one_lt_qseq (n+1); linarith
  have key : Real.logb 2 ((qseq (n+1) : ℝ) + 1) < (qseq n : ℝ) + 1 := by
    have h : Real.logb 2 ((qseq (n+1) : ℝ) + 1) < Real.logb 2 ((2 ^ (qseq n + 1) : ℕ) : ℝ) := by
      apply Real.logb_lt_logb (by norm_num) hpos
      have : ((qseq (n+1) + 1 : ℕ) : ℝ) < ((2 ^ (qseq n + 1) : ℕ) : ℝ) := by
        exact_mod_cast qseq_upper n
      push_cast at this ⊢; linarith
    have h2 : Real.logb 2 ((2 ^ (qseq n + 1) : ℕ) : ℝ) = (qseq n : ℝ) + 1 := by
      have hcast : ((2 ^ (qseq n + 1) : ℕ) : ℝ) = (2:ℝ) ^ ((qseq n : ℝ) + 1) := by
        rw [show ((qseq n : ℝ) + 1) = ((qseq n + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        push_cast; ring
      rw [hcast, Real.logb_rpow (b := 2) (by norm_num) (by norm_num)]
    linarith [h, h2.le, h2.ge]
  have hlow : tower 1 n < Real.logb 2 ((qseq (n+1) : ℝ) + 1) := by
    apply tower_lt_logb
    have := tower_one_lt_qseq (n+1); linarith
  have := invtower_lt_invtower n (Real.logb 2 ((qseq (n+1) : ℝ) + 1)) ((qseq n : ℝ) + 1) hlow key
  simpa [wb, invtower_succ] using this

lemma wa_mono : Monotone wa := monotone_nat_of_le_succ fun n => (wa_lt_succ n).le
lemma wb_anti : Antitone wb := antitone_nat_of_succ_le fun n => (wb_succ_lt n).le

lemma wa_le_wb (m n : ℕ) : wa m ≤ wb n := by
  rcases le_total m n with h | h
  · exact le_trans (wa_mono h) (wa_lt_wb n).le
  · exact le_trans (wa_lt_wb m).le (wb_anti h)

lemma wa_bddAbove : BddAbove (Set.range wa) := ⟨wb 0, by rintro _ ⟨m, rfl⟩; exact wa_le_wb m 0⟩

/-! ## Wright's theorem -/

theorem wright : ∃ ω : ℝ, ∀ n : ℕ, 1 ≤ n → (⌊tower ω n⌋₊).Prime := by
  set ω : ℝ := ⨆ n, wa n with hω
  refine ⟨ω, fun n _ => ?_⟩
  have hlo : wa n < ω := lt_of_lt_of_le (wa_lt_succ n) (le_ciSup wa_bddAbove (n+1))
  have hhi : ω ≤ wb (n + 1) := ciSup_le fun m => wa_le_wb m (n+1)
  have hhi' : ω < wb n := lt_of_le_of_lt hhi (wb_succ_lt n)
  have e1 : tower (wa n) n = (qseq n : ℝ) := tower_invtower n _ (tower_one_lt_qseq n)
  have e2 : tower (wb n) n = (qseq n : ℝ) + 1 :=
    tower_invtower n _ (by have := tower_one_lt_qseq n; linarith)
  have h1 : (qseq n : ℝ) < tower ω n := by rw [← e1]; exact tower_strictMono n hlo
  have h2 : tower ω n < (qseq n : ℝ) + 1 := by rw [← e2]; exact tower_strictMono n hhi'
  have : ⌊tower ω n⌋₊ = qseq n := by
    have hnn : (0:ℝ) ≤ tower ω n := le_trans (Nat.cast_nonneg (qseq n)) h1.le
    rw [Nat.floor_eq_iff hnn]
    constructor
    · exact_mod_cast h1.le
    · exact h2
  rw [this]
  exact qseq_prime n


end LeanFormalizations.Mills
