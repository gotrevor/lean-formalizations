/-
# Saito §3 for a general exponent `c`: the digit estimates

The `c`-general analogue of the `mdigit` section of `Mills/Irrational.lean`.  What it delivers
is the single hypothesis `transcendental_of_decay` (`Mills/SaitoLemma41.lean`) needs:

    |A^(cᵏ) − round(A^(cᵏ))| ≤ K · A^(−μ cᵏ)   for all large `k`,   μ = 19c/40 − 1.

## A shortcut worth recording

Saito derives (3.17) `|ξ^(C_k) − p_k| ≤ e^(−γC_k)` and only then, in §4, re-derives the finer
`K₁ ξ^(−θ_b C_{k+1})` bound.  For **transcendence** the exponential form is never used — it is
the *finer* bound that feeds Dubickas.  And that finer bound drops straight out of the
elementary expansion, with no logarithms at all:

* `(3.19)` with the Bernoulli inequality `(1+t)ᶜ ≥ 1 + ct` at `t = 2/pₖ^(19c/40)` gives
  `A^(c^(k+1)) − pₖ ≤ 2·pₖ^(1 − 19c/40) = 2/pₖ^μ`;
* `A^(c^(k+1)) < pₖ + 1 ≤ 2pₖ`, so `pₖ^μ > A^(μ c^(k+1))/2^μ`, i.e. the bound is
  `2^(μ+1)·A^(−μ c^(k+1))` — exactly the shape of Dubickas's input, with `K = 2^(μ+1)`.

So the whole `Real.log`/`exp` apparatus of `saito_lemma39` is bypassed on the transcendence
route.  (It is still needed for *irrationality*, where Mahler's theorem wants `e^(−εn)`.)

## What is open

Nothing in this file: it is sorry-free.  `saito_lemma36C` — Saito's Lemma 3.6 for general `c`, the
minimality step — is **proved**, conditionally on the frozen `BakerHarmanPintz2001` and
`Matomaki2007` hypotheses (primes in short intervals), which it takes as explicit arguments.
Those two `Prop`s are the remaining literature debt of the `c ≥ 4` case of Theorem 1.1; see
`PENDING_WORK.md`.
-/
import LeanFormalizations.NumberTheory.Mills.BasicC
import LeanFormalizations.NumberTheory.Mills.SaitoLemma41
import LeanFormalizations.NumberTheory.Mills.SaitoDegreeTwo
import LeanFormalizations.NumberTheory.Mills.ChainC
import LeanFormalizations.NumberTheory.Mills.SaitoRich
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- The digits of a Mills number for exponent `c`: `mdigitC c A k = ⌊A^(c^(k+1))⌋₊`. -/
noncomputable def mdigitC (c : ℕ) (A : ℝ) (k : ℕ) : ℕ := ⌊A ^ (c ^ (k + 1))⌋₊

variable {c : ℕ} {A : ℝ}

theorem mdigitC_prime (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) :
    (mdigitC c A k).Prime := by
  have := hA ⟨k + 1, by omega⟩
  simpa [mdigitC] using Nat.prime_iff.2 this

theorem mdigitC_two_le (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) :
    2 ≤ mdigitC c A k := (mdigitC_prime hA k).two_le

theorem mdigitC_le_pow (hA0 : 0 ≤ A) (k : ℕ) :
    (mdigitC c A k : ℝ) ≤ A ^ (c ^ (k + 1)) := Nat.floor_le (by positivity)

theorem pow_lt_mdigitC_add_one (A : ℝ) (k : ℕ) :
    A ^ (c ^ (k + 1)) < (mdigitC c A k : ℝ) + 1 := Nat.lt_floor_add_one _

theorem pow_succ_eq_powC (A : ℝ) (c k : ℕ) :
    A ^ (c ^ (k + 1 + 1)) = (A ^ (c ^ (k + 1))) ^ c := by
  rw [show c ^ (k + 1 + 1) = c ^ (k + 1) * c by ring, pow_mul]

/-- **Saito Lemma 3.5** for exponent `c`, lower half: `p_kᶜ < p_{k+1}`. -/
theorem mdigitC_pow_lt (hc : 2 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) :
    (mdigitC c A k) ^ c < mdigitC c A (k + 1) := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hpow : ((mdigitC c A k ^ c : ℕ) : ℝ) ≤ A ^ (c ^ (k + 1 + 1)) := by
    rw [pow_succ_eq_powC]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (mdigitC_le_pow hA0 k) c
  have hfloor : mdigitC c A k ^ c ≤ mdigitC c A (k + 1) := Nat.le_floor hpow
  refine lt_of_le_of_ne hfloor ?_
  intro hEq
  have hp := mdigitC_prime hA (k + 1)
  rw [← hEq] at hp
  have h2c := mdigitC_two_le hA k
  rcases hp.eq_one_or_self_of_dvd (mdigitC c A k) (dvd_pow_self _ (by omega)) with h | h
  · omega
  · have hlt : (mdigitC c A k) ^ 1 < (mdigitC c A k) ^ c := Nat.pow_lt_pow_right h2c (by omega)
    rw [pow_one, ← h] at hlt
    exact absurd hlt (lt_irrefl _)

/-- **Saito Lemma 3.5** for exponent `c`, upper half: `p_{k+1} < (p_k + 1)ᶜ − 1`. -/
theorem mdigitC_succ_lt (hc : 2 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) :
    mdigitC c A (k + 1) + 1 < (mdigitC c A k + 1) ^ c := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hup : A ^ (c ^ (k + 1 + 1)) < (((mdigitC c A k + 1) ^ c : ℕ) : ℝ) := by
    rw [pow_succ_eq_powC]
    push_cast
    exact pow_lt_pow_left₀ (pow_lt_mdigitC_add_one A k) (by positivity) (by omega)
  exact prime_add_one_lt_pow (mdigitC_two_le hA k) hc (mdigitC_prime hA (k + 1))
    ((Nat.floor_lt (by positivity)).2 hup)

/-- The digits grow at least like a tower: `p_1^(c^k) ≤ p_{k+1}`.  Saito (3.20) for general `c`. -/
theorem mdigitC_pow_le (hc : 2 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) :
    (mdigitC c A 0) ^ (c ^ k) ≤ mdigitC c A k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : (mdigitC c A 0) ^ (c ^ (k + 1)) = ((mdigitC c A 0) ^ (c ^ k)) ^ c := by
        rw [← pow_mul, show c ^ k * c = c ^ (k + 1) by ring]
      rw [h1]
      exact le_trans (Nat.pow_le_pow_left ih c) (mdigitC_pow_lt hc hA1 hA k).le

/-- `k < p_{k+1}`: the digits outgrow their index. -/
theorem lt_mdigitC (hc : 2 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (k : ℕ) : k < mdigitC c A k := by
  have h1 : k < 2 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : (2:ℕ) ^ k ≤ 2 ^ (c ^ k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.lt_pow_self (by omega)).le
  have h3 : (2:ℕ) ^ (c ^ k) ≤ (mdigitC c A 0) ^ (c ^ k) :=
    Nat.pow_le_pow_left (mdigitC_two_le hA 0) _
  exact lt_of_lt_of_le h1 (le_trans h2 (le_trans h3 (mdigitC_pow_le hc hA1 hA k)))

/-- `(pᶜ)^(21/40) = p^(21c/40)`: the Baker–Harman–Pintz window above `pᶜ`, re-expressed. -/
theorem rpow_pow_21_40 {p : ℝ} (hp : 0 < p) (c : ℕ) :
    (p ^ c) ^ ((21:ℝ)/40) = p ^ ((21 * (c:ℝ))/40) := by
  rw [← Real.rpow_natCast p c, ← Real.rpow_mul hp.le]
  congr 1
  ring

/-- `p^(21c/40) ≤ p^(c−1)` for `p ≥ 2`, `c ≥ 3`: the Baker–Harman–Pintz window fits inside the
Matomäki window, which is what lets one chain step feed the next. -/
theorem rpow_21_40_le_rpow_sub_one {p : ℝ} (hp : 2 ≤ p) (hc : 3 ≤ c) :
    p ^ ((21 * (c:ℝ))/40) ≤ p ^ ((c:ℝ) - 1) := by
  have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  linarith

/-! ### The crux: Saito Lemma 3.6 for exponent `c` -/

/-- **Saito (2024), Lemma 3.6, for general `c` — OPEN.**

For `ξ_c` the *least* Mills number of exponent `c`, the gap `p_{k+1} − p_kᶜ` cannot exceed
`p_k^(21c/40)` for large `k`.  Saito's proof: if it did for arbitrarily large `k`, then
Baker–Harman–Pintz makes `[p_kᶜ, p_kᶜ + p_k^(21c/40)]` prime-rich, Lemma 3.8 (Matomäki) hands
back a prime `q` in it whose own window is again rich, and iterating builds a Mills number
`w < ξ_c` — contradicting minimality.

The `c = 3` case is proved as `saito_lemma36` in `Mills/Irrational.lean`; this is the same
argument with `3` replaced by `c` throughout (`Rich`, `saito_lemma38`, `rich_chain` and
`Chain.exists_shifted_of_chain` all generalise verbatim, the exponent `2/3` of Lemma 3.8
becoming `(c−1)/c`). -/
theorem saito_lemma36C (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hc : 3 ≤ c)
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (c ^ (n : ℕ))⌋₊} A) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (mdigitC c A (k + 1) : ℝ)
        ≤ (mdigitC c A k : ℝ) ^ c + (mdigitC c A k : ℝ) ^ ((21 * (c:ℝ))/40) := by
  obtain ⟨⟨hA1, hAm⟩, hAmin⟩ := hA
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hc2 : 2 ≤ c := by omega
  obtain ⟨d₁, hd₁0, hd₁1, h38⟩ := saito_lemma38C hM hc
  obtain ⟨d₀, hd₀, Xb, hbhp⟩ := hB
  set d₂ : ℝ := min d₀ d₁ with hd₂def
  have hd₂ : (0:ℝ) < d₂ := lt_min hd₀ hd₁0
  obtain ⟨X₀, h38'⟩ := h38 d₂ hd₂
  set M : ℝ := max X₀ Xb with hMdef
  have hηmem : etaC c ∈ Set.Icc (1/2 : ℝ) (etaC c) := ⟨(etaC_mem_Icc hc).1, le_rfl⟩
  have hηbhp : (21:ℝ)/40 ∈ Set.Icc (1/2 : ℝ) (etaC c) := by
    refine ⟨by norm_num, ?_⟩
    have hc3 : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have hcpos : (0:ℝ) < (c:ℝ) := by linarith
    have h : 1/(c:ℝ) ≤ 1/3 := by rw [div_le_div_iff₀ hcpos (by norm_num)]; linarith
    rw [etaC]; linarith
  /- **The rich-prime step.**  `RichC c d₁ q` is literally the hypothesis of Lemma 3.8 at
  `X = qᶜ`, `η = 1 − 1/c`, `d₂ ≤ d₁` — so one application iterates the chain. -/
  have hstep : ∀ q : ℕ, q.Prime → X₀ ≤ (q:ℝ) → RichC c d₁ q →
      ∃ q' : ℕ, q'.Prime ∧ X₀ ≤ (q':ℝ) ∧ RichC c d₁ q' ∧ q ^ c ≤ q' ∧
        (q':ℝ) ≤ (q:ℝ) ^ c + (q:ℝ) ^ ((c:ℝ) - 1) := by
    intro q hq hX₀q hrich
    have hq2r : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.two_le
    have hq0 : (0:ℝ) < (q:ℝ) := by linarith
    have hqq : (q:ℝ) ≤ (q:ℝ) ^ c := by
      have h := pow_le_pow_right₀ (show (1:ℝ) ≤ (q:ℝ) by linarith) (show 1 ≤ c by omega)
      rwa [pow_one] at h
    have hXqc : X₀ ≤ (q:ℝ) ^ c := le_trans hX₀q hqq
    have hfeed : d₂ * ((q:ℝ) ^ c) ^ (etaC c) / Real.log ((q:ℝ) ^ c)
        ≤ (primesIn ((q:ℝ) ^ c) ((q:ℝ) ^ c + ((q:ℝ) ^ c) ^ (etaC c)) : ℝ) := by
      rw [rpow_pow_etaC hc hq0]
      unfold RichC at hrich
      refine le_trans ?_ hrich
      refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by nlinarith [hqq]))
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hq0.le _)
    obtain ⟨q', hq'p, hlo, hhi, hrich'⟩ := h38' ((q:ℝ) ^ c) hXqc (etaC c) hηmem hfeed
    rw [rpow_pow_etaC hc hq0] at hhi
    have hle : q ^ c ≤ q' := by
      have hcast : ((q ^ c : ℕ) : ℝ) ≤ ((q' : ℕ) : ℝ) := by push_cast; exact hlo
      exact_mod_cast hcast
    exact ⟨q', hq'p, le_trans hX₀q (le_trans hqq hlo), hrich', hle, hhi⟩
  -- totalise for `choose`
  have hstep' : ∀ q : ℕ, ∃ q' : ℕ, q.Prime → X₀ ≤ (q:ℝ) → RichC c d₁ q →
      q'.Prime ∧ X₀ ≤ (q':ℝ) ∧ RichC c d₁ q' ∧ q ^ c ≤ q' ∧
        (q':ℝ) ≤ (q:ℝ) ^ c + (q:ℝ) ^ ((c:ℝ) - 1) := by
    intro q
    by_cases h : q.Prime ∧ X₀ ≤ (q:ℝ) ∧ RichC c d₁ q
    · obtain ⟨q', h'⟩ := hstep q h.1 h.2.1 h.2.2
      exact ⟨q', fun _ _ _ => h'⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose F hF using hstep'
  refine ⟨⌈M⌉₊, fun k hk => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `p = p_{k+1}` in Saito's indexing
  set p : ℕ := mdigitC c A k with hpdef
  have hp2 : 2 ≤ p := mdigitC_two_le hAm k
  have hp2r : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hpM : M ≤ (p:ℝ) := by
    have h1 : (⌈M⌉₊ : ℝ) ≤ (p:ℝ) := by
      exact_mod_cast le_trans hk (lt_mdigitC hc2 hA1 hAm k).le
    exact le_trans (Nat.le_ceil M) h1
  have hpp : (p:ℝ) ≤ (p:ℝ) ^ c := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ (p:ℝ) by linarith) (show 1 ≤ c by omega)
    rwa [pow_one] at h
  have hX₀p : X₀ ≤ (p:ℝ) ^ c := le_trans (le_trans (le_max_left _ _) hpM) hpp
  have hXbp : Xb ≤ (p:ℝ) ^ c := le_trans (le_trans (le_max_right _ _) hpM) hpp
  -- Baker–Harman–Pintz at `x = pᶜ` feeds Lemma 3.8 with `η = 21/40`
  have hbhp' := hbhp ((p:ℝ) ^ c) hXbp
  have hfeed1 : d₂ * ((p:ℝ) ^ c) ^ ((21:ℝ)/40) / Real.log ((p:ℝ) ^ c)
      ≤ (primesIn ((p:ℝ) ^ c) ((p:ℝ) ^ c + ((p:ℝ) ^ c) ^ ((21:ℝ)/40)) : ℝ) := by
    refine le_trans ?_ hbhp'
    refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by nlinarith [hpp]))
    exact mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (by positivity) _)
  obtain ⟨q₁, hq₁p, hq₁lo, hq₁hi, hq₁r⟩ :=
    h38' ((p:ℝ) ^ c) hX₀p ((21:ℝ)/40) hηbhp hfeed1
  rw [rpow_pow_21_40 hp0 c] at hq₁hi
  have hq₁X₀ : X₀ ≤ (q₁:ℝ) := le_trans hX₀p hq₁lo
  have hq₁ge : p ^ c ≤ q₁ := by
    have hcast : ((p ^ c : ℕ) : ℝ) ≤ ((q₁ : ℕ) : ℝ) := by push_cast; exact hq₁lo
    exact_mod_cast hcast
  -- the chain of rich primes
  set ch : ℕ → ℕ := fun n => Nat.rec q₁ (fun _ prev => F prev) n with hchdef
  have hchsucc : ∀ n, ch (n + 1) = F (ch n) := fun _ => rfl
  have hchgood : ∀ n, (ch n).Prime ∧ X₀ ≤ (ch n : ℝ) ∧ RichC c d₁ (ch n) := by
    intro n
    induction n with
    | zero => exact ⟨hq₁p, hq₁X₀, hq₁r⟩
    | succ n ih =>
        have := hF (ch n) ih.1 ih.2.1 ih.2.2
        rw [hchsucc n]
        exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hchbound : ∀ n, (ch n) ^ c ≤ ch (n + 1) ∧
      (ch (n + 1) : ℝ) ≤ (ch n : ℝ) ^ c + (ch n : ℝ) ^ ((c:ℝ) - 1) := by
    intro n
    have ih := hchgood n
    have := hF (ch n) ih.1 ih.2.1 ih.2.2
    rw [hchsucc n]
    exact ⟨this.2.2.2.1, this.2.2.2.2⟩
  -- the `ℕ`-level window bound, for the chain condition
  have hchnat : ∀ n, ch (n + 1) ≤ (ch n) ^ c + (ch n) ^ (c - 1) := by
    intro n
    have h0 : (0:ℝ) < (ch n : ℝ) := by
      have := (hchgood n).1.two_le
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
    have h := (hchbound n).2
    rw [rpow_sub_one_eq_pow (by omega) h0] at h
    have : ((ch (n + 1) : ℕ) : ℝ) ≤ (((ch n) ^ c + (ch n) ^ (c - 1) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- glue `p_1, …, p_{k+1}` in front of the chain
  set b : ℕ → ℕ := fun m => if m ≤ k then mdigitC c A m else ch (m - k - 1) with hbdef
  have hb_le : ∀ m, m ≤ k → b m = mdigitC c A m := by
    intro m h; rw [hbdef]; simp only [if_pos h]
  have hb_gt : ∀ j, b (k + 1 + j) = ch j := by
    intro j
    rw [hbdef]
    simp only [if_neg (by omega : ¬ (k + 1 + j ≤ k))]
    congr 1
    omega
  have hb_k1 : b (k + 1) = q₁ := by
    have h0 : k + 1 - k - 1 = 0 := by omega
    rw [hbdef]
    simp only [if_neg (by omega : ¬ (k + 1 ≤ k)), h0]
    try rfl
  have hb_gt' : ∀ j, b (k + 1 + j + 1) = ch (j + 1) := by
    intro j
    have h := hb_gt (j + 1)
    rwa [show k + 1 + (j + 1) = k + 1 + j + 1 by omega] at h
  have hbprime : ∀ m, (b m).Prime := by
    intro m
    rcases le_or_gt m k with h | h
    · rw [hb_le m h]; exact mdigitC_prime hAm m
    · obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
      rw [hb_gt j]; exact (hchgood j).1
  have hb2 : ∀ m, 2 ≤ b m := fun m => (hbprime m).two_le
  -- `q₁ ≤ pᶜ + p^(c−1)` at the `ℕ` level, via `p^(21c/40) ≤ p^(c−1)`
  have hq₁nat : q₁ ≤ p ^ c + p ^ (c - 1) := by
    have h1 : (q₁:ℝ) ≤ (p:ℝ) ^ c + (p:ℝ) ^ ((c:ℝ) - 1) :=
      le_trans hq₁hi (by linarith [rpow_21_40_le_rpow_sub_one hp2r hc])
    rw [rpow_sub_one_eq_pow (by omega) hp0] at h1
    have : ((q₁:ℕ):ℝ) ≤ ((p ^ c + p ^ (c - 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hchain_lo : ∀ m, (b m) ^ c < b (m + 1) := by
    intro m
    rcases lt_trichotomy m k with h | h | h
    · rw [hb_le m h.le, hb_le (m + 1) (by omega)]
      exact mdigitC_pow_lt hc2 hA1 hAm m
    · rw [h, hb_le k le_rfl, hb_k1]
      exact pow_lt_of_prime hp2 hc2 hq₁p hq₁ge
    · obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
      rw [hb_gt j, hb_gt' j]
      exact pow_lt_of_prime (hchgood j).1.two_le hc2 (hchgood (j + 1)).1 (hchbound j).1
  have hchain_hi : ∀ m, b (m + 1) + 1 < (b m + 1) ^ c := by
    intro m
    rcases lt_trichotomy m k with h | h | h
    · rw [hb_le m h.le, hb_le (m + 1) (by omega)]
      exact mdigitC_succ_lt hc2 hA1 hAm m
    · rw [h, hb_le k le_rfl, hb_k1, ← hpdef]
      exact succ_lt_add_one_pow hp2 hc hq₁nat
    · obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
      rw [hb_gt j, hb_gt' j]
      exact succ_lt_add_one_pow (hchgood j).1.two_le hc (hchnat j)
  -- the resulting Mills number of exponent `c` undercuts `A`
  obtain ⟨w, hw1, hwfl⟩ := exists_shifted_of_chainC hc2 (hb2 0) hchain_lo hchain_hi
  have hwmills : ∀ n : ℕ+, Prime ⌊w ^ (c ^ (n : ℕ))⌋₊ := by
    intro n
    obtain ⟨m, hm⟩ : ∃ m, (n:ℕ) = m + 1 :=
      ⟨(n:ℕ).pred, (Nat.succ_pred_eq_of_pos n.pos).symm⟩
    rw [hm, hwfl m]
    exact (hbprime m).prime
  have hAw : A ≤ w := hAmin ⟨hw1, hwmills⟩
  have hdig : mdigitC c A (k + 1) ≤ b (k + 1) := by
    have hpow : A ^ (c ^ (k + 1 + 1)) ≤ w ^ (c ^ (k + 1 + 1)) := pow_le_pow_left₀ hA0 hAw _
    calc mdigitC c A (k + 1) = ⌊A ^ (c ^ (k + 1 + 1))⌋₊ := rfl
      _ ≤ ⌊w ^ (c ^ (k + 1 + 1))⌋₊ := Nat.floor_le_floor hpow
      _ = b (k + 1) := hwfl (k + 1)
  rw [hb_k1] at hdig
  have hq₁lt : (q₁:ℝ) < (mdigitC c A (k + 1) : ℝ) := lt_of_le_of_lt hq₁hi hcon
  have : (q₁:ℕ) < mdigitC c A (k + 1) := by exact_mod_cast hq₁lt
  omega

/-! ### (3.19): the elementary expansion, in the form Dubickas wants -/

/-- The core inequality of Saito (3.19), stated for bare reals: if `yᶜ ≤ uᶜ + 2u^(21c/40)` with
`u ≥ 2`, `y > 0` and `c ≥ 3`, then `y ≤ u + 2·u^(1 − 19c/40)`.  Bernoulli's inequality
`(1+t)ᶜ ≥ 1 + ct` at `t = 2/u^(19c/40)` gives `6u^(21c/40)` of room where `2u^(21c/40)` is
needed. -/
theorem le_add_rpow_of_pow_le {u y : ℝ} (hc : 3 ≤ c) (hu : 2 ≤ u) (hy : 0 < y)
    (h : y ^ c ≤ u ^ c + 2 * u ^ ((21 * (c:ℝ))/40)) :
    y ≤ u + 2 * u ^ (1 - (19 * (c:ℝ))/40) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hcR : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  set t : ℝ := 2 / u ^ ((19 * (c:ℝ))/40) with ht
  have hpos19 : (0:ℝ) < u ^ ((19 * (c:ℝ))/40) := Real.rpow_pos_of_pos hu0 _
  have ht0 : (0:ℝ) < t := by rw [ht]; positivity
  -- `u (1 + t) = u + 2 u^(1 − 19c/40)`
  have e1 : u * (1 + t) = u + 2 * u ^ (1 - (19 * (c:ℝ))/40) := by
    rw [ht, Real.rpow_sub hu0, Real.rpow_one]
    field_simp
  -- `uᶜ · 3t = 6 u^(21c/40)`
  have e2 : u ^ c * (3 * t) = 6 * u ^ ((21 * (c:ℝ))/40) := by
    rw [ht]
    have hsplit : u ^ c = u ^ ((21 * (c:ℝ))/40) * u ^ ((19 * (c:ℝ))/40) := by
      rw [← Real.rpow_add hu0, show (21 * (c:ℝ))/40 + (19 * (c:ℝ))/40 = ((c:ℕ):ℝ) by ring,
        Real.rpow_natCast]
    rw [hsplit]
    field_simp
    ring
  by_contra hcon
  push Not at hcon
  have hylt : u * (1 + t) < y := by rw [e1]; linarith
  have hnn : (0:ℝ) ≤ u * (1 + t) := by positivity
  have hcubelt : (u * (1 + t)) ^ c < y ^ c := pow_lt_pow_left₀ hylt hnn (by omega)
  -- Bernoulli
  have hbern : (1:ℝ) + (c:ℝ) * t ≤ (1 + t) ^ c := by
    have := one_add_mul_le_pow (a := t) (by linarith) c
    exact this
  have h3t : (1:ℝ) + 3 * t ≤ (1 + t) ^ c := by nlinarith [hbern, ht0, hcR]
  have hexp : u ^ c * (1 + 3 * t) ≤ (u * (1 + t)) ^ c := by
    calc u ^ c * (1 + 3 * t) ≤ u ^ c * (1 + t) ^ c :=
          mul_le_mul_of_nonneg_left h3t (by positivity)
      _ = (u * (1 + t)) ^ c := by rw [mul_pow]
  have hpos21 : (0:ℝ) < u ^ ((21 * (c:ℝ))/40) := Real.rpow_pos_of_pos hu0 _
  have hfin : u ^ c + 6 * u ^ ((21 * (c:ℝ))/40) ≤ u ^ c + 2 * u ^ ((21 * (c:ℝ))/40) := by
    calc u ^ c + 6 * u ^ ((21 * (c:ℝ))/40) = u ^ c * (1 + 3 * t) := by rw [← e2]; ring
      _ ≤ (u * (1 + t)) ^ c := hexp
      _ ≤ y ^ c := hcubelt.le
      _ ≤ u ^ c + 2 * u ^ ((21 * (c:ℝ))/40) := h
  linarith


/-! ### The decay hypothesis Dubickas needs -/

/-- **From Saito's Lemma 3.6 to Dubickas's input.**  With `μ = 19c/40 − 1 > 0`, the digits
approximate `A^(cᵏ)` to within `2^(μ+1)·A^(−μcᵏ)`.  This is the single §3 hypothesis of
`transcendental_of_decay`. -/
theorem decay_of_lemma36C (hc : 3 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊)
    (h36 : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (mdigitC c A (k + 1) : ℝ)
        ≤ (mdigitC c A k : ℝ) ^ c + (mdigitC c A k : ℝ) ^ ((21 * (c:ℝ))/40)) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 ≤ A ^ (c ^ k) - (⌊A ^ (c ^ k)⌋₊ : ℝ) ∧
      A ^ (c ^ k) - (⌊A ^ (c ^ k)⌋₊ : ℝ)
        ≤ (2 : ℝ) ^ ((19 * (c:ℝ))/40) * (A ^ (-(((19 * (c:ℝ))/40 - 1) * (c ^ k : ℕ))) : ℝ) := by
  obtain ⟨k₀, h36⟩ := h36
  have hA0 : (0:ℝ) < A := by linarith
  set μ : ℝ := (19 * (c:ℝ))/40 - 1 with hμdef
  have hcR : (3:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hμ0 : 0 < μ := by rw [hμdef]; linarith
  rw [Filter.eventually_atTop]
  refine ⟨k₀ + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : k₀ ≤ j := by omega
  set u : ℝ := (mdigitC c A j : ℝ) with hu
  have hu2 : (2:ℝ) ≤ u := by rw [hu]; exact_mod_cast mdigitC_two_le hA j
  have hu0 : (0:ℝ) < u := by linarith
  set y : ℝ := A ^ (c ^ (j + 1)) with hy
  have hy0 : (0:ℝ) < y := by rw [hy]; positivity
  have huy : u ≤ y := by rw [hu, hy]; exact mdigitC_le_pow hA0.le j
  have hyu : y < u + 1 := by rw [hu, hy]; exact pow_lt_mdigitC_add_one A j
  -- `yᶜ ≤ uᶜ + 2u^(21c/40)`
  have hone : (1:ℝ) ≤ u ^ ((21 * (c:ℝ))/40) := Real.one_le_rpow (by linarith) (by linarith)
  have hyc : y ^ c ≤ u ^ c + 2 * u ^ ((21 * (c:ℝ))/40) := by
    have h1 : y ^ c < (mdigitC c A (j + 1) : ℝ) + 1 := by
      rw [hy, ← pow_succ_eq_powC]
      exact pow_lt_mdigitC_add_one A (j + 1)
    have h2 := h36 j hj
    rw [← hu] at h2
    linarith
  -- (3.19)
  have hstep := le_add_rpow_of_pow_le hc hu2 hy0 hyc
  have hμneg : (1:ℝ) - (19 * (c:ℝ))/40 = -μ := by rw [hμdef]; ring
  rw [hμneg] at hstep
  -- `|y − u| ≤ 2 u^(−μ)`
  have habs : |y - u| ≤ 2 * u ^ (-μ) := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- `u > y/2`, so `u^(−μ) < 2^μ y^(−μ)`
  have hhalf : y / 2 ≤ u := by linarith
  have hyhalf : (0:ℝ) < y / 2 := by linarith
  have hmono : u ^ (-μ) ≤ (y / 2) ^ (-μ) :=
    Real.rpow_le_rpow_of_nonpos hyhalf hhalf (by linarith)
  have hsplit : (y / 2) ^ (-μ) = (2:ℝ) ^ μ * y ^ (-μ) := by
    rw [Real.div_rpow hy0.le (by norm_num),
      show ((2:ℝ) ^ (-μ)) = ((2:ℝ) ^ μ)⁻¹ from Real.rpow_neg (by norm_num) μ]
    field_simp
  -- assemble
  have hfinal : |y - u| ≤ 2 * ((2:ℝ) ^ μ * y ^ (-μ)) := by
    refine le_trans habs ?_
    rw [← hsplit]
    linarith [hmono]
  have hyrw : (y ^ (-μ) : ℝ) = A ^ (-(μ * ((c ^ (j + 1) : ℕ) : ℝ))) := by
    rw [hy, ← Real.rpow_natCast A (c ^ (j + 1)), ← Real.rpow_mul hA0.le]
    congr 1
    ring
  have hconst : (2:ℝ) * (2:ℝ) ^ μ = (2:ℝ) ^ ((19 * (c:ℝ))/40) := by
    rw [hμdef, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  have hufl : ((⌊A ^ (c ^ (j + 1))⌋₊ : ℕ) : ℝ) = u := by rw [hu, mdigitC]
  refine ⟨by rw [hufl]; linarith, ?_⟩
  rw [hufl]
  calc A ^ (c ^ (j + 1)) - u = |y - u| :=
        (abs_of_nonneg (show (0:ℝ) ≤ y - u by linarith)).symm
    _ ≤ 2 * ((2:ℝ) ^ μ * y ^ (-μ)) := hfinal
    _ = ((2:ℝ) * (2:ℝ) ^ μ) * y ^ (-μ) := by ring
    _ = (2 : ℝ) ^ ((19 * (c:ℝ))/40) * (A ^ (-(μ * ((c ^ (j + 1) : ℕ) : ℝ))) : ℝ) := by
        rw [hconst, hyrw]

/-- The `round` form of `decay_of_lemma36C`: the nearest integer is at least as close as the
floor. -/
theorem decay_round_of_lemma36C (hc : 3 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊)
    (h36 : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (mdigitC c A (k + 1) : ℝ)
        ≤ (mdigitC c A k : ℝ) ^ c + (mdigitC c A k : ℝ) ^ ((21 * (c:ℝ))/40)) :
    ∀ᶠ k : ℕ in Filter.atTop,
      |A ^ (c ^ k) - (round (A ^ (c ^ k)) : ℝ)|
        ≤ (2 : ℝ) ^ ((19 * (c:ℝ))/40) * (A ^ (-(((19 * (c:ℝ))/40 - 1) * (c ^ k : ℕ))) : ℝ) := by
  have hA0 : (0:ℝ) < A := by linarith
  filter_upwards [decay_of_lemma36C hc hA1 hA h36] with k hk
  obtain ⟨hlo, hhi⟩ := hk
  set y : ℝ := A ^ (c ^ k) with hy
  have hy0 : (0:ℝ) ≤ y := by rw [hy]; positivity
  have hfl : ((⌊y⌋ : ℤ) : ℝ) = ((⌊y⌋₊ : ℕ) : ℝ) := by
    rw [← Int.natCast_floor_eq_floor hy0]
    push_cast
    ring
  refine le_trans ?_ hhi
  rw [abs_sub_round_eq_min, ← Int.self_sub_floor, hfl]
  exact min_le_left _ _

/-- No power `A^(cᵐ)` (`m ≥ 1`) of a Mills number is an integer: it would make the next digit
`p^c`, which is composite.  (This is Saito's `ℓ = 1` exclusion in Lemma 4.1.) -/
theorem millsC_not_intCast (hc : 2 ≤ c) (hA1 : 1 < A)
    (hA : ∀ n : ℕ+, Prime ⌊A ^ (c ^ (n : ℕ))⌋₊) (m : ℕ) (hm : 1 ≤ m) (t : ℤ) :
    A ^ (c ^ m) ≠ (t : ℝ) := by
  intro hAm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hA0 : (0:ℝ) < A := by linarith
  have ht0 : (0:ℝ) ≤ (t : ℝ) := by rw [← hAm]; positivity
  have ht0' : 0 ≤ t := by exact_mod_cast ht0
  have hcast : ((t.toNat : ℕ) : ℝ) = (t : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg ht0'
  have hdig : mdigitC c A j = t.toNat := by
    rw [mdigitC, hAm, ← hcast, Nat.floor_natCast]
  have hdig' : mdigitC c A (j + 1) = t.toNat ^ c := by
    rw [mdigitC, pow_succ_eq_powC, hAm, ← hcast, ← Nat.cast_pow, Nat.floor_natCast]
  have := mdigitC_pow_lt hc hA1 hA j
  rw [hdig, hdig'] at this
  exact absurd this (lt_irrefl _)

/-- **Saito (2024), Theorem 1.1 for `c ≥ 5`**, modulo `saito_lemma36C`.  Here
`μ = 19c/40 − 1 ≥ 11/8 > 1`, so the Claim of Lemma 4.1 closes outright and no degree-2
analysis (Lemmas 4.2/4.3) is needed. -/
theorem transcendentalC_of_five_le (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) (hc : 5 ≤ c)
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (c ^ (n : ℕ))⌋₊} A) :
    Transcendental ℚ A := by
  obtain ⟨⟨hA1, hAm⟩, hmin⟩ := hA
  have hcR : (5:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  refine transcendental_of_decay hD hG hA1 (c := c) (by omega) (μ := (19 * (c:ℝ))/40 - 1)
    (K := (2:ℝ) ^ ((19 * (c:ℝ))/40)) (by linarith) (Real.rpow_pos_of_pos (by norm_num) _) ?_ ?_
  · exact decay_round_of_lemma36C (by omega) hA1 hAm
      (saito_lemma36C hB hM (by omega) ⟨⟨hA1, hAm⟩, hmin⟩)
  · exact fun m hm t => millsC_not_intCast (by omega) hA1 hAm m hm t


/-- `K·A^(−μcᵏ) → 0`: the decay bound eventually beats any positive `ε`. -/
theorem eventually_rpow_neg_lt {A : ℝ} (hA1 : 1 < A) {c : ℕ} (hc : 2 ≤ c) {μ K ε : ℝ}
    (hμ : 0 < μ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, K * (A ^ (-(μ * ((c ^ k : ℕ) : ℝ))) : ℝ) < ε := by
  have hA0 : (0:ℝ) < A := by linarith
  have hlog : 0 < Real.log A := Real.log_pos hA1
  have hxpos : 0 < μ * Real.log A := by positivity
  rw [Filter.eventually_atTop]
  refine ⟨⌈K / ε / (μ * Real.log A)⌉₊ + 1, fun k hk => ?_⟩
  have hNk : (k:ℝ) ≤ ((c ^ k : ℕ) : ℝ) := by
    have : k ≤ c ^ k := (Nat.lt_pow_self (by omega)).le
    exact_mod_cast this
  have hkbig : K / ε / (μ * Real.log A) < (k:ℝ) := by
    have h1 : K / ε / (μ * Real.log A) ≤ (⌈K / ε / (μ * Real.log A)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈K / ε / (μ * Real.log A)⌉₊ : ℕ) : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hgt : K / ε < μ * ((c ^ k : ℕ) : ℝ) * Real.log A := by
    have h3 := (div_lt_iff₀ hxpos).1 hkbig
    nlinarith [hNk, hxpos, h3]
  have hexp : K / ε < Real.exp (μ * ((c ^ k : ℕ) : ℝ) * Real.log A) :=
    lt_of_lt_of_le hgt (by linarith [Real.add_one_le_exp (μ * ((c ^ k : ℕ) : ℝ) * Real.log A)])
  have hrw : (A ^ (-(μ * ((c ^ k : ℕ) : ℝ))) : ℝ)
      = (Real.exp (μ * ((c ^ k : ℕ) : ℝ) * Real.log A))⁻¹ := by
    rw [Real.rpow_def_of_pos hA0, ← Real.exp_neg]
    congr 1
    ring
  rw [hrw, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _), mul_comm]
  exact (div_lt_iff₀ hε).1 hexp

/-- **Saito (2024), Theorem 1.1 for `c = 4`**, modulo `saito_lemma36C`.  Here `μ = 9/10 < 1`,
so Lemma 4.1's Claim only forces degree exactly 2, and `not_pisot_two_of_even` finishes. -/
theorem transcendentalC_of_four (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap)
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ ((4:ℕ) ^ (n : ℕ))⌋₊} A) :
    Transcendental ℚ A := by
  obtain ⟨⟨hA1, hAm⟩, hmin⟩ := hA
  intro halg
  have h36 := saito_lemma36C (c := 4) hB hM (by norm_num) ⟨⟨hA1, hAm⟩, hmin⟩
  have hμ0 : (0:ℝ) < (19 * ((4:ℕ):ℝ))/40 - 1 := by norm_num
  have hK0 : (0:ℝ) < (2:ℝ) ^ ((19 * ((4:ℕ):ℝ))/40) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨m, hβ, hnd, hclaim⟩ :=
    exists_pisot_of_decay hD hG hA1 (c := 4) (by norm_num) hμ0 hK0
      (decay_round_of_lemma36C (by norm_num) hA1 hAm h36)
      (fun m hm t => millsC_not_intCast (by norm_num) hA1 hAm m hm t) halg
  -- `μ = 9/10`, so the Claim forces `card = 1`, i.e. degree exactly 2
  have hcard1 : 1 ≤ Multiset.card (otherConj (A ^ ((4:ℕ) ^ (m + 1)))) := by
    have := card_otherConj_add_one (β := A ^ ((4:ℕ) ^ (m + 1))) (hβ.2.1.tower_top)
    omega
  have hcard2 : Multiset.card (otherConj (A ^ ((4:ℕ) ^ (m + 1)))) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h2 : (2:ℝ) ≤ (Multiset.card (otherConj (A ^ ((4:ℕ) ^ (m + 1)))) : ℝ) := by
      exact_mod_cast hcon
    norm_num at hclaim
    nlinarith [hclaim, h2]
  -- the fractional parts are eventually `< 1/2`
  have hfrac : ∀ᶠ k : ℕ in Filter.atTop,
      A ^ ((4:ℕ) ^ k) - (⌊A ^ ((4:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2 := by
    filter_upwards [decay_of_lemma36C (c := 4) (by norm_num) hA1 hAm h36,
      eventually_rpow_neg_lt (c := 4) hA1 (by norm_num) hμ0 hK0 (by norm_num : (0:ℝ) < 1/2)]
      with k hk hk2
    exact lt_of_le_of_lt hk.2 hk2
  exact not_pisot_two_of_even hA1 (c := 4) (by norm_num) (by norm_num) hβ
    (le_antisymm hcard2 hcard1) hfrac

end LeanFormalizations.Mills
