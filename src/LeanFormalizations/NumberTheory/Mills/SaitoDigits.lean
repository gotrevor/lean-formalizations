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

`saito_lemma36C` — Saito's Lemma 3.6 for general `c`, the minimality step that rests on
Matomäki.  It is the only `sorry` here, and the only genuinely deep obligation left in the
`c ≥ 5` case of Theorem 1.1.
-/
import LeanFormalizations.NumberTheory.Mills.BasicC
import LeanFormalizations.NumberTheory.Mills.SaitoLemma41
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
  sorry

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

end LeanFormalizations.Mills
