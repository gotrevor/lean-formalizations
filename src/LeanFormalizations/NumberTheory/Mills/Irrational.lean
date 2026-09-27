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

/-- **Saito (2024)**: the least Mills number is irrational, from Baker–Harman–Pintz,
Matomäki and Mahler.  Matches formal-conjectures `Mills.irrational` plus the three inputs. -/
theorem irrational (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hMa : Mahler1957)
    {A : ℝ} (hA : IsMinMills A) : Irrational A := by
  sorry

end LeanFormalizations.Mills
