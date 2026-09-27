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
  sorry

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
