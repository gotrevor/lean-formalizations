/-
# Mills-type constants are transcendental (Saito 2024, Theorems 1.1 and 1.2)

K. Saito, *Mills' constant is irrational*, Mathematika **71** (2025), e70027, arXiv:2404.19461.
Local-only full text (gitignored): `papers/saito-2024-mills-irrational.{pdf,txt}`.

For an integer `c ≥ 2`, `ξ_c` is the least `A > 1` with `⌊A^(c^k)⌋` prime for every `k ≥ 1`
(`IsMinMillsC c`; `c = 3` is `IsMinMills`, by `rfl`).  Saito proves:

* **Theorem 1.1**: for every integer `c ≥ 4`, `ξ_c` is transcendental.
* **Theorem 1.2**: either `ξ₃` is transcendental, or `ξ₃^(3^m)` is a Pisot number of degree 3
  for some `m ≥ 1`.

Both are Theorem 1.5 with constant `c_k = c` (so `C_k = c^k`, `b = c`, `I_b = ℕ`, `B = c`).
Inputs, each a hypothesis: `BakerHarmanPintz2001`, `Matomaki2007` (`Literature/Primes.lean`),
`Dubickas2022` (Saito Thm 2.6) and `Dubickas2022PisotGap` (Saito Lemma 2.7)
(`Literature/Pisot.lean`).  Saito's Theorem 1.4 (unbounded `c_k`) is not needed: `c_k` is
constant.

## Route (Saito §3–§4 with `c_k = c`)

1. **Existence** (Cor 3.4, here via BHP): BHP puts a prime in `(n^c, (n+1)^c)` for large `n`
   when `c ≥ 3` (`(n+1)^c − n^c ≥ 3n² ≫ n^(21c/40)`… check: need `n^(cθ) < c n^(c−1)`, true for
   `c ≥ 3`, `θ = 21/40`), so the `Basic.lean`/`Irrational.lean` construction runs with `c`.
2. **Lemmas 3.5, 3.6, 3.8, 3.9** for exponent `c` — generalise the `c = 3` proofs in
   `Irrational.lean` (`mdigit`, `saito_lemma36/38/39`).  Add new `c`-general lemmas; do not change
   existing statements.  Lemma 3.9 gives `γ > 0` with `|ξ^(c^k) − p_k| ≤ e^(−γ c^k)` for large
   `k`, and the finer estimate Saito uses in §4 (with `θ_b`).
3. **Lemma 4.1**: if `ξ` is algebraic, `Dubickas2022` (`α := ξ`, `q := 1`, `s_k := c^(k+1)`,
   `ε := γ`) forces `β = ξ^(c^m)` Pisot for some `m`; then `Dubickas2022PisotGap` with
   `n := c^k/c^m` bounds the conjugate power sum from below, against Lemma 3.9 from above:
   for `b ≥ 5` a contradiction outright; for `b = 4` only degree 2 survives; for `b = 3`
   degrees 2 and 3 survive.
4. **Lemma 4.2/4.3**: degree 2 is impossible for `b ∈ {3, 4}` (the recurrence
   `p_k^b = p_{k+1} + …` with the two conjugates).  Combine.

Read §4 of the paper (`papers/…txt` lines ~429–560; render pages 9–12 with
`pdftoppm -f N -l N -r 150 -png` when a displayed formula matters — text extraction drops them).
-/
import LeanFormalizations.NumberTheory.Mills.Irrational
import LeanFormalizations.NumberTheory.Mills.SaitoGeneral
import LeanFormalizations.NumberTheory.Mills.SaitoPisot
import LeanFormalizations.NumberTheory.Mills.SaitoDigits
import LeanFormalizations.Literature.Pisot

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- `A` is a Mills number for exponent `c`: `⌊A^(c^n)⌋` is prime for every `n ≥ 1`. -/
abbrev IsMillsC (c : ℕ) (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (c ^ (n : ℕ))⌋₊

/-- `A` is `ξ_c`, the least Mills number for exponent `c`. -/
abbrev IsMinMillsC (c : ℕ) (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMillsC c x} A

example (A : ℝ) : IsMinMillsC 3 A ↔ IsMinMills A := Iff.rfl

/-- **`ξ_c` exists for every integer `c ≥ 3`** (Saito Cor 3.4, here from Baker–Harman–Pintz). -/
theorem exists_minMillsC_of_BHP (hB : BakerHarmanPintz2001) {c : ℕ} (hc : 3 ≤ c) :
    ∃ A, IsMinMillsC c A :=
  exists_leastMillsC_of_BHP hB hc

/-- **Saito (2024), Theorem 1.1: `ξ_c` is transcendental for every integer `c ≥ 4`.** -/
theorem transcendental_of_four_le (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {c : ℕ} (hc : 4 ≤ c) {A : ℝ}
    (hA : IsMinMillsC c A) : Transcendental ℚ A := by
  rcases eq_or_lt_of_le hc with h4 | h5
  · -- `c = 4`: `μ = 9/10 < 1`, so the Claim only gives degree 2, killed by `not_pisot_two_of_even`
    subst h4
    exact transcendentalC_of_four hB hM hD hG hA
  · exact transcendentalC_of_five_le hB hM hD hG (by omega) hA

/-- **Saito (2024), Theorem 1.2: Mills' constant is transcendental, or some `ξ^(3^m)`
(`m ≥ 1`) is a Pisot number of degree 3.** -/
theorem transcendental_or_pisot (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) :
    Transcendental ℚ A ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsPisot (A ^ (3 ^ m)) ∧ (minpoly ℚ (A ^ (3 ^ m))).natDegree = 3 := by
  sorry

end LeanFormalizations.Mills
