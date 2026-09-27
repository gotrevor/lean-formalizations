/-
# The digits of Mills' constant, assuming RH (Caldwell–Cheng 2005)

C. K. Caldwell, Y. Cheng, *Determining Mills' constant and a note on Honaker's problem*,
J. Integer Seq. **8** (2005), Article 05.4.1.  Local-only full text (gitignored):
`papers/caldwell-cheng-2005-mills-constant.{pdf,txt}`.

formal-conjectures states `Mills.lower_bound_of_RH`: under RH the least Mills number lies in
`(1.3063778838, 1.3063778839)`.  The route:

1. **Caldwell–Cheng Lemma 5** (`primeBetweenCubes_of_schoenfeld`): Schoenfeld's RH bound gives
   `π((n+1)³) − π(n³) ≥ (3n² + 3n + 1)/(3 log(n+1)) − (3/(4π)) (n+1)^(3/2) log(n+1) > 0` once
   `n³ ≥ 2657`, i.e. `n ≥ 14`; `n = 1, …, 13` are a finite check (`decide`/`norm_num`).
   The paper's display is in §2, just after Lemma 4.
2. **The greedy chain is the least Mills number** (`minMills_mem_Ioo_of_primeBetweenCubes`):
   with a prime in every cube gap, *every* prime `p` extends (some prime lies strictly between
   `p³` and `(p+1)³`), so the chain `b₁ = 2`, `b_{k+1}` = least prime `> b_k³` never stalls,
   and lexicographic minimality of the prime sequence gives numeric minimality of `A`.  Useful
   facts: any Mills `A` has `⌊A^(3^k)⌋₊ = b'_k` with `b'_{k+1} ∈ (b'_k³, (b'_k+1)³)`
   (see `Basic.lean`), and `b'_k ↦ A` is order-preserving.
3. **Digits**: `b₁..b₄ = 2, 11, 1361, 2521008887` (OEIS A051254; each `b_{k+1}` is the least
   prime above `b_k³`, so the gaps `b_k³+1 … b_{k+1}−1` are composite: a `decide`-sized
   check), and `b₄^(1/81) ≈ 1.30637788386308`, `(b₄+1)^(1/81) ≈ 1.30637788386948` — both
   inside the target interval.  Compare exact rational 81st powers: `1.3063778838 ^ 81 < b₄`
   and `(b₄ + 1) < 1.3063778839 ^ 81`, pure `norm_num`.
-/
import LeanFormalizations.NumberTheory.Mills.Basic
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **Caldwell–Cheng (2005), Lemma 5**, integer form: under RH (via Schoenfeld) every gap
between consecutive cubes from `1³` on contains a prime. -/
theorem primeBetweenCubes_of_schoenfeld (hS : Schoenfeld1976) (hRH : RiemannHypothesis) :
    PrimeBetweenCubesFrom 1 := by
  sorry

/-- **Primes in every cube gap pin the least Mills number to ten digits.**  Unconditional
given the hypothesis; this is where the combinatorics and the arithmetic live. -/
theorem minMills_mem_Ioo_of_primeBetweenCubes (h : PrimeBetweenCubesFrom 1) {A : ℝ}
    (hA : IsMinMills A) : A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry

/-- **formal-conjectures `Mills.lower_bound_of_RH`**, with Schoenfeld as the literature input. -/
theorem lower_bound_of_RH (hS : Schoenfeld1976) (hRH : RiemannHypothesis) {A : ℝ}
    (hA : IsMinMills A) : A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 :=
  minMills_mem_Ioo_of_primeBetweenCubes (primeBetweenCubes_of_schoenfeld hS hRH) hA

end LeanFormalizations.Mills
