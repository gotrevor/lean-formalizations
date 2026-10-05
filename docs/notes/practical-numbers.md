# Practical numbers: three small observations

*Written by Claude at Trevor Morris's direction.*

A positive integer `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n` (OEIS A005153: 1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, …).  The three observations below are small.  They are recorded because we did not find them in the sources we checked.

## 1. Practical numbers in shorter intervals: exponent 0.486987…

Weingartner (arXiv:2105.13568, Theorem 2) shows that for any exponent pair `(k, l)` and any `β > (5k + l + 2)/(6(k + 1))`, the interval `[x − x^β, x]` contains `≫ x^β (log x)^(−μ)` practical numbers for large `x`.  With Bourgain's pair processed by van der Corput's A-step, `(13/194, 76/97)`, he gets `β > 605/1242 = 0.48711…` (Corollary 4).

Tao, Trudgian and Yang (arXiv:2501.16779, Theorem 20) prove that `(652397/9713986, 7599781/9713986)` is an exponent pair.  Substituting it gives

**`β > 15144869/31099149 = 0.486987…`.**

This is the minimum of Weingartner's exponent over the vertices of the known exponent-pair region: Trudgian–Yang's `(k_n, l_n)` (arXiv:2306.05599, eq. (1.14)) and the four new pairs, closed under the A and B processes.  Because the objective is linear-fractional, its minimum over the convex region is at a vertex.  Trudgian–Yang's vertex `(715/10238, 7955/10238)` alone already gives `0.487020…`.  The gain is in the fourth decimal.

On our reading of Weingartner's argument, the exponent cannot improve further except through the exponent pair.  He writes the integer as `nm` with `n ≈ x^α` in a structured set and `m` a `(x/n)^a`-smooth number in a short interval.  The argument needs `α ≥ 1/3` and `a(1 − α) ≤ 1/2`, and the resulting exponent `α + (1 − α) b(a)` increases with `α`.  So his choice `α = 1/3`, `a = 3/4` is optimal for every pair.  The exponent-pair conjecture would give `5/12`.

* Lean: `Practical.practicalShortInterval_tty` (`src/LeanFormalizations/NumberTheory/Practical/ShortIntervals.lean`), proved from the two cited theorems, which are stated as hypotheses `Literature.Weingartner2021Thm2` and `Literature.TaoTrudgianYang2025Pair`.  Mathlib has no definition of exponent pair, so both take the notion as a parameter, and the theorem holds for any notion satisfying both.
* Optimizer: `scripts/practical-exponent-opt.py`.  It asserts that Bourgain's pair alone reproduces `605/1242`.

## 2. Erdős Problem 18: `h(n!) ≥ (1/C − o(1)) (log n)²`

For practical `n`, let `h(n)` be the least `j` such that every `m ≤ n` is a sum of at most `j` distinct divisors of `n`.  Erdős proved `h(n!) < n` and asked whether `h(n!) < (log n)^(O(1))` (erdosproblems.com/18).  Erdős and Graham (*Old and New Problems and Results in Combinatorial Number Theory*, 1980, p. 33) wrote "perhaps even only `(log n)^c`".

A counting argument shows `c ≥ 2`.  The sums of at most `h` divisors of `n` come from at most `(τ(n) + 1)^h` subsets, so `n + 1 ≤ (τ(n) + 1)^(h(n))`.  For `n!`, `log n! ~ n log n` and `log τ(n!) ~ C n / log n` with `C = Σ_{k≥1} log(k+1)/(k(k+1)) = 1.2577…` (from `v_p(n!) ≈ ⌊n/p⌋` and the prime number theorem).  Hence

**`h(n!) ≥ (1/C − o(1)) (log n)² ≈ 0.795 (log n)²`.**

More generally `h(n) ≥ log n / log(τ(n) + 1) ≫ log log n` for every `n`, so in Erdős's other question, about practical `m` with `h(m) < (log log m)^(O(1))`, the exponent is at least 1.

This is likely folklore.  We did not find it on the erdosproblems.com/18 page or its discussion thread, in Pomerance–Weingartner (arXiv:2007.11062), or on p. 33 of Erdős–Graham.  Vose (1985) and later papers have not been checked.  The constant `C` is our own computation.  Numerically, `log τ(n!) · log n / n` is 1.69, 1.58, 1.51 and 1.45 at `n = 10³, 10⁴, 10⁵, 10⁶`, decreasing slowly toward `C` (`scripts/practical-factorial-divisors.py`).  The script also checks that the bound is consistent with the exact values `h(n!)` for `n ≤ 11` posted on the discussion thread.

* Lean: `Practical.card_le_pow_practicalH` and `Practical.practicalH_factorial_ge` (`h(n!) ≥ (log n)²/2` eventually), in `src/LeanFormalizations/NumberTheory/Practical/Erdos18.lean`.  Both are stated; their proofs are not yet written.
* The same file states the greedy reduction from the discussion thread (`practicalH_le_of_dense`) and its open premise for `lcm(1, …, x)` (`LcmDivisorsDense`), wired to question (a) by `erdos18a_of_lcmDivisorsDense`.  The counting bound shows that premise asks for divisor spacing at the finest scale the divisor count allows.

## 3. The binary practical constant is not disjunctive in base 2

Let `β = Σ_{n practical} 2^(−n)`.  Its `n`-th binary digit is 1 exactly when `n` is practical.

* `β` is irrational.  Suppose its digits were eventually periodic.  Then some residue class `r mod T` would be eventually all practical.  With `g = gcd(r, T)`, Dirichlet's theorem gives `n = gp` in that class with `p` prime and `p > σ(g) + 1`, and by Stewart–Sierpiński `gp` is not practical.
* `β` is not disjunctive (rich) in base 2 or in any base `2^k`.  Practical numbers greater than 1 are even, so the binary word `111` never occurs, and in base `2^k` the top digit repeated twice is a run of 1s.  The prime constant `Σ_p 2^(−p)` fails for the same reason.
* Disjunctivity in base 3, normality in bases other than powers of 2, and transcendence are open, as they are for the prime constant.

By contrast, almost nothing can be said about Weingartner's constant `c = 1.33607…` in `#{practical n ≤ x} ~ c x / log x`.  It has an explicit series, but nothing is known about its irrationality, which puts it alongside Mertens', Artin's and Brun's constants.

* Lean: `Practical.practicalBinary_irrational`, `Practical.practicalBinary_not_disjunctive_two_pow` (stated, proofs not yet written), and the open statements `PracticalBinaryDisjunctiveThree`, `PracticalBinaryTranscendental` and `PracticalConstantIrrational`, in `src/LeanFormalizations/NumberTheory/Practical/Constant.lean`.

## Sources

* A. Weingartner, *Somewhat smooth numbers in short intervals*, arXiv:2105.13568.
* T. Tao, T. Trudgian, A. Yang, *New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach*, arXiv:2501.16779.
* T. Trudgian, A. Yang, *Toward optimal exponent pairs*, arXiv:2306.05599.
* C. Pomerance, A. Weingartner, *On primes and practical numbers*, arXiv:2007.11062.
* A. Weingartner, *The constant factor in the asymptotic for practical numbers*, arXiv:1906.07819.
* P. Erdős, R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique 28 (1980).
* erdosproblems.com/18 and its discussion thread.
