# HANDOFF 2026-09-30 — Theorem C CLOSED (phases 40, 41, `c = 5`, and all Lucas sequences)

**Branch** `main` · HEAD `e6f7d43` (this doc's commit follows).  Working tree clean apart from this
file.  `lake build` green (8759 jobs).  Nothing in flight; no Aristotle job was used this lap.

## What landed (all sorry-free, all `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`)

`scripts/fact-graph` rerun after every step: **29 hypotheses throughout, unchanged**.  Nothing this
lap depends on a `Literature/` hypothesis.

| file | headline declarations |
|---|---|
| `Mills/FibonacciCovering.lean` (phase 40, `c = 2`) | `five_mul_fib_two_pow_sq`, `exists_good_prime_factor`, `fib_two_pow_covering`, `fib_two_pow_prime_free` |
| `Mills/FibonacciCoveringAllPrimes.lean` (phase 41 + `c = 5`) | `exists_shift_pow_congr`, `exists_shift_fib_prime_pow_congr`, `exists_good_prime_factor_odd`, `fib_prime_pow_covering`, `fib_prime_pow_prime_free`, `five_pow_dvd_fib_five_pow`, `exists_good_prime_factor_five`, `fib_five_pow_covering`, `fib_five_pow_prime_free`, `fib_five_pow_pm_one_not_prime`, `fib_five_pow_prime_free_all`, **`fib_prime_pow_prime_free_all`** |
| `Mills/LucasCoveringAllPrimes.lean` (all Lucas) | `covering_of_good_seq`, `prime_free_of_covering_seq`, `exists_lucasU_prime_pow_congr_mul`, `dvd_lucasU_prime_pow_add_of_good`, `exists_good_lucasU_prime_factor`, `lucasU_prime_pow_covering`, `lucasU_prime_pow_prime_free` |

**Headline.**  `fib_prime_pow_prime_free_all`: for **every** prime `c` and every `H`, the interval
`[F(c^n) − H, F(c^n) + H]` contains no prime for infinitely many `n`.  That is Saito's
*"We desire to remove the reversibility"* (arXiv:2504.14968) answered for the Fibonacci tower,
which is exactly the non-reversible case his theorem cannot reach.  `lucasU_prime_pow_prime_free`
is the same for every `U(P, ±1)` with `D = P² − 4Q ≥ 5` at every odd prime `c ∤ D`.

## The one genuinely new theorem
`exists_shift_pow_congr` — **`c`-adic convergence of `A^(c^n)` with no lifting machinery.**  For any
integer matrix `A` with `c ∤ det A` there are `d ≥ 1` and `s ≤ v_c|GLₙ(𝔽_c)|` with
`c^(n−s+1) ∣ (A^(c^(n+d)))ᵢⱼ − (A^(c^n))ᵢⱼ` for all `n ≥ s`.

Three things made it elementary, each against my initial expectation:
1. **No Teichmüller/Witt lift.**  `A^T ≡ 1 (mod c)` for `T = |GLₙ(𝔽_c)|` is just Lagrange.
2. **No binomial coefficients** in the gain step (where I expected `v_c(C(c^m,i))` bookkeeping):
   if `Z ≡ 1 (mod c^k)`, `k ≥ 1`, then `Z^c − 1 = (∑_{i<c} Z^i)(Z − 1)` and
   `∑_{i<c} Z^i ≡ c·1 ≡ 0 (mod c)`, so the geometric sum itself supplies the extra `c`.
   `geom_sum_mul` is stated for *noncommutative* rings, so the matrix ring needs no work.
3. **A general shift `d`** in place of the roadmap's guessed `d = 2`: take `d = φ(e)` with `e` the
   `c`-free part of `T`, so `e ∣ c^d − 1` and `T c^(n−s)` divides the gap `c^n(c^d − 1)`.  Costs
   nothing downstream — `c^d` is still odd, so `fib_odd_mul` applies with `2J + 1 = c^d`, and `d`
   depends only on `c`.

Matrix divisibility is carried by `SmulDvd a M := ∃ B, M = a • B`, which is entrywise `a ∣ Mᵢⱼ` but
multiplies on either side via `Matrix.smul_mul`/`Matrix.mul_smul`.

## Corrections to the roadmap's plan for §1 Theorem C (all recorded in `ROADMAP-PRIME-TOWERS.md`)
* **The `Φ_J` certificate alone is not enough.**  It is two-index: from `c^e ∣ F(c^n) − x` and
  `c^e ∣ F(c^(n+d)) − x'` one gets `c^e ∣ Φ_J(x) − x'`, and concluding `Φ_J(x) = x'` needs
  `c^e > |Φ_J(x)| ≍ φ^(c^d)`.  So the threshold on `n` grows like `c^d` and two-index comparison
  proves only that bad indices are *exponentially sparse* — not `∀ᶠ n`, and not one index good for
  all `|h| ≤ H` at once.  The `c`-adic convergence is what collapses it to a single index.
* **`c = 5` is the EASIEST prime, not the hardest.**  `5 ∣ disc` makes
  `Φ_2 = 25x⁵ − 25x³ + 5x = 5x(5x⁴ − 5x² + 1)`, so `5 ∣ Φ_2(x)` identically and `5^n ∣ F(5^n)` in
  three lines.  The `5`-adic limit is `0`, so the window condition reads `5^(n/2) ∣ h ∓ 1` directly
  — no `Φ_J` analysis at all.
* **`h = ±1` at `c = 5` are genuine filter survivors** (the window condition holds identically), so
  no covering prime can exist for them by this mechanism — a real limit of the method, not an
  unfinished proof.  They fall to factorisation, and the general
  `F(m+n) + (−1)^n F(m−n) = F(m)L(n)` identity was *not* needed: both instances are one `linarith`
  from `F(4k+1) = F(2k+1)² + F(2k)²` plus Cassini at `2k`.  `n ≥ 2` (`k ≥ 6`) is what makes both
  factors exceed `1`; at `k = 1`, `F(5) − 1 = F(2)L(3) = 1·4` is trivial.
* **The odd-`c` `GL₂` bound is easier than `c = 2`**: an odd `c` divides at most one of `p ∓ 1`, so
  one of the two valuations is `0`, where at `c = 2` both are positive and one must be exactly `1`.

## Reusable, and what they unlock
`exists_shift_pow_congr` and the `SmulDvd` section are stated for a general `n × n` integer matrix
and a general prime.  `covering_of_good_seq` / `prime_free_of_covering_seq` are stated for an
abstract `t : ℕ → ℤ`; the latter needs only `|t n| → ∞` (no monotonicity), which is why the
sign-changing non-monotone `U(P,Q)` went through unchanged.  `PmOneMod` is the `±1` closure modulo
an arbitrary modulus.  So **for any new family the only missing input is the certificate.**

## Exact next steps
1. **`DIRECTION.md` still lists phase 40 as CURRENT.**  An altitude lap owns marking 40 and 41 DONE
   and picking the next target; this lap did not edit it.
2. **Roadmap §1 Theorem B** (2×2 traces, odd `c`, `det ≡ ±1`, with the `Φ₃`/`Φ₆` exception as a
   frozen survivor fact) — the roadmap's own estimate is one phase.  It should now reuse
   `exists_shift_pow_congr` and `covering_of_good_seq` instead of rebuilding either.
3. **Roadmap §1 Theorem A** (order `d`, inert primes; Tribonacci corollary).  The filter and the
   assembly are already `d`-generic, so only the certificate is missing.
4. **The `d ≥ 3` wall, now sharp.**  Because `A^(c^(n+d')) = (A^(c^n))^(c^(d'))`, the `c`-adic limit
   satisfies `Λ^(c^(d') − 1) = I`: every limit point is a **torsion** element of `GL_d(ℤ_c)` of
   order coprime to `c`, with Teichmüller eigenvalues.  The missing certificate is exactly *no such
   torsion element in the closure of `⟨A⟩` has `(i,j)` entry `s − h`*.  `d = 2` dodges the lifts via
   the exact composition; `d ≥ 3` does not, so the build target is `W(𝔽_(c^d))` and its Frobenius.
   `scripts/order-d-inert-probe.py` says the certificate is true for Tribonacci, so this is a
   formalization wall, not a mathematical unknown.
5. `c = 5` for the **Lucas** sequences is untouched (the Fibonacci `c = 5` argument used
   `5^n ∣ F(5^n)`, which is special to Fibonacci); the analogue is `c ∣ D`, the ramified case, which
   phase 38's handoff already flagged as needing a different obstruction.
