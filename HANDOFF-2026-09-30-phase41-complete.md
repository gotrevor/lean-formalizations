# HANDOFF 2026-09-30 — phases 40 AND 41 COMPLETE (Theorem C at every prime `c ≠ 5`)

Two files, both **sorry-free** and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`):
* `NumberTheory/Mills/FibonacciCovering.lean` (phase 40, `c = 2`): `five_mul_fib_two_pow_sq`,
  `exists_good_prime_factor`, `fib_two_pow_covering`, `fib_two_pow_prime_free`.
* `NumberTheory/Mills/FibonacciCoveringAllPrimes.lean` (phase 41, odd `c ≠ 5`):
  `exists_shift_pow_congr`, `exists_shift_fib_prime_pow_congr`, `exists_good_prime_factor_odd`,
  `fib_prime_pow_covering`, `fib_prime_pow_prime_free`.

`lake build` green; `scripts/fact-graph` rerun — **29 hypotheses, unchanged**, so neither phase
adds any dependency on a `Literature/` hypothesis.  No Aristotle job was used.

**Result.**  Saito's wish in arXiv:2504.14968 (*"We desire to remove the reversibility"*) is
answered for the tower `c^n` at every prime `c ≠ 5`: for every `H` there are `m`, `L ≥ 1` and
primes `p_h` (`|h| ≤ H`) with `p_h ∣ F(c^(Lk+m)) + h` for all `k`, hence
`[F(c^n) − H, F(c^n) + H]` contains no prime for infinitely many `n`.

## The one genuinely new theorem: `c`-adic convergence with no lifting
`exists_shift_pow_congr` — for any integer matrix `A` with `c ∤ det A` there are `d ≥ 1` and
`s ≤ v_c|GLₙ(𝔽_c)|` with `c^(n−s+1) ∣ (A^(c^(n+d)))ᵢⱼ − (A^(c^n))ᵢⱼ` for all `n ≥ s`.

This is the quantitative form of "Frobenius permutes the Teichmüller lifts of the eigenvalues and a
power of it fixes them", and the point is that **it needs neither the lifts nor binomial
coefficients**:
1. `A^T ≡ 1 (mod c)` for `T = |GLₙ(𝔽_c)|` — Lagrange, exactly as in phase 30's mechanism.
2. **The gain step.**  If `Z ≡ 1 (mod c^k)`, `k ≥ 1`, then `Z^c ≡ 1 (mod c^(k+1))`, because
   `Z^c − 1 = (∑_{i<c} Z^i)(Z − 1)` (`geom_sum_mul`, which mathlib states for *noncommutative*
   rings, so the matrix ring is fine) and `∑_{i<c} Z^i ≡ c·1 ≡ 0 (mod c)`.  The geometric sum
   supplies the extra factor of `c` all by itself — no `v_c(C(c^m, i))` bookkeeping.
3. `e ∣ c^d − 1` for `d = φ(e)`, `e` the `c`-free part of `T`, so `T·c^(n−s)` divides the exponent
   gap `c^(n+d) − c^n = c^n(c^d − 1)`.

Matrix divisibility is carried by `SmulDvd a M := ∃ B, M = a • B`, which is exactly `a ∣ Mᵢⱼ`
entrywise but multiplies on either side via `Matrix.smul_mul`/`Matrix.mul_smul`.

Allowing a **general shift `d`** instead of the roadmap's guessed `d = 2` is what makes step 3
elementary, and it costs nothing downstream: `c^d` is still odd, so `FibonacciAllPrimes.fib_odd_mul`
applies with `2J + 1 = c^d`, and `d` depends only on `c`, so `|Φ_J(x)|` stays bounded by a function
of `c` and `H`.

## Refuted sub-approach (recorded so it is not retried)
The roadmap proposed using the `Φ_J` fixed-point obstruction directly.  That obstruction is
**two-index**: from `c^e ∣ F(c^n) − x` and `c^e ∣ F(c^(n+d)) − x'` one gets `c^e ∣ Φ_J(x) − x'`, and
concluding `Φ_J(x) = x'` needs `c^e > |Φ_J(x)|` where `|Φ_J(x)| ≍ φ^(c^d)`.  So the threshold on
`n` for comparing `n` and `n+d` grows like `c^d`, and two-index comparison proves only that bad
indices are exponentially sparse — not `∀ᶠ n`, and not one index good for all `|h| ≤ H` at once
(different shifts can stay bad at different indices).  The `c`-adic convergence theorem is what
collapses it to a single index.

## Other reusable declarations
Phase 40: `lucasInt`, `fib_cassini`, `lucasInt_sq`, `fib_two_mul_int`, `PmOne` (+`.mul`,
`.of_prime_factors`), `padicValNat_glCard_two_two`, `exists_entry_pow_congr_mul`, `fibMat`,
`fibMat_pow`, `fibMat_det`, `dvd_fib_two_pow_add_of_good`.

Phase 41: `PmOneMod` (+`.exists_sign`, `.mul`, `.of_prime_factors`) — the `±1` closure modulo an
arbitrary modulus; `glCard_two_eq`; `padicValNat_glCard_two_self` (`v_c|GL₂(𝔽_c)| = 1`, so the base
prime is good at every `c`); `pow_dvd_sub_or_add_of_lt_padicValNat_odd`; the whole `SmulDvd`
section; `dvd_fib_prime_pow_add_of_good`; `fib_prime_pow_lt`.

`exists_shift_pow_congr` and `SmulDvd` are stated for a general `n × n` integer matrix and a
general prime, so Theorem A (order `d`, inert primes) and the Lucas analogues get the `c`-adic
convergence for free.

## Exact next steps
1. `DIRECTION.md` still lists phase 40 as CURRENT; an altitude lap owns marking 40 and 41 DONE.
2. **`c = 5` is the only gap in Theorem C for Fibonacci.**  It is genuinely different: `5 ∣ disc`,
   so the Frobenius congruence `Φ_{(c−1)/2}(x) ≡ 5^((c−1)/2) x^c (mod c)` degenerates —
   `Φ_2 = 25x⁵ − 25x³ + 5x ≡ 0 (mod 5)`.  The roadmap's suggestion is the elementary
   `F(4k+1) ± 1` factorizations, which handle `h = ±1` only; a full `c = 5` covering theorem needs
   a different certificate (the `5`-adic limit of `F(5^n)` is `0`, not a unit).
3. Then roadmap §1 Theorem B (2×2 traces, odd `c`, `det ≡ ±1`) and Theorem A (order `d`, inert).
   Both should now reuse `exists_shift_pow_congr` rather than redoing a convergence argument.
