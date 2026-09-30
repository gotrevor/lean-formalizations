# HANDOFF 2026-09-30 — phase 40 COMPLETE (Theorem C for Fibonacci at `c = 2`)

`src/LeanFormalizations/NumberTheory/Mills/FibonacciCovering.lean` is **sorry-free**; all four
frozen statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):
`five_mul_fib_two_pow_sq`, `exists_good_prime_factor`, `fib_two_pow_covering`,
`fib_two_pow_prime_free`.  `lake build` green.  No Aristotle job was used; no earlier Mills phase
file or `Literature/` file was touched.

**Result.** Saito's wish (*"We desire to remove the reversibility"*, arXiv:2504.14968) is answered
for the tower `2^n`: for every `H` there are `m`, `L ≥ 1` and primes `p_h` (`|h| ≤ H`) with
`p_h ∣ F(2^(Lk+m)) + h` for all `k`, hence `[F(2^n) − H, F(2^n) + H]` is prime-free for
infinitely many `n`.

## What the four steps actually needed
1. **`five_mul_fib_two_pow_sq`** (`2^(n+1) ∣ 5F(2^n)²+3`) is a *self-contained* induction, not a
   consequence of phase 32.  With `x_n = 5F(2^n)²`: `F(2m) = F(m)L(m)` and Cassini give
   `L(2^n)² = x_n + 4` (the sign `(-1)^(2^n) = 1` needs `n ≥ 1`), so `x_(n+1) = x_n(x_n+4)` and
   `x_(n+1)+3 = (x_n+1)(x_n+3)`.  The inductive hypothesis `x_n+3 = 2^(n+1)c` makes
   `x_n+1 = 2^(n+1)c − 2 = 2(2^n c − 1)` even *for free* — no oddness of `F(2^n)` is used.
   `lucasInt`, `fib_cassini`, `lucasInt_sq`, `fib_two_mul_int` are local copies (phase 32 keeps
   them `private`).
2. **`exists_good_prime_factor`** = `PmOne.mul` (the set `±1 mod 2^e` is multiplicatively closed:
   `xy − st = y(x−s) + s(y−t)`) + `PmOne.of_prime_factors` (strong induction on `N` via
   `Nat.minFac`) + `padicValNat_glCard_two_two` (`|GL₂(𝔽₂)| = 2·3`, so `2` is always a *good*
   prime, which is what lets the argument assume all prime factors are odd).  The threshold is
   `n ≥ max 5 (2B + 2|h| + 8)` with `B ≥ 5(1+|h|)²+3`, so that `2^(n/2) > B`.
3. **`exists_entry_pow_congr_mul`**: phase 32's proof, with `g^(c^j) = g` iterated to
   `g^(c^(kj)) = g`.  `dvd_fib_two_pow_add_of_good` reads off entry `(0,1)` of `!![1,1;1,0]^N`.
4. **`fib_two_pow_covering`**: `Filter.eventually_all_finset (Finset.Icc (-H) H)` gives one `m`
   for all shifts; `P`/`J` are `dite`-choice functions; `L = ∏_{h ∈ S} J h` (a **product**, not an
   lcm — `Finset.dvd_prod_of_mem` + `Finset.one_le_prod'` beat `Finset.lcm_eq_zero_iff`).
5. **`fib_two_pow_prime_free`**: compare two indices.  `p_h` divides both `A_K` and `A_(K+1)`
   with `0 < A_K < A_(K+1)`; if `A_(K+1)` were prime then `p_h = A_(K+1)`, yet `p_h ≤ A_K`.
   This avoids needing any bound on the size of `p_h`.

## Reusable declarations added
`lucasInt`, `fib_cassini`, `lucasInt_sq`, `fib_two_mul_int`, `fib_two_pow_lt'`,
`le_fib_two_pow'`, `PmOne` + `PmOne.one`/`.mul`/`.of_prime_factors`,
`padicValNat_glCard_two_two`, `exists_entry_pow_congr_mul`, `fibMat`, `fibMat_pow`,
`fibMat_det`, `dvd_fib_two_pow_add_of_good`.

`exists_entry_pow_congr_mul` is the one a later phase will reuse verbatim: it is stated for a
general `n × n` integer matrix and a general prime `c`, so phase 41 (all primes) and Theorem A
(order `d`, inert) both get the whole-progression mechanism for free.  `PmOne.of_prime_factors`
is likewise generic: "all prime factors `≡ ±1 (mod 2^e)` ⟹ the number is".

## Exact next steps
1. `DIRECTION.md` still lists phase 40 as CURRENT; an altitude lap owns marking it DONE.
2. **Phase 41** (roadmap §1 Theorem C, second half): Fibonacci at every prime `c ≠ 5`.  The
   mechanism (steps 2–5) is `c`-generic already — only the **certificate** changes: instead of
   `5F(2^n)²+3` use phase 37's `Φ_j` with `2j+1 = c²`, where `x = Φ_j(x)` forces `x = 0` while
   `c ∤ F(c^n)`.  `c = 5` needs the `F(4k+1) ± 1` factorizations separately.
3. Note for phase 41: `exists_good_prime_factor` as written is specific to `c = 2` only through
   `two_pow_dvd_sub_or_add_of_lt_padicValNat` (a `GL₂` 2-part computation) and
   `padicValNat_glCard_two_two`.  The odd-`c` analogue of the first is the real work; `c` good is
   easy (`|GL₂(𝔽_c)| = c(c−1)²(c+1)`, and `v_c` of that is `1`).
