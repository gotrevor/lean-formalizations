# Is the Copeland–Erdős constant transcendental under a prime-pattern conjecture? (probe, 2026-09-29)

**Verdict: no route.  The Mahler/Champernowne mechanism needs a structured block whose length is proportional to its digit offset.  Consecutive primes cannot supply one, even under Hardy–Littlewood or Cramér.**

`CE = 0.2357111317192329…` (the primes concatenated in base 10).  It is known normal (Copeland–Erdős 1946), hence irrational.  Its transcendence is open.

## The idea

Champernowne is transcendental (phase 18, `Champernowne.lean`, from `Roth1955`).  The k-digit block `10^(k−1), …, 10^k − 1` is an arithmetic progression, and an AP concatenated in base `10^k` sums to a rational with denominator `10^N · (10^k − 1)²`.  Here N is the block's digit offset.  So I asked: if there were infinitely many runs of L consecutive primes in AP (the CPAP conjecture, a Hardy–Littlewood consequence), would each run hand Ridout a good approximation to CE?  That would give "HL ⇒ CE transcendental", a new conditional theorem.

## Why it dies (the arithmetic)

Take a run of L consecutive k-digit primes in AP at digit offset N.
- **Offset.**  The primes below 10^k contribute ≈ `10^k / ln 10` digits, so `N ≍ 10^k`.
- **Approximation.**  `r = a/q` with `q = 10^N · D` and `D ≈ 10^(2k)` coprime to 10.  The error is ≈ `10^−(N + Lk)`.
- **Stephan/Ridout form** (`Stephan2026Ridout`, `S₂ = {2, 5}`).
  - LHS: `|CE − r| · |q|₂|q|₅ ≈ 10^−(2N + Lk)`.
  - RHS: `max(a, q)^(−2−ε) ≈ 10^−(2N + 4k + ε(N + 2k))`.
  - The inequality needs `Lk > 4k + εN`.
  - ε is fixed, so this means **`Lk ≫ N ≍ 10^k`**.
- **The general `Ridout1957`** gives the same condition.  It takes ν ≥ 2k/(N+2k), and the κ achieved is `1 + (L−2)k/N`, so κ > 1 + ν again needs `Lk ≍ N`.
- **Roth alone** is worse: it needs `Lk > N(1+ε)`.

Champernowne passes because its block has `Lk ≍ 9k·10^(k−1) ≍ N`.  For primes, a run of L consecutive primes in AP needs a common difference divisible by roughly every prime below L.  So `d ≥ e^((1+o(1))L)`.  Under Cramér, gaps near `10^k` are `O(k²)`, which forces `L = O(log k)`.  So `Lk = O(k log k) ≪ 10^k`, and no prime-pattern conjecture closes the gap of **exponential size**.

## Reopen if

- a structured sub-block of the prime sequence whose digit length is a positive fraction of its offset (none is conjectured); or
- a transcendence criterion that tolerates approximations of quality `1 + o(1)`, e.g. a quantitative Subspace Theorem with ε → 0 as fast as `k / 10^k` (far beyond anything known).

`Maze.lean` row: "Transcendence of Copeland–Erdős via consecutive primes in AP".
