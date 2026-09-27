# HANDOFF 2026-09-27 — Mills + Wright COMPLETE (sorry-free, axiom-clean)

`src/LeanFormalizations/NumberTheory/Mills/` is sorry-free.  All four frozen headlines are
`[propext, Classical.choice, Quot.sound]`:

- `Wright.lean` — `wright : ∃ ω : ℝ, ∀ n ≥ 1, (⌊tower ω n⌋₊).Prime`.  **Unconditional.**
- `Basic.lean` — `exists_mills_of_primeBetweenCubes`, `exists_least_of_exists`,
  `exists_least_of_primeBetweenCubes`, plus the leaf `prime_add_one_lt_cube`.
  Conditional exactly where DIRECTION says: on `PrimeBetweenCubesFrom N` (Ingham).
  `IsMills`/`IsMinMills` untouched, still verbatim from formal-conjectures.

## The one real idea (both theorems)

The nested intervals must have a **strictly** decreasing right endpoint, or they collapse to a
single point whose tower/cube values are exactly the (composite) endpoint — the construction
then genuinely fails, it is not a proof artifact.

- Wright: Bertrand at `2^q` only gives `p ≤ 2^(q+1)`, and `p + 1 = 2^(q+1)` (a Mersenne prime)
  is not excludable.  Apply Bertrand at **`2^q − 1`** instead: `2^q` is composite so the prime
  returned still exceeds it, and `p ≤ 2(2^q − 1) = 2^(q+1) − 2` gives the strict margin free.
- Mills: `(n+1)³ − 1 = n(n² + 3n + 3)` is composite for `n ≥ 2` (`prime_add_one_lt_cube`).

Strictness at *both* ends of `ω`/`A` comes from stepping one index further:
`a n < a (n+1) ≤ ⨆ a ≤ b (n+1) < b n`.

## Machinery worth reusing

- `Wright.lean`: `invtower x n = (logb 2)^[n] x`, `tower_invtower` (inverts `tower` as soon as
  `tower 1 n < x`, the hypothesis that keeps every intermediate iterate positive and which
  propagates because `2 ^ q n < q (n+1)`), `tower_lt_logb`, `lt_logb_two_iff`.
- `Basic.lean`: no iteration helper needed — for `x ↦ x³` the `n`-fold iterate is `x ^ (3^n)`,
  so the endpoints are literal `rpow`s `x ^ ((3^k : ℕ) : ℝ)⁻¹` and `Real.rpow_inv_natCast_pow`
  does the inversion.
- `exists_least_of_exists` avoids sequences entirely: with `m = sInf S` and `q = ⌊m^(3^n)⌋₊`,
  openness of `{x | x^(3^n) < q+1}` plus `exists_lt_of_csInf_lt` produces one `A ∈ S` with
  `q ≤ A^(3^n) < q+1`, so `q = ⌊A^(3^n)⌋₊` is prime.  `m > 1` because every Mills number is
  `≥ 5/4` (`⌊A³⌋₊` prime ⇒ `A³ ≥ 2`).

## NOT done, deliberately (DIRECTION's red list)

Ingham's theorem; `PrimeBetweenCubesFrom` at any concrete `N`; irrationality/digits of Mills'
constant.  No lap may headline an unconditional Mills theorem.
