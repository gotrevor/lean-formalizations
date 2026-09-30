# Handoff — phase 53 COMPLETE (2026-09-30)

## What landed

`src/LeanFormalizations/NumberTheory/Mills/TribonacciCovering.lean` is **sorry-free** and the
three frozen statements are **axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only —
no `native_decide`, although the phase charter allowed it):

- `trib_three_pow_covering (k h) (|h| ≤ 3) : tribCoverPrime h ∣ trib (3^(1980k+95)) + h`
- `trib_three_pow_prime_free : ¬ Prime (trib (3^(1980k+95)) + h)` for `|h| ≤ 3`
- `trib_three_pow_prime_free_often : ∃ᶠ n in atTop, ∀ |h| ≤ 3, ¬ Prime (trib (3^n) + h)`

So `[T(3^n) − 3, T(3^n) + 3]` is prime-free for infinitely many `n` — Theorem C of
`ROADMAP-PRIME-TOWERS.md` for an order-3 recurrence, by explicit covering certificate.

## The proof, in five reusable pieces

1. `pow_eq_pow_of_dvd_sub` — in any monoid, `a^o = 1` and `o ∣ N − r` (with `r ≤ N`) give
   `a^N = a^r`. This is the whole periodicity engine; nothing about matrices.
2. `tribMatMod p := (Int.castRingHom (ZMod p)).mapMatrix tribMat` and
   `trib_cast_eq : ((trib N : ℤ) : ZMod p) = ((tribMatMod p)^N) 2 0`, from `map_pow` plus
   `TheoremA.tribMat_pow_apply`. Closed through defeq (`exact h`), per the
   `lean-mapmatrix-defeq-not-simp-equal` gotcha.
3. `order_dvd_exp_sub` — `o ∣ 3^95 * (3^1980 − 1)` implies `o ∣ 3^(1980k+95) − 3^95 % o`:
   `Nat.dvd_sub_mod` for the `3^95` reduction and `Nat.sub_dvd_pow_sub_pow` for
   `3^1980 − 1 ∣ 3^(1980k) − 1`, glued by `omega` on the ℕ-subtraction split.
4. `dvd_trib_add_of_cert` — the one certificate-consuming lemma; everything per-prime is a
   three-argument instantiation of it.
5. `not_prime_of_dvd_of_lt` + `trib_ge_self`/`big_trib` — `T(3^(1980k+95)) ≥ 3^95 − 2 > 593`,
   so a covering prime is always a *proper* divisor.

## Two performance gotchas worth remembering

- **`norm_num` cannot do `52 ∣ 3^95 * (3^1980 − 1)`** — it leaves `3^1980 − 1` unevaluated and
  hangs. `decide +kernel` closes all seven such goals in ~1 s each (GMP in the kernel).
- **`npowRec` on mathlib's closure-based `Matrix` is ~0.1 s per multiply under `native_decide`.**
  Exponents up to ~250 are free; `(tribMatMod 593)^3256 = 1` took ~5 minutes, and a first
  version of this file was still elaborating at 27 minutes. Fix: stage the power through
  **literal** matrices — `3256 = 8·11·37`, prove `A^8 = !![…]`, `(!![…])^11 = !![…]`,
  `(!![…])^37 = 1`, then `pow_mul` twice (`tribMatMod_593_pow_order`). Whole file: 10 s.
  With the staging, `decide +kernel` beats `native_decide` outright, which is why the file
  ended up axiom-clean.

## Next

Phase 53 is closed; `DIRECTION.md` has it marked DONE and `FACT-GRAPH.md` is regenerated
(30 edges, 31 hypotheses). Pick the next phase from `DIRECTION.md` / `Maze.lean`.
