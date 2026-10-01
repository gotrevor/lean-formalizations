# Door 1 for Erdős #385: the F_q[T] analogue (CLOSED ROUTE)

Closed 2026-10-01.  Prior art is in `LIT-ERDOS-385.md` §1.
- Sawin posed this analogue in the comments on Tao's post (2024-08-22) and showed GRH alone falls
  short at fixed `q`.
- Large `q` is a one-line corollary of BBR (arXiv:1302.0625, Thm 2.3).
- Fixed `q` sits at the square-root barrier (Gorodetsky arXiv:1810.00483, Thm 1.1, needs
  `h > n/2`).

Probe: `scripts/erdos385-ff-probe.py q nmax [--list]`.  Tests: `scripts/test_erdos385_ff_probe.py`
(hand-derived expectations, run through the CLI).

## Statement used

`f` monic of degree `n` over `F_q`; `mfd(g)` is the least degree of an irreducible factor.
- **Good** means some reducible monic `g ≠ f` of degree `n` has `deg(f − g) < mfd(g)`.
- **Witness form**: some monic irreducible `P` with `2 deg P ≤ n`, `P ∤ f` has `f div P` free of
  factors of degree `< deg P`.  This is the analogue of `m = p·⌊n/p⌋`, proved by uniqueness of
  division.
- **(ii) analogue**: the largest witness degree `A(f)` tends to infinity.
- **Top analogue**: `A(f) = ⌊n/2⌋`, a balanced semiprime in `I(f, ⌊n/2⌋)`.

**Degeneracy (recorded; not found in the literature sweep).**  If `f(a) ≠ 0`, then
`g = f − f(a)` is a witness of degree 1.  So:
- bad ⇒ `T^q − T ∣ f` and `f + c` is irreducible for all `c ≠ 0`;
- every bad `f` has `deg f ≥ q`;
- the (i) analogue is **trivially true when `q > deg f`**.

The degree-`q` case is realised by Artin–Schreier for `q = 3, 5` (`T^q − T` is bad), but not for
`q = 7`, where `T^7 − T` is good.  Only the (ii)/top analogues carry content at large `q`.

## Computation (q prime, exhaustive over all monic f of each degree)

| q | degrees with bad f (counts) | no bad f for | top analogue holds for every f |
|---|---|---|---|
| 2 | 2..16: 1,2,3,6,7,14,18,28,24,48,38,38,17,22,14 | 17..25 | 21..25 |
| 3 | 3, 5, 7 (1, 6, 9) | 8..15 | 10..15 |
| 5 | 5 only (`T^5 − T`) | 6..10 | 6..10 |
| 7 | none | 2..8 | 2..8 |

The bad set dies out early, like A322293 at 267680.  The last bad degree falls fast with `q`:
16, 7, 5, none.  For `q = 2`, `min A(f)` is `⌊n/2⌋` from `n = 21` on.

## Why closed

- Sieve-only arguments still meet the known-false sibling.  Classes `0 mod P` for `deg P < h`
  cover every non-constant polynomial of degree `< h`, leaving only `F_q^*`.  CRT transports this
  to any `f ≡ 0 mod ∏_{deg P ≤ H} P`.
- Level equals sifting range (`s = 1`), and the condition `mfd(g) > deg(f − g)` is
  scale-invariant, so there is no slack.
- Weil RH reaches only `h > n/2 + log_q n`.  The top analogue misses by a polynomial-in-`n` factor
  (Sawin's computation: `(n − m − 1)² q^{n/2}` per character).

**reopenIf:** either of these, applied to factorization types with two factors of degree `> h`
in **every** `I(f, h)` with `h < n/2`:
- a fixed-`q` short-interval estimate below the square root for prime-type factorization
  functions; or
- a Sawin–Shusterman-style special-`q` geometric input.
