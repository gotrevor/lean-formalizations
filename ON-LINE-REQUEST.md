# Online requests — no-three-in-line / HJSW frontier

## ✅ CLOSED — HJSW 1975 construction (no action)
The prior ask (HJSW explicit point set + collinearity proof) is **fully resolved**: `hjsw_lower` is
proven & axiom-clean via the closed-form sheared hyperbola `shearSel p`. No paper scan needed.

---

## 2026-06-19 — Nagura's theorem (1952): the tuned numerical inequality (UNBLOCKS `nagura_prime`)

**What I need.** The explicit proof of **Nagura's theorem** — for `n ≥ 25` there is a prime in
`(n, 6n/5]` — specifically the *precise central-binomial / Chebyshev numerical inequality* it turns on,
in enough detail to formalize. Primary source:

> J. Nagura, "On the interval containing at least one prime number", Proc. Japan Acad. **28** (1952),
> 177–181.

Or any modern exposition that gives the explicit estimate (e.g. expositions deriving "a prime in
`(n, 1.2n]`" from bounds on the Chebyshev `θ`/`ψ` functions or on `C(2n,n)`'s prime factorization).

**Exactly what to extract:**
1. The precise inequality that plays the role of mathlib's `Bertrand.real_main_inequality`
   (`x·(2x)^√(2x)·4^(2x/3) ≤ 4^x` for `x ≥ 512`) but tuned for ratio `6/5` — i.e. the function whose
   sign change forces a prime in `(n, 6n/5]`, and the threshold `N₀` above which it holds.
2. How the `(6n/5, 2n]` prime product (or the `θ(2n) − θ(6n/5)` gap) is bounded **sharply** — this is
   the crux. My elementary bounds are provably too weak (see below).
3. The exact small-`n` range `[25, N₀)` to discharge by computation, and whether `25` is tight.

**Why it unblocks me / what I already established (don't re-suggest the crude route).** This lap I
built the full elementary Chebyshev lower-bound infrastructure in `PrimeGap.lean`, all axiom-clean:
`four_pow_lt_mul_lcm` (`4ⁿ<n·lcm(1..2n)`), the von-Mangoldt↔lcm bridge `log_lcm_Icc_eq_psi`, and the
ψ/θ **lower** bounds `psi_lower`/`theta_lower` (mathlib has only upper bounds). **But I proved these
are insufficient for `6/5`:** the best *elementary* lower constant is `θ(x) ≳ (log4/2)x ≈ 0.69x`
(lcm/central-binomial cap it there; true `θ(x)~x` needs PNT), and feeding it into the central-binomial
split gives `C(2n,n) ≤ (2n)^√(2n)·4^(31n/15)` with `31/15 ≈ 2.07 > 1` — no contradiction. So Nagura
genuinely needs its *sharper* estimate, not a reparametrization of Bertrand. I need the paper's actual
inequality to formalize the `nagura_prime` crux (everything downstream — the `5/4` no-three-in-line
constant — is already wired).

(Aristotle job `1644a603` is also attempting `nagura_prime` from scratch; this request is the by-hand
backup / cross-check.)

---

## 2026-06-19 (UPDATE) — Nagura request now SECONDARY; primary ask is *refined Chebyshev constants*

**Status change.** The general-`N` no-three-in-line constant has been pushed **unconditionally** past
Bertrand's `3/4` — to `15/16` and then `6/5` — WITHOUT `nagura_prime`, via a from-scratch refined
two-sided Chebyshev stack (`psi_refined_lower`/`theta_refined_lower`/`psi_refined_upper`, all
axiom-clean, in `PrimeGap.lean`). My leading constant is `A = (7/15)log2+(3/10)log3+(1/6)log5 ≈ 0.9213`
(lower) and `(6/5)A ≈ 1.106` (upper), from the elementary `2,3,5,30` Chebyshev `T`-combination + a
6-fold telescoping iterate. This yields a prime in `(n, c·n]` for any fixed `c > 6/5`.

**What I now need (to go from `6/5` toward HJSW's `3/2 − o(1)`):** the **sharper elementary Chebyshev
bounds** and the optimal `T`-function prime combination — i.e. the Rosser–Schoenfeld / Diamond–Erdős /
Costa Pereira line that pushes the explicit constants `0.92 ≤ ψ(x)/x ≤ 1.106` toward `1` by using a
*better linear combination* of `log(⌊x/k⌋!)` (more primes / larger modulus than `2,3,5,30`).
Specifically:
1. The explicit coefficient vector `(c_k)` (analogue of my `1,−1,−1,−1,+1` at `1,2,3,5,30`) that
   maximizes the lower constant `A = ∑ c_k (log k)/k`-type sum subject to the floor combination staying
   in `{0,1}` (the period/`decide` condition) — and the resulting best elementary constants.
2. Costa Pereira's "elementary proof of the prime number theorem"-style sharpening, or Diamond–Erdős,
   giving explicit `ψ(x) ≥ (1−ε)x` for any ε via finite combinations — with the combination written out.
3. (Still useful, secondary) Nagura's exact `6/5` numerical inequality for the small-`n` (`n≥25`)
   `nagura_prime`, now NON-blocking but the path to the exact `5/4` constant.

This unblocks PENDING_WORK path 2 (generalize `floor_comb_bounds`/`logFactorial_leading_identity` to the
chosen coefficient vector and re-run the assembly), the only route that scales toward `3/2`.
