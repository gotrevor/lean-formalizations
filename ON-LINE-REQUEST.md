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
