# Fauzan 2026, "ζ(5) is irrational" — analysis and computational audit

**Status (2026-09-22, against Zenodo v1): NOT refuted.  Every claim that can be checked at
reachable K holds, and the outer-range p-adic bounds hold with equality at most primes.  The
constants all reproduce.  What remains unverified is the inner-range Proposition 4.1 (needs
K ≥ 320 000 to instantiate) and the o(K²) bookkeeping around it.  The paper is a serious object,
not a Sun-style Zenodo artifact.  Confidence it is correct: ~40%, up from a ~5% prior.**

| | |
|---|---|
| Paper | Aabir Fauzan (Aalto), *ζ(5) is irrational*, [Zenodo 22826419](https://zenodo.org/records/22826419), 17 Sep 2026, v1.  "Subsequent revisions on arXiv once announced there" — not on arXiv as of 2026-09-22. |
| Local | `papers/fauzan-2026-zeta5-irrationality.{pdf,txt}` (PDF gitignored; md5 `30dafe4adbb13a79f202e94a046c8c8d` = Zenodo's) |
| Probes | `fauzan-zeta5-hankel-probe.py [n]` (exact Δ_K for K=40n), `fauzan-zeta5-constants.py`, `fauzan-zeta5-inner-heuristic.py` — uv shebangs, run directly |
| Surfaced | r/mathematics, u/yaymayata2, 2026-09-22 ("GPT couldn't find a concrete gap"); Trevor's claude.ai chat said "almost certainly not" on priors alone |
| AI provenance | "A generative AI tool was used in a supporting role for editing … and consistency checks."  Author claims full responsibility. |

## 1. What it claims, in our screen's vocabulary

The three-way screen (`~/personal/claude/knowledge/core/projects/irrationality-construction-screen.md`)
says every known family has two of: (A) positivity nonvanishing, (B) bounded denominators, (C)
narrow beam.  Our 2026-09-04 verdict on the moment/Hankel family for Catalan was that it has (A)
and (C) and loses (B) **by a constant**: numerator rate `log cap` vs denominator rate `lcm`.

This paper is the moment/Hankel family with two changes that attack exactly that constant:

1. **The determinant is a polynomial in X of degree h = λK, not a linear form.**  Entries
   `G_ij(X) = μ_X(D_N(t)^6 t^{i+j}/D_K(t))` are affine in X; `Δ_K(X) = det` has degree h with
   integer leading coefficient (2.9).  The irrationality step is `b^h Q(a/b) ∈ ℤ_{>0}` against
   `Q(ζ(5)) < e^{-cK²}`: the polynomial's *height never enters*, only its degree, which costs
   `λK log b` against a `K²` decay.  So (B) is replaced by a race between two K² constants.
2. **A varying weight `D_N^6/D_K`** (the Christoffel-type transform we found harmful for
   Catalan) plus the ζ(5)-specific arithmetic of the pole values `j⁴(X − H_j^{(5)}) − 1/4 + 1/(2j)`:
   the p-adic side uses a Bernoulli distribution formula (Lemma 3.2) and residue-class bases
   (§4) to show the determinant's denominators are far smaller than the entries' suggest.

The race, per K²: real decay `U = −1.36700` (Lemma 6.1, potential theory with an explicit
16-arcsine comparison measure) against arithmetic clearing `A_200 = 1.34959` (§5).  Margin
`0.0174`, i.e. **1.3%** of either side.  `1600·0.0174 = 27.85 > 139/5`.

## 2. What we checked, and how

`fauzan-zeta5-hankel-probe.py n` builds `G_K(X)` exactly (python-flint), computes
`Δ_K(X) ∈ ℚ[X]` by evaluation at h+1 integer points + Newton interpolation, and tests the paper's
own propositions wherever their hypotheses hold at that K.

| Claim | K=40 (h=37) | K=80 (h=74) | K=120 (h=111) | K=160 (h=148) | K=200 (h=185) |
|---|---|---|---|---|---|
| (2.9) leading coefficient | ✅ exact | ✅ exact | ✅ | ✅ | ✅ |
| Δ_K(ζ(5)) > 0 | ✅ | ✅ | ✅ | ✅ | ✅ |
| (3.12) small-prime bound, all p | ✅ (large slack) | ✅ | ✅ | ✅ | ✅ |
| Prop 4.3 outer range (4.14), p ∈ (K/3, K] | ✅ **equality at 4/6 primes**, slack 1 at the other two | ✅ equality at 11/13 | ✅ 14/18 | ✅ 15/21 | ✅ 21/28 |
| p > K ⇒ Δ_K p-integral | ✅ all primes to 2K | ✅ | ✅ | ✅ | ✅ |
| residual denominator beyond 2K | 1 | 1 | 1 | 1 | 1 |

`fauzan-zeta5-constants.py` (mpmath, 2 min):

| Constant | Paper | Recomputed |
|---|---|---|
| Table 1 measure: Σc_j = λ, nested, lengths > 1/225 | | ✅ |
| Lemma 6.1: sup_t (2U^ρ − V) ≤ M0 = −6.645 | | sup = **−6.6499** at t≈0.6195 ✅ (slack 0.005) |
| I(ρ) | −2.126593445148 | −2.12659344515 ✅ |
| C* (6.3) | 2.653035990340 | 2.65303599034 ✅ |
| U = λM0 − I(ρ) + C* | −1.3669955 | −1.36699556 ✅ |
| (5.18) ∫₃²⁰ R/x³ | 0.0427882 | 0.0427857 ✅ (midpoint rule) |
| (5.16) ∫₂₀^∞ R/x³ ≤ −0.05602 | | ∫₂₀^2000 = −0.05965 ✅ |
| (5.10) I_out | 1.3307396 | 1.3307411 ✅; prime sum at K=120000 gives 1.3271 (converging from below) |
| (4.14) vs (5.8): −γ_p^out − K(R0−d)(p/K) | O(1) | max 7 over all outer primes at K=120000 ✅ |
| (7.2) −1600(A_200+U) | 27.852 > 27.8 | ✅ |
| Moment representation (2.10), monomials e≤3 and poles j=1,2,5 | | ✅ quadrature to 15 digits |

R(x) computed two ways — from (5.4)-(5.6) directly and from the expansion (5.12)-(5.13)+(B.1) —
agree to 1e-27 on [3,20], so the paper's algebra there is right.

### 2.1 Larger K — the same picture

| K | outer primes with (4.9) | equality | max slack | inner window p²>5K: true − predicted | log F_K(ξ)/K² (→ ≤ −1.367) | −log cont(F_K)/K² (→ ≤ 1.3496) | log P_K(ξ)/K² |
|---|---|---|---|---|---|---|---|
| 40 | 6 | 4 | 1 | (empty) | −1.276 | 1.110 | −0.166 |
| 80 | 13 | 11 | 39 | p=23: +14 | −1.329 | 1.199 | −0.130 |
| 120 | 18 | 14 | 78 | p=29,31,37: +18, +25, +21 | −1.348 | 1.223 | −0.125 |
| 160 | 21 | 15 | 59 | p=29…53: +16 to +37, all positive | −1.357 | 1.230 | −0.127 |
| 200 | 28 | 21 | 138 | p=37…61: +18 to +32, all positive | −1.363 | 1.251 | −0.112 |

Reading: the outer bound (4.14) is a valid lower bound at every tested prime and is *sharp* at
most of them (the slack sits at the smallest primes of the range, p just above K/3, where the
rank correction `min(r_p, ·)` is coarse).  In the only window where Prop 4.1's hypothesis on p
holds (`p² > 5K`), the true valuation exceeds its asymptotic prediction `pΓ(K/p)` every time.
The real side climbs monotonically toward the paper's U from above, as the `24K log K` term in
(6.16) predicts; the arithmetic side climbs toward A from below.  Neither has crossed its limit.
The primitive-polynomial ledger is negative at every K, but the sign at K ≤ 200 is dominated by
lower-order terms and proves nothing about the K² race.

## 3. What is NOT checkable, and where a specialist should look

1. **Proposition 4.1 (inner range K/M < p ≤ K/3).**  Its construction reserves `L_0 = 4M+10`
   rows for the zero class, needs `K ≥ 200M²`, `M ≥ 40`, hence `K ≥ 320 000`, `h ≥ 296 000`.  No
   determinant of that size will ever be computed.  It is fully load-bearing: replacing it by the
   crude (3.12) on the inner range would cost ≈ `2λ = 1.85` per K², far more than the `0.0174`
   margin.  The paper's asymptotic form of its conclusion, `γ_p^in = pΓ(K/p) + O_M(1)`, can be set
   beside the true `v_p^G(Δ_K)` at small K (the `pΓ(K/p)` column of the probe): in the window
   `p² > 5K` the true valuation exceeds the prediction (K=80, p=23: −188 vs −202), as it should if
   the bound is a valid lower bound; below that window (p=5,7 at K=80) the true valuation falls
   short of the prediction by 100+, which is where the paper does NOT use Prop 4.1.  Consistent,
   not probative.
2. **The o(K²) terms.**  (5.11) is a lim sup with `O_M(1)` per prime, `O(K^{3/2} log K)` for
   `p ≤ √(5K)`.  Any K² term hiding in those would eat a 1.3% margin.  The `O_M(1)` claim in (5.7)
   rests on the allocation being uniform at the `2Hx ∈ ℤ` transitions — stated, not proved in
   detail.
3. **Lemma 3.2 (the distribution formula for the harmonic functional) — CHECKED.**  It carries
   the inner range and is an identity in ℚ_p, checkable independently of K.
   `fauzan-zeta5-distribution-check.py p` evaluates the right side of (3.7) for `g = 1/(x−r)` with
   the Tate-algebra expansion (3.5) for far poles and `Y = p⁵X + C_p`, and compares the X-free
   part with `H^{(5)}_{d(r)}`: at p=7 and p=11, for r ∈ {0,…,23, −1,…,−12}, the difference has
   valuation ≥ 59 (= the series truncation), `v_p(C_p) = 5` as claimed, the polynomial case
   reproduces Bernoulli multiplication exactly, and the negative control (B₁ = +1/2) fails at
   valuation 1.  So the formula, its sign conventions, and the `d(r)` reflection rule are right.
   What Lemma 3.1 adds on top (norm ≤ p of τ on the Tate algebra, integrality under the degree
   restriction `deg U₀ ≤ p+1`) is short and standard (von Staudt–Clausen).
4. **Tightness is itself a tell.**  The outer bounds being exact at K=40 and K=80 means the author
   computed them for small K and tuned (α=3/40, λ=37/40, the 16-interval measure, M=200).  That
   is how a real proof gets its constants, and also how a wrong one gets its confidence.

## 4. Relation to our own work

- **The screen needs a fourth column.**  (B) "bounded denominators" is the linear-form condition.
  A degree-λK polynomial with integer coefficients trades (B) for
  "arithmetic K² constant < real K² constant", with the height free.  Our Catalan Hankel
  refutation (`catalan-hankel-sublattice.md`) measured exactly those two constants for the
  Catalan moment matrix — `log 4 = 1.386` vs lcm rate `4` — and lost by 2.6 per m².  Fauzan's
  win, if real, comes from (i) the external field `D_N^6/D_K` moving the real constant and
  (ii) residue-class cancellation in the harmonic-sum denominators moving the arithmetic one.  Both
  are worth re-examining for Catalan: `T_m = Σ (−1)^r/(2m+2r+1)²` partial sums have the same
  "pole values congruent within a class mod p" structure.  → screen leaf updated with a pointer.
- **Same instrument as the Sun audit** (`sun-2026-catalan-irrationality.md`): read the whole
  paper, compute its own integer exactly, compare with its own claims.  Sun failed at the first
  2-adic valuation.  Fauzan passes every exact check available.  The difference in kind is worth
  recording: Sun's paper was a chain of asserted inequalities; this one comes with rational
  enclosures, explicit tables, and constants that reproduce to 12 digits.

## 5. Run log

- 2026-09-22: `fauzan-zeta5-hankel-probe.py` n=1..4 (K=40..160; 8 s, 1 min, ~6 min, ~25 min);
  `fauzan-zeta5-constants.py` (2 min); `fauzan-zeta5-distribution-check.py` 7 and 11;
  `fauzan-zeta5-inner-heuristic.py` 40, 80.  Logs in the session scratchpad; the tables above are
  the record.  n=5 (K=200, h=185, ~50 min) clean: 28 outer primes, 21 with equality.
