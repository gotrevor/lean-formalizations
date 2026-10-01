# Door: the exceptional set of Erdős #385, and the repulsion test

Opened 2026-10-01.  Companion to `PROBE-ERDOS-385.md` (doors 2 and 3) and `LIT-ERDOS-385.md`.
Scripts: `scripts/erdos385-blocking-density.py`, `scripts/erdos385-bad-structure.py`.

## TL;DR

1. **Lemma R (rigidity, new as far as LIT and Tao's thread show, proof below).**  If
   `lpf(n − p) ≤ p` for every prime `p ≤ y` (with `n ≥ y + 2`), then `y# ∣ n`.  Equivalently, the
   only residue class mod `y#` in which every position `a ∈ [2, y]` is blocked is `0`.  So the
   blocking density is exactly `g(y) = 1/y#`, confirmed by exhaustive count for `y ≤ 23`.
2. **Corollary (deterministic).**  A bad `n` (i.e. `F(n) = n`) with `n < y#` has `n − 1` prime AND
   `n − p` prime for some prime `3 ≤ p ≤ y`.  So every bad `n` sits at the top of a prime pair with
   gap `< (1 + o(1)) log n`.  Checked on all 88 bad `n` in `[50, 10^6]`, with no violations.
3. **Elementary count (Lemma R + a uniform Brun twin-prime upper bound):**
   `#{n ≤ X : F(n) = n} ≪ X log log X / (log X)²`.  Lean-feasible with mathlib's Selberg sieve.
4. **Full count (Lemma R's probabilistic cousin + McDiarmid + the arithmetic large sieve):**
   `#{n ≤ X : F(n) = n} ≪_ε X exp(−(log X)^{1/2 − ε})`.  Beats every power of `log X`.  A paper
   level outline, not a treadmill target.
5. **Repulsion (door 3): no usable signal (85%).**  Carriers at different scales are independent
   within residue classes at small and mid scales.  Adjacent mid scales show a weak pairwise
   repulsion of 0.91–0.95 (z ≈ −4 to −8).  But the joint failure "no carrier with `p ≤ 512`" is
   **23× the product of the marginals**, and the two top scales couple at 4.6× (z = +8).  The net
   dependence runs in the conspiracy direction Tao feared.

## Definitions

- `p(m)` = least prime factor; `F(n) = max{m + p(m) : m < n composite}`.  CKS: `F(n) ≥ n` for
  `n ≥ 5`.  **Bad** := `F(n) = n`, equivalently no good position.
- Position `a ≥ 1` is **unblocked** for `n` if `lpf(n − a) > a`, i.e. no prime `q ≤ a` divides
  `n − a`.  It is **good** if unblocked and `n − a` composite, since then `m = n − a` has
  `m + p(m) > n`.
- So `n` is bad iff every unblocked `n − a` (`a < √n`) is prime.  `a = 1` is always unblocked, so
  `n − 1` is prime.
- For `s` mod `y#`, `a ≤ y` is unblocked for all `n ≡ s` iff `s ≢ a (mod q)` for every prime
  `q ≤ a`.  Write `U_y(s)` for the unblocked set in `[2, y]` and `u_y(s) = |U_y(s)|`.
- **Carrier** (form 2): a prime `p` with `p ∤ n`, `⌊n/p⌋ ≥ p`, and `⌊n/p⌋` free of primes `< p`.
  Each carrier gives the good position `a = n mod p`, and every good position arises this way.
  So bad ⟺ no carrier.

## Lemma R and its proof

**Lemma R.**  Let `y + 2 ≤ n` and suppose `lpf(n − p) ≤ p` for every prime `p ≤ y`.  Then every
prime `p ≤ y` divides `n`.

*Proof.*  Strong induction over primes.  `n − 2 ≥ 2` and `lpf(n − 2) ≤ 2` give `2 ∣ n`.  Suppose
every prime `< p` divides `n`.  Let `q = lpf(n − p) ≤ p`, a prime since `n − p ≥ 2`.  If `q < p`
then `q ∣ n` and `q ∣ n − p`, so `q ∣ p`, which is impossible.  Hence `q = p`, so `p ∣ n`.  ∎

Only prime positions are used.  The residue form: `u_y(s) = 0 ⟺ s ≡ 0 (mod y#)`.

| y | y# | g(y) = P(u = 0) | g(y)·y# | P(u ≤ 1) | P(u ≤ 2) | E u (exact = Mertens sum) |
|---|---|---|---|---|---|---|
| 11 | 2,310 | 4.33e-4 | **1** | 3.94e-2 | 3.39e-1 | 2.82 |
| 13 | 30,030 | 3.33e-5 | **1** | 7.49e-3 | 1.60e-1 | 3.22 |
| 17 | 510,510 | 1.96e-6 | **1** | 2.15e-3 | 4.82e-2 | 3.98 |
| 19 | 9,699,690 | 1.03e-7 | **1** | 4.72e-4 | 1.93e-2 | 4.33 |
| 23 | 223,092,870 | 4.48e-9 | **1** | 1.33e-4 | 6.01e-3 | 5.01 |

So `g(y)` is exactly the trivial lower bound `1/y# = e^{−(1+o(1))y}`, far below the
`exp(−cA/log A)` I guessed in the probe.

`u ≤ 1` is not rigid: `s ≡ c` (constant) has `u` tiny.  `P(u ≤ 1)` decays like `e^{−0.47y}`
over `11 ≤ y ≤ 23`.  Monte Carlo lower tail (200k samples): `P(u ≤ E u / 2)` is 4.8e-4 at
`y = 29`, 1.5e-5 at `y = 97`, and 0 observed for `y ≥ 199`.

**Corollary R′.**  Bad `n`, `y + 2 ≤ n < y#` ⇒ some prime `3 ≤ p ≤ y` has `n − p` prime.

*Proof.*  `n` is even because `n − 1` is an odd prime, so `n − 2` is composite.  If no `n − p` is
prime for `p ≤ y`, badness forces `lpf(n − p) ≤ p` for every such `p`.  Lemma R then gives
`y# ∣ n`, so `y# ≤ n`, a contradiction.  ∎

`#385`'s "bad ⇒ 3 ∣ n or n − 3 prime" is the `y = 3` instance.

## Part A: the exceptional-set bounds

### A1. Elementary: `#{bad n ≤ X} ≪ X log log X / (log X)²` (confidence 90% correct as stated)

Pick `y` with `y# ≥ (log X)²`, so `y ~ 2 log log X` (Chebyshev).  For bad `n < X`, either:

- `y# ∣ n`: at most `X/y# + 1 ≤ X/(log X)² + 1` such `n`; or
- by R′, `n − 1` and `n − p` are both prime for some prime `3 ≤ p ≤ y`.  That is a prime pair with
  gap `b = p − 1 ≤ y`.

Uniform Brun / Selberg (Halberstam–Richert Thm 3.11, `𝔖(b) ≪ b/φ(b)`):
`#{m ≤ X : m, m + b prime} ≤ C (b/φ(b)) X/(log X)²`.  Summed over `b ≤ y` this costs `≪ y`.

Total `≪ X/(log X)² + y X/(log X)² ≪ X log log X/(log X)²`.  No sum over subsets `S` and no
singular-series bookkeeping is needed, because Lemma R hands us one specific second prime.

### A2. Full: `#{bad n ∈ (X/2, X]} ≪_ε X exp(−(log X)^{1/2−ε})` (confidence 75% that the outline closes; constants unchecked)

Set `y = ¼ log X` (so `y# ≤ X^{1/3}`) and `Q = X^{1/3}`.  Condition on `s = n mod y#`.

1. **Forbidden classes.**  For each prime `q ∈ (y, Q]` and each `a ∈ U_y(s) ∪ {1}`, bad `n` has
   `n ≢ a (mod q)`.  Otherwise `q ∣ n − a` with `q > a` and `n − a > q`, so `n − a` is composite
   with `lpf > a`, a good position.  These are `ω(q) = u_y(s) + 1` classes per prime, the same for
   every `n ≡ s`.  This replaces the "sum over subsets S" of the probe: once `s` is fixed, the
   set of forced primes is deterministic.
2. **Arithmetic large sieve** (Montgomery 1968) on `n = s + y#·m`, `m ≤ X/y#`:
   `#{bad n ≡ s} ≤ (X/y# + Q²)/L(s)`, with
   `L(s) = Σ_{d ≤ Q, p∣d ⇒ p ∈ (y,Q]} μ²(d) ∏ ω(p)/(p − ω(p))`.
   - If `u_y(s) + 1 ≥ K := c y/log y`, keep `K` classes per prime.
   - Restrict to `d` = products of `j = ⌈(log X)^{1/2}⌉` distinct primes in `(y, Q^{1/j}]`.
   - Since `Σ 1/p ≥ (1/3) log log X` on that range, `L ≥ (eK log log X/(3j))^j ≥ exp((log X)^{1/2})`.
3. **Tail of `u_y(s)`.**  Need `P_s(u_y(s) < K) ≤ exp(−c y^{1/2−ε})`.
   - Positions `T ⊂ (y/2, y]` surviving the classes `s_q` for primes `q ≤ z = y^{1/2−ε}`.
   - Their number is `≥ c_ε y/log y`.  This is deterministic in the small residues, by the linear
     sieve lower bound at `s = log(y/2)/log z > 2`; one class per prime, remainder `≤ 1`.
   - The residues `s_q` for `q ∈ (z, y]` are independent uniform (CRT).  Let `Y` = number of
     positions in `T` unblocked by them.  Then `E Y ≥ |T| ∏_{z<q≤y}(1 − 1/q) ≫ y/log y`.
   - `s_q` moves `Y` by at most `2(y/(2q) + 1)`, so `Σ c_q² ≪ y²/(z log z)`.
   - McDiarmid: `P(Y < EY/2) ≤ exp(−c (y/log y)²·z log z/y²) = exp(−c y^{1/2−ε}/log y)`.
   - Finally `u_y(s) ≥ Y`.
4. Sum: `#{bad} ≤ X·P(u < K) + Σ_{u ≥ K} 3(X/y#)/L ≪ X exp(−c y^{1/2−ε}) + X exp(−(log X)^{1/2})`.

**What blocks the next improvement.**

- (i) **The tail exponent.**  The linear sieve needs `s > 2`, so `z ≤ y^{1/2}`, and McDiarmid
  charges the influence `y/z` of primes near `z`.  The data suggest the true tail is far lighter:
  fixed-`k` tails decay like `e^{−cy}`.  A tail of `exp(−c y/log y)` at `K ≍ E u` would give
  `X exp(−c log X · log log log X/log log X)`.
- (ii) **That is the ceiling of this framework.**  The moduli exceed `y ≍ log X` and
  `d ≤ √X`, so `d` has `≤ log X/log log X` prime factors.  Hence `L ≤ X^{o(1)}`.
- (iii) **`X^{1−δ}` needs positions `a ≫ log X`**, whose blocked status depends on `n` mod
  primes `> log X`.  Those residues cannot be conditioned on (too many classes).  This is the
  covering problem itself again, so `X^{1−δ}` is out of reach here (80%).

### A3. Calibration against A322293

The independent "Cramér" model is `P(n bad) = ∏_{a unblocked, a<√n} P(an a-rough number near n is
prime)`, with the latter `≈ 1/(log n ∏_{q≤a}(1 − 1/q))`.  It is summed over the actual controls,
i.e. all `n ≤ 10^6` with `n − 1` prime:

| n block | model | actual |
|---|---|---|
| [2^6, 2^13) | 15.4 | 83 |
| [2^13, 2^14) | 0.52 | 1 |
| [2^14, 2^18) | 0.23 | 0 |
| [2^18, 2^19) | 0.000 | **2** (267672, 267680) |

The model undercounts about 5× and gives the last two bad `n` essentially zero probability.  So
the failures at different positions are positively correlated (conspiracy), consistent with
Part B.  The 100 terms are far more than independence predicts, but they stop where the
conditioning runs out.  The `10^12` search is consistent with a finite list.

Bad `n` residues: `P(3 ∣ n)` = 0.66 vs 0.50 for controls.  `P(q ∣ n)` is about 1.2–1.5× baseline
for `q ∈ {5, 7, 11, 13}`, the mild primorial tilt Lemma R predicts.

### A4. Novelty and worth (honest)

- **Lemma R and R′**: probably unrecorded (65%; not in Tao's post, the erdosproblems thread, or
  `LIT-ERDOS-385.md`).  A one-line induction, but it sharpens Tao's primorial construction.
  `n ≡ 0 mod y#` is not just *a* way to block `[2, y]`, it is the *only* way.  R′ turns that into
  a structural fact about every bad `n`.
- **A1** is the natural "first real" count, beyond the trivial `π(X)`.  Easy for an expert (80%
  they would call it routine).  Its value is that it is elementary and fully Lean-able.
- **A2** is a genuine almost-everywhere theorem for the bad set (60% unpublished).  It is
  modest, since an exceptional-set bound cannot reach finiteness: the Siegel scenario is a
  measure-zero enemy.
- **Against DOOR-ALMOSTALL (Tao's "almost all n have F(n) = n + n^{1/2+o(1)}", via
  Guth–Maynard):** that statement is far stronger qualitatively, because it controls `F(n) − n`
  for typical `n`.  But its exceptional set is a density statement.  A zero-density route is
  limited near `σ = 1` by the Vinogradov–Korobov zero-free region.  So unconditionally I expect
  an exceptional measure no better than `X exp(−c (log X)^{1/3−ε})` (55%, not checked).  A2's
  bound on the bad set itself is then quantitatively stronger, and A1/A2 need no zeros at all.
  If DOOR-ALMOSTALL lands a power saving, A2 adds nothing quantitative, and Lemma R, R′ and A1
  remain the elementary companion.

## Lean candidates (frozen statements for a treadmill phase)

Mathlib has the Λ² Selberg upper-bound sieve (`Mathlib/NumberTheory/SelbergSieve.lean`) and
`primorial`.  PNT+ (already required) builds Brun–Titchmarsh on it (`BrunTitchmarsh.lean`), which
is the template for discharging the Brun prop below.  There is no large sieve and no McDiarmid,
so A2 is paper-only.  The #430 statement mirrors formal-conjectures PR #5261's
`Erdos430.terms` (do not propose #430 to FC; that PR exists).

```lean
namespace Erdos385Door

/-- `n` is good iff some composite `m < n` has `n < m + minFac m`
(iff `n < Erdos385.F n` in formal-conjectures). -/
def Good (n : ℕ) : Prop := ∃ m, 2 ≤ m ∧ m < n ∧ ¬ m.Prime ∧ n < m + m.minFac

-- L1 (cheapest, one lap): bad ⇒ n − 1 prime, and the CKS floor.
theorem prime_pred_of_not_good {n : ℕ} (hn : 5 ≤ n) (h : ¬ Good n) : (n - 1).Prime := sorry

-- L2 (Lemma R and Corollary R′; the new content).
theorem dvd_of_minFac_sub_le {n y : ℕ} (hyn : y + 2 ≤ n)
    (h : ∀ p, p.Prime → p ≤ y → (n - p).minFac ≤ p) :
    ∀ p, p.Prime → p ≤ y → p ∣ n := sorry

theorem exists_prime_sub_of_not_good {n y : ℕ} (h : ¬ Good n) (hyn : y + 2 ≤ n)
    (hlt : n < primorial y) :
    ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ y ∧ (n - p).Prime := sorry

-- L3 (edge to formal-conjectures PR #5261's #430 statement).
/-- Mirror of `Erdos430.terms` (formal-conjectures PR #5261). -/
def terms430 (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 1 n).filter fun m => ∀ p ∈ m.primeFactors, n - m < p

theorem good_iff_exists_composite_term (n : ℕ) : Good n ↔ ∃ m ∈ terms430 n, ¬ m.Prime := sorry

theorem erdos430_iff_eventually_good :
    (∀ᶠ n in Filter.atTop, ¬ ∀ m ∈ terms430 n, m.Prime) ↔ (∀ᶠ n in Filter.atTop, Good n) := sorry

end Erdos385Door

namespace Literature

/-- Uniform Brun/Selberg upper bound for prime pairs with gap `b`
(Halberstam–Richert, *Sieve Methods*, Thm 3.11, with `𝔖(b) ≪ b/φ(b)`).
Dischargeable from mathlib's `SelbergSieve`, following PNT+'s `BrunTitchmarsh`. -/
def BrunUniformGap : Prop :=
  ∃ C : ℝ, ∀ b X : ℕ, 1 ≤ b → b ≤ X → 2 ≤ X →
    (((Finset.range X).filter (fun m => m.Prime ∧ (m + b).Prime)).card : ℝ)
      ≤ C * ((b : ℝ) / (Nat.totient b)) * X / (Real.log X) ^ 2

end Literature

open Classical in
-- L4 (headline, A1): from `Literature.BrunUniformGap` + L2 + a Chebyshev lower bound for primorial.
theorem Erdos385Door.card_not_good_le (hB : Literature.BrunUniformGap) :
    ∃ C : ℝ, ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter (fun n => ¬ Erdos385Door.Good n)).card : ℝ)
        ≤ C * X * (Real.log (Real.log X)) ^ 2 / (Real.log X) ^ 2 := sorry
```

- **Recommended phase:** L1–L3 plus L4 in one target file, with L2 as the crux.
- The `(log log X)²` gives slack for a crude primorial lower bound such as `y# ≥ 2^{π(y)}` if
  Chebyshev's `θ(y) ≫ y` is not to hand; PNT+ has it anyway.
- Discharging `BrunUniformGap` is a separate, sizeable phase in the PNT+ `BrunTitchmarsh` style.
  It is optional: L4 stands as a Prop-gated edge without it.

## Part B: repulsion between scales (door 3)

Run: `scripts/erdos385-bad-structure.py 1000000`.  Controls are all `n ≤ 10^6` with `n − 1`
prime (78,483).  Coupling tests use `n ≥ 2^18`, so every scale lies below `√n`; without that cut,
an empty high annulus is trivially "no good `a`" and `n`-size fakes a correlation.

- **Good positions by annulus** `a ∈ (2^{j−1}, 2^j]`.  The ratio
  `P(none_I ∧ none_J)/(P(none_I)P(none_J))` is 0.93–1.10 for `j ≤ 7` within `n mod 210`.  The
  raw 0.74/0.79 at `j2–j3` and `j3–j4` are explained entirely by `n mod 210`.
  - The top pairs couple positively: `j7–j8` 2.0, `j8–j9` 3.1, shrinking to 2.4 once we also
    stratify on which primes `11..61` divide `n`.
  - Stratifying on the carrier count flips them to 0.65.  That is the trivial multinomial
    conservation artifact, not repulsion: a fixed number of carriers placed in one annulus is
    absent from the other.
- **Carriers by dyadic range of `p`** (the right variable, since bad ⟺ no carrier):
  - Within `n mod 210` and divisibility by `11..61`, pairs are independent (1.00) at `p ≤ 8`.
  - Adjacent mid ranges are mildly repulsive: `(8,16]–(16,32]` 0.94 (z −7), `(16,32]–(32,64]`
    0.91 (z −8), `(32,64]–(64,128]` 0.94 (z −4).  Real, not explained by small-prime divisibility,
    mechanism unknown, about a 7% effect.
  - The two top ranges `(128,256]–(256,512]` couple at **4.6×** (z +8; 3.8× after
    stratification).
  - Globally: `P(no carrier with p ≤ 512)` = 3.6e-5, against a marginal product of 1.5e-6,
    i.e. **23× enhancement**.
- **Small-prime kill profile** (Tao's Siegel scenario: survivors of `0 mod q`, `q ≤ √h`, in
  `[n−h, n)`, normalized):
  - Bad `n` sit at the median of same-size controls at every scale (ratio about 1.0, percentile
    0.26–0.92).
  - They die because the unblocked survivors happen to be prime, not because small primes wipe
    out the interval.
  - At heights `≤ 3·10^5` this says nothing about Siegel zeros either way.
- **Quadratic-character bias**: the mean of `(D / n − a)` over the unblocked (hence prime)
  `n − a` is within ±0.05 of the controls for all 9 discriminants `|D| ≤ 13`.  That is noise at
  this sample size.  `χ_{−3}(n) = −0.34` for bad `n` is just `n − 1` prime plus `3 ∣ n`.

**Verdict (85% no).**  Tao's repulsion would need negative dependence between carrier scales,
strong enough to make "no carrier anywhere" impossible.  The measured dependence is about
independent within residue classes, with a weak adjacent-scale repulsion (≈ 0.92).  It is
dominated by positive coupling: 23× joint enhancement, top scales 4.6×.  The "best-case `m`"
reading (any one carrier suffices) is exactly what was measured.  Nothing here suggests a
mechanism.  The one unexplained item worth a footnote is the ~8% adjacent-range repulsion at
`p ∈ (8, 128]`; a cheap follow-up is to see whether it persists at `10^8` and whether it comes
from `⌊n/p⌋` and `⌊n/p'⌋` sharing small factors.  Do not plant a phase on it.
