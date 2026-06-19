# Online requests — no-three-in-line / HJSW frontier

## ✅ 2026-06-19 — RESOLVED IN-HOUSE (construction found; request now LOW priority)
The construction crux below was **solved locally** without the paper: a closed-form selection rule
for the sheared hyperbola was discovered and verified (exact integer determinant) for every prime
`3 ≤ p ≤ 109`. See `SELECTION-RULE-FOUND.md`. The remaining work is a routine (if intricate)
modular-arithmetic *proof* of the count, not a search for the construction. **A scan of HJSW 1975
would still be a nice cross-check** of the published point set / proof, but it is no longer blocking.
The detailed (now-historical) ask is preserved below for context.

---

## 2026-06-19 — HJSW 1975 explicit construction + collinearity proof (UNBLOCKS `hjsw_lower`)

**What I need.** The *explicit point set* and the *no-three-collinear proof* from:

> R. R. Hall, T. H. Jackson, A. Sudbery, K. Wild, "Some advances in the no-three-in-line
> problem", J. Combinatorial Theory Ser. A **18** (1975), 336–341.

Specifically:
1. The exact definition of the `3(n−2)/2`-point configuration (for which `n`? the statement uses
   `n = 2p`, `p` prime, giving `3(p−1)` points in the `2p × 2p` grid — confirm this and the precise
   grid/coordinate conventions). Is it really points on the modular hyperbola `xy ≡ k (mod p)`, and
   if so **which lifts** into `[0, 2p)²` are chosen, and for which `k`?
2. The argument that no three of those points are collinear over ℝ — in particular how it handles
   triples whose `x`-coordinates coincide mod `p` (the cross-"arc" collinearities), which is the
   part the single-arc Vandermonde argument does NOT cover.

**Why it unblocks me.** I have proven, axiom-clean, that a single modular-hyperbola arc
`xy ≡ k (mod p)` has no three collinear points (`hyperbola_noThreeCollinear`, the Vandermonde
determinant reduction). The open part of `hjsw_lower` is purely the *covering count*: assembling
`3(p−1)` actual grid points and ruling out collinearities between points on different lifted arcs.
I need the paper's exact construction + that cross-arc argument to formalize it.

**What I already ruled out experimentally (so don't re-suggest these).** Using a verified decidable
certificate (`decNoThree`, `native_decide`), I searched the natural "3 of the 4 rectangle-corners
`{r,r+p}×{s,s+p}` per residue `r` (with `s = r⁻¹ mod p`)" family:
- For `p = 5` valid 12-point configs EXIST (e.g. `witness5` in `Anchors.lean`, certified).
- For `p = 7` an **exhaustive** search over all keys `k ∈ {1..6}` AND all `4^6` corner-drop
  assignments found **NO** valid 18-point config. So the HJSW construction is **NOT** "3 of 4
  rectangle corners per residue" for any `k` — that was a `p = 5` coincidence. The real construction
  must differ (different curve, different lift rule, multiple curves, or a subset with non-uniform
  per-residue counts). I need the paper to know what it actually is.
- The three-arcs-in-three-`p×p`-blocks family (with reflections, `k=1`) also fails for `p = 7`.
- **Stronger negative result (computed this lap):** for `p = 7`, take ALL `24 = 4(p−1)` lifts of a
  *single* hyperbola `xy ≡ k (mod p)` into `[0,2p)²`. The collinear triples among them have a minimum
  hitting set of size `≥ 7` for **every** `k ∈ {1..6}` (exhaustive over `C(20,6)` drops), so the
  maximum no-three subset of one curve's lifts is `≤ 17 < 18`. **⇒ HJSW cannot be a single modular
  hyperbola; it must combine ≥ 2 distinct curves** (or use a genuinely different construction). So the
  precise question I need answered: *which* curves/keys, and *which* lifts, does HJSW combine, and how
  is the cross-curve non-collinearity proven?
- **Obstruction characterized:** the single-curve collinear triples are all **slope ±1 alignments** —
  `(r,s)` and its diagonal lift `(r+p,s+p)` lie on the line `y = x+(s−r)`, and distinct residues with
  equal `s−r` pile onto the same line (≥3 points). So whatever HJSW does, it must avoid letting three
  chosen points share a slope-±1 line. If the paper's trick is exactly "pick lifts to break the
  slope-±1 alignments", confirming that (and the rule) is what I need.

A scan of any modern exposition giving the construction explicitly (Brass–Moser–Pach *Research
Problems in Discrete Geometry* §10.1; Pór–Wood; Flammenkamp's pages) would also do.

### 2026-06-19 update — sharpened ask (after ruling out the whole hyperbola-lift family)
I have now *proven* (and computationally confirmed) several negatives that narrow exactly what I
need from the paper:
- **Uniform "3 of the 4 lifts of a single hyperbola `xy ≡ k`" reaches `3(p−1)` iff `p = 5`.** Each
  base point `P_a=(a,a⁻¹)` sits on a slope-`+1` line shared with `P_{−a⁻¹}` and a slope-`−1` line
  shared with `P_{a⁻¹}`; avoiding a collinear triple forces it to drop *both* a diagonal and an
  anti-diagonal lift, but 3-of-4 drops only one — impossible unless `a` is an involution fixed
  point (`a²=±1`). Only `p=5` has all `p−1` base points fixed. (Exhaustive `4^(p−1)` check: p=5 ✓,
  p=7 ✗.)
- **Even non-uniform single-hyperbola lifts cap at `≤17` at `p=7`** (collinear-triple hypergraph has
  min hitting set `≥7`), and a fresh probe shows **no** structured single base reaches `18` at
  `p=7`: `xy=k`, `y²−x²=c`, `x²+y²=c`, `y=x^m` (m coprime p−1), `(x+1)(y+1)=k`, `y=x²` all fail.
  Prior lap: 2-hyperbola-lift unions also cap `<18`.

So the precise things I still need from HJSW 1975 (or any explicit exposition):
1. **The exact point set** — is it lifts of a curve at all? If so, *which curve(s)*, *which key(s)*,
   and *which lifts* (the non-uniform selection rule) — and how does it dodge the slope-`±1`
   over-constraint above? If it is NOT lift-based, what is the closed-form coordinate description?
2. **The cross-point non-collinearity argument** (the part beyond a single arc's Vandermonde).
3. Confirm the grid/coordinate convention (`n = 2p`, count `3(p−1)`) matches the paper's `3(n−2)/2`.

This is now the *sole* blocker for `hjsw_lower`; the geometric reduction (real-collinear ⇒ residues
mod-`p`-collinear ⇒ two lifts coincide) is already formalized & axiom-clean in `Hyperbola.lean`.
