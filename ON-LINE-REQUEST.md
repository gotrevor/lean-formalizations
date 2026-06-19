# Online requests — no-three-in-line / HJSW frontier

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
- For `p = 7` an **exhaustive** search over all `4^6` corner-drop assignments found **NO** valid
  18-point config. So the HJSW construction is **NOT** "3 of 4 rectangle corners per residue" — that
  was a `p = 5` coincidence. The real construction must differ (different curve, different lift rule,
  or non-uniform per-residue selection). I need the paper to know what it actually is.

A scan of any modern exposition giving the construction explicitly (Brass–Moser–Pach *Research
Problems in Discrete Geometry* §10.1; Pór–Wood; Flammenkamp's pages) would also do.
