# Online research requests — lean-formalizations

A networked host session fulfills these: commit an `ON-LINE-FINDINGS-<date>-<topic>.md`, DELETE the
answered item below, and remove this file once nothing is left open.

---

## 2026-06-19 — HJSW `3N/2` no-three-in-line construction (the covering / count)

**Theorem.** Hall, Jackson, Sudbery, Wild, "Some advances in the no-three-in-line problem,"
*J. Combin. Theory Ser. A* 18 (1975) 336–341. They place `(3/2 − o(1))·N` points on an `N×N` grid
with no three collinear — the best *proven* lower constant, unimproved since 1975.

**What I have already (committed, axiom-clean).** `Combinatorics/NoThreeInLine/Hyperbola.lean`:
the single-arc algebraic crux is DONE — the hyperbola `xy ≡ k (mod p)` arc
`{(x, (k·x⁻¹) mod p) : x ∈ [1,p)}` has no three collinear (`hyperbola_noThreeCollinear`), via
collapsing the mod-`p` determinant with the relation `x·y = k` to `−k·(a−b)(a−c)(b−c) ≡ 0`. This
gives only `~N` points (same order as the Erdős parabola already formalized). I have also verified
on paper that extending `x ∈ [1, 2p)` keeps no-three-collinear (each residue then appears twice;
a collinear triple would force all three to share a residue, impossible with only 2 values per
residue) — but those `2(p−1)` points sit in a `2p × p` *rectangle*, ratio `1` in a square grid, so
this alone does NOT reach `3/2`.

**What I need (the genuine content of `3/2`, which I cannot reconstruct from memory):**
1. **The exact point set.** For prime `p ≈ ?·N`, the precise set of grid points HJSW use — which
   hyperbola(s) `xy ≡ kᵢ`, over which `x`-range, and how many translated/reflected arcs (the PLAN
   notes "~3 translated arcs"). Give the explicit coordinates as integer formulas.
2. **The grid side `N` vs `p`.** What is `N` in terms of `p` (e.g. `N = 3p/2`? `2p`?), and how the
   `3/2` ratio arises (point count `≈ 3p/2` in an `N×N = ?` grid).
3. **The cross-arc non-collinearity argument.** Naively stacking two `2p×p` doubled arcs into a
   `2p×2p` square would give ratio `2` (too good) — so collinearities BETWEEN arcs must obstruct
   that and cap the gain at `3/2`. What is the precise lemma controlling inter-arc collinearity, and
   why does the count land at `3(N−2)/2` rather than `2N`? This is the part I most need spelled out.

**Why it unblocks me.** I have the algebraic crux and the collinearity↔determinant bridge formalized
and green. The only missing piece is the *combinatorial covering* — the explicit construction +
count + cross-arc argument. With the exact point set and the count lemma, I can formalize the full
`maxNoThreeInLine N ≥ 3(N−2)/2` headline. A scan of the actual paper (or a clear secondary source
such as Brass–Moser–Pach §10.1, or Flammenkamp / Wikipedia citing HJSW) giving the explicit
construction would let me close it.
