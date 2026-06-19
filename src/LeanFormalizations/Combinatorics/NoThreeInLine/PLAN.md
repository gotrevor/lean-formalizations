# No-three-in-line — plan & frontier

## Done (axiom-clean, sorry-free)

1. **Definitions** (`Defs.lean`) — faithful `Collinear ℝ` predicate; fixes the upstream
   `Green72.AllowedSet` mis-statement.
2. **`2N` upper bound** (`UpperBound.lean`) — pigeonhole: ≤ 2 per row × `N` rows.
3. **Erdős `Θ(N)` lower bound** (`Parabola.lean`) — `(i, i² mod p)` for prime `p`; mod-`p`
   determinant `(b−a)(c−a)(c−b) ≢ 0`. Lifted to all `N ≥ 2` via Bertrand.

## Frontier (open work, in rough order of effort)

### A. Hall–Jackson–Sudbery–Wild `3N/2` (the "hard mile")
The best *proven* lower constant (1975, unimproved). Points on a hyperbola `xy ≡ k (mod p)`
with `p ≈ N/2` prime, lifted across a covering of the grid by ~3 translated arcs to reach
`3(N−2)/2` points. Two pieces:
- **Arc non-collinearity — ✅ DONE (`Hyperbola.lean`, axiom-clean, 2026-06-19).** Three points on
  `xy ≡ k (mod p)` collinear ⇒ the mod-`p` determinant vanishes; collapsing it with the defining
  relation `x·y = k` on each point (`hyperbola_xy_eq`) gives `−k·(a−b)(a−c)(b−c) ≡ 0`, which the
  field `ZMod p` (`k ≢ 0`) forbids unless two coincide (`hyperbola_noThreeCollinear`). Also done:
  the **doubled (wide) arc** `x ∈ [1,2p)\{p}` keeps no-three-collinear (`hyperbolaWide_*`,
  `2(p−1)` points) — the precise "two abscissae per residue ⇒ horizontal-line collapse ⇒ third
  shares residue ⇒ pigeonhole" mechanism the covering exploits. NOTE: these arcs alone give only
  `~N` points in a square grid (same order as the Erdős parabola) — they are the *crux*, not the
  bound. The `3/2` is entirely in the covering below.
- **The count / covering — ⛔ NEEDS THE PAPER (online request filed 2026-06-19).** Assemble `3N/2`
  actual grid points: which hyperbola(s)/`x`-ranges, the grid side `N` vs `p`, and the cross-arc
  non-collinearity lemma that caps the gain at `3/2` (naive stacking would give `2`). This is the
  genuinely fiddly combinatorics I cannot reconstruct from memory. See `ON-LINE-REQUEST.md`.

Mathlib has what's needed: `ZMod p` field, `Matrix.det`, `Nat.exists_prime_lt_and_le_two_mul`.

### B. Corrected asymptotic heuristic `~1.814·N` (Guy–Kelly, Ellmann 2004)
NOT a theorem — a density heuristic (`π/√3 ≈ 1.814`). Out of scope as a proof; could be recorded
as commentary only.

### C. Main Conjecture (open)
Solutions are finite: `∃ N₀, ∀ N ≥ N₀, maxNoThreeInLine N < 2N`. Unproven. If stated, it is a
`sorry` target in the `formal-conjectures` style (`@[category research open]`), never a claimed
proof. Its natural home is the DeepMind `formal-conjectures` repo (gated on the CLA), not here.

### D. Verified witnesses (anti-vacuity anchors) — ✅ DONE (`Anchors.lean`, 2026-06-19)
`collinear_diagonal` (a real collinear grid triple — `Collinear ℝ` is not always false, so
`NoThreeCollinear` is not vacuously true) and `not_collinear_corner` (a genuine non-collinear
triple — `Collinear ℝ` is not always true). With `collinear_iff_det3_zero` and the proven
nonempty family `parabola_noThreeCollinear`, the predicate is pinned to its geometric meaning.
(A full `native_decide` "this explicit `2k`-set has no 3 collinear" still needs a decidable
mirror of `NoThreeCollinear` on a concrete `Finset` — reachable via `collinear_iff_det3_zero`
reduced to an integer determinant check over all triples; lower priority.)
