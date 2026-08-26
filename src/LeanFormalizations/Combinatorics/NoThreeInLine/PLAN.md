# No-three-in-line — plan & frontier

## Done (axiom-clean, sorry-free)

1. **Definitions** (`Defs.lean`) — faithful `Collinear ℝ` predicate; the `k = 3`
   instance of upstream `Green72.AllowedSet`.
2. **`2N` upper bound** (`UpperBound.lean`) — pigeonhole: ≤ 2 per row × `N` rows.
3. **Erdős `Θ(N)` lower bound** (`Parabola.lean`) — `(i, i² mod p)` for prime `p`; mod-`p`
   determinant `(b−a)(c−a)(c−b) ≢ 0`. Lifted to all `N ≥ 2` via Bertrand.

## Frontier (open work, in rough order of effort)

### A. Hall–Jackson–Sudbery–Wild `3N/2` — ✅ DONE & axiom-clean (lap 14)
`three_mul_pred_le_maxNoThreeInLine : 3(p−1) ≤ maxNoThreeInLine(2p)` (odd prime `p`), trust base only.
The genuine **half-band** pinwheel (`Pinwheel.lean`) — the naïve `{0,p}²`-corner version was brute-force
FALSE (no-three for no drop rule; a class is coupled on a `+1` AND a `−1` line, can't break both with one
drop). Crux `pinwheel_diagonal_false` (cross-class slope-`±1` incidence) proved via the σ-reflection +
the `±p`-offset of the partner class's kept points, over all 4 `(left/right)×(lower/upper)` families.
**Remaining frontier = the all-`N` `(3/2−ε)N` corollary** (needs a prime `p≈N/2`; PNT-grade — Bertrand
gives only ratio `3/4`). Original plan text (now history):

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
- **The count / covering — 🔨 UNBLOCKED + SCAFFOLDED (2026-06-19 lap 13).** The real construction
  (findings harvested → `archive/findings/`) is a **12-of-16-block "pinwheel"** carved from a SINGLE
  hyperbola `H(k,p)` over `2p×2p` (NOT stacked arcs): keep 3 of the 4 corners of each residue class.
  `Pinwheel.lean` defines it (drop-rule-parametrized) and proves `pinwheel_card = 3(p−1)` +
  `pinwheel_grid` axiom-clean for any drop. `HyperbolaLine.lean` has the load-bearing general Lemma
  (`hyperbola_line_two_congruent`: collinear hyperbola triple ⇒ two CONGRUENT) and both σ-reflection
  lemmas (HJSW Thm 2 Step 2). `pinCorner_not_collinear` kills the same-class subcase. **Remaining crux
  = `pinwheel_exists_noThree`** (one disclosed `sorry`): a drop-rule killing the cross-class slope-`±1`
  incidence (slopes 0/∞ are automatically safe — unique class per row/column). Headline
  `three_mul_pred_le_maxNoThreeInLine : 3(p−1) ≤ maxNoThreeInLine(2p)` is stated, reduced to that crux.
  See `PENDING_WORK.md` ITEM 1 for the 3 attack paths.

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
