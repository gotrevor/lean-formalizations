# No-three-in-line — plan & frontier

## Done (axiom-clean, sorry-free)

1. **Definitions** (`Defs.lean`) — faithful `Collinear ℝ` predicate; fixes the upstream
   `Green72.AllowedSet` mis-statement.
2. **`2N` upper bound** (`UpperBound.lean`) — pigeonhole: ≤ 2 per row × `N` rows.
3. **Erdős `Θ(N)` lower bound** (`Parabola.lean`) — `(i, i² mod p)` for prime `p`; mod-`p`
   determinant `(b−a)(c−a)(c−b) ≢ 0`. Lifted to all `N ≥ 2` via Bertrand.

## Frontier (open work, in rough order of effort)

### A. Hall–Jackson–Sudbery–Wild `3N/2` (the "hard mile")
The best *proven* lower constant (1975, unimproved). `hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2p)`.
Two pieces:
- **Arc non-collinearity** — ✅ **DONE, axiom-clean** (`Hyperbola.lean::hyperbola_noThreeCollinear`).
  Three points on `xy ≡ k (mod p)` collinear ⇒ the Vandermonde reduction
  `k·(a−b)(b−c)(c−a) = a·b·c·D` (via `linear_combination` from `aᵢyᵢ = k`); `ZMod p` a domain
  forces two `aᵢ` equal. This covers triples with **distinct** `x` mod `p` (one arc).
- **The count / covering** — ⛔ **OPEN, the crux.** Assemble `3(p−1)` actual grid points and rule
  out collinearities between points on *different* lifted arcs (where `x`-coords coincide mod `p`,
  so the single-arc argument does not apply). This is the genuinely hard combinatorics.

**Experimental status (2026-06-19).** Built a verified decidable certificate
`Anchors.lean::decNoThree` (`decNoThree s → NoThreeCollinear s`, axiom-clean) + `native_decide`, and
used it to *search* the natural "3 of the 4 rectangle-corners `{r,r+p}×{s,s+p}` per residue, with
`s = r⁻¹ mod p`" family:
- `p = 5`: valid 12-point configs exist — `witness5` (certified `hjsw_lower_five`, off-headline).
- `p = 7`: **exhaustive** search over all `4^6` corner-drop assignments found **NONE** of size 18.
So HJSW is **not** the rectangle-corner family (a `p=5` coincidence). Need the paper's actual
construction → see root `ON-LINE-REQUEST.md`. Next lap: act on the findings doc when it lands; until
then the certificate makes any candidate construction cheap to validate computationally first.

Mathlib has what's needed: `ZMod p` field, `Matrix.det`, `Nat.exists_prime_lt_and_le_two_mul`.

### B. Corrected asymptotic heuristic `~1.814·N` (Guy–Kelly, Ellmann 2004)
NOT a theorem — a density heuristic (`π/√3 ≈ 1.814`). Out of scope as a proof; could be recorded
as commentary only.

### C. Main Conjecture (open)
Solutions are finite: `∃ N₀, ∀ N ≥ N₀, maxNoThreeInLine N < 2N`. Unproven. If stated, it is a
`sorry` target in the `formal-conjectures` style (`@[category research open]`), never a claimed
proof. Its natural home is the DeepMind `formal-conjectures` repo (gated on the CLA), not here.

### D. Verified witnesses (decidable anchors)
The record configurations (e.g. `n=70`, Heule 2026) are finite decidable checks, not theorems.
A `native_decide` anchor "this explicit set of `2k` points has no 3 collinear" would be an
anti-vacuity lock in the spirit of the other repos' `Anchors.lean`, but needs a decidable mirror
of `NoThreeCollinear` on a concrete `Finset` (collinearity → determinant ≠ 0, all triples).
Cheap, optional, high-confidence.
