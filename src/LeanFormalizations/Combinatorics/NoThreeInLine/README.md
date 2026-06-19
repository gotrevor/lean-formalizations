# No-three-in-line problem

The no-three-in-line problem (Dudeney 1917; **Ben Green's open problem 72**): how many points
can be placed on an `N × N` grid so that no three lie on a common line — every line of every
rational slope, not just rows/columns/diagonals?

**Status (2026-06-18): both proven results formalized, axiom-clean, sorry-free.**

| Result | Theorem | Status |
|--------|---------|--------|
| `2N` upper bound (pigeonhole) | `maxNoThreeInLine_upper`, `upper_bound` | ✅ proven |
| Erdős parabola lower bound (prime `p`) | `prime_le_maxNoThreeInLine`, `erdos_exists_parabola` | ✅ proven |
| Lower bound for all `N ≥ 2` (Bertrand) | `maxNoThreeInLine_gt_half` | ✅ proven |
| Order `Θ(N)` | `maxNoThreeInLine_order` (`p ≤ max ≤ 2p`) | ✅ proven |

`#print axioms` on every headline = `[propext, Classical.choice, Quot.sound]` (bare trust base).

## What to audit (the trusted surface)

Only `Statement.lean` and the three definitions in `Defs.lean` need a human read against the
problem; everything else is machine-checked proof delegating to them.

* **`Defs.lean`**
  * `toReal (i,j) = ((i:ℝ),(j:ℝ))` — embed a grid point into the real plane.
  * `IsGridSet N s` — `∀ p ∈ s, p.1 < N ∧ p.2 < N`, i.e. `s ⊆ [0,N) × [0,N)`.
  * `NoThreeCollinear s` — `∀ p q r ∈ s, Collinear ℝ {toReal p, toReal q, toReal r} → p = q ∨ p = r ∨ q = r`.
    This is the genuine geometric collinearity (`Mathlib`'s `Collinear ℝ`), so it forbids three
    distinct points on **any** real line. It is the **corrected** form of the
    `formal-conjectures` entry `Green72.AllowedSet`, whose `not_collinear` field is mis-stated
    (asserts `Collinear` with no negation, and over the whole set rather than the chosen triple).
  * `maxNoThreeInLine N := sSup {s.card | IsGridSet N s ∧ NoThreeCollinear s}` — the grid maximum.
* **`Statement.lean`** — the headlines, each delegating to the engines.

## Engines (proof, not trusted surface)

* `Collinearity.lean` — `collinear_imp_det3_zero` (collinear ⇒ vanishing `2×2` determinant) and
  `collinear_of_eq_snd` (equal `y` ⇒ collinear), both via `collinear_iff_of_mem`.
* `UpperBound.lean` — `≤ 2` points per row (three would be collinear), summed over `N` rows.
* `Parabola.lean` — Erdős's `(i, i² mod p)`: collinearity forces the integer determinant to
  vanish, which mod `p` factors as `(b−a)(c−a)(c−b) ≡ 0`; `ZMod p` a field ⇒ two points coincide.

## Provenance & novelty

* Not formalized anywhere: 0 hits for a no-three-in-line proof across the 705-repo Reservoir
  mirror (2026-06-18); the only Lean trace is the `formal-conjectures` `Green72` stub file, all
  `sorry`. See `SOURCES.md`.
* References: Ben Green, *Open Problems* (#72); Erdős, via Roth 1951 / Hall–Jackson–Sudbery–Wild
  1975; [Wikipedia](https://en.wikipedia.org/wiki/No-three-in-line_problem). The mod-`p` parabola
  argument is the standard `Θ(n)` construction.

## Frontier (`PLAN.md`)

* **HJSW `3N/2`** — the hyperbola `xy ≡ k (mod p)`, best proven constant (unimproved since 1975).
* **Main Conjecture** — solutions are finite (open); a statement-only `sorry` target.
