# No-three-in-line problem

The no-three-in-line problem (Dudeney 1917; **Ben Green's open problem 72**): how many points
can be placed on an `N × N` grid so that no three lie on a common line — every line of every
rational slope, not just rows/columns/diagonals?

**Status (2026-06-19): Erdős/upper-bound results proven & axiom-clean; HJSW `3N/2` in progress —
arc non-collinearity proven, the covering count is a disclosed `sorry`.**

| Result | Theorem | Status |
|--------|---------|--------|
| `2N` upper bound (pigeonhole) | `maxNoThreeInLine_upper`, `upper_bound` | ✅ proven |
| Erdős parabola lower bound (prime `p`) | `prime_le_maxNoThreeInLine`, `erdos_exists_parabola` | ✅ proven |
| Lower bound for all `N ≥ 2` (Bertrand) | `maxNoThreeInLine_gt_half` | ✅ proven |
| Order `Θ(N)` | `maxNoThreeInLine_order` (`p ≤ max ≤ 2p`) | ✅ proven |
| HJSW hyperbola-arc non-collinearity | `hyperbola_noThreeCollinear` | ✅ proven |
| HJSW `3(p−1) ≤ max(2p)` (covering count) | `hjsw_lower` | ⛔ `sorry` (needs paper construction) |
| HJSW count verified at `p = 5` | `hjsw_lower_five` | ✅ `native_decide` witness |

`#print axioms` on every *proven, axiom-clean* headline = `[propext, Classical.choice, Quot.sound]`.
`hjsw_lower_five` additionally uses the `native_decide` axiom (it is a finite check, off the
general-headline path).

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
* `Hyperbola.lean` — HJSW frontier. `hyperbola_noThreeCollinear`: the modular-hyperbola arc
  `xy ≡ k (mod p)` has no three collinear (the Vandermonde reduction
  `k·(a−b)(b−c)(c−a) = a·b·c·D`). `hjsw_lower` (the `3(p−1)` covering count) is a disclosed `sorry`.
* `Anchors.lean` — `decNoThree` (decidable mirror) with `decNoThree_iff : decNoThree s ↔
  NoThreeCollinear s` (so `NoThreeCollinear` is `Decidable`), built on the full equivalence
  `det3 = 0 ⟺ Collinear ℝ` (`collinear_{imp,of}_det3_zero`). Plus `witness5` / `hjsw_lower_five`,
  a `native_decide`-certified 12-point witness of the HJSW count at `p = 5`. Used to experimentally
  falsify the naive hyperbola-lift constructions (see `PLAN.md`).

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
