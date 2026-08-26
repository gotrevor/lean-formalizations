# Compass-and-straightedge impossibilities (constructible numbers)

**Result.** A full formalization of **Wantzel's theorem (1837)** — *both directions* of
the equivalence between the algebra of quadratic towers and actual compass-and-
straightedge geometry — and its classical corollaries:

- **Doubling the cube** is impossible: `∛2` is not constructible.
- **Trisecting the 60° angle** is impossible: `cos 20°` is not constructible.
- **The regular nonagon and heptagon** are not constructible (`2cos 40°`, `2cos(2π/7)`
  have degree 3 — that is the form the repo proves).
- **Squaring the circle** is impossible: `√π` is not constructible (unconditional — the
  transcendence of `π` is proved in this repo).
- **Positive side:** the regular **pentagon** *is* constructible (`cos(π/5)=(1+√5)/4`).

The impossibilities fall out of one engine: a constructible real has degree a **power of
two** over `ℚ`. The headline is the equivalence itself:

```
isConstructible_iff_constructiblePoint :
  IsConstructible x ↔ ConstructiblePoint (x, 0)
```

`ConstructiblePoint` is the *faithful geometric* definition (a point reachable from
`{(0,0),(1,0)}` by line/circle intersections); `IsConstructible` is the algebraic
square-root-tower definition. Both directions are proved and axiom-clean.

## What to audit (`Statement.lean`)

The headline theorems, stated against the audited definitions `IsConstructible` /
`IsSqrtTower`:

- `cbrt2_not_constructible : ¬ IsConstructible cbrt2` (where `cbrt2 = (2:ℝ) ^ ((1:ℝ)/3)`)
  — **doubling the cube**.
- `no_constructible_cube_root_of_two : ¬ ∃ x, IsConstructible x ∧ x ^ 3 = 2`.
- `cos20_not_constructible : ¬ IsConstructible (cos (π/9))` — **trisecting 60°**.
- `twoCos20_not_constructible`.
- `squaring_the_circle_impossible_uncond : ¬ IsConstructible (√π)` — **squaring the
  circle**, unconditional (π-transcendence supplied in-repo).
- `squaring_the_circle_impossible (hπ : Transcendental ℚ π) : ¬ IsConstructible (√π)`
  — the hypothesis-carrying form, kept for reuse.

Each is `#print axioms`-clean: `[propext, Classical.choice, Quot.sound]` — no
`sorry`, no custom axiom, no `native_decide`.

## The definition (faithfulness surface — `SqrtTower.lean`)

```
IsSqrtTower : IntermediateField ℚ ℝ → Prop      -- ⊥, or K with a real √ adjoined (a*a ∈ K)
IsConstructible x := ∃ K, IsSqrtTower K ∧ x ∈ K
```

A *square-root tower* is a subfield of `ℝ` reached from `ℚ` by repeatedly adjoining
the square root of an element already present — exactly the algebra of compass and
straightedge. The definition is shown to be "alive":

- `isConstructible_ratCast` — every rational is constructible.
- `IsConstructible.sqrt` — closed under `√` (the compass step).
- `IsConstructible.{add,sub,mul,neg,inv}` — the constructibles form a **subfield**
  (`IsSqrtTower.sup_exists`: any two towers embed in a common one).
- `IsConstructible.isAlgebraic` — every constructible number is algebraic over `ℚ`.
- `IsConstructible.of_quadratic` — a real root of `t²+bt+c=0` with constructible
  `b,c` is constructible (the algebra of a *line ∩ circle* intersection).

## The engine (`SqrtTower.lean`)

- `IsSqrtTower.finrank_eq_pow_two` — **every square-root tower has degree `2ⁿ` over
  `ℚ`** (tower law + each quadratic step `[K(a):K] ≤ 2` from `a` being a root of
  `X² - a²`).
- `IsConstructible.finrank_adjoin_eq_pow_two` — hence `[ℚ(x):ℚ] = 2ⁿ` for
  constructible `x` (`ℚ(x) ≤ K`, and a divisor of `2ⁿ` is a power of two).
- `not_isConstructible_of_finrank_adjoin_eq_three` — the degree-3 obstruction.

## The degree-3 / transcendence inputs

- `CubeRoot.lean`: `finrank_adjoin_cbrt2 = 3` via `minpoly ℚ ∛2 = X³ - 2`,
  irreducible by **Kummer** (`2` not a cube in `ℚ`, from irrationality of `∛2`).
- `Trisection.lean`: `finrank_adjoin_twoCos20 = 3` via the triple-angle identity
  `8cos³20° - 6cos20° - 1 = 0` and irreducibility of the monic `X³ - 3X - 1` (a
  rational root would be an integer dividing `1`; neither `±1` works — integral root
  theorem).

## Provenance

P.-L. Wantzel, *Recherches sur les moyens de reconnaître si un problème de géométrie
peut se résoudre avec la règle et le compas* (J. Math. Pures Appl., 1837). Squaring
the circle additionally needs Lindemann's transcendence of `π` (1882).

## Status / scope

**Layer 1 (algebraic core): PROVED, axiom-clean** (`SqrtTower.lean`). The degree-`2ⁿ`
obstruction that powers the impossibility results.

**Layer 2 (geometric faithfulness): PROVED, axiom-clean** (`ConstructiblePoint.lean`).
`ConstructiblePoint : ℝ×ℝ → Prop` is the inductive geometric definition (intersections
of lines/circles through constructible points). `ConstructiblePoint.isConstructible_coords`
shows both coordinates land in a quadratic tower — the geometry ⟹ algebra bridge, via
`line_meet_line` (Cramer), `line_meet_circle` (quadratic formula) and `circle_meet_circle`
(radical axis). A positive witness `constructiblePoint_equilateral_vertex` confirms the
predicate is genuinely inhabited.

**Converse (algebra ⟹ geometry): PROVED, axiom-clean** (`Converse.lean`). The compass
arithmetic: `AxisConstructible x := ConstructiblePoint (x,0)` is closed under `+,−,·,⁻¹,/`
and `√` by explicit ruler-and-compass constructions (intercept theorem for `·`/`⁻¹`,
Thales/geometric-mean for `√`, parallelogram-translate primitive `cp_translate`). A
square-root-tower induction (`isSqrtTower_le_axisField`) packages this into the converse,
giving the full `isConstructible_iff_constructiblePoint`.

**Squaring the circle is unconditional.** mathlib has only the analytic part of
Lindemann–Weierstrass, so this repo proved π-transcendence itself
(`Transcendence.transcendental_pi_axiomClean`); `squaring_the_circle_impossible_uncond`
discharges the hypothesis and is axiom-clean. The hypothesis-carrying
`squaring_the_circle_impossible` is kept alongside it.
