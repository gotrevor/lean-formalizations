# Compass-and-straightedge impossibilities (constructible numbers)

**Result.** The algebraic core of **Wantzel's theorem (1837)** and its corollaries —
the three classical Greek construction problems that resisted for two millennia:

- **Doubling the cube** is impossible: `∛2` is not constructible.
- **Trisecting the 60° angle** is impossible: `cos 20°` is not constructible.
- **Squaring the circle** is impossible (given `π` transcendental): `√π` is not
  constructible.

All three fall out of one engine: a compass-and-straightedge–constructible real has
degree a **power of two** over `ℚ`.

## What to audit (`Statement.lean`)

The headline theorems, stated against the audited definitions `IsConstructible` /
`IsSqrtTower`:

- `cbrt2_not_constructible : ¬ IsConstructible (2 ^ (1/3))` — **doubling the cube**.
- `no_constructible_cube_root_of_two : ¬ ∃ x, IsConstructible x ∧ x ^ 3 = 2`.
- `cos20_not_constructible : ¬ IsConstructible (cos (π/9))` — **trisecting 60°**.
- `twoCos20_not_constructible`.
- `squaring_the_circle_impossible (hπ : Transcendental ℚ π) : ¬ IsConstructible (√π)`
  — **squaring the circle**, conditional on the transcendence of `π`.

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

**Layer 1 (algebraic core): PROVED, axiom-clean.** This is the half of Wantzel that
powers the impossibility results.

**Layer 2 (geometric faithfulness): open.** A fully geometric definition (a point is
constructible if obtained from `{(0,0),(1,0)}` by line/circle intersections) and the
bridge "constructible point ⟹ coordinates in a quadratic tower" is a separate
multi-lap development. The algebraic substrate it needs — constructibles are a
subfield closed under `√` — is in place here. See `PENDING_WORK.md`.

**Squaring the circle** is conditional on `Transcendental ℚ π`, which mathlib does
not yet have (only the analytic part of Lindemann–Weierstrass). Stated with that as
an explicit hypothesis, so the theorem is unconditionally axiom-clean.
