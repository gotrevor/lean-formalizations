# HANDOFF — no-three-in-line, HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`, created to
grind the **no-three-in-line** frontier without colliding with separate work in the sibling repo
`~/src/lean-formalizations` (which has unrelated FastGrowing/Goodstein-independence WIP). Even
though the whole `~/src` tree is visible to you, **work ONLY in this clone** (`lean-formalizations-ntl`).
Do not edit, build, or commit anything under `~/src/lean-formalizations`.

## What is already DONE (axiom-clean, sorry-free — do not redo)
`src/LeanFormalizations/Combinatorics/NoThreeInLine/` — Ben Green's open problem 72:
- **2N upper bound** (`UpperBound.lean`): pigeonhole, ≤2 points per row.
- **Erdős Θ(N) lower bound** (`Parabola.lean`): `(i, i² mod p)`; mod-p determinant
  `(b−a)(c−a)(c−b) ≢ 0` since `ZMod p` is a domain. Lifted to all `N≥2` via Bertrand.
- Audit surface `Statement.lean`; faithful `NoThreeCollinear` predicate in `Defs.lean` (the
  CORRECTED form of formal-conjectures' broken `Green72.AllowedSet`).
- All 5 headlines: `#print axioms = [propext, Classical.choice, Quot.sound]`. Read `README.md`
  and `PLAN.md` in that directory first.

## Your TASK: the frontier in `PLAN.md`, in order

### Primary — Hall–Jackson–Sudbery–Wild `3N/2` (`Combinatorics/NoThreeInLine/Hyperbola.lean`)
The best *proven* lower constant (1975), unimproved. Improves Erdős's `~N` to `3(N−2)/2`.
- **Construction:** for `p = N/2` prime and nonzero `k`, place points on the hyperbola
  `x·y ≡ k (mod p)`. Three points on it collinear over ℝ ⟹ a determinant relation that, mod `p`,
  is a nonzero polynomial in the coordinates — which `ZMod p` (a domain) forbids unless two
  coincide. Same "integral domain kills the product" move as the parabola, more bookkeeping (the
  relation is degree-2 in each variable; reuse `collinear_imp_det3_zero`).
- **The `3/2` count** is the genuinely fiddly part: the mod-`p` arc is lifted/covered across the
  `N×N` grid (~3 translated copies) to yield `3(N−2)/2` actual grid points. This is where the real
  work lives; the non-collinearity is the easier half.
- **Goal theorem** (state it faithfully in the audit surface against `Defs.lean`'s predicates):
  for infinitely many `N` (e.g. `N = 2p`, `p` prime), `3*(N-2)/2 ≤ maxNoThreeInLine N`. Pick the
  exact faithful form yourself from the HJSW paper / Wikipedia; the STATEMENT is the entire trust
  surface, so get it right and put it in `Statement.lean`.

### Secondary (only after HJSW, or if HJSW stalls a lap)
- **Decidable witness anchors** (`Anchors.lean`, à la the other targets): a `native_decide`
  example "this explicit set of `2k` points has no 3 collinear" as an anti-vacuity lock. Needs a
  decidable mirror of `NoThreeCollinear` on a concrete `Finset` (collinearity ⟺ `det3 ≠ 0` over
  all triples). Keep it OFF the headline axiom path.
- **Main Conjecture** statement only (`@[category research open]`, a `sorry` target) — its real
  home is the DeepMind formal-conjectures repo, so here a faithful statement is optional.

## Rules (charter)
- **Axiom-clean or it doesn't count.** Every new headline must end at
  `#print axioms = [propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom, no
  `native_decide` leaking into a headline's axiom set. Verify with `lake env lean` + `#print axioms`.
- **Faithful statement** in `Statement.lean` (the designated audit surface). The constants
  (`3/2`, the grid bounds) are the most error-prone — write them out explicitly.
- **Commit green.** The `.githooks/pre-commit` runs `lake build`; only commit when it passes.
  Incremental builds are ~seconds (mathlib is prebuilt in this clone's `.lake`).
- Deep work may be left mid-proof across laps with a `sorry` + an attack note in `PLAN.md`, but
  never claim a result axiom-clean while it has a `sorry`.
- Refresh `STATUS.md` / this `HANDOFF.md` each review lap with real `#print axioms` output.

## Build
`lake build` (whole repo) or `lake build LeanFormalizations.Combinatorics.NoThreeInLine.Statement`.
mathlib is already built here — do NOT `lake exe cache get` (no network in the box anyway).
