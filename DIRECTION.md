# DIRECTION — read FIRST (operator directive, 2026-06-18, Trevor via Ren)

## Target: the **no-three-in-line** frontier (Ben Green's open problem 72)

This is an **isolated clone** (`~/src/lean-formalizations-ntl`, branch `ntl-hjsw`) dedicated to
the no-three-in-line frontier. The base results (2N upper bound + Erdős Θ(N) lower bound) are
already DONE and axiom-clean. Your job is the frontier in
`src/LeanFormalizations/Combinatorics/NoThreeInLine/PLAN.md`. **Read `HANDOFF.md` next — it has
the full task + math.**

### Primary target: HJSW `3N/2` (a hard, multi-lap proof — STAYING is the whole point)
Hall–Jackson–Sudbery–Wild's hyperbola construction `x·y ≡ k (mod p)` giving `3(N−2)/2` points
with no three collinear. **Expect many grind laps. That is fine — chip at it lap by lap.** Do NOT
declare it "out of scope," do NOT decide a narrow axiom is the "realistic destination," do NOT
wander off. The non-collinearity reuses the parabola's "ZMod p is a domain" move; the `3/2`
covering count is the real work. State it faithfully in `Statement.lean` (the audit surface).

After HJSW lands axiom-clean: the secondary items in `PLAN.md` (decidable witness anchors; an
optional Main-Conjecture statement). There is enough frontier to keep grinding.

### Run mode: UNBOUNDED (no self-stop)
`--allow-stop` is NOT armed for this run. Do NOT write a stop sentinel. Keep grinding the frontier
lap by lap; the operator ends the run with `lean-treadmill stop lean-formalizations-ntl`.

### ⛔ DO NOT TOUCH
- The sibling repo `~/src/lean-formalizations` (it has unrelated FastGrowing / Goodstein-
  independence WIP). Even though `~/src` is all visible, work ONLY in this clone.
- The completed, axiom-clean threads here: `NumberTheory/Transcendence/`,
  `Geometry/Constructible/`, `NumericalSemigroups/Curtis/`, `RealAnalysis/PowerTower/`,
  `Logic/Goodstein/`. Do not modify or reopen them; do not re-add any axiom.
- The DONE no-three-in-line base (`Defs/Collinearity/UpperBound/Parabola/Statement`). Build ON it.

## Standing rules
- **Axiom-clean or it doesn't count**: every headline `#print axioms = [propext, Classical.choice,
  Quot.sound]`. No `sorryAx`, no custom axiom, no `native_decide` leak into a headline.
- **Faithful statement** is the entire trust surface — write the `3/2` and grid bounds explicitly.
- **Commit green** (the `.githooks/pre-commit` runs `lake build`; mathlib is prebuilt here, builds
  are seconds). **DO NOT push.** Leaving a mid-proof `sorry` + a `PLAN.md` attack note across laps
  is fine; never call a result axiom-clean while it has a `sorry`.
- Verify lemma names against this repo's mathlib (`v4.29.1`); `push_neg` is deprecated → `push Not`.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue elsewhere.
