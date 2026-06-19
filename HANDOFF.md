# HANDOFF — lean-formalizations (2026-06-19)

## Bounded Goodstein run: COMPLETE ✅

**`goodstein_terminates : ∀ m, ∃ N, goodsteinSeq m N = 0`** is fully proved and
axiom-clean: `#print axioms = [propext, Classical.choice, Quot.sound]`.
`lake build` green (8278 jobs), `src/` sorry-free. This was the sole target of the
bounded run (`DIRECTION.md`); per that directive the run ends here.

### What landed (`src/LeanFormalizations/Logic/Goodstein/`)
- **`Defs.lean`** — faithful hereditary-base **bump**: peel the top power
  (`e = log b n`, `c = n/b^e`, `r = n%b^e`), `bump b n = c·(b+1)^(bump b e) + bump b r`,
  `bump b 0 = 0` (well-founded; both recursive args `< n`). `goodsteinSeq m (k+1)
  = bump (k+2) (G k) - 1`. Verified faithful: trajectories `m=2:[2,2,1,0]`,
  `m=3:[3,3,3,2,1,0]`, and `bump 2 266 = 3^81+81+3`.
- **`Anchors.lean`** — 14 `example`s (m=0..3 full trajectories) discharged by
  `native_decide` (off the headline axiom path).
- **`Engine.lean`** — `toOrdinal` (base `b ↦ ω`), the combined induction
  `toOrdinal_mono_and_bound` (strict monotonicity + CNF leading bound, mutually
  recursive) and its ℕ-twin `bump_mono_and_bound`; `bump_lt_pow`; the structural
  heart `toOrdinal_bump : toOrdinal (b+1) (bump b n) = toOrdinal b n`; `seqOrd`,
  `seqOrd_step` (descent), and `goodstein_terminates_engine` (well-foundedness via
  `Ordinal.lt_wf.has_min`).
- **`Statement.lean`** — thin audit surface; delegates to the engine.

### Out of scope (documented, not attempted)
Kirby–Paris PA-independence ("PA ⊬ Goodstein") — metamathematics about PA, see the
Goodstein `README.md`.

## Repo state
All five threads complete and axiom-clean: `NumberTheory/Transcendence` (e + π,
Lindemann), `Geometry/Constructible` (Wantzel, Layer 1), `NumericalSemigroups/Curtis`,
`RealAnalysis/PowerTower` (sharp Euler iff), and now `Logic/Goodstein`. **0 math
axioms**; every headline `#print axioms` is the bare trust base.

## If picking a new target (next run — operator's call)
`PENDING_WORK.md` / older HANDOFFs list ideas: Constructible Layer-2 geometric
faithfulness, general Hermite–Lindemann, gathering the Erdős repos. None were in
scope for the (now-finished) bounded Goodstein run.
