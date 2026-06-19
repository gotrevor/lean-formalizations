# Baton — Goodstein run START (2026-06-18, Trevor via Ren)

## Where we are
Fresh bounded run launched to formalize **Goodstein's theorem (termination)**:
`∀ m, ∃ N, goodsteinSeq m N = 0`. Everything else in the repo is complete and
axiom-clean; this is the only target. Authoritative instructions: **`DIRECTION.md`**.

## Scaffold (committed, builds green-with-sorries)
`src/LeanFormalizations/Logic/Goodstein/`:
- `Defs.lean` — `base k = k+2`; `goodsteinSeq` is a **STUB** (returns the seed) to
  be replaced by the faithful hereditary-base definition.
- `Anchors.lean` — hand-computed trajectories m = 0,1,2,3 as `sorry`'d `example`s
  (anti-vacuity lock; discharge by `native_decide` once the def is real).
- `Statement.lean` — headline `goodstein_terminates`, `sorry`.
- `README.md` — provenance, the trajectory table, what-to-audit, scope note.

Wired into `src/LeanFormalizations.lean`. `src/` had 0 sorries before; this scaffold
is the only source of sorries, so the `--allow-stop` gate is closed until Goodstein
is genuinely done.

## First moves (next lap)
1. Replace the `goodsteinSeq` stub with the faithful definition (`Nat.digits`,
   well-founded recursion). Discharge the `Anchors` by `native_decide` — that
   proves the definition computes the right small trajectories.
2. Build the hereditary-base → ordinal map (`Ordinal.CNF`/`coeff`/`eval`), then the
   bump-invariance and strict-decrease lemmas; finish via `Ordinal.wellFoundedLT`.
   (Full plan: `DIRECTION.md`.)

## Stop condition
Faithful def + all anchors discharged + `goodstein_terminates` proved + `src/`
sorry-free + `#print axioms goodstein_terminates` clean → refresh docs, commit,
write the stop sentinel (command in `DIRECTION.md`), end. Do NOT start anything else.
