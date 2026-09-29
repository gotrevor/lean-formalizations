# HANDOFF — phase 25 COMPLETE (2026-09-29)

**Branch:** `main`  **HEAD at lap end:** `2974766` (proofs: `564ae0a`)  **Build:** green, `lake build` clean

**Scope:** `sorry-free:src/LeanFormalizations/NumberTheory/Transcendence/Periods.lean` — **MET.**

All ten frozen statements proved, `#print axioms` clean (`propext`, `Classical.choice`,
`Quot.sound` only). Full `lake build` green; commit `564ae0a`. `scripts/fact-graph` rerun
(30 edges, 27 hypotheses). `DIRECTION.md` phase-25 section marked done.

## What landed

| statement | route |
|---|---|
| `sixExponentials_of_sharp` | sharp six at `β = 0`; `x₀y₀ = 0` vs `LinearIndependent.ne_zero` |
| `fiveExponentials_of_sharp` | `y₃ = γ/x₁`, shift `(1,3)` by `γ` (sixth exponential `e⁰ = 1`); Baker in the ℚ-dependent branch |
| `apery_of_zetaValues` / `zeta5_of_zetaValues` / `ballRivoal_of_zetaValues` | one lemma `irrational_zeta_odd`, uniform in `k`, at `k = 0`, `k = 1`, all `k` |
| `transcendental_zeta_three_div_pi_cube` / `irrational_catalan_div_pi_sq` | one lemma `transcendental_div_pi_pow` |
| `algebraicIndependent_zeta_three_zeta_five` | `h 2` composed with `Fin.succ` |
| `catalanG_eq` | `norm_num` after unfolding `tail` |
| `transcendental_catalan` | component `1` of the conjecture pair |

## Verdict on the operator correction

Confirmed in the kernel. `SixExponentialsSharp`'s conclusion `xᵢyⱼ = βᵢⱼ` is exactly the
strength the survey's misprinted shifted form lacks: it contains BOTH the six and (with Baker)
the five exponentials theorem. The ℚ̄ repair suggested in the phase-24 handoff was correctly
rejected. Baker's input to the five-exponentials route remains unavoidable — the recorded
non-derivability note in `ExponentialsKnown.lean` stands.

## Gotchas (also in the file header)

* `AlgebraicIndependent` has no `.congr`; transport along a family equality with `rw`.
* Indexing a `Fin.cons` family at a **numeral** (`(2 : Fin 3)`) fights the dependent motive —
  compose with `Fin.succ` (`h.comp Fin.succ (Fin.succ_injective 2)`); `fin_cons_two` helper for
  the `Fin 2` case.
* `set_option ... in` must precede the docstring, not sit between docstring and declaration.
* `field_simp` inside `ℂ` after `push_cast` can blow the heartbeat budget — do the algebra in
  `ℝ` and lift with `Complex.ofReal_mul`/`ofReal_pow`.

## Exact next steps (for a fresh session)

1. Nothing is pending in phase 25 — the scope is closed and the stop sentinel is written
   (`~/src/.treadmill/lean-formalizations.stop`). The treadmill will not relaunch.
2. The next phase needs an operator directive in `DIRECTION.md`. Candidate targets, in the
   order the repo's own notes rank them:
   - `WALDSCHMIDT-2023.md` lists the survey items still uncovered (§ beyond Conj 1 / rank).
   - `src/LeanFormalizations/Maze.lean` — each row's `reopenIf` names the new idea a closed
     route would need; grep it BEFORE planting anything.
   - `SharpSixVariants.lean` and the Leopoldt scaffold (`StressTests.lean`) were committed by
     another session as `2307035`; their sorries are designated-open and were untouched here.
     Whoever owns that thread should pick it up, not this one.
3. Re-run `scripts/fact-graph` after any new phase (it is current as of this commit:
   30 edges, 27 hypotheses).

## Notes

Operator's call. Uncovered survey items are listed in `WALDSCHMIDT-2023.md`; `Maze.lean` records
routes already closed. Note another session committed `SharpSixVariants.lean` and the Leopoldt
scaffold (`2307035`) during this lap — those sorries are designated-open, untouched here.
