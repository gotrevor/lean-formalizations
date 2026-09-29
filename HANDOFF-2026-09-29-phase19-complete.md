# HANDOFF 2026-09-29 — phase 19 COMPLETE: Waldschmidt 2023, Conjecture 1 and its derivations

Commit `99f8e17`.  `src/LeanFormalizations/NumberTheory/Transcendence/Waldschmidt2023.lean` is
**sorry-free**; all five frozen statements are `#print axioms`-clean (`propext`,
`Classical.choice`, `Quot.sound`).  Full `lake build` green.  One lap.

## What was proved

| statement | route |
|---|---|
| `algIndepLogs_of_schanuel` | Conj 1 is exactly the algebraic-exponentials case of Schanuel; one line off phase 16's `algebraicIndependent_of_exp_isAlgebraic`. |
| `fourExponentials_of_algIndepLogs` | the survey's own route, via the new `false_of_exp_algebraic_of_quad'`. |
| `bakerHomogeneous_of_algIndepLogs` | `AlgebraicIndependent.extendScalars` (ℚ → ℚ̄) then `eq_zero_of_algebraicIndependent_linear` at base ℚ̄. |
| `algebraicIndependent_log_two_pi` | `λ = log 2, log 2 + 2πi`; trade the field for `ℚ(log 2, π)` via the phase-15 master step. |
| `transcendental_log_of_lindemann` | Conj 1 at `n = 1` from `LindemannWeierstrassAlgIndep`. |

**Nothing was underivable.**

## The one piece of real content

Phase 16's heart lemma `Exponentials.false_of_exp_algebraic_of_quad` is stated with
`hS : SchanuelConjecture`, but it consumes `hS` *only* through
`algebraicIndependent_of_exp_isAlgebraic` — which is literally Conjecture 1.  So
`false_of_exp_algebraic_of_quad'` is that proof with the hypothesis weakened to
`AlgIndepLogsConjecture`, and the four-exponentials derivation now sits at the survey's stated
strength instead of one conjecture too strong.  (The lemma body is duplicated rather than
refactored, because phase 16's names are frozen.)

Corollary worth noting: Conjecture 1 gives Baker's homogeneous theorem with **no analytic input
at all** — the whole step is field theory over an algebraic extension.

## Reusable leaves added

* `isAlgebraic_add'` — sums stay algebraic over an intermediate field (companion to phase 15's
  `isAlgebraic_mul_rat` / `_sub_rat` / `_div_rat`).
* `false_of_exp_algebraic_of_quad'` — the quadratic-relation kill under Conjecture 1.
* `linearIndependent_log_two_log_two_add_two_pi_I`.

## Gotchas

* `LinearIndependent ℕ` on a singleton: `linearIndependent_unique_iff` needs a `Ring`, so ℕ is
  excluded.  Use `linearIndependent_iff'ₛ` (the `ₛ` semiring variants) instead.
* `IsAlgebraic.tower_top` into `↥(integralClosure ℚ ℂ)` wants a `Field` instance it cannot get;
  use `IsAlgebraic.extendScalars (S := integralClosure ℚ ℂ) (algebraMap ℚ _).injective`.
* `simp` rewrites `((Real.log 2 : ℝ) : ℂ)` to `Complex.log 2` via `Complex.ofReal_log`, which
  derails imaginary-part computations.  Use a tight `simp only` list, then `norm_num`.
* `π` is not in scope without `open Real`; write `((Real.pi : ℝ) : ℂ)`.

## What remains of the survey (`WALDSCHMIDT-2023.md`)

Three items, each needing machinery the repo does not have yet:
* §2 Leopoldt's conjecture — p-adic logarithms and regulators; a separate project.
* §5 rank of matrices of logarithms, Roy's `rk ≥ ½ r_str`, Conj 1 ⇔ `rk = r_str` — needs a
  structural-rank definition.  This is the most attackable of the three and the natural phase 20
  if the survey thread continues.
* Conj 7, Roy's conjecture (equivalent to Schanuel) — derivation `D` and height bounds; state it
  from the rendered page, not a pdftotext dump.

Also still available: `Literature.StrongFourExponentialsConjecture` was stated this phase but has
no consequences derived from it yet.
