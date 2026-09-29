# HANDOFF 2026-09-29 — phase 21 COMPLETE (bedrock)

Branch `main`, HEAD `63e8203` (this doc) on top of the phase-21 proof commit.
Working tree clean; `lake build` green; treadmill stop sentinel written.

`src/LeanFormalizations/NumberTheory/Transcendence/Bedrock.lean` is **sorry-free**; all eleven
frozen statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  Full
`lake build` green; committed.

## What landed

* Hermite–Lindemann family: `transcendental_cexp_of_algebraic`, `transcendental_log_of_algebraic`,
  `transcendental_sin_of_algebraic`, `transcendental_cos_of_algebraic`.
* Gelfond–Schneider: `transcendental_two_rpow_sqrt_two`, `transcendental_log_three_div_log_two`.
* Nesterenko: `transcendental_exp_pi`, `transcendental_pi_add_exp_pi`,
  `transcendental_pi_mul_exp_pi`, `transcendental_gamma_quarter`,
  `transcendental_exp_neg_pi_div_two`.

## The one design point worth remembering

**Hermite–Lindemann must be stated over the algebraic numbers.**  `transcendental_algClosure_cexp`
gives `Transcendental (integralClosure ℚ ℂ) (exp a)` for algebraic `a ≠ 0`; the `ℚ`-form is its
`Transcendental.restrictScalars`.  `sin`/`cos` need the strong form: `e^{ia}` is a root of
`X² − 2(cos a)X + 1` resp. `X² − 2i(sin a)X − 1`, whose coefficients are algebraic but *not*
rational, so a `Transcendental ℚ` statement would not contradict them.

## Reusable leaves added

* `linearIndependent_nat_single` — `ℕ`-linear independence of a one-element family in
  `integralClosure ℚ ℂ` (`linearIndependent_unique_iff` needs a domain with subtraction, so this
  is done by hand: cancel `a`, then `CharZero`).  This is the shape LW's hypothesis wants.
* `isAlgebraic_of_quad` — a root of a monic quadratic over any nontrivial `CommRing` base.
* `not_quad_cexp_I_mul` — the shared `sin`/`cos` core.
* `algebraicIndependent_pi_exp_pi_complex_of_nesterenko` — the `π, e^π` pair over `ℂ`,
  unconditionally (the Schanuel-free twin of `Schanuel.algebraicIndependent_pi_exp_pi_complex`).
* `irrational_log_three_div_log_two` — from `Schanuel.linearIndependent_log_primes ![2,3]`.

## Gotchas

* `AlgebraicIndependent.map'` takes **AlgHom injectivity directly**; `LinearIndependent.map'` takes
  a `ker = ⊥` proof.  Copying the Schanuel idiom costs a build cycle.
* `linear_combination` will not use `I² = −1`; add `+ c * Complex.I_sq` explicitly.
* `algebraMap (integralClosure ℚ ℂ) ℂ (2 * x)`: `simp` leaves `↑2 = 2`; use
  `simp only [map_neg, map_mul, map_ofNat]; rfl`.

## Next (exact steps for a fresh session)

Nothing in `Bedrock.lean` is open — the phase-21 scope is finished, so the next session needs a
NEW directive planted in `DIRECTION.md` (altitude lap owns that file).  Candidates, in order:

1. **Leopoldt §2** — the last uncovered item of `WALDSCHMIDT-2023.md`.  Pattern to follow: put the
   conjecture as a hypothesis `Prop` in `Literature/`, then derive consequences in a new
   `NumberTheory/Transcendence/Leopoldt.lean` with frozen statement names.
2. **More bedrock.**  The toolkit now in `Bedrock.lean` makes several further unconditional
   classics cheap: `tan a` at nonzero algebraic real `a`; `sinh`/`cosh`; `e^{a}` for algebraic `a`
   with `a ≠ 0` in the *real* form; Baker-style `α₁^{β₁}·α₂^{β₂}` once `Literature.Baker1966` is
   used as input (it already exists, added in phase 17).
3. `Maze.lean` rows whose `reopenIf` is now satisfied — grep it before planting anything.

Before starting any of these: grep `src/LeanFormalizations/Maze.lean` (routes already walked and
closed) and read the `Bedrock.lean` header for the toolkit inventory.
