# HANDOFF 2026-09-29 — phase 15 COMPLETE: what follows from Schanuel's conjecture

`NumberTheory/Transcendence/Schanuel.lean` is **sorry-free**; all ten frozen statements are
machine-checked and `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  Everything
takes `hS : Literature.SchanuelConjecture` (verbatim from formal-conjectures; never an `axiom`).

## The ten

| statement | route |
|---|---|
| `gelfondSchneider_of_schanuel` | `z = (log a, b log a)`; if `a^b` were algebraic the whole field is algebraic over the **one-generator** field `ℚ(log a)`, so `trdeg ≤ 1 < 2` |
| `lindemannWeierstrassAlgIndep_of_schanuel` | `z = u`; `ℕ→ℤ→ℚ` linear independence, Schanuel per finite subfamily, base change to `Q̄` |
| `algebraicIndependent_pi_exp_pi` | `z = (iπ, π)` (Nesterenko consistency edge) |
| `algebraicIndependent_exp_one_pi` | `z = (1, iπ)`; `ℚ(1,iπ,e,−1)` is algebraic over `ℚ(e,π)` |
| `transcendental_exp_one_add_pi` / `..._mul_pi` | else `π = (e+π)−e` resp. `(eπ)/e` is algebraic over `ℚ(e)` |
| `algebraicIndependent_exp_one_exp_exp_one` | `z = (1, e)`; needs `e` irrational, from the repo's unconditional `e_transcendental` |
| `algebraicIndependent_log_primes` | `z = (log p₁,…,log pₙ)`; linear independence is unique factorization |
| `algebraicIndependent_wright_tower`, `transcendental_wright_tower` | the induction of the file header |

## The reusable toolkit (top of the file, generic base field)

* `algebraicIndependent_of_le_trdeg_adjoin` — **the counting step**: `n` elements generating a
  field of `trdeg ≥ n` are algebraically independent.  Uses mathlib's
  `Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite` after
  `isAlgebraic_algebraAdjoin_of_adjoin_eq_top` (a field is algebraic over the *algebra* it is the
  fraction field of — the scoped instances in `IntermediateField.algebraAdjoinAdjoin`).
* `trdeg_le_adjoin_of_forall_isAlgebraic` — trdeg is unchanged under an algebraic extension
  (`trdeg_add_eq` on `F ⊆ L ⊆ L ⊔ N`, via `IntermediateField.extendScalars`).  This is what lets
  the Schanuel field be traded for the field you actually care about.
* `algebraicIndependent_of_schanuel` — the front-end: `z` `ℚ`-linearly independent + every
  generator of `ℚ(z,e^z)` algebraic over `ℚ(y)` ⟹ `y` algebraically independent.
* `not_two_le_trdeg_adjoin_singleton`, `not_isAlgebraic_of_algebraicIndependent_pair` — the two
  contradiction shapes used to turn independence into transcendence.
* `eq_zero_of_algebraicIndependent_linear` — an algebraically independent family admits no
  nontrivial **affine** relation (read off `MvPolynomial` coefficients).

## Gotchas worth keeping

1. **State the toolkit over a general base field.**  With `F = ℚ` the two `Algebra ℚ ↥K`
   instances (`DivisionRing.toRatAlgebra` vs `IntermediateField.algebra'`) are not syntactically
   equal and instance search fails *inside* proofs.  At the ℚ interface they are defeq:
   `convert hsch using 2 <;> rfl` (used once, in `algebraicIndependent_of_schanuel`).
2. `AlgebraicIndependent` unfolds to `Function.Injective`, so `h.le_trdeg_adjoin` dot-notation
   resolves into the `Function` namespace — spell the full name.
3. `AlgebraicIndependent.of_comp (algebraMap ℝ ℂ)` loops the elaborator (it wants an `AlgHom`);
   use `IsScalarTower.toAlgHom ℚ ℝ ℂ`.
4. mathlib has **no** `LinearIndependent ℕ` API; `linearIndependent_int_of_nat` in this file is
   the bridge (mapRange `Int.toNat` on both signs, then `Finsupp` injectivity).

## Unconditional by-products (usable elsewhere)

`linearIndependent_log_primes` (ℤ and ℚ forms), `factorization_prod_primes`,
`isAlgebraic_two_rpow_rat`, `irrational_two_rpow_rat`, `linearIndependent_int_of_nat`.

## No contradiction found

Trevor's hope was to bump into one.  Nothing here conflicts with anything in the repo: the three
consistency edges (Gelfond–Schneider, Lindemann–Weierstrass, Nesterenko's `π, e^π`) all came out
of Schanuel exactly as they should, which is the evidence that `Literature.SchanuelConjecture`
says what we think it says.  The Wright row of `Maze.lean` is *not* closed by this: every level
`≥ 2` being transcendental is consistent with every level sitting just above a prime, so
irrationality of the least Wright constant is untouched.

## Next (suggestions, nothing is blocked)

* More consequences are cheap now: `2^√2` and `e^{e^e}`, algebraic independence of
  `log 2, log 3, …` **with** `π` (`z = (iπ, log p₁, …)`), transcendence of `e + log 2`,
  and Baker's theorem (linear forms in logarithms) as the `n`-generator version of the
  `algebraicIndependent_log_primes` argument.
* The four-exponentials conjecture is *not* a Schanuel consequence; if someone wants it, it needs
  its own `Literature/` entry.
