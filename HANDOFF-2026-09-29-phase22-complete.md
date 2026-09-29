# HANDOFF 2026-09-29 — phase 22 COMPLETE

`src/LeanFormalizations/NumberTheory/Transcendence/BedrockBaker.lean` is **sorry-free**, and all
five frozen statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only):

* `transcendental_tan_of_algebraic`
* `transcendental_sinh_of_algebraic`
* `transcendental_cosh_of_algebraic`
* `transcendental_pi_add_log_two`
* `transcendental_two_rpow_sqrt_two_mul_three_rpow_sqrt_three`

No statement was false or underivable.  Full route + gotchas are in the file header (`## Result
(phase 22)`).  New reusable leaves, all in `LeanFormalizations.Bedrock`:

* `not_quad_cexp_real` — real-exponential twin of `not_quad_cexp_I_mul`.
* `baker_relation` — `BakerHomogeneous` repackaged as "any `ℚ̄`-relation `c₀·1 + Σ cᵢλᵢ = 0` among
  `1` and `ℚ`-independent logs of algebraics is trivial".  This is the form every Baker
  application wants; use it rather than unfolding `LinearIndependent` again.
* `logTwoPair`, `exp_logTwoPair`, `linearIndependent_logTwoPair` — the survey's own p. 4 example.
* `isAlgebraic_sqrt_nat`, `linearIndependent_logTwoThree` (the `ℂ`-valued version of the `ℚ`-linear
  independence of `log 2, log 3`).

Gotcha worth keeping: plain `simp` rewrites `((Real.log 2 : ℝ) : ℂ)` into `Complex.log 2`, after
which `Complex.ofReal_im` no longer fires and imaginary-part arguments stall.  Write `2πi` as
`((2 * Real.pi : ℝ) : ℂ) * Complex.I` and use `simp only` with `Complex.mul_I_im`/`mul_I_re`.

## Next

`WALDSCHMIDT-2023.md` still lists Leopoldt §2 and Conj 7 (Roy's equivalent of Schanuel) as
uncovered.  More bedrock in the same vein is also open (e.g. Baker-inhomogeneous consequences via
`Literature.Baker1966`, or `Γ` values beyond `1/4` via Nesterenko).
