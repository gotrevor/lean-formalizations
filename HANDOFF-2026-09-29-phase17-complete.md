# HANDOFF 2026-09-29 — phase 17 COMPLETE

**Branch** `main`.  **Completion commit** `206efab` ("phase 17 COMPLETE: strong six
exponentials under Schanuel"); this doc is the checkpoint on top of it.  Working tree clean,
`lake build` green, nothing in flight (no Aristotle job, no open `ON-LINE-REQUEST`).

**Lap commits** (oldest first): `30188dc` five exponentials via `Baker1966` · `b2aea43`
`AffineRankOne.const_ratio` · `5bfdd29` `StrongSix` basis extraction · `206efab` the assembly.

**Exact next step**: phase 18 as queued in `DIRECTION.md` — Champernowne's constant is
transcendental (Mahler 1937) via `roth1955_of_stephan`.  Before freezing any statement, check
the approximation exponent numerically: the run of consecutive k-digit integers gives a
rational with denominator ≈ (10^k − 1)², and the claim is that this beats q^(−2−ε).  Normality
of Champernowne is out of scope (that belongs in normal-numbers).  After it, continue through
Waldschmidt 2023 statement by statement: theorems → `Literature/`, conjectures → hypothesis
`Prop`s, derived implications → proofs.

`src/LeanFormalizations/NumberTheory/Transcendence/ExponentialsKnown.lean` is **sorry-free**,
and every theorem in it is `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

## The two open statements, both closed

### 1. `fiveExponentials_of_shifted (h : SixExponentialsShifted) (hB : Baker1966)`

One line once `Baker1966` was available: the operator's new `Literature.Baker1966`
(inhomogeneous linear forms in logarithms) specialises to the file's `BakerTwoLogs` by taking
`n = 2` and `β = (γ, −r₀, −r₁)` (`bakerTwoLogs_of_baker1966`).  The reduction itself
(`fiveExponentials_of_shifted_of_baker`) was already proved last lap.  This confirms the lap-16
analysis: the five-exponentials reduction needs *exactly* Baker for two logarithms, nothing more.

### 2. `strongSixExponentials_of_schanuel` — Roy's strong six exponentials theorem under Schanuel

New modules:

* `Transcendence/AffineRankOne.lean` — pure algebra, no `ℂ`.
  `aff a b = C a + ∑ₖ C (bₖ) * Xₖ` in `MvPolynomial (Fin n) K`, `K` a field.
  **`const_ratio`**: if `P₀,P₁,P₂` are `K`-linearly independent affine polynomials and
  `Q₀,Q₁,Q₂` are affine with `QᵢPⱼ = QⱼPᵢ`, then `Qⱼ = c·Pⱼ` for a *single constant* `c ∈ K`.

  **The idea that made this cheap**: differentiate.  Applying `pderiv k` to `QᵢPⱼ = QⱼPᵢ` and
  eliminating gives `Tₖ · Pⱼ = P₀ · (C(∂ₖQⱼ)P₀ − C(∂ₖPⱼ)Q₀)` with
  `Tₖ = C(∂ₖQ₀)P₀ − C(∂ₖP₀)Q₀` (morally `P₀² ∂ₖ(Q₀/P₀)`).  If every `Tₖ = 0` then `Q₀ = c·P₀`
  and cancelling `P₀` in the domain spreads it to all `j`; if some `Tₖ ≠ 0`, combining the
  identity for `j = 1, 2` produces a nontrivial `K`-linear relation among `P₀,P₁,P₂`.
  **No unique factorization / no degree theory** — the first attempt went through
  `MvPolynomial` being a UFD and coprimality of linear forms, which is much heavier.

* `Transcendence/StrongSix.lean` — the transport from `ℂ` to that polynomial ring.
  - `LogSet = {ℓ | IsAlgebraic ℚ (exp ℓ)}`; `mem_span_of_mem_logAlgSpan`: `𝓛̃` sits inside the
    `ℚ̄`-span of `insert 1 LogSet` (`ℚ̄ = algebraicClosure ℚ ℂ`, an `IntermediateField`, hence a
    field — and `LinearIndependent (integralClosure ℚ ℂ)` is *defeq* to
    `LinearIndependent ↥(algebraicClosure ℚ ℂ)`, so the frozen statement needs no massaging).
  - `exists_logBasis`: finitely many members of `𝓛̃` lie in the `ℚ̄`-affine span of one
    **`ℚ`-linearly independent** finite family of logarithms.  Order matters: run
    `exists_linearIndependent ℚ LogSet` on the *whole* (infinite) log set first — a subfamily of
    a linearly independent family is still independent — then cut to a finite subfamily with
    `Submodule.mem_span_finite_of_mem_span`.  Doing it the other way round forces an ugly
    common-refinement of six separate representations.
  - `strongSix`: Schanuel ⇒ `AlgebraicIndependent ℚ μ`
    (`algebraicIndependent_of_exp_isAlgebraic`) ⇒ `AlgebraicIndependent ℚ̄ μ`
    (`AlgebraicIndependent.extendScalars`, mathlib) ⇒ `aeval μ` injective ⇒ the six products are
    `aff`s with `QᵢPⱼ = QⱼPᵢ` ⇒ `const_ratio` ⇒ `x₁ = c·x₀` with `c` algebraic ⇒ contradiction.

  Where `ℚ̄`-independence is indispensable: `const_ratio` concludes `c ∈ K` and only a
  `K`-linear relation among the `x` is a contradiction.  With `K = ℚ` the theorem is false —
  `not_strongSixExponentialsOverQ` in the target file is the kernel-checked refutation.

## Gotchas worth keeping

* `Finset.equivFin` reasoning on `Finset ℂ` blows the default heartbeat budget; both big
  declarations carry `set_option maxHeartbeats 1000000 in`.
* `set P := fun j => aff ..` does **not** rewrite hypotheses stated as `aff (qa i) (qb i) * ...`
  — those are beta-reducts, not the literal lambda.  Re-`have` the hypothesis at the new names
  (`have hcross' : ∀ i j, Q i * P j = Q j * P i := hcross`) and it typechecks by defeq.
* `linear_combination` treats `C (a*b)` and `C a * C b` as different atoms: `simp only
  [map_sub, map_mul, map_neg]` first.

## Next

`DIRECTION.md` phase 18 (queued, not planted): Champernowne's constant is transcendental via
`roth1955_of_stephan`.  Check the approximation exponent numerically before freezing statements.
