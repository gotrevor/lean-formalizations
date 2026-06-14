# HANDOFF — lean-formalizations (target: Curtis 1990)

**Repo purpose.** An umbrella for *solved-but-unformalized* results, with a soft spot
for **no-formula / impossibility** meta-theorems. One target right now:

## 🎯 THE TARGET — Curtis 1990, the no-Frobenius-formula theorem

Prove the two `sorry`s in
`src/LeanFormalizations/NumericalSemigroups/Curtis/Statement.lean`:

- `no_polynomial_relation` — **THEOREM**: no nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]` vanishes
  on the graph of the Frobenius number over Curtis's admissible family `A`. (I.e.
  the Frobenius number of a triple is not algebraic over its generators.)
- `no_finite_polynomial_formula` — **COROLLARY**: no finite menu of polynomials
  computes `g` piecewise. (`F = ∏(fᵢ − Y)` vanishes on the graph → contradiction.)

`Statement.lean` is the **designated audit surface** — keep it faithful to the paper
(`papers/Curtis-1990-Frobenius-formula.pdf`, present locally). Build the proof
**engine in sibling files** and have `Statement.lean` delegate, so the audited
statement and the proved statement stay definitionally identical.

This is genuinely hard (Dirichlet + algebraic geometry). **Multi-lap expected** —
advance each lap (read the paper, formalize one prerequisite); a disclosed
`sorry`/`axiom` with a citing docstring is baseline, not failure. Don't give up.

## Proof roadmap (Curtis's 3-page argument)
Suggested order — easiest foothold first:
1. **Lemma 2 first** (most elementary): an exact closed form for `g⟨s₁,s₂,s₃⟩` on a
   restricted family, via the **Brauer–Shockley Apéry-set** fact `g(S) = (max of
   S(s)) − s`. Builds on mathlib's `AddSubmonoid.closure` / `FrobeniusNumber`.
2. **The finish**: substitute Lemma 2's value for `Y`; feed infinitely many triples
   whose ratios → an irrational α; homogenize; the curve vanishes on a whole line,
   forcing `deg F ≥ (p−1)/2` for every prime `p`. Core is **"a nonzero univariate
   polynomial has finitely many roots"** (mathlib: `Polynomial.setOf_isRoot` finite
   / `card_roots`).
3. **Lemma 1** (the engine for step 2): Dirichlet primes in AP + Farey adjacency
   (`|rs − qt| = 1`). mathlib HAS Dirichlet
   (`Nat.setOf_prime_and_...`/`Dirichlet`); check whether Farey adjacency exists or
   needs building (Stern–Brocot / continued fractions are in mathlib).

## mathlib hooks (confirmed present)
- `FrobeniusNumber (n : ℕ) (s : Set ℕ)` and 2-var `frobeniusNumber_pair`
  (`Mathlib.NumberTheory.FrobeniusNumber`).
- `MvPolynomial` + homogenization; `Polynomial` root-finiteness; Dirichlet's theorem.

## Current state
- Statement-only seed. `Statement.lean` carries both theorems `sorry`'d; intended to
  be green-with-sorry on `main`. (If it does NOT compile, lap 1 = fix the statement's
  Lean — coercions ℕ→ℂ, the `eval` point vectors, the `{s₁,s₂,s₃} : Set ℕ` literal,
  and confirm `FrobeniusNumber` is referenced correctly — then proceed.)
- No remote. No prior batons.

## Standing rules (this repo)
- **DO NOT push** (no remote; the host handles any publishing — repo is unpublished).
- **Commit every green build** (verify green from real `lake build` output first).
- Keep `Statement.lean` **faithful**; build the engine elsewhere and delegate.
- Aim **axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`);
  a disclosed `axiom`/`sorry` + citing docstring is fine for a genuinely-hard
  sub-lemma — then keep chipping to discharge it.
- Reference corpus (cross-lap memory) at
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` — `grep` it
  before re-deriving any tactic/build friction.
- Blocked needing the open web (a mathlib API, an existing formalization, a proof
  from the literature)? Append a dated item to `ON-LINE-REQUEST.md` and continue.

→ Start: read `Statement.lean` + the Curtis README, skim the PDF, then take the next
step on the roadmap.
