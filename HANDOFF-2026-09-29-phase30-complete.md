# Handoff: phase 30 COMPLETE — one conjecture behind Fermat and Mills

**Date**: 2026-09-29 · **Branch**: `main`

## Result

`src/LeanFormalizations/NumberTheory/Mills/SharedConjecture.lean` is **sorry-free**, and all three
frozen statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`):

- `fermat_of_doubleExpTraceComposite`
- `mills_transcendental_of_doubleExpTraceComposite`
- `lt_padicValNat_glCard_prime_base`

`ThreeAdic.lean`'s five frozen statements are unchanged and still axiom-clean; `Literature/` was
not touched.

## What landed

**1. The Mills glue is now a reusable lemma.** `ThreeAdic.exists_companion_of_algebraic_mills`
was factored out of the old `mills_threeAdic` body verbatim: from `IsMinMills A` + `IsAlgebraic ℚ A`
it produces a nonsingular integer `3 × 3` companion matrix `C`, a shift `m` and a threshold `i₀`
with `tr C^(3^i) = ⌊A^(3^(m+i))⌋` for `i ≥ i₀`, together with primality and strict monotonicity of
that trace sequence. `mills_threeAdic` is now three lines plus the step-3 assembly. The Mills half
of phase 30 is then immediate: the conjecture at `c = 3, h = 0` gives frequently-composite traces,
which contradicts eventually-prime.

**2. The right generalisation of step 1 is a congruence, not a divisibility.**  Phase 29's step 1
concluded `p ∣ tr C^(3^(m+j))`. Stated instead as

`exists_trace_pow_congr : ∃ j ≥ 1, (p:ℤ) ∣ tr C^(c^(m+j)) − tr C^(c^m)`

the shift `h` of `DoubleExpTraceComposite` **cancels for free** — no second proof is needed for the
shifted sequence, and the base generalises from `3` to any prime `c` with `3 → c` textual
substitution only (`Nat.Prime.coprime_iff_not_dvd hc` and `hc.pos` are the only places primality is
used). This is why the third frozen statement cost almost nothing beyond phase 29.

**3. Fermat.** `C = diagonal ![2,1]`, `c = 2`, `h = 0`; `Matrix.diagonal_pow` gives
`tr C^N = 2^N + 1`, so `tr C^(2^k) = F_k`. Growth is `k < 2^k ≤ 2^(2^k)` (`Nat.lt_two_pow_self`
twice). Note this is genuinely unconditional-modulo-the-conjecture: no Fermat-specific input.

## State

Verified from real output this session: `lake build` green (8748 jobs, pre-commit hook), target file
`grep -c sorry` = 0, all five `#print axioms` above clean. `scripts/fact-graph` rerun (30 edges,
29 hypotheses). Commits this lap: `5f95edd` (step 3 + the ThreeAdic refactor) and the commit adding
this handoff with the Fermat and Mills halves. Nothing pushed.

## Next

The conjecture `DoubleExpTraceComposite` is now the single named obligation behind both Fermat and
Mills in this repo. Two directions:

- **Narrow it.** The conjecture as stated is presumably open in general, but special cases are not.
  For `C` with a **repeated eigenvalue** or a rational eigenvalue the trace factors algebraically
  (`tr C^(c^k) + h` becomes a value of a polynomial with a nontrivial factorisation for the right
  residues of `k`), so a sub-conjecture restricted to `C` with distinct irrational eigenvalues and
  no algebraic factorisation is the honest statement of the difficulty. Worth isolating in Lean.
- **Finish the 3-adic obstruction instead.** `PROBE-MILLS-3ADIC.md`'s residual six classes of
  `f mod 3` for a totally real cubic Pisot `β` satisfying Saito's (1.3) is the unconditional route,
  and `lt_padicValNat_glCard_prime_base` now gives the same machinery at every prime base — so the
  same obstruction can be run 3-adically *and* 2-adically (base `c = 2` on the Fermat side) and the
  two might be combined.
