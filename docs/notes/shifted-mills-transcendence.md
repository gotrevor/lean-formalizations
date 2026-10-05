# Shifted Mills constants are transcendental

*Written by Claude at Trevor Morris's direction.*

## The result

For a sequence of positive integers `C_1 < C_2 < …`, let `ξ(C)` be the least real `A > 1` such that `⌊A^(C_k)⌋` is prime for every `k ≥ 1`.  Mills' constant is `ξ(3^k)`.

**Theorem E+.**  For every integer `s ≠ 0`, the constant `ξ(3^k + s)` is transcendental.  The index starts where every ratio `C_(k+1)/C_k` is at least 2, so `3^(k₀) ≥ s` when `s > 0`, and `k₀ = 1` when `s < 0`.

The case `s = −2` (exponents 1, 7, 25, 79, …) is Theorem E.  Its constant begins `2.0066301472…`, on the usual assumption that the greedy prime chain never gets stuck.  The theorem does not use those digits.

The case `s = 0`, Mills' constant itself, is not covered.  Without RH its transcendence is open.  Saito (arXiv:2508.16068) proves it under RH.

## What it assumes

The Lean proof has exactly two hypotheses, both published theorems stated as named `Prop`s:

* `BakerHarmanPintz2001`: for large `x`, the interval `[x, x + x^(21/40)]` contains at least `d₀ x^(21/40) / log x` primes.  This is Baker, Harman and Pintz, Proc. London Math. Soc. 83 (2001).
* `Dubickas2022`: Dubickas, Lemma 6 of the 2022 paper.  It is a consequence of Corvaja and Zannier, Acta Math. 193 (2004).  For algebraic `α > 1`, either some `α^(s_m)` is a Pisot number, or `‖q α^(s_k)‖ > e^(−ε s_k)` for all large `k`.

Neither Saito's paper nor Baker's theorem on linear forms in logarithms is an input.  Saito's general Type B theorem uses Baker, through his Lemma 5.14.  For the family `3^k + s`, the proof replaces that step with the Skolem–Mahler–Lech theorem for order-3 integer recurrences, which is proved in the repository.

## Weaker prime inputs

The exponent `21/40` is not needed.  Write `PrimesShortInterval θ` for the statement that `[x, x + x^θ]` contains at least `d₀ x^θ / log x` primes for large `x`.

* **Every `θ < 5/9` suffices.**  `PrimesShortInterval θ` and `Dubickas2022` give Theorem E+ (`SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval'`).  So Heath-Brown–Iwaniec (1979, any `θ > 11/20`) is enough on its own.  Huxley's `7/12` and Ingham's `5/8` are not.  The exponent enters twice: through the record step, and through the decay `‖ξ^(C_k)‖ ≪ ξ^(−μ C_k)` for `μ < 2 − 3θ`.  The degree-3 endgame needs `μ > 1/3`.
* **For `5/9 ≤ θ < 2/3`, two more inputs are needed** (`ShiftHitPrime.xi_shift_transcendental_of_hitPrime`).  One is Dubickas's Lemma 8, which gives eventual records in every degree.  The other is the open statement `HitPrime`, with its half-shift twin: for a Pisot polynomial of degree `≥ 4` and `s ≠ 0`, some fixed prime divides `tr β^(3^n + s)` for infinitely many `n`.  The step that fails is the 3-adic argument below.  It does not extend to degree 4: `ShiftRigidityUnipotent.lean` gives explicit quartics (`f₀`, `f₂`) that satisfy every 3-adic constraint.  Their traces fail to be prime only because a small prime happens to divide them.

## Where it is in Lean

Repository: <https://github.com/gotrevor/lean-formalizations>, directory `src/LeanFormalizations/NumberTheory/Mills/`.

* Headline: `SaitoTypeB.xi_shift_transcendental_classical` in `SaitoTypeB.lean`.  `xi_shifted_transcendental_classical` is the `s = −2` case.
* Exponents: `ShiftedMillsAll.shiftC j s k = 3^(k+j) + s`.
* The same theorem conditional on Saito's Type B theorem instead: `ShiftedMillsAll.xi_shift_transcendental`.

## How the proof goes

1. **Reduction to a cubic Pisot number.**  Saito's method, re-proved in `SaitoTypeBParts.lean`, `SaitoTypeBRecords.lean` and `SaitoTypeBNoGap.lean`, gives two cases.  Either `ξ` is transcendental, or `ξ^g` is a cubic Pisot number `β` with `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` for all large `k`.  Here `g` is `3^b` or `2·3^b`.
2. **The traces cannot all be prime** (`ShiftRigidity.lean` for `g = 3^b`, `HalfShiftRigidity.lean` for `g = 2·3^b`):
   * Prime traces force a 3-adic window, whose Teichmüller limits satisfy a linear identity in the conjugates `β_k^s`.
   * The Galois group acts transitively on the conjugates.  Since `s ≠ 0`, the weights `β_k^s` are not all equal, so the identity forces every Teichmüller limit to be equal (an `S₃` or circulant argument).
   * That puts the minimal polynomial in the class `(X − z)³ mod 3`.  Then `3` divides `tr(β^s)`, which contradicts `tr(β^s) = ±1`.
   * The remaining case is when `ℚ(β)` is the cyclic cubic field of conductor 13.  A finite rank certificate over `ℚ(ζ₁₃)` closes it (`E1Certificate.lean`).

Saito's own theorems for related shifted families (for example `ξ(r·3^k − 1)`) exclude the Pisot case by size, which needs huge parameters.  Here it is excluded by arithmetic, with no size condition.  At `s = 0` the weights are all 1 and the arithmetic argument says nothing.  That is why Mills' constant stays open.

## Remaining trust

* The two literature `Prop`s.  Corvaja–Zannier has been formalized independently by R. Stephan (`rwst/Subspace-Theorems`), so it can be discharged once the toolchains match.  Baker–Harman–Pintz is not formalized.
* The faithfulness of `Saito2025TypeBTrace` matters only for the second, alternative headline.  Its audit is `saito-2025-faithfulness-audit.md` in this directory.
* The Lean kernel.  The conductor-13 certificate and the Frobenius-period check of the 27 monic cubics mod 3 are kernel-checked computations.

Proof write-up with referee notes: `PROOF-THEOREM-E.md`.  Paper draft: `paper/prime-towers.tex`.
