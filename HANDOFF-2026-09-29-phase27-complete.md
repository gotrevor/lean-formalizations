# HANDOFF — phase 27 complete (2026-09-29)

## State
`main` @ `50514ad`, `lake build` GREEN (8745 jobs).  Scoped target
`sorry-free:src/LeanFormalizations/NumberTheory/Leopoldt/RankOne.lean` met.

## What landed
`NumberTheory/Leopoldt/RankOne.lean` is sorry-free; both frozen statements are
`#print axioms`-clean (`propext, Classical.choice, Quot.sound`):
- `rank_cyclotomic_eight : Units.rank (CyclotomicField 8 ℚ) = 1`
- `leopoldt_cyclotomic_eight_seven : LeopoldtConjecture (CyclotomicField 8 ℚ) 7`

New file `NumberTheory/Leopoldt/PrincipalUnits.lean` carries the real content, and it is
strictly stronger than the directive asked for:
- `leopoldt_of_rank_le_one (p) (hrank : Units.rank K ≤ 1) : LeopoldtConjecture K p` —
  **every** number field, **every** prime.  No abelian hypothesis, no `p` odd, no
  unramifiedness, no `p`-adic logarithm, no `ℤ_p`-action on `U⁽¹⁾`.

## Why the phase-26 plan was unnecessary
1. The exponent `N = card (𝓞 K ⧸ v)ˣ` that makes a unit principal is prime to `p`, hence a
   `ℤ_p`-unit.  So it suffices to prove `N·a = 0`, and one may replace the exponents `m n` by
   `N · m n` throughout.  The residue-class subsequence in the `Literature/Leopoldt.lean`
   header is avoidable.
2. `valuation_zpow_sub_one`: on a principal unit, `W (θ^t − 1) = W (θ − 1)` **exactly** when
   `t` is prime to `p`.  So only the `p`-part of the exponent can move `ε^m` towards `1`; and
   `a ≠ 0` in `ℤ_p` bounds that `p`-part (`exists_pow_split`).  Antitonicity of
   `j ↦ W (ε^(N p^j) − 1)` then gives a nonzero lower bound, contradicting the local limit.

Rank `≤ 1` is used only in `card_le_rank`: multiplicative independence of `r` units makes them
`ℤ`-linearly independent in `Additive (𝓞 K)ˣ`, whose `ℤ`-rank is `rank K`
(`NumberField.Units.finrank_eq`), so `r ≤ 1` and the local lemma only ever sees one unit.

## Gotchas worth carrying
- `Valued.mem_nhds` / `isOpen_ball` now speak in `MonoidWithZeroHom.ValueGroup₀`, not `Γ₀`.
  Bridge with `Valuation.embedding_restrict` and `ValueGroup₀.embedding_strictMono`.
- `valuedAdicCompletion_eq_valuation' v y : Valued.v (algebraMap K (v.adicCompletion K) y) =
  v.valuation K y` works with `exact` but **not** with `rw` (the statement is phrased with the
  `WithVal.equiv` coercion, which is only defeq to `algebraMap`).
- `Ideal.Quotient.field` creates a `Ring`-instance diamond against
  `Ideal.Quotient.instRingQuotient`: a `(p : F) = 0` hypothesis stated before the `Field`
  `haveI` is not accepted after it.  Avoided by using `IsDomain` + `sub_pow_char` instead of a
  field, so only the quotient's own `CommRing` is ever in play.
- `CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero` has **explicit** `n` and
  `K`, so TC resolution never finds it; supply it by hand.
- `Additive.ofMul_prod` / `ofMul_zpow` live at the **root** namespace (`ofMul_prod`).

## Next
Phase 28 (recorded at the top of `DIRECTION.md` and in `PENDING_WORK.md`): rank ≥ 2, i.e. the
Baker–Brumer wall.  For `r ≥ 2` the valuation argument genuinely fails — it controls one unit's
`p`-part, not a mix of `r` of them — and the statement then really does imply `ℚ_p`-linear
independence of `p`-adic logarithms.  Attack order: (1) `padicLog` on the principal units of
`v.adicCompletion K` (only step with real content), (2) Brumer as a `Literature/` axiom with a
faithfulness argument, (3) rank-2 Leopoldt for ℚ(ζ₇).
