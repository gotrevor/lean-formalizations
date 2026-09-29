# HANDOFF 2026-09-29 — phase 24 COMPLETE: weakest hypotheses, what follows from Conjecture 1

`NumberTheory/Transcendence/WeakSchanuel.lean` is **sorry-free**; all five frozen statements are
machine-checked and `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

| statement | route |
|---|---|
| `gelfondSchneider_of_algIndepLogs` | `λ = (log a, b log a)`; Conj 1 makes them alg. indep., but `λ₂ ∈ ℚ̄(λ₁)` |
| `baker1966_of_algIndepLogs` | pass to a `ℚ`-basis of `span ℚ (range ℓ)` (`logSubmodule`), then `eq_zero_of_algebraicIndependent_linear` over `ℚ̄` |
| `algebraicIndependent_log_primes_of_algIndepLogs` | direct; unique factorisation gives `ℚ`-independence |
| `algebraicIndependent_pi_log_primes_of_algIndepLogs` | `iπ` is a log of `−1`; trade `iπ` for `π` by trdeg |
| `strongFourExponentials_of_algIndepLogs` | `StrongSix.strongSix` at `Fin 2 × Fin 2` + the new `AffTwo.constRatioTwo` |

## The flagged item resolved

The strong-four-exponentials row was marked "Ren, about 70% confident, not checked against a
source". **It is correct.**  The only genuine obstruction was that Roy's derivation argument
(`AffineRankOne.const_ratio`) needs *three* columns — it works by forcing the three `Pⱼ` into a
two-dimensional space, which is vacuous with two.  New route, in the `AffTwo` section:

* `sym_coeff` — from `A·D = B·C` for affine forms `aff a b = a + ∑ bₖXₖ`, apply `pderiv k`,
  `pderiv l` and `eval 0` to get `AᵢD_j + A_jDᵢ = BᵢC_j + B_jCᵢ` on coefficient vectors
  `cv a b = Fin.cons a b`.
* `exists_minor_ne` — `A, B` linearly independent gives `p, q` with `A p B q − A q B p ≠ 0`.
* `eq_smul_of_sym` — with `f v = α v p + β v q` chosen so `f A = 0`, `f B = 1`, the identity at
  `(p, ·)` and `(q, ·)` gives `f A·D_j + A_j·f D = f B·C_j + B_j·f C`; combining at `j = p, q`
  gives `2 f A f D = 2 f B f C`, so `f C = 0` (char 0), so `C_j = (f D)·A_j`.
* `constRatioTwo` — the polynomial-level wrapper.

**Schanuel is never used.**  `strongSix` touches `hS` only through
`algebraicIndependent_of_exp_isAlgebraic`, so the whole of Roy's strong six exponentials
theorem is *also* a consequence of Conjecture 1 alone — worth recording in the fact graph.

## Reusable by-products

* `AffTwo.eq_smul_of_sym` — pure linear algebra: `A⊙D = B⊙C` + `A,B` independent ⟹ `C ∈ K·A`.
  This is unique factorisation of a rank-one symmetric tensor, done without a UFD.
* `logSubmodule` — the logarithms of algebraic numbers as a `ℚ`-submodule of `ℂ`, and
  `isAlgebraic_exp_rat_mul`, `isAlgebraic_exp_of_mem_span`.
* `exists_rat_basis` — a finite family of complex numbers in a `ℚ`-basis of its own span,
  with the basis elements certified to lie in the span (`exists_rat_coords` in
  `StructuralRank.lean` does not expose independence or membership).

## Next

Run `scripts/fact-graph`.  Uncovered Waldschmidt-2023 items remain: Leopoldt §2 and Conj 7
(Roy's equivalent of Schanuel).  The observation above (Conj 1 ⇒ strong *six* exponentials,
not just four) is a one-line new edge that the graph should carry.

## Addendum (same lap): Conj 1 ⇒ strong SIX exponentials

`strongSix_of_algIndepLogs` is now a theorem, not a remark.  `StrongSix.strongSix` touches
`hS : SchanuelConjecture` in exactly one place — `algebraicIndependent_of_exp_isAlgebraic hS μ
hμli hμexp`, which is `AlgIndepLogsConjecture` applied verbatim — so the whole of Roy's theorem
rests on the weaker hypothesis.  Axiom-clean.  The fact graph carries the edge.

## Addendum 2: the vacuous `SixExponentials` edge, repaired

`ExponentialsKnown.lean`'s header flags that the only "strong ⇒ six exponentials" edge in the
repo, `sixExponentials_of_strongOverQ`, has a hypothesis machine-refuted as FALSE
(`not_strongSixExponentialsOverQ`), so the edge is vacuous.  It is now replaced by a real one.

Two things had to be got right, and both are recorded as theorems rather than prose:

1. **Strong four exponentials does not imply four exponentials.**  The strong forms hypothesise
   `ℚ̄`-linear independence; the four/six exponentials statements supply only `ℚ`-linear
   independence.  When `x` is `ℚ`-independent but `ℚ̄`-dependent, `x₁ = c·x₀` with `c` algebraic
   irrational, and "all `exp (xᵢyⱼ)` algebraic" says `exp ℓ` and `exp (c·ℓ)` are both algebraic
   at `ℓ = x₀y₀ ≠ 0` — Gelfond–Schneider, which no strong-exponentials hypothesis supplies.
   Hence `fourExponentials_of_strongFour_of_gs` carries `hGS` as a second hypothesis.
2. **Strong SIX is the wrong hypothesis for this repair.**  The degenerate `y` case cannot be
   fed back to strong six: a `ℚ̄`-dependent triple need not contain a `ℚ̄`-independent pair.
   Strong four is the right input — if no pair of the `yⱼ` is `ℚ̄`-independent then they are all
   `ℚ̄`-multiples of `y₀`, which is again the Gelfond–Schneider case.

`sixExponentials_of_algIndepLogs` then discharges both hypotheses from Conjecture 1
(`strongFourExponentials_of_algIndepLogs` and `not_isAlgebraic_exp_mul_of_algIndepLogs`, the
branch-free complex Gelfond–Schneider).  Axiom-clean.  New leaves: `exists_algebraic_ratio`,
`mem_logAlgSpan_of_exp_isAlgebraic`, `sixExponentials_of_fourExponentials`.
