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
