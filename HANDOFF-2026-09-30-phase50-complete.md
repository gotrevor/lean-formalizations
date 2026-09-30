# Phase 50 COMPLETE — Dold congruence for every charpoly coefficient

`src/LeanFormalizations/NumberTheory/Mills/ExteriorDold.lean` is **sorry-free**; both frozen
statements `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  `lake build` green
(8771 jobs); `scripts/fact-graph` regenerated (30 edges, 31 hypotheses).

* `charpoly_coeff_prime_pow_congr` — `p^(k+1) ∣ coeff j χ_(A^(p^(k+1))) − coeff j χ_(A^(p^k))`
* `aeval_charpoly_prime_pow_congr` — `χ_(A^(p^k))(A^(p^(k+1))) ≡ 0 (mod p^(k+1))` entrywise

## Route as built (matches the file header)
`compound j M := LinearMap.toMatrix B B (exteriorPower.map j (Matrix.toLin' M))`, `B` =
`(Pi.basisFun R (Fin n)).exteriorPower j`, indexed by `Set.powersetCard (Fin n) j`.

* **Cauchy–Binet is free**: `exteriorPower.map_comp` + `LinearMap.toMatrix_comp` ⟹ `compound_mul`,
  hence `compound_pow`.  mathlib has NO Cauchy–Binet, so the direct minor definition would have
  cost a determinant-expansion proof.
* `compound_apply`: entries are minors, from `ιMultiDual_apply_ιMulti`; the index order comes out
  transposed, fixed by `det_transpose`.
* `trace_compound` matches mathlib's `Matrix.charpoly_coeff_eq_sum_minors` after reindexing
  `Fin j → ↥s` by `powersetCard.orderIsoOfFin` (`det_submatrix_equiv_self`) and converting the
  subtype sum to the `Finset.powersetCard` sum (`Finset.sum_coe_sort` + `Equiv.subtypeEquivRight`).
* `gauss_minors`: reindex the `powersetCard` index to `Fin m` (`Fintype.equivFin`,
  `Matrix.reindexAlgEquiv` for `map_pow`, a hand-proved `trace_reindex`), then apply
  `GaussCongruenceProof.gaussCongruenceTrace_holds`.
* Corollary: `aeval_self_charpoly` on `A^(p^(k+1))`, subtract the two charpolys, evaluate
  coefficientwise (`dvd_aeval_entry`).

## GOTCHA worth keeping
Doing the compound-matrix layer at `R = ℤ` directly **fails**: `rw` hits an instance diamond on
`⋀[ℤ]^j (Fin n → ℤ)` (`Submodule.module` vs `AddCommGroup.toIntModule`) and the rewrite motive is
rejected as not type-correct under `instances` transparency; `simp only` silently no-ops.  Prove
the whole layer over a generic `CommRing R` and specialize only at the Gauss step.

## NEXT
Theorem A route step 3 (`ROADMAP-PRIME-TOWERS.md` §4a): `σ : q(B) ↦ q(B^p)` as a ring endomorphism
of `(ℤ/p^(k+1))[B]`, `B = A^(p^k)` — `aeval_charpoly_prime_pow_congr` is exactly the well-definedness
input.  Await the next DIRECTION.md phase plant.
