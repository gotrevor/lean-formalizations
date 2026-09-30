# Phase 51 COMPLETE — the Frobenius orbit sum is scalar

`src/LeanFormalizations/NumberTheory/Mills/OrbitSum.lean` is **sorry-free**; all three frozen
statements `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  `lake build` green
(8772 jobs); `scripts/fact-graph` regenerated (30 edges, 31 hypotheses).

* `pow_prime_pow_add_card_congr` — `A^(c^(n+d)) ≡ A^(c^n) (mod c^(n+1))`
* `orbit_sum_congr` — `Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n))·I (mod c^(n+1))`
* `orbit_sum_entry_congr` — off-diagonal entries of the orbit sum vanish (Theorem A's input)

## Route as built — it differs from the file header, deliberately

The header's route builds `σ : q(B̄) ↦ q(B̄^c)` on `R[B̄]` and then proves "fixed ring = scalars".
**That route cannot pin the constant when `c ∣ d`** (the trace argument only gives `d·s ≡ d·tr B`),
which the header itself flags.  What is built instead identifies the constant exactly:

1. **Roots, at matrix level.** `aeval_charpoly_tower`: `χ_B(B^(c^k)) ≡ 0 (mod c^(n+1))` for every
   `k`, from phase 50 `aeval_charpoly_prime_pow_congr` at level `n+k−1` plus
   `charpoly_coeff_tower_congr` (the charpoly is constant along the tower mod `c^(n+1)`).
2. **Transfer to polynomials.** `coeff_dvd_of_aeval_dvd`: if `deg r < d` and `r(B) ≡ 0 (mod c^m)`
   entrywise then `c^m` divides every coefficient of `r`.  Induction on `m`; the `m = 1` step is
   `eq_zero_of_aeval_mapMatrix_eq_zero` (χ̄_B irreducible ⇒ it is the minimal polynomial of `B̄`,
   by a Bézout/coprimality argument in `(ZMod c)[X]`).  Consequence `charpoly_comp_dvd`:
   `χ̄_B ∣ χ̄_B(X^(c^k))` over `ZMod (c^(n+1))` — this is what the header hid inside "σ is well
   defined", and it is needed at *every* `k`, not just `k = 1`.
3. **Unit differences.** `T = AdjoinRoot χ̄_B` is local: `π : T → K = AdjoinRoot χ̄_A` has kernel
   `cT` (`dvd_of_castHom_eq_zero` + `C_dvd_iff_dvd_coeff`), and `(c : T)^(n+1) = 0`, so
   `π u ≠ 0 ⇒ IsUnit u`.  In the residue field `root_pow_frobenius_injOn` gives
   `y^(c^i) ≠ y^(c^j)` for `i ≠ j < d`: otherwise `y^(c^m) = y` with `0 < m < d`, and then *every*
   element of `K` (all `c^d` of them) is a root of `X^(c^m) − X`.
4. **Factor.** `eq_prod_X_sub_C_of_roots` (new, generic over any `CommRing`): a monic degree-`m`
   polynomial with `m` roots of pairwise **unit** difference equals `∏ (X − C r_k)`.  Then
   `prod_X_sub_C_nextCoeff` gives `Σ_(k<d) x^(c^k) = −nextCoeff χ̄_B = tr B` **exactly**, `c ∣ d`
   or not.
5. **Back to matrices.** The identity is a divisibility in `(ZMod c^(n+1))[X]`
   (`orbit_sum_poly`); evaluating at `B̄` (Cayley–Hamilton kills `χ̄_B`) is an `aeval`, so no ring
   hom into the non-commutative matrix ring is needed.

Statement 1 is independent of all that: `χ̄_A` irreducible ⇒ `AdjoinRoot χ̄_A` is a field of order
`c^d` ⇒ `χ̄_A ∣ X^(c^d) − X` ⇒ `Ā^(c^d) = Ā`, then `n` phase-47 Teichmüller lifting steps.

## GOTCHAS worth keeping
* `AdjoinRoot.lift` needs a **commutative** target, so it cannot map into `Matrix`.  Go the other
  way: state the conclusion as `f ∣ p` in `R[X]` and apply `Polynomial.aeval` (which is happy in a
  non-commutative algebra).
* `Polynomial.Monic` is *definitionally* `leadingCoeff = 1`, so dot-notation on a `Monic` hypothesis
  resolves in the `Eq` namespace and fails.  Write `Polynomial.Monic.natDegree_mul h1 h2` etc.
* `simp only [iterateFrobenius_def] at h` does not fire through a `Function.Injective ⇑f`; produce
  the pointwise equation first, then apply `f.injective`.
* `set`-bound `hpb := AdjoinRoot.powerBasis' …` loses the definitional link needed by
  `AdjoinRoot.powerBasis'_dim`; inline the term instead of naming it with `have`.

## NEXT
Theorem A itself (`ROADMAP-PRIME-TOWERS.md` §4a, step 6): feed `orbit_sum_entry_congr` into the
covering/prime-free-interval engine (phase 41 `CoveringEngine`) to get `u(c^n) + h` composite i.o.
for order-`d` recurrences at inert `c`.  Await the next `DIRECTION.md` phase plant.
