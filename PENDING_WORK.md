# PENDING_WORK — Curtis 1990 engine

Open obligations in `src/LeanFormalizations/NumericalSemigroups/Curtis/Engine.lean`.
Headline theorem `no_polynomial_relation` reduces (spine machine-checked) to two
`sorry`s. The corollary `no_finite_polynomial_formula` and `finite_specCurve_eq_zero`
are fully proved (axiom-clean modulo the main theorem).

## Sorry 1 — `half_le_totalDegree` (Step B, degree-counting finish) — TRACTABLE
Goal: `F ≠ 0`'s specialization `specCurve F p` nonzero + all `substCurve F p k = 0`
(k = 2..(p-1)/2+1) ⟹ `(p-1)/2 ≤ F.totalDegree`.

All sub-pieces located/confirmed in scratch. Remaining assembly:

1. **Bridge (proved):** `substCurve_eq_aeval_specCurve` already gives
   `substCurve F p k = aeval ![X 0, X 1, c_k] (specCurve F p)`, `c_k := C(k-2)·X 0 + X 1 − C p`.
2. **View `H := specCurve F p` as univariate in Y:** `Hy := finSuccEquiv ℂ 2 (rename (Equiv.swap (0:Fin 3) 2) H)`.
   - Degree (PROVED in scratch): `Hy.natDegree = H.degreeOf 2`, via
     `rw [natDegree_finSuccEquiv]; have h := degreeOf_rename_of_injective (Equiv.injective (Equiv.swap (0:Fin 3) 2)) 2; rwa [Equiv.swap_apply_right] at h`.
   - `H.degreeOf 2 ≤ H.totalDegree`: `degreeOf_le_totalDegree H 2`.
   - `H.totalDegree ≤ F.totalDegree`: `H = specCurve F p = aeval (deg ≤1 map) F`; need a
     `totalDegree_aeval_le`-style bound (substituting `C p` (deg 0) and `X j` (deg 1)).
     ATTACK: prove by `MvPolynomial.totalDegree` monotonicity under such substitutions, or
     bound via `aeval` of monomials. (If no direct lemma, induction on `F`.)
3. **Each `c_k` is a root of `Hy`** — the one genuinely missing lemma:
   `Polynomial.eval (rename' c_k) Hy = (the Y:=c_k substitution of H) = substCurve F p k = 0`.
   Need bridge `Polynomial.eval q (finSuccEquiv ℂ 2 G) = aeval (Fin.cons q ![X 0, X 1]) G`
   (q : MvPolynomial (Fin 2) ℂ), provable by `algHom_ext` analogous to mathlib's
   `MvPolynomial.eval_eq_eval_mv_eval'` (which only handles scalar `y`). Then compose with the
   `rename (swap 0 2)` and reconcile `Fin.cons`/`![..]` indexing with `substCurve_eq_aeval_specCurve`.
4. **Distinctness of `c_k`:** `c_k − c_{k'} = (k−k')·X 0 ≠ 0` for `k ≠ k'` in range (coefficients
   `(k:ℂ)−2` distinct since `k ≤ (p-1)/2+1 < p` and char 0). So `k ↦ c_k` injective on the range.
5. **Count:** the `(p-1)/2` distinct roots `c_k` sit in `Hy.roots.toFinset`; with `Hy ≠ 0`
   (from `H ≠ 0` via `finSuccEquiv`/`rename` injective), `card_roots'`:
   `#roots.toFinset ≤ Multiset.card roots ≤ Hy.natDegree`. Chain with step 2.

Net: `(p-1)/2 = #{c_k} ≤ Hy.natDegree = degreeOf 2 H ≤ totalDegree H ≤ totalDegree F`.

## Sorry 2 — `substCurve_eq_zero` (Step A: Lemmas 1 + 2 + limit) — DEEP, multi-lap
Goal: `F` vanishes on graph ⟹ each `substCurve F p k = 0`.
Decomposes into:
- **Lemma 1** (Dirichlet primes in AP + Farey adjacency): infinitely many admissible
  `(p, xₙ, yₙ)`, `xₙ` prime, `xₙ≡1`, `yₙ≡p−k+1 (mod p)`, `gcd=1`, `yₙ/xₙ→α` irrational.
  mathlib has Dirichlet (`Nat.setOf_prime_and_...`/`Dirichlet`); Farey adjacency `|rs−qt|=1`
  likely needs building (Stern–Brocot / `Nat.continuant`?). **Aristotle: Lemma 2 submitted
  (job 03706c46); Lemma 1 is the next candidate once Lemma 2 returns.**
- **Lemma 2** (Brauer–Shockley Apéry value `g = (k−2)s₂+s₃−s₁`): **OUT TO ARISTOTLE**
  (`tools/aristotle/curtis-lemma2-prompt.txt`, job `03706c46`). Self-contained, elementary.
- **Limit argument**: `G(xₙ,yₙ)=0`, `yₙ/xₙ→α`, `xₙ→∞` ⟹ leading form `G_D(1,α)=0` for all
  irrational α in an interval ⟹ `G_D(1,T)≡0` (infinitely many roots) ⟹ `G_D=0` ⟹ `G=0`.
  This *replaces* Curtis's projective homogenization with an elementary `Filter.Tendsto` limit
  + `Polynomial.eq_zero_of_infinite_isRoot`. (Cleaner than the paper.)

## Attack-path summary (pick one per lap)
- **A (recommended next): finish `half_le_totalDegree`** — purely algebraic, all lemmas
  identified above; only the eval→root bridge (3) and `totalDegree_aeval_le` (2) are new.
- **B: harvest Aristotle Lemma 2** when job `03706c46` returns; port onto real defs.
- **C: Lemma 1** — build/locate Farey adjacency, combine with mathlib Dirichlet.
- **D: the limit argument** — independent of Lemmas 1/2; can be built against their statements.
