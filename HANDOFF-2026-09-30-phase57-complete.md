# HANDOFF — phase 57 COMPLETE: Theorem D in full (some root a `c`-unit)

**Branch** `main` · **HEAD at handoff** `7ce4fb0` ("Phase 57 COMPLETE: Theorem D in full
(some root a c-unit), axiom-clean") · `lake build` **GREEN** (8778 jobs) · stop sentinel signalled
via `box done --green`.

**State:** the phase-57 target `src/LeanFormalizations/NumberTheory/Mills/TheoremDMixed.lean` is
sorry-free and its headline is `#print axioms`-clean.  Nothing is left open in this phase.

**Exact next steps for a fresh session** (do NOT reopen phase 57):
1. Read `DIRECTION.md` — phase 57 is met, so the top entry needs a new phase planted by an altitude
   lap.  Candidate successor named in the phase-56/57 headers: **Proposition D′** (the excluded class
   `f ≡ X^d (mod c)` is provably invisible to the method), which would close Theorem D's statement
   space completely; the other standing pointer is Saito's Remark 4.4 (degree-3 Pisot).
2. Before planting, `grep src/LeanFormalizations/Maze.lean` for routes already walked/closed.
3. Designated-open elsewhere, untouched by this phase and NOT to be attacked casually: the two
   active-crux `sorry`s in `NumberTheory/Transcendence/DubickasNoSubspace.lean`
   (`PENDING_WORK.md` §PHASE 9).

`src/LeanFormalizations/NumberTheory/Mills/TheoremDMixed.lean` is **sorry-free**, and the frozen
headline

```
floor_pow_prime_pow_add_not_prime_full
```

is `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  It says: for a monic
irreducible `f ∈ ℤ[X]` of degree `d ≥ 2` with a Pisot root `α > 1`, any prime `c` with
`f ≢ X^d (mod c)` and any shift `s` with `α^s > d + 1`,

```
⌊α^(c^n + s)⌋ is not prime for infinitely many n.
```

Phase 56 needed *every* root to be a `c`-unit (`c ∤ f(0)`); this needs only *some* root to be, which
is the paper's hypothesis and the method's full reach (the excluded class `f ≡ X^d (mod c)` is
provably invisible to the method — Proposition D′).

## The two ideas that made it work

### 1. `det (1 − T^Q) = 0` instead of `tr (T^Q) = m`

The header route asks for `tr(T^Q) ≡ m (mod c^k)` with `1 ≤ m ≤ d` the number of unit roots.  That
integer `m` costs a Hensel coprime factorization `f ≡ X^r·g (mod c^k)`, the CRT splitting of
`(ℤ/c^k)[X]/f`, and the *rank* of an idempotent over `ℤ/c^k` — none of which mathlib has, and the
rank needs "f.g. projective over a local ring is free".

All the size argument actually consumes downstream is *some* `u_k ≠ 0`.  Over `ℂ` that is
`∏_k (1 − u_k^Q) = det (1 − T^Q) = 0` — **a single integer polynomial equation**, so the
Nullstellensatz transfer swallows it unchanged.  And modulo `c^(n+1)` it is free:

* `T^(Q+1) = T` makes `E := T^Q` idempotent (`pow_idem_of_pow_succ`);
* `ZMod (c^(n+1))` has no nontrivial idempotents (`zmod_idem_eq_zero_or_one`, by
  `Prime.pow_dvd_of_dvd_mul_right` on `z(z−1)`), so `det(1 − E)` — itself idempotent — is `0` or `1`,
  and `1` would make `1 − E` invertible, forcing `E = 0` (`det_one_sub_eq_zero_of_idem`);
* `E ≠ 0` is already visible **mod `c`**.

No `m`, no rank, no Hensel lift.

### 2. The limit matrix from eventual periodicity in a finite monoid

`C mod c` is singular, so phase 56's `C^(Q c^n) ≡ I (mod c^(n+1))` has no analogue.  What survives
is that `Mat_d(𝔽_c)` is a *finite monoid*: `∃ a, Q ≥ 1, D^(a+Q) = D^a` (`exists_period`), hence
`D^(N+uQ) = D^N` for every `N ≥ a`.  Since `c^ν ≥ a` for `ν ≥ a`, taking `N := c^ν`, `u := c^ν`
gives the base congruence **at a pure prime-power exponent**

```
D^(c^ν (Q+1)) = D^(c^ν)   in Mat_d(𝔽_c),
```

which matters because the frozen statement is about `⌊α^(c^n+s)⌋`, so the exponent may not carry a
stray factor `L`.  Phase 47's `TeichmullerCongruence.pow_congr_lift` then buys the **level**, not
the exponent: `exists_mixed_limit` delivers, for every `ν ≥ n₀`, both congruences modulo
`c^(ν−n₀+1)`.  `D^(aQ) ≠ 0` is the *only* use of `f ≢ X^d (mod c)`, through the nilpotency criterion
`map_eq_X_pow_of_compM_pow_eq_zero`: a vanishing power of the companion matrix gives
`f mod c ∣ X^M` (via `modByMonic` + Cayley–Hamilton + the cyclic vector `e₀`), hence `= X^d` by
`dvd_prime_pow Polynomial.prime_X` + `eq_of_monic_of_associated`.

## Map of the file

| step | lemma | content |
|---|---|---|
| 0 | `exists_period`, `pow_add_period`, `pow_mul_period` | eventual periodicity in a finite monoid |
| 0b | `aeval_compM_self`, `dvd_of_aeval_compM_eq_zero`, `map_eq_X_pow_of_compM_pow_eq_zero` | the nilpotency criterion |
| — | `map_matrix_pow/sub/one/mul`, `trace_map_eq`, `polyVal_map`, `eval_map_int_hom` | ring-hom plumbing |
| 1 | `zmod_idem_eq_zero_or_one`, `det_one_sub_eq_zero_of_idem`, `pow_c_pow_congr`, `pow_idem_of_pow_succ` | the determinant trick |
| 1 | **`exists_mixed_limit`** | `T^(Q+1) ≡ T`, `det(1−T^Q) ≡ 0` mod `c^(ν−n₀+1)` |
| 2 | `exists_zero_of_family`, `exists_root_enum_field` | phase 56's Nullstellensatz + root enum, over any alg. closed char-0 field |
| 2b | `right_cancel_of_isUnit_det`, `polyVal_pow_succ_eq`, `exists_polyVal_pow_eq_one` | the two mixed Vandermonde payoffs |
| 2c | `AlgQ`, **`exists_spectral_solution_mixed`** | the `d²+3` system, solved in the algebraic numbers |
| 3 | `transport_solution`, `exists_algEquiv_of_roots` | integer system is ring-hom stable; Galois conjugation |
| 3–4 | **`exists_complex_solution_nonzero_at_root`** | move a nonzero spectral value onto `α` |
| 4 | `norm_le_one_of_pow_succ_eq`, **`not_exists_spectral_mixed`** | `α^s ≤ d + 1` |
| — | **`floor_pow_prime_pow_add_not_prime_full`** | the headline |

## Why the solution must live in `AlgQ`, not `ℂ`

Step 3 conjugates the solution by a field automorphism, and `Aut(ℂ/ℚ)` is not constructible in
mathlib (it needs Steinitz over a transcendence basis).  But `T^(Q+1) = T` forces every spectral
value into `{0} ∪ μ_Q`, so the whole solution is algebraic anyway.  Running the Nullstellensatz over
`AlgQ := algebraicClosure ℚ ℂ` (it is algebraically closed and of characteristic zero, which is all
the proof used about `ℂ`) puts the solution where `minpoly.exists_algEquiv_of_root` on
`Normal ℚ AlgQ` applies.  `transport_solution` then carries it along `τ` and along `AlgQ ↪ ℂ`,
because the system has **integer** coefficients.

Two smaller adaptations: `c ∤ f(0)` is gone, so `f.coeff 0 ≠ 0` (still needed for `det C ≠ 0` in the
stuck-alternation filter) comes from irreducibility — `X ∣ f` would make `f` degree 1.  And the size
argument now needs only `‖u_k‖ ≤ 1` for all `k` (from `u^(Q+1) = u`) plus `‖u_(i₀)‖ = 1` at `α`,
which is exactly what step 3 supplies.

## Next

`DIRECTION.md` phase 57 is met.  Untouched designated-open work elsewhere: the two active-crux
`sorry`s in `NumberTheory/Transcendence/DubickasNoSubspace.lean` (`PENDING_WORK.md` §PHASE 9) — not
part of this phase, deliberately not attacked.
