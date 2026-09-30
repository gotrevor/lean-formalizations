# Phase 52 COMPLETE — Theorem A, and Tribonacci `T(3^n)+h` / `T(5^n)+h`

`src/LeanFormalizations/NumberTheory/Mills/TheoremA.lean` is **sorry-free**; all three frozen
statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only).

## What is proved

`entry_prime_pow_add_not_prime` — **Theorem A.**  `A ∈ M_d(ℤ)`, `χ_A` irreducible mod the prime
`c`, `d` odd, `μ_(≤d)(ℤ_c) = {±1}`, `u(N) = (A^N)_(ij)` with `i ≠ j`, `|u(c^n)| → ∞`, and
`c ∤ u(c^r)` for some `r < d`.  Then for **every** `h ∈ ℤ`, `u(c^n) + h` is composite i.o.

`trib_three_pow_add_not_prime`, `trib_five_pow_add_not_prime` — the Tribonacci corollaries.

## How the survivor argument runs at order `d`

Assume `t_n := u(c^n) + h` is prime for all large `n`.

1. **Return step.**  Phase 32's `exists_entry_pow_congr` at the prime `t_n` gives a later index
   with `t_(n+q) ≡ t_n`, hence `|t_(n+q)| = |t_n|`; its hypothesis survives the step, so iterate
   (the phase-33 *iterated-return* trick) against `|u| → ∞`.  Conclusion:
   `n < v_c(|GL_d(𝔽_(t_n))|)`.  Needs `c ∤ det A`, which is `not_dvd_det_of_irreducible`
   (else `X ∣ χ̄_A`, impossible for `d ≥ 2` — and `i ≠ j` already forces `d ≥ 2`).
2. **Window** (`exists_sign_dvd_sub`, the genuinely new piece).  Phase 44 Lemma 4 gives
   `1 ≤ i ≤ d` with `c^(n/d) ∣ t_n^i − 1`; the window turns that into `t_n ≡ ±1 (mod c^(n/d − d))`.
   Split `i = c^a · i₀`, `c ∤ i₀`.  The coprime part descends for free
   (`dvd_sub_one_of_coprime_exp`: the geometric factor is `≡ i₀`, a unit).  For odd `c` the order
   of `p^(c^a)` in `𝔽_c` divides both `i₀ ≤ d` and `c − 1`, so `μ` pins it to `{1,2}`; the `−1`
   branch is absorbed by replacing `p` with `−p`, and the `c`-part descends by mathlib's LTE
   (`dvd_sub_one_of_pow_pow_odd`).  For `c = 2` the analogue is `two_pow_descend`: the squaring
   descent loses a sign each step, but every intermediate `z^(2^a)` is an **odd square**, hence
   `≡ 1 (mod 8)`, which kills the `+1` branch until the very last step.  Cost `a ≤ d`.
3. **Orbit sum.**  Phase 51 gives `c^(n+1) ∣ Σ_(k<d) u(c^(n+k))`, so mod `c^min(E, n+1)` we get
   `Σ_(k<d) ε_k ≡ d·h` with `ε_k ∈ {±1}` — and for `n` large both sides are bounded by `d|h| + d`
   below the modulus, so `Σ ε_k = d·h` **exactly**.  `d` odd makes `Σ ε_k` odd, killing `h = 0`;
   `|Σ ε_k| ≤ d` then forces `h = ±1` and (by `Finset.sum_eq_zero_iff_of_nonneg` applied to
   `1 − h·ε_k ≥ 0`) every `ε_k = h`.
4. **Period.**  Hence `c ∣ u(c^n)`.  Choosing `n = r + Q·d` from the start and using phase 51's
   period (`entry_period`) carries this to `c ∣ u(c^r)` — contradiction.

Note step 4 only ever needs `k = 0`, so the residue bookkeeping is done by *choosing* `n ≡ r`,
not by covering the window `[n, n+d)`.

## Tribonacci

`tribMat = !![1,1,1;1,0,0;0,1,0]`, `(tribMat^N) 2 0 = trib N`, `charpoly = X³ − X² − X − 1`
(computed via `Matrix.det_fin_three` on the charmatrix), irreducible mod 3 and mod 5 by
`irreducible_of_degree_le_three_of_not_isRoot` + `decide +revert` on the roots.  `hmu` holds since
neither `2` nor `4` has a divisor in `[3,3]`; `r = 1` works because `T(3) = 1` and `T(5) = 4`.
Growth: `trib_ge : (n:ℤ) + 2 ≤ trib (n+4)`.

## Reusable gotchas from this lap

- `decide` under a local `haveI : Fact _` instance fails with "expected type must not contain free
  variables" — use `decide +revert`.
- `(ZMod c)[X]` in a type ascription parses `[X]` as list indexing; write `Polynomial (ZMod c)`.
- `simp only [tribMat, …]` unfolds the matrix *inside* `tribMat ^ N` too; rewrite the induction
  hypotheses **first**, then unfold.
- ℕ∞ cancellation: `WithTop.add_le_add_iff_right (h : a ≠ ⊤)`.

## Next

`DIRECTION.md` has no phase 53 planted yet.  Open frontier in the Mills stack: the
`ShiftedTraceRigidity` node (phases 45–48 chipped at sub-nodes R1/R4) is the remaining
our-own-math obligation behind Theorem E.
