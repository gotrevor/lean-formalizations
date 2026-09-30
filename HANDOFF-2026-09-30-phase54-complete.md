# HANDOFF 2026-09-30 — phase 54 COMPLETE

- **Branch:** `main` (clean; nothing pushed — host pushes)
- **HEAD at handoff:** `b701cc0` "Phase 54 handoff + FACT-GRAPH refresh"
- **Proof commit:** `1f22118` "Phase 54 COMPLETE: Theorem A for any d when h != 0; Tetranacci T4(2^n)+h composite for every h"
- **Build:** full `lake build` green (8775 jobs); pre-commit hook verified it.
- **Treadmill:** stop requested and signalled via `box done --green`; will not relaunch.

## What landed
`src/LeanFormalizations/NumberTheory/Mills/TheoremAEven.lean` is **sorry-free and axiom-clean**
(`propext, Classical.choice, Quot.sound` only); full `lake build` green.

1. **Theorem A′** — `entry_prime_pow_add_not_prime'`: phase 52's `Odd d` weakened to `Odd d ∨ h ≠ 0`.
   `TheoremA.lean` was refactored: the body now lives in the new public
   `TheoremA.entry_prime_pow_add_not_prime_gen` (extra hypothesis `hdh : Odd d ∨ h ≠ 0`), and the
   frozen phase-52 statement is a one-line wrapper `… (Or.inl hodd)`. **No frozen statement changed.**
   The parity hypothesis was load-bearing in exactly one spot: ruling out `h = 0` in the survivor
   count `Σ_(k<d) S k = d·h` with `S k ∈ {±1}`. For `h ≠ 0` the bound `|d·h| ≤ d` gives `h = ±1`
   directly, for any `d ≥ 1`.

2. **Tetranacci for EVERY `h`** — `tetra_two_pow_add_not_prime`. Two disjoint arguments:
   - `h ≠ 0` (`tetra_two_pow_add_not_prime_of_ne_zero`): Theorem A′ at `c = 2`, `d = 4`, `i = 3`,
     `j = 0`, `r = 2` (`T₄(2²) = T₄ 4 = 1` is odd), `hmu = Or.inl rfl`.
   - `h = 0` (`tetra_two_pow_not_prime`): no Theorem A needed. `TheoremA.entry_period` at `m = 0`,
     `q = a+1`, `d = 4` gives `2 ∣ T₄(2^(4q)) − T₄(2^0) = T₄(2^(4q)) − T₄ 1 = T₄(2^(4q))`, and
     `tetra_ge` gives `T₄(2^n) ≥ 13` there, so it is even and `> 2`.

## New reusable pieces (all in TheoremAEven.lean)
`tetraMat`, `tetraMat_pow_col/_pow_apply`, `tetraMat_charpoly` (`X⁴−X³−X²−X−1`),
`tetraMat_charpolyBar_two` (`= cyclotomic 5 (ZMod 2)`), `tetraMat_charpolyBar_two_irreducible`,
`tetra_bounds`, `tetra_ge`, `tetra_tendsto`.

## Gotchas worth carrying forward
- **Degree-4 irreducibility over `𝔽₂`** is NOT reachable by
  `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` (phase 52's trick). The clean route is
  `ZMod.irreducible_of_dvd_cyclotomic_of_natDegree`
  (`Mathlib/RingTheory/Polynomial/Cyclotomic/Factorization.lean`): identify the reduction with
  `cyclotomic n (ZMod p)`, then the whole content is `natDegree = orderOf (p : (ZMod n)ˣ)`.
- `orderOf` on `(ZMod 5)ˣ` is **not** `decide`-able (stuck instance). Use
  `orderOf_eq_prime_pow (p := 2) (n := 1)` with the two `decide`-able side goals
  `x^2 ≠ 1`, `x^4 = 1`.
- `Matrix.det_succ_row_zero` on a 4×4 leaves `Fin.succAbove` and `diagonal` applications; put
  `Matrix.diagonal, Fin.succAbove` in the simp set. Do **not** add `Fin.lt_def` — it loops.
- `−1 = 1` in `(ZMod 2)[X]` is best done with `CharTwo.sub_eq_add` (once per subtraction), not by
  a `C`-level rewrite.
- No `Matrix.det_fin_four` in mathlib; `det_succ_row_zero` + `det_fin_three` works.

## Verification done this lap
```
#print axioms LeanFormalizations.Mills.TheoremAEven.entry_prime_pow_add_not_prime'  -- propext, Classical.choice, Quot.sound
#print axioms LeanFormalizations.Mills.TheoremAEven.tetra_two_pow_add_not_prime     -- ditto
#print axioms LeanFormalizations.Mills.TheoremA.entry_prime_pow_add_not_prime       -- ditto (unchanged by the refactor)
#print axioms LeanFormalizations.Mills.TheoremA.trib_three_pow_add_not_prime        -- ditto (unchanged by the refactor)
```
`grep -c sorry TheoremAEven.lean` = 0.  `scripts/fact-graph` rerun: 30 edges, 31 hypotheses.

## Exact next steps (for whoever picks this up)
1. **Nothing is owed on phase 54.** Do not reopen `TheoremAEven.lean` or `TheoremA.lean`; both are
   proved and axiom-clean, and the phase-52/54 statements are frozen.
2. The next phase is an **altitude/operator call** — `DIRECTION.md` has no phase 55 directive yet, so
   a reflection lap must plant one before proof work resumes. Grep
   `src/LeanFormalizations/Maze.lean` first: it records closed routes and each row's `reopenIf`.
3. Natural continuations visible from here, if a directive is wanted:
   - **`c = 5` for Tetranacci is deliberately NOT claimed.** The charpoly is irreducible mod 5 too,
     but `μ₄ ⊂ ℤ₅` (since `4 ∣ 5 − 1`) breaks the `μ_(≤d) = {±1}` window hypothesis. Closing `c = 5`
     needs a genuinely wider window lemma, not a re-run of Theorem A.
   - **Pentanacci / general order `d`** is now nearly free for any `c` where the window holds: the
     only per-sequence work is the companion-matrix `pow_col` induction, the charpoly computation,
     the growth bound, and irreducibility — see the gotchas above, especially the cyclotomic route
     for degree `≥ 4`.
   - **Theorem C (prime-free intervals) for order 4** would mirror phase 53's covering certificate.
