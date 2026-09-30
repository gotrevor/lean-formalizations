# HANDOFF 2026-09-30 — phase 38 COMPLETE (LucasUnitAllPrimes sorry-free, axiom-clean)

**Branch** `main` · HEAD `c4628d5` (this doc's commit follows). Nothing in flight; no Aristotle
job was needed — the whole phase went through locally.

`src/LeanFormalizations/NumberTheory/Mills/LucasUnitAllPrimes.lean` is sorry-free; all four
frozen statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):
`lucasU_odd_mul`, `lucasOddPoly_far`, `not_dvd_lucasU_prime_pow`,
`lucasU_unit_prime_pow_add_not_prime`.  `lake build` green; `scripts/fact-graph` rerun
(30 edges, 29 hypotheses — unchanged, the phase adds no hypothesis).

**Result.** For every `P` with `D = P² − 4Q ≥ 5`, every `Q = ±1`, every odd prime `c ∤ D`, and
every integer `h`: `U_(c^n)(P,Q) + h` fails to be prime for infinitely many `n` (given
`|U(c^n)| → ∞`, which is a frozen hypothesis).  Split and inert `c` alike.

**The three ideas.** (full write-up: `SWEEP-PRIME-MODULUS.md` § Phase 38)
1. Phase 37's obstruction — `det(A^N) = −Q^N` brings a second variable into the doubling
   coefficient — **dissolves for `Q = ±1` at odd `N`**, where `Q^N = Q` is a constant.  So
   Cayley–Hamilton gives `A² = L·A − Q·I`, `A⁴ = T·A² − I` with `T = D U_N² + 2Q`, and
   `U((2j+1)N) = Φ_j(U_N)` exactly as in phase 37.
2. `lucasOddPoly_far`'s abstract exception (`D = 6, ε = −1`, where `Φ_1(±1) = ±3`) is
   **unreachable**, because `ε = −1` forces `D = P² + 4` and `P² = 2` has no integer solution.
3. `c ∤ U(c^n)` is cheapest as a Legendre split, and gives the stronger `U(c^n) ≡ ±1 (mod c)`:
   non-square `D` is phase 36 verbatim; square `D = d²` is twenty lines — build `α = (P+d)/2`
   and `β = P − α` in `ZMod c`, use `z^(c^n) = z` (iterated `ZMod.pow_card`) and subtract
   phase 36's `pow_eq_lucasU` at the two roots.

The endgame needed two adaptations over phase 37 (`U` is negative and non-monotone): the filter
output is taken at `p = |t n|` and pushed through `dvd_neg` (the residue pair `{1−h, −1−h}` is
closed under that flip), and monotonicity is replaced by phase 33's **iterated return**.

## Reusable declarations added
`lucasU_zero`, `lucasU_one`, `lucasA_pow_apply_zero_one`, `lucasA_pow_succ_apply_one_one`,
`lucasA_pow_trace_sq` (`V_N² = D U_N² + 4Q^N`), `lucasOddAux`, `lucasOddPoly_eq_mul`,
`lucasOddPoly_neg`, `lucasOddAux_growth`, `lucasOddAux_mono`, `lucasOddPoly_far_pos`,
`not_dvd_of_unit`, `two_ne_zero_zmod`, `lucasU_prime_pow_split_eq_one`,
`exists_lucasU_prime_pow_congr`, `dvd_lucasOddPoly_sub`, `abs_eq_of_prime_dvd_prime`.

`lucasU_prime_pow_split_eq_one` and `lucasA_pow_trace_sq` are the two that a later phase will
want: the first is the split-prime Frobenius input for any `(P,Q)` with `c ∤ D` (it does **not**
use `Q = ±1`), the second is the `V² − D U² = 4Q^N` identity in matrix form.

## Exact next steps (for a fresh session)
1. `lake build` is green at HEAD; the only `sorry`s left in `src/` are designated-open audit
   surface from earlier phases, untouched by this lap.
2. **An altitude lap must re-own `DIRECTION.md`** — this lap did not edit it, so it still lists
   phase 38 as CURRENT.  Mark phase 38 DONE and pick the next target.
3. Natural phase 39 candidates, in increasing order of difficulty:
   - **`|Q| ≥ 2` at split `c`.**  The wall is real and now isolated: at odd `N`,
     `det(A^N) = Q^N` is a genuine second variable, so the composition identity becomes
     `U((2j+1)N) = Φ_j(U_N, Q^N)` — a two-variable polynomial.  The endgame needs `Q^(c^n)` to
     also be eventually constant modulo `c^(n/2)`, which is a second application of the same
     filter, so the attack is: prove the two-variable composition identity first (it is the same
     Cayley–Hamilton computation with `T = D U_N² + 2Q^N`), then decide whether the pair
     `(x_n, Q^(c^n) mod c^(n/2))` is eventually periodic.
   - **`c = 2` for `Q = ±1`**: phase 33 covers `P, Q` both odd; `P` even with `Q = ±1` is open.
   - **`c ∣ D`** (ramified), where `U(c^n) ≡ 0 (mod c)` genuinely happens, so step 3 fails and
     the whole route needs a different obstruction.
