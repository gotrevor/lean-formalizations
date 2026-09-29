# HANDOFF — phase 27 complete + phase 28 steps 1–5 (2026-09-29, lap end)

## State
`main` @ `a253d03`, `lake build` GREEN (8745 jobs), working tree clean.
Scoped target `sorry-free:src/LeanFormalizations/NumberTheory/Leopoldt/RankOne.lean` **met**
(0 sorries).  All remaining `sorry`s in `src/` are designated-open (CorvajaZannier,
CorvajaZannierStephan, DubickasNoSubspace) and were not touched.

## Phase 27 (the assigned scope) — DONE
`NumberTheory/Leopoldt/RankOne.lean` sorry-free; both frozen statements `#print axioms`-clean
(`propext, Classical.choice, Quot.sound`):
- `rank_cyclotomic_eight : Units.rank (CyclotomicField 8 ℚ) = 1`
- `leopoldt_cyclotomic_eight_seven : LeopoldtConjecture (CyclotomicField 8 ℚ) 7`

Both are corollaries of `leopoldt_of_rank_le_one : Units.rank K ≤ 1 → LeopoldtConjecture K p`,
for **every** number field and **every** prime — no abelian hypothesis, no `p` odd, no
unramifiedness, no `p`-adic logarithm, no `ℤ_p`-action.  The phase-26 plan was unnecessary.

## Phase 28 (the rank ≥ 2 wall) — steps 1–5, all in `Leopoldt/PrincipalUnits.lean`, all axiom-clean

1. `valuation_pow_char_sub_one` — the **exact** one-step formula
   `W (θ^p − 1) = max (W p · W x) (W x ^ p)` whenever those differ; `pow_char_ne_one_of_principal`
   (no `p`-torsion away from the tie `W p = W x ^ (p−1)`).  The tie is **sharp**: `θ = −1` in `ℚ₂`
   realises it and is genuine 2-torsion.
2. `valuation_pow_pow_char_sub_one` — in the **deep regime** `W x ^ (p−1) < W p` (the classical
   `log`/`exp` range `ν x > e/(p−1)`), which is *self-propagating*, the growth is exact for all `j`:
   `W (θ^(p^j) − 1) = W p ^ j · W (θ − 1)`.  `pow_pow_char_ne_one_of_deep`: `U^(m)` is torsion-free
   for `m > e/(p−1)`.  No unramifiedness needed after all.
3. `valuation_zpow_sub_one_le`, `..._of_dvd`, `valuation_zpow_sub_zpow_le` — the Cauchy estimate:
   `p^j ∣ k − l ⟹ W (θ^k − θ^l) ≤ W p ^ j · W (θ − 1)`, i.e. uniform continuity of `k ↦ θ^k`.
4. `valuation_prod_one_add_sub_one_lt`, `valuation_prod_one_add_sub_one` — **the leading term
   survives**: if `W (x i₀)` is strictly largest then `W (∏ (1 + xᵢ) − 1) = W (x i₀)` exactly.
5. `false_of_tendsto_one_of_valuation_ge` (topology endgame, factored out),
   `valuation_zpow_sub_one_eq` (**exact level formula** `W (θ^m − 1) = W p ^ j · W (θ − 1)` for
   `m = p^j t`, `p ∤ t`, with no dependence on `t`), and the headline of the phase:
   `false_of_unique_leading_level` — **arbitrary `r`**: split-form exponents with `p`-part fixed in
   `n`, all `θ i` deep principal and `≠ 1`, leading level uniquely maximised ⟹ `∏ θ i ^ (m n i) → 1`
   is impossible.

### The main conceptual result of the lap
**The rank-≥2 wall is a residue-field cancellation problem, not a missing construction.**  The
valuation-theoretic side of Leopoldt is now complete at every rank.  Exactly two gaps remain:

1. *(bookkeeping, tractable)* derive the split form from the real hypotheses — `a i ≠ 0` makes
   `v_p(m n i)` eventually constant (already done for `r = 1` inside
   `eq_zero_of_local_tendsto_one`), `a i = 0` makes it `→ ∞`.  Needs a `Fin r`-indexed
   "eventually" intersection plus a `PadicInt` valuation; then step 5 applies verbatim.
2. *(the wall)* the **tie** — several indices at the same leading level, whose residue-field
   leading coefficients may cancel, letting `ν` jump.  That is exactly a nonvanishing statement
   for a linear form in `p`-adic logarithms (Baker/Brumer) and must be imported as a `Literature/`
   statement.  **This supersedes the `padicLog`-first route written at the start of phase 28**: the
   logarithm was never the obstruction.

## Next lap (entry point)
Gap (1): state `leopoldt_of_unique_level` in terms of `a` — replace step 5's split-form hypothesis
by `∀ i, a i ≠ 0 → (unique leading level)`.  Then gap (2) as `Literature/Brumer.lean` with a
faithfulness argument, and rank-2 Leopoldt for ℚ(ζ₇) from it.  Full spec at the end of
`PENDING_WORK.md`.

## Gotchas carried (also in HANDOFF-2026-09-29-phase27-complete.md)
- `Valued.mem_nhds` / `isOpen_ball` speak in `MonoidWithZeroHom.ValueGroup₀`; bridge with
  `Valuation.embedding_restrict` + `ValueGroup₀.embedding_strictMono`.
- `valuedAdicCompletion_eq_valuation' v y` works with `exact`, **not** `rw`.
- `Ideal.Quotient.field` makes a `Ring`-instance diamond; use `IsDomain` + `sub_pow_char` instead.
- `CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero` has explicit `n`, `K` — TC
  resolution never finds it.
- `ofMul_prod` / `ofMul_zpow` are root-namespace, not `Additive.*`.
- ℤₘ₀ order lemmas that work: `mul_lt_of_lt_one_right`, `mul_lt_mul_of_pos_left/right`,
  `mul_le_mul_right'`, `pow_le_one'`, `zero_lt_iff`.  `ring` does **not** work there (not a ring);
  use `simp [pow_succ, mul_comm, mul_left_comm]`.
