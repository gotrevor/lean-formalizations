# HANDOFF 2026-09-27 — Dubickas 2022 phase 7 COMPLETE (Theorem 1 + Theorem 2 monic-quadratic case)

## Status: `src/LeanFormalizations/NumberTheory/Transcendence/` is SORRY-FREE and AXIOM-CLEAN

```
transcendental_growth_of_monic_quadratic : [propext, Classical.choice, Quot.sound]
theorem1                                 : [propext, Classical.choice, Quot.sound]
oeis_constants                            : [propext, Classical.choice, Quot.sound]
```

All three frozen phase-7 names are proved.  The only hypotheses are the two frozen literature
inputs `Dubickas2022` (his Lemma 6, Corvaja–Zannier) and `Dubickas2022PisotGap` (his Lemma 8,
Smyth/Mignotte/Baker), exactly as `DIRECTION.md` specified.  Nothing in `Literature/` was edited.

## The structural insight that made this a one-lap job

DIRECTION flagged formula (6) as "the likely long pole".  It *is* the analytic core, but the
decisive discovery is upstream of it: **for `d = 2`, `a₀ = 1` Dubickas's substitution (4) makes
the recursion EXACT.**  With `y n = x n + a₁/2`,

    y (n+1) = y n ^ 2 - c,      c = (a₁² − 2a₁ − 4a₂)/4     — no `O(y^(d−2))` error term at all.

Consequences, all of which shrank the route:

* **Lemma 10 is not needed.** Dubickas needs "two polynomials agreeing at infinitely many `x_n`
  coincide" only because his `y_{n+1} = Q(y_n)` is derived on a tail.  Here the single constant `c`
  is fixed from the start, so once a tail forces `y_{n+1} = y_n²` (resp. `y_n² − 2`) we read off
  `c = 0` (resp. `c = 2`) directly.
* **Lemma 7 (Chebyshev) is not needed.** Its only role was to produce `z_{n+1} = z_n² − 2` from
  `z_n = α₁^(dⁿ) + α₂^(dⁿ)`.  Replaced by a squaring identity (below).
* **Conditions (17)/(18) are literally `c ∈ {0, 2}`** — `4c = a₁² − 2a₁ − 4a₂` — so no
  case-by-case (15)/(16) polynomial identity work.

## Files

### `Transcendence/DubickasGrowth.lean` (new) — formula (6)
* `abs_log_le_two_mul` — `|log u| ≤ 2|u−1|` for `u ≥ 1/2`.
* `exists_growth_const` — **Dubickas (6)**: for `y_{n+1} = y_n² − c` with `y_n → ∞`, there is
  `α > 1`, `C > 0`, `n₀` with `|y_n − α^(2ⁿ)| ≤ C/α^(2ⁿ)` for `n ≥ n₀`.
  Proof: `a_n := 2^(−n) log y_n` has `a_{n+1} − a_n = 2^(−n−1) log(1 − c/y_n²)`, dominated by
  `2|c|/(2^(n+1) y_n²)`; `cauchySeq_of_dist_le_of_summable` +
  `dist_le_tsum_of_dist_le_of_tendsto` give the limit AND the tail bound `2|c| 2^(−n) y_n^(−2)`,
  which is exactly the `y_n^(−2)` strength needed to exponentiate into `O(α^(−2ⁿ))`
  (a merely geometric tail bound would NOT suffice — it must carry `y_n^(−2)`).
* `tendsto_pow_two_pow_atTop`, `tendsto_rpow_growth` — `z_n^(2^(−n)) → α` for any `z` within a
  *bounded* distance of `α^(2ⁿ)`; applies to `y_n` and to `x_n = y_n − a₁/2` alike.

### `Transcendence/DubickasPisot.lean` (new) — Lemma 9 and §5
* `exists_pisot_pow` — Lemma 9 step 1.  `2 y_n = 2 x_n + a₁ ∈ ℤ` plus the (6) rate gives
  `‖2 α^(2^k)‖ ≤ 2C α^(−2^k)`, which beats `e^(−ε 2^k)` at `ε = (log α)/2`; that refutes the
  second alternative of `Dubickas2022` (`q = 2`, `s_k = 2^k`), so `β := α^(2^m)` is Pisot.
* `c_eq_zero_or_two` — steps 2–4.  The three moves:
  1. `y_{m+j} = trace(β^(2^j))` **exactly** for large `j` (`pisot_conjPowSum_add_mem_int` makes
     the trace an integer, `norm_conjPowSum_le` makes the non-`β` part `o(1)`, and both doubled
     are integers within distance `< 1`).
  2. **The squaring identity** (replaces Lemmas 7 and 10): with `S_N = Σ_{j≥2} β_jᴺ`,
     `T_N² = T_{2N} + 2β^N S_N + (S_N² − S_{2N})`, and `T_{2N} = T_N² − c`, so
     `c = 2 β^N S_N + S_N² − S_{2N}` for `N = 2^j`.  The last two terms are `O(|β₂|^(2N))` hence
     bounded, so `‖S_N‖ ≤ K β^(−N)` — precisely the decay hypothesis of the phase-6 lemma
     `Mills.pisot_degree_bound` **at `μ = 1`**, giving `card (otherConj β) · 1 ≤ 1`.
  3. `deg β = 1` ⟹ `S_N = 0` ⟹ `c = 0`.  `deg β = 2` ⟹ `S_N = γᴺ` ⟹ `c = 2(βγ)^N` for both
     `N` and `2N`, so `c/2 = (c/2)²` and `c ∈ {0, 2}`.  (Note step 3 never needs the unit
     property `ββ₂ = ±1` — the self-consistency of `c` across `N ↦ 2N` does that work.)

### `Transcendence/Dubickas.lean` (frozen statements, now proved)
* `transcendental_growth_of_monic_quadratic` — assembles the above.
* `tendsto_of_quadratic` + `*_rec` / `*_tendsto` for the five sequences (`b = 1` for κ, η, τ;
  `b = 2` for ζ and Sylvester — `1 ≤ t² − 1` fails at `t = 1`, which is why `b` is a parameter).
* `theorem1` — the five `a₁² − 2a₁ − 4a₂` values are `−4, 4, −1, −5, −4`: `by decide` each.
* `halfGrowth_of_growth`, `oeis_constants` — `√α` via `Real.continuousAt_rpow_const`, and
  `IsAlgebraic.pow 2` transfers algebraicity back up.

## Reuse note (for the next lap)

Phase 6's `NumberTheory/Mills/SaitoPisot.lean` carried the whole conjugate-multiset toolkit
(`otherConj`, `conjPowSum`, `conjMax`, `pisot_conjPowSum_add_mem_int`, `pisot_one_le_prod_norm`,
`card_otherConj_add_one`, `conjMax_lt_one`, `norm_conjPowSum_le`, `pisot_degree_bound`).  Phase 7
imported it unchanged; `pisot_degree_bound` was stated generally enough in `μ` that `μ = 1` fell
out for free.  That generality paid for itself — worth keeping as a habit.

## Next (not phase 7)

`DIRECTION.md` has no phase 8.  Open elsewhere in the repo (all designated-open, untouched this
lap): `Mills/SaitoDigits.lean:114` `saito_lemma36C`, `Mills/Transcendental.lean:79`
`transcendental_or_pisot`, the Catalan `SmallForms` frontier, and the no-three-in-line all-`N`
`(3/2−ε)N` corollary needing PNT-grade primes near `N/2`.
