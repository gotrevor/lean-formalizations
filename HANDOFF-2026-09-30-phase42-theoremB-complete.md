# HANDOFF 2026-09-30 — phase 42 (Theorem B) CLOSED

**Branch** `main` · HEAD `645c26e` (proof + docs), previous checkpoint `d93ebaa` (statements 1 and 3).
Stop sentinel written (`box done --green`); the treadmill will not relaunch. `lake build` green (8761 jobs). Target file
`src/LeanFormalizations/NumberTheory/Mills/TraceClassification.lean` is **sorry-free**; all three
frozen statements are `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`.
`scripts/fact-graph`: 30 edges, 29 hypotheses. Nothing in flight; no Aristotle job used.

## What landed

| declaration | content |
|---|---|
| `trace_pow_prime_congr` | `c^(n+1) ∣ tr C^(c^(n+1)) − V_c(tr C^(c^n), ε)`: exact CH composition + LTE on `det` |
| **`trace_prime_pow_add_not_prime`** | Theorem B: `tr C^(c^n) + h` composite i.o. for every `h`, outside `Φ₃`/`Φ₆` |
| **`trace_phi_survivor`** | the `Φ₃`/`Φ₆` classes converge: `c^(n+1) ∣ tr C^(c^n) − τ`, `τ = ±1` |

Helper lemmas (all public): `lucasU`, `pow_eq_lucasU_smul`, `dvd_lucasU_sub`, `dvd_lucasV_sub'`,
`dvd_lucasV_sub_q`, `pow_succ_dvd_pow_sub_pow`, `pow_pow_dvd_sub`, `lucasV_seven`,
`lucasV_one_one_period/_mod/_prime`, `lucasV_tau_one_prime`, `lucasU_five_six`,
`smulDvd_pow_six_sub_one`, `lucasV_neg'`, `abs_add_ge`, `dvd_two_mul_lucasV_sub_pow_q`,
`lucasV_prime_mod_q`, `lucasV_one_pos_lt`, `lucasV_one_strictMono`, `lucasV_one_growth`.

## Mathematical content — the two route corrections
See `PENDING_WORK.md` (top entry) for the full write-up. In brief:
1. **No derivative argument for the survivors.** `C^6 ≡ 1 (mod c)` (CH in `lucasU` coordinates,
   `U₆(±1,1)=0`, `U₅(±1,1)=−1`) + phase 41's matrix LTE gives `D^6 ≡ 1 (mod c^(n+1))`; then the
   trace of **`D^7`** (not `D^6`) yields `V₇(s,1) − s = (s−τ)·W` with `c ∤ W`, a *single* power
   of `(s−τ)`. Via `tr D^6 ≡ 2` one only gets `(s−τ)²`, i.e. half the exponent.
2. **No monotonicity for Theorem B.** `hgrow` + phase 33's iterated-return chain: a prime with a
   small `c`-part of `|GL₂(𝔽_p)|` recurs at the same absolute value forever, contradicting
   `|tr C^(c^n)| → ∞`.
3. **Frobenius generalized off `q = −1`.** `dvd_two_mul_lucasV_sub_pow_q` runs phase 35's
   binomial argument with `B = !![x,−q;1,0]`, `B' = !![0,q;−1,x]` (both trace `x`, det `q`,
   `BB' = qI`), giving `V_c(x,q) ≡ x (mod c)` for every `q`. That is what makes
   `tr C^(c^n) ≡ tr C (mod c)` available at general `det`.

## Exact next steps
1. `DIRECTION.md` still lists phase 42 as CURRENT — an **altitude lap owns** marking it DONE and
   picking the next target. This lap deliberately left it untouched.
2. **Roadmap §1 Theorem A** (order `d`, inert primes; Tribonacci at `c = 3, 5, 23`): the phase-41
   engine is `d`-generic and phase 42 supplies the `d = 2` certificate pattern; what is missing is
   the field trace of Frobenius in `AdjoinRoot χ_A` (orbit sum `Σ_{i<d} A^(c^(n+i))` scalar).
3. `c = 5` for the **Lucas** sequences (ramified, `c ∣ D`) remains untouched.
4. `ROADMAP-PRIME-TOWERS.md` §1 Theorem B now has a Lean-DONE note.
