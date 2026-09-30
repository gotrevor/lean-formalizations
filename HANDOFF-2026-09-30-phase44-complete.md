# HANDOFF 2026-09-30 — phase 44 COMPLETE (Theorem D/E groundwork)

## Status

`src/LeanFormalizations/NumberTheory/Mills/TheoremDGround.lean` is **sorry-free**; all three
frozen statements are `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` only).
`lake build` green (8764 jobs); `scripts/fact-graph` regenerated (30 edges, 29 hypotheses).

No statement was false — `ROADMAP-PRIME-TOWERS.md` needed no counterexample entry.

## How the three lemmas closed

**Lemma 3 `not_stuck_twice`** (pure combinatorics). The insight: the two witnesses coincide.
`k = 1 + j n'` at `n` gives index `n + (1 + j n')·j n`; `k = j n` at `n' = n + j n` gives
`n' + j n · j n'`. Both equal `n + j n + j n·j n'`. So `ε` at that index differs from `ε n`
(n-side) and from `ε n'` (n'-side), while `k = 1` at `n` gives `ε n' ≠ ε n`. Three mutually
distinct-ish constraints in `Bool` — closed by `cases ... <;> simp`.

**Lemma 2 `dvd_trace_sub_of_orderOf_dvd`**. The `ZMod p` reduction is copied verbatim from
`SharedConjecture.exists_trace_pow_congr` (`htr`, `hdetD`). The hypothesis `hord` is universally
quantified over `GL` elements reducing to `C`, so the proof must *produce* one:
`(Matrix.isUnit_iff_isUnit_det D).2 hdetD` gives `u` with `↑u = D`, feeding `hord u hu`.
Then `orderOf_dvd_iff_pow_eq_one` ⟹ `u^(a−b) = 1` ⟹ `u^a = u^b` (via `a = b + (a−b)`) ⟹
`D^a = D^b` by `congrArg` on the coercion ⟹ traces agree mod `p`.

**Lemma 4 `exists_pow_sub_one_of_lt_padicValNat_glCard`**. Two new reusable helpers:
- `glCard_factor_eq : p^d − p^i = p^i * (p^(d−i) − 1)` (`2 ≤ p`, `i < d`). ℕ-subtraction:
  introduce `s` with `p^(d−i) = s+1`, then `rw [hs', hpow, hr, Nat.add_sub_cancel]`.
- `padicValNat_glCard_eq_sum : padicValNat c (glCard d p) = ∑ i : Fin d, (p^(d−i) − 1).factorization c`
  for primes `p ≠ c` — the `d`-fold generalisation of `FibonacciPrimePow.padicValNat_glCard_two`.
  Route: `Nat.factorization_def` → `Nat.factorization_prod` → `Finset.sum_apply'` → per-factor
  `factorization_mul` with `p.factorization c = 0`.

Pigeonhole: if every `v_c(p^(d−i) − 1) ≤ n/d` then the sum is `≤ (n/d)·d ≤ n`, contradicting
`hn`. So some `i` has `n/d < v_c(p^(d−i) − 1)`, and `Nat.Prime.pow_dvd_iff_le_factorization`
gives `c^(n/d) ∣ p^(d−i) − 1`.

### Gotchas worth remembering
- **`set F : Fin d → ℕ := ... with hF` breaks `Finset.sum`**: `set` folds the body into
  `Finset.univ.sum F`, which then no longer matches `∑ i, F i` for later `rw`/`omega`. Fix: don't
  `set`; write the expression out.
- **`omega` cannot commute a product.** `Nat.div_mul_le_self n d : n / d * d ≤ n` is stated with
  `(n/d)*d`; phrasing the sum bound as `d * (n/d)` left `omega` with two unrelated atoms.
  State the bound as `n / d * d` and add `mul_comm` to the `simp [Finset.card_univ]`.

## NEXT (for an altitude lap to schedule — DIRECTION.md still has phase 44 as CURRENT)

Phase 44 was groundwork only; the **Galois-rigidity step** of Theorem D is explicitly *not* in
this phase and is the next real wall (`PROOF-THEOREM-D.md`, beyond Lemmas 2–4). Theorem E's
Step 3 also now has its elementary prerequisites in place.
