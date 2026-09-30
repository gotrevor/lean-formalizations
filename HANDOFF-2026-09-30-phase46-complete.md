# HANDOFF — phase 46 complete (2026-09-30)

branch `main`, HEAD `70011bd` (proof commit `df603cc`)

## What landed

`src/LeanFormalizations/NumberTheory/Mills/ShiftedWindow.lean` is **sorry-free** and its
frozen statement `window_of_eventually_prime` is **axiom-clean**
(`[propext, Classical.choice, Quot.sound]`).

For a `3x3` integer matrix `C` with `det C != 0`: if `|tr C^(3^n-2)| -> infinity` and
`tr C^(3^n-2)` is prime for all large `n`, then eventually
`3^(n/3-1) | tr C^(3^n-2) - 1` or `3^(n/3-1) | tr C^(3^n-2) + 1`.

That is Step 3 of `PROOF-THEOREM-E.md` — the first sub-node of the open
`ShiftedTraceRigidity` node that phase 45's Theorem E rests on.

`scripts/fact-graph` regenerated: 30 edges, 31 hypotheses.

## The one real mathematical improvement over the header route

The header's route handles the `i = 3` branch conditionally ("`p^2+p+1 === 3 (mod 9)` when
`p === 1 (mod 3)`, and `p === 2 (mod 3)` is impossible"). That case split is unnecessary:
**`y^2 + y + 1 = 0` has no solution in `ZMod 9` at all** (`decide`), so

    v_3(p^2 + p + 1) <= 1   for EVERY p,

with no congruence hypothesis. `factorization_three_sq_add_self_add_one_le` states it.
This is exactly the source of the `-1` in the exponent `n/3 - 1`: `3^e | (p-1)(p^2+p+1)`
plus that bound gives `e - 1 <= v_3(p-1)`. The `3 ∤ p` hypothesis was dropped from
`dvd_sub_or_add_of_dvd_pow_sub_one` accordingly (it is still needed upstream, but only to
supply `p != 3` to the `GL_d` window lemma).

## New public lemmas (reusable downstream)

* `sub_two_sub_two (B s) (2 <= B) : B*(s+1) - 2 - (B - 2) = B*s`
  — the shifted-exponent difference `(3^(n+kj) - 2) - (3^n - 2) = 3^n (3^(kj) - 1)` in Nat.
* `nine_not_dvd_sq_add_self_add_one`, `factorization_three_sq_add_self_add_one_le` — above.
* `dvd_sub_or_add_of_dvd_pow_sub_one` — `3^e | p^i - 1`, `1 <= i <= 3`, `2 <= p`
  ⟹ `p === +/-1 (mod 3^(e-1))`. i=1 direct; i=2 by coprimality (3 cannot divide both
  `p-1` and `p+1`, they differ by 2); i=3 by the valuation bound.
* `exists_period_orderOf_dvd d hc hv` — **the piece to reuse.** Given
  `padicValNat c (glCard d p) <= m`, produces `j >= 1` with
  `orderOf u | c^m (c^(kj) - 1)` for every `u : GL (Fin d) (ZMod p)` and every `k`.
  This is an `orderOf`-level restatement of `FibonacciCovering.exists_entry_pow_congr_mul`.
  **Why it was needed:** the entrywise lemma is stated only for bare exponents `c^n` and
  does NOT transfer to the shifted tower `c^n - 2`. At `orderOf` level it composes directly
  with `TheoremDGround.dvd_trace_sub_of_orderOf_dvd`, which takes arbitrary `a`, `b`.

## Gotchas hit (for the reference corpus)

* `ZMod.natCast_zmod_eq_zero_iff_dvd` is gone; current name is `ZMod.natCast_eq_zero_iff`.
* `p^2 - 1 = (p-1)*(p+1)` in Nat: do NOT try `ring_nf`/`omega` on truncated subtraction.
  Pattern that works: `obtain <s, hs> := Nat.exists_eq_add_of_le hp2`, then
  `have h1 : p - 1 = s + 1 := by omega`, then `e1 : (p-1)*(p+1) + 1 = p^2 := by rw [h1, hs]; ring`,
  then `Nat.sub_eq_of_eq_add e1.symm`. Same shape for the cube.
* `n >= 1` is genuinely load-bearing in the exponent identity: at `n = 0`, `3^0 - 2 = 0` in
  Nat, not `-1`, and the identity is false. Harmless under `atTop`.

## Next (the actual crux, NOT this phase)

`ShiftedTraceRigidity` Steps 4-6 of `PROOF-THEOREM-E.md` — the Galois-rigidity step. That is
where the remaining uncertainty on Theorem E sits; phase 46 only supplied its 3-adic window.
Phase 44's `not_stuck_twice` (Lemma 3) is the combinatorial companion already in hand.
`DIRECTION.md` is owned by altitude laps — let one plant phase 47.
