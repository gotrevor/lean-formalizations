# HANDOFF 2026-09-27 — Mills phase 3 COMPLETE: unconditional lower bound

## State
Branch `mills`. `lake build` fully green. **`src/LeanFormalizations/NumberTheory/Mills/` is
sorry-free** (all seven files). Phase 3's stop condition is met.

## What landed this lap
`lower_bound_of_isMills` in `Mills/LowerBound.lean` — **every** Mills number `A > 1` satisfies
`1.3063778838 < A`, with **no added hypothesis** — plus `lower_bound` (the `IsMinMills` corollary).
Both `#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`.

## The insight
The planned four-way case split along the greedy chain (`p1 = 2` vs `>= 3`, `p2 = 11` vs `>= 13`,
...) was unnecessary. `gseq_le_digits` (RH.lean) already does that work uniformly and it is
**already unconditional**: it proves `gseq k <= floor (A ^ 3^(k+1))` for any Mills `A` using only
`lpa_le` (Euclid: a prime exists above any `n`) and the self-generated chain bound
`c^3 < floor (A ^ 3^(k+2))` derived from primality of the digits. `PrimeBetweenCubesFrom` enters
`RH.lean` solely via `gseq_hi`, i.e. solely for the **upper** bound. So the proof is four lines:
instantiate at `k = 3` (`gseq_three : gseq 3 = 2521008887`) to get `A^81 >= 2521008887`, then
`norm_num` on `(1.3063778838)^81 < 2521008887`.

Lesson worth keeping: before decomposing a stated case-split plan, check whether an existing
lemma's *hypothesis usage* is narrower than its statement suggests.

## Next
Mills lane is done (Wright, conditional Mills, least Mills, RH digits, Saito irrationality,
unconditional lower bound). Nothing open in `Mills/`. The remaining genuine debt in the lane's
dependencies is the frozen `Literature/Primes.lean` `Prop`s (BakerHarmanPintz2001, Matomaki2007,
Mahler1957, Schoenfeld1976) — published theorems, deliberately hypotheses, not this lane's targets.
