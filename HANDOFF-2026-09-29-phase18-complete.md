# HANDOFF 2026-09-29 — phase 18 COMPLETE: Champernowne's constant is transcendental

`src/LeanFormalizations/NumberTheory/Transcendence/Champernowne.lean` is **sorry-free**; all four
frozen statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only):

* `champernowne_prefix` — `⌊C·10^11⌋ = 12345678910` (definition anchor)
* `irrational_champernowne` — **unconditional**
* `transcendental_champernowne (hR : Roth1955)`
* `transcendental_champernowne_of_stephan (h : Stephan2026Ridout)`

## What actually had to be invented

The header of the file carries the full route.  The three things that were not in the plant:

1. **Irrationality is a prerequisite, not a bonus.**  `Roth1955` is stated with an `Irrational α`
   hypothesis, so transcendence cannot be reached without it.  It was proved from the same block
   approximations: if `C = q` then `(q − p_m/q_m)·q.den·champDen m` is a *nonzero integer*, giving
   `|q − p_m/q_m| ≥ 1/(q.den·champDen m)`; instantiating `m = q.den` contradicts
   `|C − p_m/q_m| ≤ 2·10^{−N_{m+1}}` because `N_{m+1} − N_m ≈ 9m·10^m` dwarfs `log₁₀ champDen m`.

2. **Strictness comes from the leading-term gap, not from a sign argument.**  Both
   `C − p_m/q_m ≠ 0` (needed for irrationality) and injectivity of `m ↦ p_m/q_m` (needed to feed
   Roth an infinite set) follow from `gtail m ≥ 10^{−N_{m+1}}` versus
   `ctail ≤ (1/5)·10^{−N_{m+1}}`: the geometric continuation overshoots by a factor ~10 because
   its first dropped term is `10^{m+1}·T^{−(B+1)}` while `C`'s next term is `10^{m+1}/10^{N+m+2}`,
   one decimal place smaller.  So `C − p_m/q_m ∈ [−2·10^{−N_{m+1}}, −(4/5)·10^{−N_{m+1}}]`.
   No separate "distinctness" argument was needed: a repeated value forces `4/5 ≤ 1/5`.

3. **`prefixNum` beats denominator bookkeeping.**  Instead of proving that the partial sum's
   reduced denominator divides `10^N`, define the integer `123…K` recursively
   (`prefixNum (K+1) = prefixNum K · 10^{len(K+1)} + (K+1)`) and prove
   `cpartial K = prefixNum K / 10^{digitsUpTo K}` by a one-line induction.  Then `champApprox m`
   is literally `champNum m / champDen m` and `Rat.den_dvd` gives the denominator bound.

## Lean gotchas worth keeping

* `pow_add` rewrites the *first* `10^(m+1)` it sees — including one in a numerator.  Prepare the
  denominator as a separate `have ... := by rw [← pow_mul, ← pow_add, ← pow_add]` and `rw` that.
* `set X := …` after such a rewrite will not fold; `set` before, or rewrite with a prepared `have`.
* `Summable.sum_add_tsum_nat_add k h : ∑ i ∈ range k, f i + ∑' i, f (i+k) = ∑' i, f i` is the one
  workhorse for every split here; reindex with `tsum_congr fun i => by congr 1; omega`.
* `Rat.mul_den_eq_num q : q * q.den = q.num` (not `Rat.num_div_den` + `field_simp`).
* `Int.floor_eq_iff` takes no positivity side-goal in this mathlib.
* `decide` evaluates `digitsUpTo 10 = 11`, `prefixNum 10 = 12345678910` fine — no `native_decide`.

## Next

Per DIRECTION: continue through Waldschmidt 2023 statement by statement (theorems → `Literature/`,
conjectures → hypothesis `Prop`s, derived implications → proofs).  Normality of `C₁₀` is explicitly
**out of scope here** — it belongs in `normal-numbers`.
