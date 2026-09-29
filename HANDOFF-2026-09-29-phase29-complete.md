# Handoff: phase 29 COMPLETE — the 3-adic obstruction to an algebraic Mills constant

**Date**: 2026-09-29 · **Branch**: `main`

## Result

`src/LeanFormalizations/NumberTheory/Mills/ThreeAdic.lean` is **sorry-free**, and all five frozen
statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only):

- `dvd_trace_pow_three_of_glCard`
- `lt_padicValNat_glCard`
- `threeAdic_pm_one`
- `mills_threeAdic`
- `transcendental_of_not_pm_one`

No frozen statement turned out to be false; `Literature/` was not touched.

## What the lap actually established

The new math of `PROBE-MILLS-3ADIC.md` is now machine-checked in full. For any integer matrix `C`
with `det C ≠ 0` whose trace sequence `t_k = tr C^(3^k)` is eventually prime and strictly
increasing, `t_k → ±1` in `ℤ₃`. Specialised to Saito's Pisot branch, an algebraic Mills constant
forces the Mills primes to converge to `±1` 3-adically.

## The three route decisions worth carrying forward

**1. LTE without the three-case split.** The needed bound is
`padicValNat_pow_sub_one_le : v₃(tˢ − 1) ≤ v₃(t² − 1) + v₃(s)` for `3 ∤ t`. The clean route is to
first pass from `s` to `2s` — free, since `tˢ − 1 ∣ t²ˢ − 1` — because the base then becomes
`u = t²  ≡ 1 (mod 3)` unconditionally. That collapses the usual `t ≡ 1` / `t ≡ 2`, `s` even/odd
case analysis into one case, plus the cube step `v₃(z³ − 1) ≤ v₃(z − 1) + 1`, which is a `mod 9`
`decide` on `z² + z + 1`. Do not try the textbook LTE statement directly; it is strictly more work
and mathlib's `padicValNat.pow_sub_pow` does not cover the `p ≡ −1` branch usefully here.

**2. Trace of a matrix power = root power sum, without charpoly machinery.** mathlib has
`Matrix.trace_eq_sum_roots_charpoly` but nothing about the charpoly of a *power*, and
diagonalisation is not worth it. Instead: the explicit companion matrix `companion3 a b c`, its
Cayley–Hamilton identity proved by `fin_cases`+`ring` on 9 entries, and then
`companion3_trace_pow` by strong induction on the resulting 3-term linear recurrence, with
`N = 0,1,2` matched against Vieta by `linear_combination`. Both sequences satisfy the same
recurrence and the same three initial values, so they coincide. This is far cheaper than any
eigenvalue route and generalises to any degree with the same shape.

**3. Where the two halves meet.** Step 2 gives `v₃|GL_n(𝔽_{t_k})| > k` (unbounded in `k`);
`padicValNat_glCard_le` gives `v₃|GL_n(𝔽_t)| ≤ n(2e+n)` (a constant) whenever `3^e` divides
neither `t − 1` nor `t + 1`. Gauss congruence makes the residue `t_k mod 3^e` eventually constant,
so one witness index `k₁ > n(2e+n)` suffices to force that residue to be `±1`.

## State

Verified from real output this session: `lake build` green (8747 jobs), `grep -c sorry` on the
target file = 0, all five `#print axioms` clean. Commits this lap, in order: `44fdc05` (step 1),
`d5b5f35` (step 2), `36e7090` (LTE infrastructure), `f0ba432` (glCard bound), `2bd8375` (step 3),
`2ea31fb` (companion matrix leaf), `86f9f35` (steps 4+5 with the Vieta leaf open), and the final
commit closing `exists_vieta_of_cubic_pisot`. Nothing pushed.

## Next

`PROBE-MILLS-3ADIC.md`'s "What is left": exclude the six residual classes of `f mod 3` for a
totally real cubic Pisot `β` satisfying Saito's (1.3). That is the step from "the primes tend to
`±1`" to an actual contradiction, and it is the natural phase 30. Also unformalised: Saito's
Problem 1.1 for totally real cubic Pisot `β` via the eventually-constant floor offset `h ∈ {0,−1}`.
