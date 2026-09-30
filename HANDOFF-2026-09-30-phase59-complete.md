# Handoff: Mills phase 59 complete — `ξ(3^k + 3^a s′)` transcendental, `3 ∤ s` dropped

**Date**: 2026-09-30 · **Branch**: `main` · **HEAD**: `693e396` (clean tree)

## 🎯 What was done
`DIRECTION.md`'s phase 59 directive: drop phase 58's `3 ∤ s` hypothesis.  The frozen statement
`ShiftedMillsThreePow.xi_shifted_three_pow_transcendental` is proved, conditional only on
`Literature.Saito2025TypeBTrace` + `Literature.Siegel1944SmallestPisot`.  Shift is now any
`s = 3^a · s′` with `s′` even, `3 ∤ s′`, `s′ ≥ 8`, and `3^a s′ ≤ 3^(j+1)`.

## 🧠 The structural point
`C_k = 3^a · largeC j′ s′ k` (`def threePowC`).  Everything Saito needs is *scale-invariant*, so
(B1)–(B3) and the delicate (B5′) transfer from phase 58's `largeC` lemmas mechanically:
`threePowC_ratio_of_largeC` scales the `29/10` bound, `threePowC_B5` scales `largeC_B5`
(`Nat.mul_dvd_mul_left`).  Euler therefore runs on the 3-free part `D_m = C_m / 3^a` and never on
`C_m` itself — which is exactly the step that breaks when `3 ∣ s`.

Two genuinely new pieces:
1. **`a < j` is forced, not assumed.**  `8·3^a ≤ 3^a s′ ≤ 3^(j+1)`, while `j ≤ a` would give
   `3^(j+1) ≤ 3·3^a < 8·3^a`.  So `j = a + j′` with `j′ ≥ 1`, and `s′ ≤ 3^(j′+1)`.
2. **The period bound is `g ∣ 3^a`, not `g = 1`** (`dvd_three_pow_of_eventually_dvd`):
   `g ∣ 3C_k − C_(k+1) = 3^a·2s′`; `C_k` is odd (both factors odd) so `g` is odd, so `g ∣ 3^a s′`;
   then `g ∣ C_k − 3^a s′ = 3^a·3^(k+j′)`, and `Nat.gcd_mul_left` + `3 ∤ s′` give
   `gcd(3^a s′, 3^a 3^(k+j′)) = 3^a`.  `Nat.dvd_prime_pow` then gives `g = 3^b`, `b ≤ a`.

`threePowC_split`/`_dvd`/`_div`: `C_k / 3^b = threePowC (a−b) j′ s′ k = 3^(k+(a−b+j′)) + σ` with
`σ = 3^(a−b) s′ ≥ s′ ≥ 8`.  So `β = ξ^(3^b)` is a cubic Pisot number whose exponents have exactly
phase 58's shape, and both endgame branches reuse `four_lt_pisot_pow`,
`floor_pow_prime_pow_add_not_prime_full`, `powTrace_eq_traceSeq`,
`dvd_traceSeq_of_map_eq_X_pow` verbatim, with `β^σ > 4` from Siegel as before.

## ✅ State
- `ShiftedMillsThreePow.lean` sorry-free; no `private`; earlier files and `Literature/` untouched.
- `lake build` green (8781 jobs, observed directly and via the pre-commit gate).
- `#print axioms xi_shifted_three_pow_transcendental` → `[propext, Classical.choice, Quot.sound]`.
- `scripts/shifted-mills-three-pow-probe.py`: 72 `(a, s′)` cases, 0 failures, controls fail.
- `scripts/fact-graph` regenerated: 30 edges, 32 hypotheses.  Committed `693e396`.
- Nothing in flight; no Aristotle job this lap.

## ⚠️ Gotchas
- `positivity` will **not** prove `0 ≤ ξ ^ N` from a `1 < ξ` hypothesis in context (it only inspects
  the term).  Use `pow_nonneg (by linarith [hleast.1.1]) _`.  This bit once at
  `Int.natCast_floor_eq_floor`.
- `hleast.unique hξ'` only typechecks because `threePowC a j′ s′ k` is rewritten to the frozen
  statement's `3^(k+j) + 3^a s′` first (`hexp` + `simpa only`); `threePowC_eq`'s RHS exponent is
  `k + (a + j′)`, so the `a + j′ = j` rewrite is load-bearing.
- `simp only [threePowC, largeC]` suffices for the `3C_k = C_(k+1) + 3^a·2s` identity;
  `largeC_succ` is redundant there (the linter says so).

## 🎬 Next actions
1. `DIRECTION.md` has no phase 60 — an altitude lap owns planting it.  Candidates:
   - **`ShiftedTraceRigidity`** (phase 45's still-open node) — still the strongest; `powTrace_eq_traceSeq`
     puts Saito's `Tr(β^N)` in the integer companion-matrix world where phases 47–52 live.
     Grep `src/LeanFormalizations/Maze.lean` first.
   - **odd `s`**: breaks step 2 at "`C_k` odd ⇒ `g` odd", so it needs a different parity argument.
   - **drop `s′ ≥ 8`**: bound `ξ` directly instead of through Siegel.
2. Phases 58 and 59 together cover: `ξ(3^k + s)` transcendental for every `s` whose 3-free part is
   even and `≥ 8`.
