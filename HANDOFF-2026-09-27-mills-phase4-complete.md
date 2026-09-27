# Handoff: Mills phase 4 COMPLETE — explicit no-RH upper bound landed

**Date**: 2026-09-27 · **Branch**: `mills` · **HEAD**: `7c1919c`

## 🎯 Objective (met)
`DIRECTION.md` phase 4: prove `exists_minMills_lt_of_dudek` in `Mills/UpperBound.lean` —
from the frozen `Literature.Dudek2016`, the least Mills number exists and is
`< 2 · exp(exp(33.3)/3)`, with no RH. Done; `Mills/` is sorry-free again.

## 🧠 The one idea to carry forward
**Scale matters: the naive generalization is off by a cube.** Parametrizing the nested-interval
construction by its starting point `m₀` gives a Mills number in `[m₀, m₀+1)`, i.e. `A ≈ E` where
`E = exp(exp 33.3)`. The frozen target is `2·exp(exp(33.3)/3) ≈ 2·E^(1/3)` — astronomically
*smaller*, so that form is useless. The fix is an index shift: if `m₀` is prime, build
`B ∈ [m₀, m₀+1)` as before and take `A = B^(1/3)`. Then `A^(3^(k+1)) = B^(3^k)`, so the digit at
`n = 1` is `m₀` itself and `A³ < m₀ + 1` — the cube-root scale that matches the target.
Corollary worth remembering: `IsMills` constrains only indices `≥ 1`, so the chain's index-0 term
needs no primality in the unshifted form (that is why `cubeSeq_prime_succ` suffices there), but it
*does* need primality in the shifted form.

## ✅ State (observed, not assumed)
- `exists_minMills_lt_of_dudek`, `minMills_lt_of_dudek` proved.
- `#print axioms` on those two plus `exists_mills_of_primeBetweenCubes` and `lower_bound`:
  `[propext, Classical.choice, Quot.sound]`.
- `grep -rn "sorry\|admit" src/.../Mills/` → no matches. Full `lake build`: 8682 jobs, success
  (pre-commit hook re-ran it). Committed `7c1919c`. Nothing pushed (no egress).

## 🔧 What changed in `Basic.lean` (no existing statement altered)
- `cubeSeq h m₀ : ℕ → ℕ` now starts at a chosen `m₀` with `max N 2 ≤ m₀`; the old blanket
  `cubeSeq_spec` split into `cubeSeq_ge`, `cubeSeq_prime_succ`, `cubeSeq_prime` (the last needs
  `m₀.Prime`). `mu`/`nu`/`floor_pow_iSup` all carry `m₀`.
- New `iSup_mu_lt` / `le_iSup_mu`: the built number sits in `[m₀, m₀+1)`.
- New public `exists_mills_lt_of_primeBetweenCubes` (unshifted) and
  `exists_mills_cube_lt_of_primeBetweenCubes` (shifted, `A³ < m₀+1`).
- `exists_mills_of_primeBetweenCubes` is now a two-line corollary of the former.

## 🎬 Next actions
1. **Nothing is open in the Mills lane.** Branch `mills` wants a host push + merge to `main`
   (plus the README row check). Do not reopen `Mills/` or invent side quests in it.
2. A new lap needs a **fresh `DIRECTION.md` objective**: phase 4 was the last one written and is
   complete. Pick from the repo's target catalog.

## ⚠️ Gotchas
- `push_neg` is deprecated in this pin — use `push Not at h`.
- `Literature/Primes.lean` `Prop`s (`Schoenfeld1976`, `BakerHarmanPintz2001`, `Matomaki2007`,
  `Mahler1957`, `Dudek2016`) are frozen published theorems carried as hypotheses. Not axiom debt,
  not targets; strengthening one would silently vacuate everything downstream.
- `IsMills` / `IsMinMills` are byte-level copies of formal-conjectures' statements — the audit
  surface. Never tidy them.
- `lt_of_pow_lt_pow_left₀ n (0 ≤ b)` is the cube-comparison lemma in this pin.
