# Handoff: π-transcendence PROVEN — repo is 100% axiom-free

**Date**: 2026-06-16 · **Branch**: main · **HEAD**: `d1b2293` (+ docs commits) · **MATH AXIOMS: 0**

## 🎯 Headline
**Transcendence of `π` (Lindemann 1882) is fully proved and axiom-clean**, and the previously
cited `hermite_lindemann` axiom has been **discharged and deleted**. The entire repo now
carries **zero math axioms**: `grep '^axiom' src/` is empty, and every headline
`#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]`.

- `Transcendence.transcendental_pi_axiomClean : Transcendental ℚ Real.pi` — axiom-clean.
- `Constructible.squaring_the_circle_impossible_uncond : ¬ IsConstructible (√π)` — now
  fully unconditional **and** axiom-clean (rewired off the deleted axiom).

## ✅ What this lap built (≈26 commits `b2b56f9`…HEAD, all axiom-clean)
The complete machine-checked Lindemann π-transcendence, in five files under
`NumberTheory/Transcendence/`:
- **`PiLindemann.lean`** — combinatorial reduction (`pi_exp_relation`: `e^{iπ}=−1 ⟹
  K+∑_{σ_t≠0}e^{σ_t}=0`); the general non-monic analytic engine `no_intPoly_exp_relation`
  (integer-`N`/mod-`p` over an arbitrary `F.aroots`, generalizing the `e` proof); the `hsum`
  bridge (`aroots_integralNormalization`, `hsum_of_monic_rootsum`); the descent
  (`esymm_aroots_mem_range`, `subsetSum_poly_lifts`); the glue (`exists_ratPoly_removeZeroRoots`,
  `exists_intPoly_aroots_eq`); and the capstone `subsetSum_relation_impossible`.
- **`MonicRootSums.lean`** — fact (a) `sum_aeval_roots_int` (monic root-sum integrality via
  Newton's identities, Aristotle `9a19f72e`, kernel-verified); the conjugate-instantiation
  capstones `subsetSum_relation_impossible_of_{conjugatePoly,esymm}` and
  `transcendental_pi_of_subsetSumEsymm` (indexes the roots of `minpoly ℚ (iπ)` by `Fin d`).
- **`SubsetSumEsymm.lean`** — fact (b) `subsetSum_esymm_rational` (fundamental theorem of
  symmetric polynomials applied to the subset-sums; Aristotle `b7252abe`, kernel-verified).
- **`PiTranscendental.lean`** — `transcendental_pi_axiomClean`, combining the two.
- **`HermiteLindemann.lean`** — reduced to just the `isAlgebraic_pi_complex_of_real` helper
  (axiom + axiom-based `transcendental_pi` deleted).

`lake build` green (8274 jobs); `src/` sorry-free; **0 math axioms**.

## 🎬 Next actions (the transcendence thread is DONE — pick a new target)
The squaring-the-circle / transcendence thread is **complete and axiom-free**. Open work:
1. **Power-tower sharp `iff` lower direction** (`PENDING_WORK.md`): divergence for
   `0<x<e^{-e}` via a genuine attracting 2-cycle. Cleanest open non-blocked target; fresh
   real-analysis (`RealAnalysis/PowerTower/EngineLower.lean`); memory `power-tower-2cycle-crux.md`.
2. **General Hermite–Lindemann for arbitrary algebraic α** (`log 2`, `cos 1`, …): the π
   assembly is mostly α-agnostic (`no_intPoly_exp_relation` + the symmetric-function descent
   work for any algebraic exponent). A bounded extension; not required by any headline.
3. PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.

## ⚠️ Gotchas / notes
- `SubsetSumEsymm.lean` + `MonicRootSums.lean` use `import Mathlib` (broad) deliberately —
  they're the kernel-verified Aristotle environment; don't narrow.
- Re-check `#print axioms` after any future Aristotle port (`grind`/`simp_all` can inject
  `sorryAx`).
- **Aristotle CLI gotcha**: `aristotle submit "<prompt>"` raises `ENAMETOOLONG` for any 255+
  char run lacking `/` (pathlib bug). Sprinkle `/` (append ` -- ref/x` per line) or use
  `--project-dir`. See `tools/aristotle/README-cli-gotcha.md`.
- The `Curtis/Lemma2.lean` lint warnings are intentional — leave them.

## 📁 Key files
- `NumberTheory/Transcendence/{PiLindemann,MonicRootSums,SubsetSumEsymm,PiTranscendental,
  HermiteLindemann}.lean`
- `STATUS.md` (axiom ledger: 0 axioms) · `PENDING_WORK.md` (item B = ✅ DONE) ·
  `tools/aristotle/` (prompts + CLI gotcha).

---
**→ Next session: the transcendence thread is COMPLETE and axiom-free — do not re-open it.
Pick a NEW target (default: power-tower sharp iff). Don't re-derive the π assembly.**
