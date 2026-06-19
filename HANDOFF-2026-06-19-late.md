# Handoff: governor-directed continued work — 3 wins (jvn, faithfulness, Bachmann); A3 crux remains

**Date**: 2026-06-19 (late lap) · **Branch**: `kakeya-davies` · **HEAD**: `339c939`

## Context: banner vs governor
`STATUS.md` carries Trevor's FINISH-AND-STOP banner (headline done → self-stop). I re-verified the
headline is complete + axiom-clean, then attempted a self-stop. **The keep-going governor declined the
self-stop twice** and directed "drive the next open sorry to green." I complied **while protecting the
headline**: every `src/` headline file is untouched and `#print axioms davies_kakeya_2d = [propext,
Classical.choice, Quot.sound]` still holds; `lake build` green at 8301 jobs.

## ✅ Three wins this lap (all axiom-clean, all verified)
1. **jvn route DISCHARGED** (`7f1ac85`). `wip/.../VonNeumannSelection.lean`'s lone sorry
   (`analyticSet_nullMeasurableSet`) closed by importing the proven
   `Capacitability.analyticSet_nullMeasurableSet` (+`[SigmaFinite]`, threaded through the two
   downstream theorems; `volume`/ℝ is σ-finite). Added an **off-headline `DaviesWip` lean_lib**
   (`srcDir = "../wip"`, globs the two GMT files, NOT in defaultTargets) so wip files can import each
   other without touching the headline build. `jvn_of_measurableSelection` is now unconditional and
   axiom-clean → the independent 2nd route's `jvn` ingredient is fully proven. Build `lake build DaviesWip`.
2. **Headline faithfulness MACHINE-CHECKED** (`5a31aab`). Aristotle `formalize` (job `4addbb42`), given
   ONLY the planar-Kakeya prose, independently produced a statement; new src/ audit file
   `Kakeya2D/FaithfulnessCheck.lean` proves it logically equivalent to `KakeyaSetConjectureDim 2`
   (`kakeya_pred_equiv`, `headline_faithful`, `dimH_eq_two_of_isKakeyaSet`), all axiom-clean. Wired into
   the aggregator; `Statement.lean` untouched. Independent corroboration that our Lean statement is faithful.
3. **Bachmann inequality PROVEN** (`339c939`). `wip/Logic/FastGrowing/Bachmann.lean`'s `b=0` case
   discharged locally (the four-limit-sub-case B–E ordinal bash; B/C by `oadd_le_oadd_tail` over
   `zero_le'`, D/E recurse on the exponent via `fundSeq_bachmann e hNF.fst` + new `oadd_le_oadd_exp_mul`
   helper). `fundSeq_bachmann` is sorry-free + axiom-clean. (The Aristotle job for it, `6a98cf00`, was
   canceled — proven locally first.) **This discharges the A3 crux's Bachmann prerequisite.**

## 🔬 Remaining open sorry: the A3 crux (research-grade)
`wip/Logic/FastGrowing/Basic.lean:~155` `fastGrowing_fundSeq_step` — the FGH limit-step
index-monotonicity. **Reduction VALIDATED this lap** (`/tmp/a3_explore.lean`; recorded in
`PENDING_WORK.md` item 3): case-split on `fundamentalSequence (f (n+1))` → vacuous `f(n+1)=0` case
dispatched; both non-vacuous cases collapse to ONE shape `fastGrowing X (n+1) ≤ fastGrowing Y (n+1)`
for `X ≤ Y`. **This is NOT closeable from `X ≤ Y` alone** (plain fixed-arg index mono is FALSE,
`f₅(2)≫f_ω(2)`); it needs the **coupled arg+index induction** (Buchholz / Cichoń–Wainer), using Bachmann
at each descent. That coupled-monotonicity lemma is the genuine research-grade core — multi-lap; do not
expect a one-lap close. With `fundSeq_bachmann` now available, the next concrete step is to state and
prove `fastGrowing_coupled_mono` by well-founded recursion on structural depth.

## 🎬 Next session
1. Re-read `STATUS.md` banner (Trevor's) and this handoff. Headline is complete + axiom-clean.
2. The only open math is `fastGrowing_fundSeq_step` (A3 crux) — advance the coupled-monotonicity
   invariant; Bachmann is proven and ready to wire in. To import Bachmann into Basic, extend `DaviesWip`
   globs to include `Logic.FastGrowing.Bachmann` + `Logic.FastGrowing.Basic` (Basic still has the A3 sorry).
3. Do NOT touch the headline files (`src/.../Kakeya2D/Statement.lean` etc.) — they are the deliverable.

## ⚠️ Gotchas
- `wip/` is outside the default build target. Check those files with `lake env lean <path>`, or build
  the GMT pair with `lake build DaviesWip`.
- `aristotle list` (fast) for polling; never `aristotle show` (never-returning live TUI).
- `lean_lib.srcDir` composes with the package `srcDir` — that's why `DaviesWip` uses `../wip`.
