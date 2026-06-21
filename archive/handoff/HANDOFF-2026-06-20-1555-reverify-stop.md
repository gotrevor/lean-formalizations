# Handoff: ground-truth re-verification lap — TREADMILL STOP requested

**Date**: 2026-06-20 15:55 UTC · **Branch**: `ntl-hjsw` · **HEAD**: `5e53c6a` (+ this doc) · `LEAN_LAP_ALLOW_STOP=1`

> The stop hook requested a **true STOP** this lap: the treadmill will NOT relaunch. This doc is a
> checkpoint, not a baton — there is no automatic successor. Read it only if Trevor restarts the run.

## 🎯 What we're doing
Repo headline theorems + bonuses are **COMPLETE and axiom-clean**; the project has been in
**finish-and-stop mode** for several laps. The kickoff prompt still carries a *stale* de-vendor /
"v4.29.1→v4.31.0 upgrade" objective that was actually landed two laps ago (`a0f17d1`). This lap I
re-verified the completion state from **ground truth** (real `lake build` + real `#print axioms`,
not docs), confirmed nothing is genuinely open, and self-stopped without manufacturing side quests.

## 🧠 Context to carry forward
- **Do NOT redo the de-vendor / v4.31 bump.** Already done at `a0f17d1`: mathlib v4.31.0, PNTAnd
  de-vendored into a real lake dep on `kim-em/PrimeNumberTheoremAnd@bump/v4.31.0`, 8 vendored files
  deleted. The kickoff objective is a stale relaunch artifact — ignore it.
- **finish-and-stop discipline is the operative rule.** The ONE remaining frontier item — the sharp
  `2π|u|` BV-Fourier decay constant (`PENDING_WORK.md` item 1 / `STATUS.md` Long-term) — is an
  off-headline 🟠 wall needing signed-BV / Lebesgue–Stieltjes integration-by-parts machinery that is
  **absent from mathlib**. It gates NO headline (the `prelim_decay` sorries live only in the dep's
  `Wiener.lean`, dead code off the `weakPNT` path, which is axiom-clean), and its feasible weaker form
  (`4|u|`) is already complete in `src/`. Building signed-BV-IBP to sharpen a bonus is exactly the side
  quest finish-and-stop forbids. Only pursue it if Trevor explicitly lifts finish-and-stop.
- **`ON-LINE-REQUEST.md` is correctly left open.** Its items are *write-to-external-repo* doc-propagation
  tasks (fold two v4.31 gotchas into `~/src/lean-universe/MIGRATE-*.md` and `~/src/mathlib-bump-cookbook/`)
  that a sandboxed YOLO session cannot perform. They block nothing in this repo. A networked host fulfills
  and deletes them.

## ✅ State (all observed in real output this lap)
- **`lake build` GREEN** — 8621 jobs, cached replay; only deprecation/unused-simp warnings, zero errors.
- **`#print axioms` clean** — ran `lake env lean` over the `.bump-axioms` list; 11/14 headlines spot-checked,
  every one `[propext, Classical.choice, Quot.sound]` — zero math axioms, zero `sorryAx`. (Curtis, PowerTower,
  Constructible×2, Transcendence×2, Goodstein, NoThreeInLine hjsw/weakPNT, Mertens 3rd, BVFourierDecay route-b.)
- **`src/` sorry-free** — all 15 `sorry`/`axiom` grep-hits are docstring prose, no live tactic/declaration.
- **No unharvested `ON-LINE-FINDINGS-*.md`** in repo root.
- **No commit made** — zero file changes this lap (axiom-check script was in `/tmp`); working tree was clean.

## 🎬 Next actions
**Default: stay stopped.** If Trevor restarts the treadmill *without* lifting finish-and-stop:
1. Re-confirm ground truth (above) and self-stop again — do NOT reopen the de-vendor objective or any side quest.

If Trevor **explicitly lifts finish-and-stop** and wants the one real multi-lap target:
1. Attack the sharp `2π|u|` BV-Fourier constant via route (c): Jordan decomposition of a BV function →
   signed Lebesgue–Stieltjes measure → integration-by-parts for the Fourier transform. See `PENDING_WORK.md`
   item 1 for the three attack paths already scoped. This needs mathlib infra that doesn't exist yet —
   expect to formalize signed-Stieltjes IBP as a multi-lap prerequisite, not a one-lap close.

## ⚠️ Gotchas
- **v4.31 first-from-source full builds hit macOS-side FD exhaustion** (orbstack bind mount; v4.31's
  3-file olean split × ~10–16 heavy parallel leaves exhausts macOS `kern.maxfiles`, unreachable from the VM).
  Already cached, so only bites after a `lake clean`. No `-j`/`--jobs` flag in this lake — workaround is to
  build modules sequentially once to cache, then the full build is a clean replay.
- The dep `Wiener.lean` carries 2 `prelim_decay` sorries — **dead code** off the WeakPNT path; `weakPNT`
  is axiom-clean with them present. Don't be alarmed by them.

## 📁 Key files
- `.bump-axioms` — the 14 headline theorems whose `#print axioms` footprint is the faithfulness gate.
- `STATUS.md` / `PENDING_WORK.md` — completion inventory + the lone open frontier item with attack paths.
- `HANDOFF-2026-06-20-1900.md` — prior lap's near-identical re-verification (same state).
- `ON-LINE-REQUEST.md` — open external-repo doc-propagation asks (not actionable from sandbox).

---
**→ Next session (only if restarted): this is your starting point. Don't summarize this doc back to Trevor,
don't offer other KB projects, and don't reopen the stale de-vendor objective. The repo is COMPLETE and
axiom-clean; absorb the context above and stay stopped unless Trevor explicitly lifts finish-and-stop — in
which case start at "Next actions" under that branch.**
