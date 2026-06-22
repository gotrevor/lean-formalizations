# ON-LINE-FINDINGS — 2026-06-21 — propagated the two v4.31 gotchas to the shared docs

Fulfills the `ON-LINE-REQUEST.md` item *"propagate two v4.31 gotchas to the shared bump cookbook
(sandbox can't write outside repo)."* The box (`lean-formalizations-ntl`, branch `ntl-hjsw`, bump
`a0f17d1`) can only write inside its own repo; a networked host session folded both items into the
canonical docs. **Both done.**

## 1. `lean-formalizations-ntl` marked DONE in MIGRATE §2

`~/src/lean-universe/MIGRATE-v4.29.1-to-v4.31.0.md` — committed `56de4b9`.

- Replaced the stale *"🟡 mid-bump, UNCOMMITTED"* entry with the DONE entry: `a0f17d1`, branch
  `ntl-hjsw`, **NOT bare-mathlib** — *de-vendored* the hand-ported PNTAnd tower into a real lake dep on
  `kim-em/PrimeNumberTheoremAnd @ bump/v4.31.0` (deleted 8 vendored files; two consumers now
  `import PrimeNumberTheoremAnd.Consequences` for `WeakPNT''` / `pi_alt'`).
- Captured the faithfulness story (baseline lost → gated the erdos-1050 way; 13 headlines
  `#print axioms`-clean now, incl. `weakPNT` / `prime_number_theorem` *through the external dep*; the
  dep's `Wiener.lean:323/342` `prelim_decay` sorries are dead-code off the WeakPNT path).
- Recorded the 3 own-file proof-body fixes mapped to cookbook entries: Mertens `using!` + `convert …
  <;> first | rfl | (field_simp <;> ring)` (escape-hatch `using!` + cookbook **A** field-variant);
  MertensConstant `Function.comp_def` (cookbook **M**); PrimeGap `factorization_eq_zero_of_non_prime`
  → `…_not_prime` (lemma rename). Build green, 8620 jobs.
- Also added `davies` (8 fixes) + `ntl` (3 fixes) to the §2 "Cost data so far" line so the per-repo
  cost table is current.

> Note: `56de4b9` is a concurrent host session's commit (a §1 anchor→store wording cleanup) — the
> shared `.git/index` swept my staged MIGRATE edit into it. Both changes are correctly present in the
> committed tree; lean-universe has no remote, so this is local-only.

## 2. New cookbook entry U — v4.31 3-file olean split exhausts host FDs

`~/src/mathlib-bump-cookbook/` — committed `2f38cdb`, **pushed** (public repo).

- Added **Part 3 — Build-environment gotchas (not a source fix)** with entry **U**: v4.31 writes three
  files per module (`.olean` + `.olean.private` + `.olean.server`), tripling open-file pressure; a
  from-source full build inside an OrbStack/Docker bind-mount on macOS exhausts the **macOS host** FD
  limit (`kern.maxfiles`), not the VM's (`ulimit -n` = 1048576 is innocent). Symptom: `Too many open
  files` on a *rotating* set of leaf files — spurious, each builds fine alone. Fix: this `lake` has no
  `-j`/`--jobs` flag, so serialize the heavy wave to cache, then let the full build replay it
  (`find src -name '*.lean' | sed … | while read m; do lake build "$m"; done` then `lake build`).
- Updated the README "How to use it" grouping to list the new build-environment group, plus the
  previously-missing **S** and **T** entries.

## Verification

Both edits read back as committed (grep for `ntl-hjsw` in the MIGRATE HEAD copy; entry `U` +
`Too many open files` in the cookbook). Cookbook pushed to `github.com:gotrevor/mathlib-bump-cookbook`
(`c39f8a0..2f38cdb`).
