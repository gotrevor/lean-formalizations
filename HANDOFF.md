# HANDOFF — lean-formalizations (thin pointer)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

This file is a **thin pointer**. The durable overview is **`STATUS.md`**; the per-lap baton
is the newest **`HANDOFF-<date>.md`**; open items/attack paths live in **`PENDING_WORK.md`**.

## Where things stand (2026-06-19 lap 11 — 🎉🎉🎉 "goodsteinLength GROWS LIKE f_{ε₀}", TWO-SIDED)
The charter headline **C3 is done**; ladder A–C complete. Both directions machine-checked:
- **LOWER (every `o < ε₀`):** `goodsteinLength_dominates_fastGrowing` (`o.NF → ∃ N, ∀ m≥N,
  f_o(m) ≤ goodsteinLength m + 2`). New file `Logic/Goodstein/TowerDomination.lean`; engines
  `two_mul_le_goodsteinLength_iter` (powered by `towerN_le_fastGrowing` — the lap-10 "needs
  `f_{ω^ω}`-strength deep-seed bound" worry was FALSE) + `omegaTower_succ_le_seqONote_repr`, lifted to
  all ε₀ via tower cofinality `exists_repr_lt_omegaTower` (axiom-clean).
- **UPPER:** `goodsteinLength_le_fastGrowing_ordinal` (`goodsteinLength m + 2 ≤ f_{o_m}(2)`), via the
  Cichoń identity + the new `hardy_le_fastGrowing` (`hardy o n ≤ fastGrowing o n`). **Fully axiom-clean.**
- C3 audit surface `Logic/Goodstein/GrowthStatement.lean` (+ anchor `fastGrowingε₀_eq_towerO`).
- **B4 at finite levels DONE** (`hardy_omega_pow_ofNat`: `H_{ω^k}(n)+1=f_k(n+1)`, axiom-clean) via the
  new Hardy additive law `hardy_oadd_tail` + coefficient lemma `hardy_oadd_coeff` (all in `Hardy.lean`).
- Build 🟢 (8295 jobs); commits `4856b9a`→…→`904f5ea`→`5bf832f`→`6a63e12`. **Charter ladder
  A1–A4, B1–B4(finite), C1–C3 COMPLETE.**
- **NEXT:** only extensions remain (B4 at limit α — clean form is false there; optional sharpenings).
  See `PENDING_WORK.md` → "NEXT FRONTIER" + the "Next" list below.

## (lap 10 — climbed to o=ω^ω; baton `HANDOFF-2026-06-19-1257.md`)
- Closed `o=ω`, `o=ω^j`, `o=ω^ω` individually (`DominationOmega.lean`) via the self-similarity TOWER
  (`GoodsteinLike.lean`). **Superseded** by lap-11's general `TowerDomination.lean` (which subsumes all
  three), but the per-level closures remain as anti-vacuity witnesses — don't delete them.

## Next (the lap-12 frontier — START HERE)
**The charter ladder is COMPLETE (A1–A4, B1–B4-finite, C1–C3 + two-sided "grows like `f_{ε₀}`").** Only
genuine extensions remain — none clearly high-value; pick by appetite:
1. **B4 at LIMIT α.** Finite B4 `H_{ω^k}(n)+1=f_k(n+1)` is DONE+axiom-clean (`hardy_omega_pow_ofNat`,
   `6a63e12`) via the new `hardy_oadd_tail` (additive law) + `hardy_oadd_coeff` (coefficient lemma).
   The clean form is FALSE at limit α (`H_{ω^ω}(1)+1=8≠f_ω(2)=2048`). A correct limit statement
   (inequality sandwich, or the successor-cofinal subsequence) is the open piece — subtle.
2. **Optional sharpenings:** strict domination removing `+2` (needs general index monotonicity,
   A3-hard); a single ε₀ capstone via `ε₀ = sup_o repr o`; a tighter `f_{ε₀}` upper bound.
3. If nothing here appeals, the project's headline goals are met — a reflection/audit lap or
   PR-polishing (mathlib-shaping the `FastGrowing`/`Goodstein` modules) is reasonable.
2. **DO NOT** re-iterate the now-COMPLETE two-sided growth theorem (lower `goodsteinLength_dominates_fastGrowing`
   + upper `goodsteinLength_le_fastGrowing_ordinal`) or reopen the superseded `ppCount` sparsity route.
3. Optional sharpenings (lower priority): strict domination removing `+2` (needs general index
   monotonicity, A3-hard); a single ε₀ capstone via `ε₀ = sup_o repr o`.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` on closed theorems.
- New Goodstein work goes in files that only *import* `DominationBaseCases.lean` (editing it re-runs
  ~5 min of `native_decide`); `TowerDomination.lean` / `GoodsteinLike.lean` are the cheap surfaces.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
