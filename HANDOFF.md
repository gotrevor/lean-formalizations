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
- Build 🟢 (8295 jobs); commits `4856b9a`→`9b1e779`→`08afea0`→`9f8cb56`→`904f5ea`.
- **NEXT:** **B4 `H_{ω^α}=f_α`** — the last charter ladder item (long-horizon). `hardy_le_fastGrowing`
  is the `≤`-half; B4 wants the exact identity at `ω^α` with mathlib's `ω[n]=n+1` shift handled
  (measure the offset on small cases first). See `PENDING_WORK.md` → "NEXT FRONTIER".

## (lap 10 — climbed to o=ω^ω; baton `HANDOFF-2026-06-19-1257.md`)
- Closed `o=ω`, `o=ω^j`, `o=ω^ω` individually (`DominationOmega.lean`) via the self-similarity TOWER
  (`GoodsteinLike.lean`). **Superseded** by lap-11's general `TowerDomination.lean` (which subsumes all
  three), but the per-level closures remain as anti-vacuity witnesses — don't delete them.

## Next (the lap-12 frontier — START HERE)
1. **B4 `H_{ω^α} = f_α`** — the last charter ladder item. `hardy_le_fastGrowing` gives the
   `≤`-at-same-index half. For B4: MEASURE the offset first — repo's `hardy_omega` (`H_ω(n)=2n+1`) vs
   `fastGrowing_one` (`2n`) shows the `ω[n]=n+1` convention adds `+1` at `ω`; generalize that offset up
   the tower (`H_{ω^α}` vs `f_α`) with `native_decide` on small cases before fixing the statement.
   Good bounded Aristotle candidate once the offset is pinned. See `PENDING_WORK.md` → "NEXT FRONTIER".
2. **DO NOT** re-iterate the now-COMPLETE two-sided growth theorem (lower `goodsteinLength_dominates_fastGrowing`
   + upper `goodsteinLength_le_fastGrowing_ordinal`) or reopen the superseded `ppCount` sparsity route.
3. Optional sharpenings (lower priority): strict domination removing `+2` (needs general index
   monotonicity, A3-hard); a single ε₀ capstone via `ε₀ = sup_o repr o`.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` on closed theorems.
- New Goodstein work goes in files that only *import* `DominationBaseCases.lean` (editing it re-runs
  ~5 min of `native_decide`); `TowerDomination.lean` / `GoodsteinLike.lean` are the cheap surfaces.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
