# STATUS — lean-formalizations 📊
**Umbrella for solved-but-unformalized impossibility / no-formula meta-theorems.** · **Build**: 🟢 green (8255 jobs) · **Updated**: operator redirect · 2026-06-14 · `fe18f0a`

## Where it stands
**Curtis 1990 is COMPLETE and axiom-clean** — verified by real `#print axioms`: all 7 headline results reduce to the pure trust base `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms anywhere in `src/`). The single deep crux (`substCurve_eq_zero`) was closed by a reformulation that bypassed Curtis's Lemma 1 / limit argument entirely.

**Active run (operator-bounded, 2026-06-14):** a **verification-hardening** pass — add independent faithfulness cross-checks that raise confidence the formalized *statements* capture Curtis, then **STOP**. The four items (full specs in `DIRECTION.md`): (1) n=2 boundary check / Sylvester hypersurface; (2) more Lemma-2-vs-`FrobeniusNumber` anchors; (3) a concrete refuted candidate formula; (4) document the not-algebraic / sub-families-have-formulas findings + fix stale docstrings. No new math targets — `--allow-stop`-scoped to 1–4.

## What's happened (newest first)
- **2026-06-14 (operator redirect, Trevor via Ren):** Audited Curtis for statement-faithfulness (not just axiom-cleanliness) — verdict: faithful + non-vacuous. Scoped a BOUNDED verification-hardening run (items 1–4) to make the faithfulness case airtight, then self-stop. **Parked** the constructible-numbers pivot and mathlib-upstream to a future run (`PENDING_WORK.md` → P1/P2). Archived stale dated batons; `DIRECTION.md` rewritten as the live work-order.
- **2026-06-14 (review lap):** Verified Curtis complete & axiom-clean from real `#print axioms` on all 7 headlines. (Had chosen constructible-numbers as the next target — now parked by the operator.)
- **2026-06-14 1511:** Closed the crux `substCurve_eq_zero`; repo went `sorry`-free + axiom-clean. Added faithfulness anchors (`⟨3,7,8⟩`), the ℤ/ℚ (any ℂ-algebra) corollary, the n≥3 generalization, and `grid_vanish` generalized to any infinite field.
- **2026-06-14 1423 & earlier:** Built the Curtis engine spine, Step B, Lemma 2 (Brauer–Shockley, via Aristotle, verified), the corollary, the finite-bad-prime lemma — all under the then-open crux.

## Outstanding
### Short-term (THIS run — mirror PENDING_WORK top)
- Build verification items 1–4 (`DIRECTION.md`): n=2 boundary check; extra numerical anchors; refuted-candidate witness; findings doc + stale-docstring fixes. No `sorry`; omit intractable stretch parts. **Then STOP.**
### Long-term (PARKED — future runs, Trevor's call; NOT this run)
- Constructible-numbers / doubling-the-cube impossibility (`PENDING_WORK.md` P1) — genuinely absent from mathlib; provable algebraic core + hard geometric bridge.
- Curtis mathlib upstream of the n≥3 impossibility (P2) — outward-facing, web/CLA-gated.
### To completion
- Curtis 1990: ✅ done (axiom-clean). This run: done when items 1–4 are built (stretch parts optional) + green + sorry-free.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `no_polynomial_relation` | Curtis 1990 (Frobenius of a triple not algebraic over generators), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ trust-base only — **0 math axioms** |
| `no_finite_polynomial_formula` | ℂ corollary (no finite formula list), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_of_algebra` | any ℂ-algebra coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_int` | ℤ coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_rat` | ℚ coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_multivar` | n≥3 (paper's full title), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Anchors.frobeniusNumber_3_7_8` | faithfulness witness (Frobenius⟨3,7,8⟩=5) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |

**Math-axiom count (🟢+🟡+🟠) across all headlines: 0.** Every base is the bare trust base — no 🔴 anywhere, correct since every Curtis headline is unconditional. (This run's new check theorems should land axiom-clean too; re-run `#print axioms` on them before stopping.)

## Pointers
- Live work-order: **`DIRECTION.md`** (operator-bounded run) · resume doc: **`HANDOFF.md`** (authoritative)
- Open items / scope: `PENDING_WORK.md` (active 1–4 + parked P1/P2/P3)
- Archived batons: `archive/handoff/HANDOFF-2026-06-14-{1423,1511,1545}.md`
