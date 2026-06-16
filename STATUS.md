# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8270 jobs) · **Updated**: review lap · 2026-06-16 · `f003bf3`

## Where it stands
Three independent threads, all building green. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple) and the **power-tower** convergence theorem are complete and fully axiom-clean. The **constructible-numbers / Wantzel** thread is complete as a full iff (algebra ⇔ geometry) with five classical impossibilities + two positive constructions; its one remaining extension — making *squaring the circle* unconditional — was advanced this lap from "conditional on a `Transcendental ℚ π` hypothesis" to "**unconditional modulo a single cited axiom** (`hermite_lindemann`)". The active frontier is now **discharging that axiom**: this lap shipped the algebraic reduction for transcendence of `e` (the accessible α=1 instance) with the analytic Hermite-assembly crux isolated as one disclosed `sorry`. An Aristotle job is grinding the full `e` proof in parallel.

## What's happened (newest first)
- **2026-06-16 (review lap):** π-transcendence narrowing shipped: stated **Hermite–Lindemann** (nonzero algebraic α ⟹ `exp α` transcendental) as ONE disclosed `axiom` and machine-checked `Transcendental ℚ π` from it (Euler identity `exp(iπ) = -1`), giving `squaring_the_circle_impossible_uncond` (`#print axioms` = trust base + `hermite_lindemann`). Then opened the **transcendence-of-`e`** attack (`ETranscendental.lean`): algebraic reduction proved axiom-clean, analytic crux isolated, Aristotle job `e502fd22` launched on the full proof. New dir `NumberTheory/Transcendence/`.
- **2026-06-15 2358/2343:** Constructible/Wantzel thread COMPLETE — full equivalence `isConstructible_iff_constructiblePoint` both directions (forward = degree obstruction; converse = explicit compass arithmetic). 5 impossibilities (cube, trisection, nonagon, heptagon, + geometric-point versions), pentagon positive. All axiom-clean.
- **2026-06-15:** Constructible Layer 1 (algebraic degree engine `IsSqrtTower.finrank_eq_pow_two`) + 3 classical impossibilities; Layer 2 geometric faithfulness bridge.
- **2026-06-14 (operator redirect):** Curtis verification-hardening run (n=2 boundary / Sylvester hypersurface, extra Frobenius anchors, refuted-candidate witness, findings doc) — complete, self-stopped.
- **2026-06-14:** Power-tower convergence on the full Euler interval `[e^(-e), e^(1/e)]` proved + axiom-clean; lower-bound crux `two_cycle_collapse` via slope/Banach (not the invalid tangent-subtraction sketch). Sharp-iff lower direction (`0<x<e^(-e)` diverges) omitted, no sorry.
- **2026-06-14 1511 & earlier:** Curtis crux `substCurve_eq_zero` closed (reformulation bypassing Lemma 1); repo sorry-free + axiom-clean. Engine, Step B, Lemma 2 (Brauer–Shockley, via Aristotle, verified) built.

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **Discharge the analytic crux `no_intPoly_aeval_eq_zero`** (Hermite assembly of `exp_polynomial_approx`) → transcendence of `e`, axiom-clean. Concrete roadmap in `ETranscendental.lean` header + `PENDING_WORK.md`. Aristotle `e502fd22` in flight.
### Long-term
- **Discharge `hermite_lindemann` itself** (general algebraic α / full Lindemann–Weierstrass) → makes squaring-the-circle fully unconditional. Needs symmetric functions over Galois conjugates (mathlib gap). `e`-transcendence is the first prerequisite; `π` needs the conjugate-product extension.
- Power-tower sharp iff lower direction (genuine 2-cycle existence; multi-lap real analysis). PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · Power-tower convergence ✅ · Wantzel iff ✅ · squaring-the-circle: unconditional **once `hermite_lindemann` is discharged**. Transcendence of `e`: done once the crux is closed.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Curtis.no_polynomial_relation` | Curtis 1990, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `PowerTower.tower_converges_of_mem` | convergence on `[e^-e, e^1/e]`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.isConstructible_iff_constructiblePoint` | Wantzel iff, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.cbrt2_not_constructible` (+ trisection/nonagon/heptagon) | classical impossibilities, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.squaring_the_circle_impossible` | impossibility, **cond.** on `Transcendental ℚ π` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms (hypothesis explicit) |
| `Constructible.squaring_the_circle_impossible_uncond` | impossibility, uncond. | `[…trust base, hermite_lindemann]` | 🟡 1 axiom = Hermite–Lindemann (proven theorem, project-scale; being chipped via `e`) |
| `Transcendence.transcendental_pi` | `π` transcendental, uncond. | `[…trust base, hermite_lindemann]` | 🟡 same 1 axiom |
| `Transcendence.exists_intPoly_aeval_eq_zero` | reduction lemma | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Transcendence.e_transcendental` | `e` transcendental, uncond. | `[…trust base, sorryAx]` | 🚧 1 disclosed `sorry` (analytic crux, in progress) |

**Math-axiom count (🟢+🟡+🟠): 1** — `hermite_lindemann` (🟡, project-scale: proven theorem behind the Lindemann–Weierstrass algebraic part; current frontier, next prerequisite = transcendence of `e` then symmetric-function extension for `π`). No 🔴 anywhere (correct: every headline is unconditional, and the one conditional theorem keeps its hypothesis explicit). One disclosed `sorry` (`e_transcendental`'s crux) — the active chip, not normalized debt.

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest **`HANDOFF-*.md`** · online asks: `ON-LINE-REQUEST.md`
- Frontier files: `NumberTheory/Transcendence/{HermiteLindemann,ETranscendental}.lean`
