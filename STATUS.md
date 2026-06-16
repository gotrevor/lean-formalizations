# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8270 jobs) · **Updated**: review lap · 2026-06-16 · `68ada1e`

## Where it stands
Three independent threads, all building green and `src/` **sorry-free**. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple) and the **power-tower** convergence theorem are complete and fully axiom-clean. The **constructible-numbers / Wantzel** thread is complete as a full iff (algebra ⇔ geometry) with five classical impossibilities + two positive constructions; *squaring the circle* was advanced this lap from "conditional on a `Transcendental ℚ π` hypothesis" to "**unconditional modulo a single cited axiom** (`hermite_lindemann`)". And the **transcendence of `e`** (Hermite 1873) is now **fully proved and axiom-clean** — the assembly of mathlib's analytic part of Lindemann–Weierstrass — discharging the `α=1` instance of `hermite_lindemann`. The remaining frontier is the general `hermite_lindemann` (hence `π`), needing symmetric functions over Galois conjugates.

## What's happened (newest first)
- **2026-06-16 (review lap):** π-transcendence narrowing shipped: stated **Hermite–Lindemann** (nonzero algebraic α ⟹ `exp α` transcendental) as ONE disclosed `axiom`, machine-checked `Transcendental ℚ π` from it (Euler `exp(iπ) = -1`) → `squaring_the_circle_impossible_uncond`. Then **PROVED transcendence of `e`** end-to-end (`ETranscendental.lean`): algebraic reduction + analytic decay/prime-selection + Hermite-polynomial roots + the full integer-`N`/mod-`p` assembly of `exp_polynomial_approx`. `e_transcendental` is `#print axioms`-clean — the α=1 instance of the cited axiom discharged. New dir `NumberTheory/Transcendence/`.
- **2026-06-15 2358/2343:** Constructible/Wantzel thread COMPLETE — full equivalence `isConstructible_iff_constructiblePoint` both directions (forward = degree obstruction; converse = explicit compass arithmetic). 5 impossibilities (cube, trisection, nonagon, heptagon, + geometric-point versions), pentagon positive. All axiom-clean.
- **2026-06-15:** Constructible Layer 1 (algebraic degree engine `IsSqrtTower.finrank_eq_pow_two`) + 3 classical impossibilities; Layer 2 geometric faithfulness bridge.
- **2026-06-14 (operator redirect):** Curtis verification-hardening run (n=2 boundary / Sylvester hypersurface, extra Frobenius anchors, refuted-candidate witness, findings doc) — complete, self-stopped.
- **2026-06-14:** Power-tower convergence on the full Euler interval `[e^(-e), e^(1/e)]` proved + axiom-clean; lower-bound crux `two_cycle_collapse` via slope/Banach (not the invalid tangent-subtraction sketch). Sharp-iff lower direction (`0<x<e^(-e)` diverges) omitted, no sorry.
- **2026-06-14 1511 & earlier:** Curtis crux `substCurve_eq_zero` closed (reformulation bypassing Lemma 1); repo sorry-free + axiom-clean. Engine, Step B, Lemma 2 (Brauer–Shockley, via Aristotle, verified) built.

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **Discharge `hermite_lindemann` for `π`** (general algebraic α): extend the now-proven `e` assembly with symmetric functions over the Galois conjugates of `iπ` (`∏(1 + e^{β_j})`). The reusable core (`exp_polynomial_approx` assembly) is done; the missing piece is the conjugate-product / symmetric-function integrality (mathlib gap). Multi-lap.
### Long-term
- Full Lindemann–Weierstrass (linear independence of `exp` at distinct algebraic exponents) → both `e` (✅ have) and `π` and beyond, fully unconditional squaring-the-circle.
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
| `Transcendence.e_transcendental` (+ `transcendental_exp_{nat,int,rat}`) | `e`, `eⁿ`, `eᵃ`, `e^q` transcendental (Hermite 1873; rational-exponent Hermite–Lindemann), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully proved this lap** |

**Math-axiom count (🟢+🟡+🟠): 1** — `hermite_lindemann` (🟡, project-scale: proven theorem behind the Lindemann–Weierstrass algebraic part; current frontier, next prerequisite = symmetric-function / conjugate-product extension for `π`). The `α=1` instance is now independently discharged (`e_transcendental`). No 🔴 anywhere (every headline unconditional; the one conditional theorem keeps its hypothesis explicit). **Zero `sorry` in `src/`.**

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest **`HANDOFF-*.md`** · online asks: `ON-LINE-REQUEST.md`
- Frontier files: `NumberTheory/Transcendence/{HermiteLindemann,ETranscendental}.lean`
