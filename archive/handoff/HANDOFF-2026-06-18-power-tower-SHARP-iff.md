# Handoff: power-tower SHARP iff PROVEN — bounded run complete, repo axiom-free

**Date**: 2026-06-18 · **Branch**: main · **HEAD**: `f51696f` · **MATH AXIOMS: 0**

## 🎯 What this lap did (the operator-directed bounded target)
The 2026-06-17 `DIRECTION.md` asked for **one** thing: finish Euler's power-tower
theorem to the **sharp `iff`** by proving the lower-endpoint divergence
(`0 < x < e^(-e) ⟹ the tower diverges`). **DONE, axiom-clean.** Both MANDATORY
theorems are real proved theorems:

- `EngineLower.tower_diverges_lower {x} (hx0 : 0 < x) (hlt : x < eNegE) : ¬ ∃ L, Tendsto (tower x) atTop (𝓝 L)`
- `Statement.tower_converges_iff_full {x} (hx : 0 < x) : (∃ L, Tendsto (tower x) atTop (𝓝 L)) ↔ x ∈ Set.Icc eNegE eInvE`

`#print axioms tower_converges_iff_full = [propext, Classical.choice, Quot.sound]`.
`lake build` green (8274 jobs), `src/` sorry-free, `grep '^axiom' src/` empty.

## 🧠 How it was proved (the genuine attracting 2-cycle)
The hard half asserts a 2-cycle *exists* (converse of the proven `two_cycle_collapse`).
Route, all in `RealAnalysis/PowerTower/EngineLower.lean`:
1. `fixedpoint_exists` — `f t = x^t` has a fixed point `y ∈ (0,1)` (IVT on `x^t - t`).
2. `log_fixedpoint_lt_neg_one` — **the repelling seed**: `x < e^(-e) ⟹ log y < -1`.
   Clean proof by contradiction: from `y·log x = log y` and `log x < -e`, if `log y ≥ -1`
   then `y = exp(log y) ≥ 1/e`, so `-y·e ≤ -1`, forcing `log y < -y·e ≤ -1` — contradiction.
   (No `v·e^v`-monotonicity lemma needed; this was the one analytic worry and it dissolved.)
3. `strict_two_cycle_exists` — the attracting 2-cycle `β₀ < y < γ₀` (fixed points of `g=f∘f`,
   `x < β₀`, `γ₀ < 1`). Built by IVT on `h = g - id` on **both** sides of `y`: `g' > 1` on a
   neighbourhood of `y` (continuity of `g'` + `g'(y) = (log y)² > 1`) ⟹ `h` strictly increasing
   there ⟹ `h < 0` just left of `y`, `h > 0` just right; pair each with the explicit boundary
   signs `h(1) = x^x - 1 < 0`, `h(x) = x^(x^x) - x > 0`.
4. `tower_diverges_lower` — the even/odd subsequences are trapped on opposite sides
   (`a(2n) ≥ γ₀ > β₀ ≥ a(2n+1)`, by invariance induction using `g` monotone + `g(β₀)=β₀`,
   `g(γ₀)=γ₀`), so their limits `β ≤ β₀ < γ₀ ≤ γ` are distinct ⟹ no overall limit.

The even/odd subsequence construction (limits `β, γ` and the 2-cycle relations) was factored
out of `tower_converges_lower` into **`tower_subseq_limits`** (now needs only `0 < x < 1`; the
endpoint `e^(-e)` enters only via the crux). Both directions build on it.

## ✅ State
- `lake build` green = **8274 jobs** (only the intentional `Curtis/Lemma2.lean` lint warnings).
- `src/` sorry-free; `grep '^axiom' src/` empty; repo carries **0 math axioms**.
- 3 commits this lap (refactor → proof → docs). STATUS.md, both READMEs, PENDING_WORK refreshed.

## 🎬 Next (a NEW target — this thread is DONE)
The power-tower thread is complete and axiom-clean; **do not reopen it.** Open frontier
(see `PENDING_WORK.md` / `STATUS.md`):
- **General Hermite–Lindemann for arbitrary algebraic α** (`log 2`, `cos 1`): the π assembly's
  `no_intPoly_exp_relation` + symmetric-function descent are α-agnostic; a bounded extension.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.

## ⚠️ Gotchas worth carrying
- `strictMonoOn_of_deriv_pos` pins its function `f` from the `ContinuousOn` arg; if you pass a
  `Continuous.sub continuous_id` term, `f` picks up a `Pi.sub`/`id`-lambda form and a later
  `rw [hasDerivAt….deriv]` won't match. Fix: state the `ContinuousOn` with an explicit lambda
  (`have hcont_h : ContinuousOn (fun t => …) … := …`) so `f` is the plain lambda, and build the
  derivative `HasDerivAt` with the same explicit lambda.
- `n ↦ 2n`, `n ↦ 2n+1` tend to `atTop` via `tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id`.

## 📁 Key files
- `RealAnalysis/PowerTower/EngineLower.lean` — `tower_subseq_limits`, `fixedpoint_exists`,
  `log_fixedpoint_lt_neg_one`, `strict_two_cycle_exists`, `tower_diverges_lower`.
- `RealAnalysis/PowerTower/Statement.lean` — headline `tower_converges_iff_full`.
- `STATUS.md` (ledger: 0 axioms) · `PENDING_WORK.md` (active item → complete).
