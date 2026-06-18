# DIRECTION — read FIRST (operator directive, 2026-06-17, Trevor via Ren)

## ⛔ BOUNDED RUN. Prove the power-tower SHARP IFF (the `0 < x < e^(-e)` divergence), then STOP.

The repo is in great shape and you are NOT starting anything new. As of 2026-06-16:
- `src/` is **100% axiom-free** (0 custom axioms, 0 `sorry`/`admit`; `lake build` green, 8274 jobs).
- **Three threads are COMPLETE + axiom-clean — DO NOT TOUCH THEM:**
  - **Curtis 1990** (no-Frobenius-formula) — done.
  - **π/e-transcendence + squaring-the-circle** — the `hermite_lindemann` axiom was *discharged
    and deleted*; π is proved from first principles (full Lindemann assembly, two Aristotle
    facts kernel-verified). **Do not reopen. Do not re-add the axiom. Do not touch
    `NumberTheory/Transcendence/` or `Geometry/Constructible/`.**
  - **Constructible numbers / Wantzel** — full iff + 5 classical impossibilities. Done.

⚠️ The PRIOR restart (2026-06-15/16) drifted: it built the constructible + π threads instead of
this. That work turned out well, but it was **not** the directed goal. THIS is the goal, and it
is the one real mathematical frontier left in the repo.

This run's job: finish Euler's power-tower theorem to the **sharp iff** by proving the
**lower-bound divergence** — for `0 < x < e^(-e)` the tower does NOT converge. This is the
genuinely hard half (it asserts a nontrivial attracting 2-cycle *exists* — the converse of the
already-proven `two_cycle_collapse`, which showed none exists for `x ≥ e^(-e)`). **Expect
several grind laps. That is fine — chip at it lap by lap; do NOT declare it "out of scope" or
wander to a different target.** When the two targets below are proved + axiom-clean, self-stop.

---

## Targets (engine work in `EngineLower.lean`; `Statement.lean` stays the faithful audit surface)

### MANDATORY — the lower divergence + the sharp iff
```lean
/-- Below the lower Euler bound the tower does not converge (a genuine 2-cycle). -/
theorem tower_diverges_lower {x : ℝ} (hx0 : 0 < x) (hlt : x < eNegE) :
    ¬ ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L)

/-- Euler's theorem, SHARP: the infinite power tower converges iff x ∈ [e^(-e), e^(1/e)]. -/
theorem tower_converges_iff_full {x : ℝ} (hx : 0 < x) :
    (∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L)) ↔ x ∈ Set.Icc eNegE eInvE
```
Expose `tower_converges_iff_full` in `Statement.lean` as the new headline, with a faithful
docstring. It stitches three already-proven facts + the one new one:
- `x ∈ [e^(-e), e^(1/e)]` ⟹ converges: `tower_converges_of_mem` (HAVE).
- `x > e^(1/e)` ⟹ diverges: `tower_diverges` (HAVE).
- `0 < x < e^(-e)` ⟹ diverges: `tower_diverges_lower` (the NEW piece).

---

## Proof plan for `tower_diverges_lower` (reuse the existing lower-half machinery)

Everything you need is in `EngineLower.lean`; you are running its argument **in reverse**. Let
`f t = x^t` (antitone, `f_antitone`), `g = f∘f` (increasing, `g_mono`), `y` the unique fixed
point of `f` in `(0,1)`, and `a n = tower x n` with `a (n+2) = g (a n)` (`tower_add_two`).

### A. The fixed point `y` is REPELLING for `x < e^(-e)`
The convergence side proved `g'(t) ≤ |log x|/e ≤ 1` for `x ≥ e^(-e)` (`deriv_bound`,
`hasDeriv_g`). For `x < e^(-e)` you have `|log x| > e`, and *at the fixed point* `y` the slope is
`g'(y) = (log x · y)² ... ` — compute it from `hasDeriv_g`/`hyfix` and show **`g'(y) > 1`**.
(`g'(y) = (f'(y))²` and `f'(y) = y·log x = log y`; so `g'(y) = (log y)²`, and `x < e^(-e)`
forces `log y < -1`, i.e. `(log y)² > 1`.) This is the analytic seed: `y` repels.

### B. A strict 2-cycle `β < y < γ` exists (IVT on `g - id`)
`φ t = g t - t` is continuous on `(0,1)`. `φ y = 0`, and `φ'(y) = g'(y) - 1 > 0` (Part A), so
`φ < 0` just left of `y` and `φ > 0` just right of `y`. With the boundary behavior of `g` on
`(0,1)` (`g` maps into `(0,1)`; near the ends `φ` has the opposite sign), IVT
(`intermediate_value_Ioo`) gives fixed points `β ∈ (0,y)` and `γ ∈ (y,1)` of `g`, with
`β < y < γ`. These are the 2-cycle endpoints (`f β = γ`, `f γ = β` by the same limit identities
used in `tower_converges_lower`).

### C. The tower from `a₀ = 1` lands on the 2-cycle, not on `y` ⟹ no limit
The even/odd subsequences `E n = a(2n)`, `O n = a(2n+1)` are monotone + bounded (as already
constructed for `tower_converges_lower`) and converge to limits `γ' , β'` with `f β' = γ'`,
`f γ' = β'`, `β' ≤ y ≤ γ'`. Show these limits are **strict** (`β' < γ'`) for `x < e^(-e)` —
i.e. NEGATE `two_cycle_collapse`. The clean route: `E 0 = 1 > y` and `E` is antitone bounded
below by `γ` (the Part-B fixed point), so `γ' ≥ γ > y`; symmetrically `β' ≤ β < y`. Hence
`β' < γ'`. Then if the full tower converged to some `L`, both subsequences → `L`, forcing
`β' = γ' = L` — contradiction. (Use `tendsto_of_even_odd` contrapositive.)

### D. Conclude
`tower_diverges_lower` from C; then `tower_converges_iff_full` by stitching (above). Keep the
new lemmas in `EngineLower.lean`; the headline + faithful docstring go in `Statement.lean`.

If the strict-bracket bookkeeping in C is fiddly, the *instability* framing (Lóczi
arXiv:1908.05559 §3) is the rigorous reference — see Rules.

---

## Rules (same as every run here)
- **No `sorry`/`admit` at the end.** A stuck step is a lemma-name/bookkeeping issue — grind it,
  don't bail and don't switch targets. This is a multi-lap proof; partial green progress
  committed each lap is exactly right.
- **Stay in your lane.** Touch ONLY `RealAnalysis/PowerTower/`. Do NOT modify
  `NumberTheory/Transcendence/`, `Geometry/Constructible/`, or `NumericalSemigroups/Curtis/` —
  all complete + axiom-clean. Do NOT re-add any axiom anywhere. Keep the repo at 0 math axioms.
- Verify every lemma name against this repo's mathlib (`v4.29.1`). `push_neg` is deprecated →
  `push Not at h`. Reuse the existing engine helpers (`hasDeriv_g`, `deriv_bound`,
  `two_cycle_collapse`, `tendsto_of_even_odd`, `f_antitone`, `g_mono`, `tower_add_two`,
  `endpoint_fixed_point_lower`, `eNegE`, `eInvE`) wherever they apply.
- Commit every green build (from a real `lake build`). **DO NOT push.**
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web (e.g. the exact mathlib name for a fixed-point/IVT lemma, or
  Lóczi arXiv:1908.05559 §3 for the rigorous instability/2-cycle-existence argument)? Append a
  dated item to `ON-LINE-REQUEST.md` and continue on a different sub-lemma.

---

## Completion = stop condition (`--allow-stop` is armed)

⚠️ **READ THIS — the repo is ALREADY sorry-free and axiom-free. That is NOT your stop
condition.** The `--allow-stop` sorry-gate is open from lap 1, but a lap that self-stops with
`tower_converges_iff_full` still unproven has **FAILED this directive**. Do NOT write the stop
sentinel, and do NOT declare completion, until the two MANDATORY theorems below are real proved
theorems in the source. "Everything builds green" is the starting state, not the goal.

On ANY lap, once ALL hold, certify completion and self-stop (don't churn):
- `tower_diverges_lower` (MANDATORY) is PROVED;
- `tower_converges_iff_full` (MANDATORY headline) is PROVED and exposed in `Statement.lean`;
- `src/` is sorry-free, `lake build` green;
- `#print axioms tower_converges_iff_full` = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no custom axioms, no `native_decide` in the headline path).

Then refresh `STATUS.md` + `HANDOFF.md` + the PowerTower `README.md` + the top `README.md`
table row (power tower → sharp iff complete), commit, and:
```
printf 'source=lap\nreason=power-tower sharp iff complete (converges iff x ∈ [e^-e, e^1/e], axiom-clean)\n' > "$LEAN_STOP_SENTINEL"
```
then end the turn. If a `sorry` lingers or either MANDATORY theorem is unproved, do NOT stop —
finish it.
