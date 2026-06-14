# DIRECTION — read FIRST (operator directive, 2026-06-14, Trevor via Ren)

## ⛔ BOUNDED RUN. Prove the power-tower LOWER half, then STOP.

The **upper half** (`x ≥ 1`, endpoint `e^(1/e)`) is COMPLETE and axiom-clean
(`Engine.lean`, `tower_converges` / `tower_diverges` / `tower_converges_iff`). Do
NOT reopen it. Curtis 1990 is also DONE — do not touch it.

This run's job: the **lower half** — convergence of the tower for `e^(-e) ≤ x < 1`,
the *oscillating* regime. This is the genuinely harder half (the sequence is no
longer monotone), but the crux is elementary and rides on the SAME `add_one_le_exp`
trick as the upper half. A full plan is below. **Expect several grind laps** — this
is bigger than the upper half. That is fine; chip at it lap by lap, do not give up
and declare it "out of scope". When `src/` is sorry-free and the mandatory targets
are proved + axiom-clean, self-stop.

### The constant
Add `eNegE : ℝ := Real.exp (-Real.exp 1)` to `Defs.lean` (= `e^(-e) ≈ 0.0659`).
Anchor (machine-check, mirror `endpoint_fixed_point`): `eNegE ^ (Real.exp (-1)) =
Real.exp (-1)` — i.e. at `x = e^(-e)` the fixed point is `y = 1/e`.

---

## Targets (put the engine in a NEW sibling `EngineLower.lean`; keep `Statement.lean` the faithful audit surface)

### MANDATORY — the full convergence interval
```lean
/-- Euler's theorem, convergence direction: the infinite power tower converges for
every `x ∈ [e^(-e), e^(1/e)]`. -/
theorem tower_converges_of_mem {x : ℝ} (hx : x ∈ Set.Icc eNegE eInvE) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L
```
Stitch three cases: `x ≥ 1` (reuse `tower_converges_engine`), `x = 1` trivial, and
the new `e^(-e) ≤ x < 1` lower half. Expose it in `Statement.lean` as the headline
`tower_converges_of_mem` with a faithful docstring.

### STRETCH (OPTIONAL) — upgrade to the sharp iff
```lean
theorem tower_converges_iff_full {x : ℝ} (hx : 0 < x) :
    (∃ L, Tendsto (tower x) atTop (𝓝 L)) ↔ x ∈ Set.Icc eNegE eInvE
```
Needs the two NON-convergence directions: `x > e^(1/e)` (have it — `tower_diverges`)
and `0 < x < e^(-e)` (the genuine 2-cycle — `β < γ`, harder). If the
`x < e^(-e)` direction costs more than ~2 focused laps, **OMIT it** (leave a one-line
note in `PENDING_WORK.md`, NO `sorry`) and ship the mandatory convergence theorem as
the deliverable. Do not let the stretch block self-stop.

---

## Proof plan for the lower half (`e^(-e) ≤ x < 1`) — elementary, no derivatives

Let `f t = x ^ t` and `a n = tower x n`, so `a (n+1) = f (a n)`, `a 0 = 1`.

### A. `f` is continuous and strictly decreasing; unique fixed point `y ∈ (0,1)`
- Continuity of `fun t => x ^ t` for `x > 0`: rewrite `x ^ t = Real.exp (t * Real.log x)`
  (`Real.rpow_def_of_pos`) — continuous as `exp ∘ affine`. (Or find the direct lemma.)
- Strictly decreasing (`0 < x < 1`): `Real.rpow_lt_rpow_of_exponent_gt`
  (verify name/dir: base in `(0,1)`, bigger exponent ⟹ smaller value).
- Fixed point `y`: `φ t = x ^ t - t` is continuous, `φ 0 = 1 > 0`, `φ 1 = x - 1 < 0`
  ⟹ IVT (`intermediate_value_Ioo` / `Icc`) gives `y ∈ (0,1)` with `x ^ y = y`.
  Uniqueness: `φ` strictly decreasing ⟹ at most one zero. Record `hyfix : x ^ y = y`,
  `hy01 : 0 < y ∧ y < 1`, and `hlogy : Real.log y = y * Real.log x` (`Real.log_rpow`).

### B. Even/odd subsequences are monotone + bounded ⟹ converge
`g t = x ^ (x ^ t)` is strictly **increasing** (decreasing ∘ decreasing). Note
`a (n+2) = g (a n)`.
- Even `E n = a (2*n)`: `E 0 = 1`, `E 1 = x^x ≤ 1`, and `g` increasing ⟹ `E`
  antitone (induction). Bounded below by `0`. ⟹ `E n → γ` (use `tendsto_atTop_ciInf`
  on the antitone bounded subsequence; `γ = ⨅ n, E n`).
- Odd `O n = a (2*n+1)`: `O 0 = x`, `O 1 = x^(x^x) ≥ x` (base<1: `x^(x^x) ≥ x^1 ⟺
  x^x ≤ 1`), `g` increasing ⟹ `O` monotone. Bounded above by `1`. ⟹ `O n → β`.
- Limits satisfy `g γ = γ`, `g β = β`, and `f β = γ`, `f γ = β` (take limits in
  `O n = f (E n)` and `E (n+1) = f (O n)`, using continuity of `f`). Also `β ≤ y ≤ γ`.
- The FULL sequence converges ⟺ `β = γ` (even+odd subsequences cover ℕ; if `β = γ`
  then `tower x → β` and `f β = β` ⟹ `β = y` by uniqueness). Lemma:
  `tendsto_of_even_odd` style — `Tendsto (a ∘ (2·)) → c` and `Tendsto (a ∘ (2·+1)) → c`
  ⟹ `Tendsto a atTop (𝓝 c)` (search mathlib; or prove via `Nat.even_or_odd` + ε).

### C. THE CRUX — `β = γ` for `x ≥ e^(-e)` (tangent line = `add_one_le_exp`)
The tangent of `f` at `y`, for ALL `t > 0`:
```
(★)   x ^ t  ≥  y + (Real.log y) * (t - y)
```
Proof of (★): `x ^ t = Real.exp (t * log x)`; with `y = x^y = exp (y * log x)`, write
`x^t = y * Real.exp ((t - y) * log x)`. Set `u = (t - y) * log x`. Then
`(log y)*(t-y) = (y*log x)*(t-y) = y*u`, and `x^t = y*exp u ≥ y*(1+u) = y + (log y)(t-y)`
by `Real.add_one_le_exp u` (times `y > 0`). ∎

Now suppose a strict 2-cycle, `β < γ`, with `f β = γ`, `f γ = β`. Apply (★):
- at `t = γ`:  `x^γ ≥ y + (log y)(γ - y)`, and `x^γ = f γ = β`  ⟹  `β ≥ y + (log y)(γ - y)`.
- at `t = β`:  `x^β ≥ y + (log y)(β - y)`, and `x^β = f β = γ`  ⟹  `γ ≥ y + (log y)(β - y)`.
Subtract:  `β - γ ≥ (log y)(γ - β)`. Since `γ - β > 0`, divide:  `-1 ≥ log y`, i.e.
```
log y ≤ -1   ⟹   y ≤ 1/e   ⟹   log x = (log y)/y ≤ -1/y ≤ -e   ⟹   x ≤ e^(-e).
```
(Last chain: `log y ≤ -1` and `0 < y ≤ 1/e`; `log x = log y / y` from
`log y = y log x`; `log y/y ≤ -1/y` and `-1/y ≤ -e` since `y ≤ 1/e`; then `exp`.)

This contradicts `x > e^(-e)`. Hence **no strict 2-cycle**, so `β = γ`, so the tower
converges to `y`. For the boundary `x = e^(-e)` exactly: `add_one_le_exp` is strict
off `0` (`Real.add_one_lt_exp`, needs `u ≠ 0`), so the subtraction is strict for
`β ≠ γ`, still forcing `β = γ`. (Handle `x = e^(-e)` and `x > e^(-e)` together via
`Real.add_one_lt_exp` on the `t = γ` application where `γ ≠ y`.)

### D. Conclude
Package as `tower_converges_lower {x} (hlo : eNegE ≤ x) (hhi : x < 1) : ∃ L, Tendsto … ∧ x^L = L`,
then stitch with the upper half in `tower_converges_of_mem`.

---

## Rules (same as every run here)
- **No `sorry`/`admit` at the end.** The plan is complete and elementary; a stuck
  step is a lemma-name/bookkeeping issue — grind it, don't bail. Stretch items may be
  OMITTED (deleted + one-line `PENDING_WORK.md` note), never left as `sorry`.
- Verify every lemma name against this repo's mathlib (`v4.29.1`). `push_neg` is
  deprecated → `push Not at h`. Reuse existing engine helpers (`base_le_eInvE`,
  `log_le_div_e`, `eInvE`, `endpoint_fixed_point`) where they apply.
- Engine in `EngineLower.lean` (imports `Defs`); `Statement.lean` delegates and stays
  the faithful audit surface. Add an `eNegE`-anchor + a `native_decide`/`norm_num`
  note documenting the `1/e`-vs-`e^(-e)` trap (Penn's board says `1/e`; the true
  lower bound is `e^(-e)` — `x = 0.1 < 1/e` converges, so `1/e` is wrong).
- Commit every green build (from a real `lake build`). **DO NOT push.**
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web (e.g. the exact mathlib name for even/odd-subsequence
  ⟹ convergence, or Lóczi arXiv:1908.05559 §3 for the rigorous lower-bound argument)?
  Append a dated item to `ON-LINE-REQUEST.md` and continue on something else.

---

## Completion = stop condition (`--allow-stop` is armed)

On ANY lap, once ALL hold, certify completion and self-stop (don't churn):
- `tower_converges_of_mem` (MANDATORY) is PROVED; the lower-half engine is complete;
- `src/` is sorry-free, `lake build` green;
- `#print axioms` on the new headline(s) is `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no custom axioms, no `native_decide` in the headline path);
- the STRETCH iff is either proved OR explicitly omitted-with-a-note (not `sorry`).

Then refresh `HANDOFF.md` + the two READMEs (Status → lower half done) + the top
`README.md` table row, commit, and:
```
printf 'source=lap\nreason=power-tower lower half complete (converges on [e^-e, e^1/e], axiom-clean)\n' > "$LEAN_STOP_SENTINEL"
```
then end the turn. If a `sorry` lingers or `tower_converges_of_mem` is unproved, do
NOT stop — finish it.
