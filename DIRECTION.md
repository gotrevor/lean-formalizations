# DIRECTION — read FIRST (operator directive, 2026-06-14, Trevor via Ren)

## ⛔ BOUNDED RUN. Discharge the two power-tower sorries (upper half), then STOP.

Curtis 1990 is **COMPLETE, axiom-clean, and DONE** — do not reopen, extend, or
re-verify it. Ignore the previous run's items 1–4 (all built last run).

This run has exactly ONE job: finish the **upper half** of the infinite power
tower (Euler 1783) in `src/LeanFormalizations/RealAnalysis/PowerTower/`. Two
`sorry`s remain; both are provable by **elementary** means (NO calculus — no
derivatives, no critical points). A full proof plan is below.

### The target
`Statement.lean` has three load-bearing theorems (keep it the faithful audit
surface — do not weaken any statement) plus a proved anchor:
- `tower_converges` — **`sorry`**, the analytic core. ← discharge this
- `tower_diverges` — **`sorry`**. ← discharge this
- `tower_converges_iff` — already PROVED from the two above (the headline).
- `endpoint_fixed_point : eInvE ^ exp 1 = exp 1` — already PROVED.

`Defs.lean` has `tower x n` (= ⁿx, `^` is `Real.rpow`), `eInvE = exp (1 / exp 1)`
(= e^(1/e)), and `tower_zero/succ/one`. Audit-faithful; don't change the defs.

### Out of scope this run (DO NOT START)
- ❌ The **lower half** `e^(-e) ≤ x < 1` (oscillating regime, 2-cycle stability of
  `g(t)=x^(x^t)`). That is a separate future cycle. Do NOT scaffold it — adding new
  `sorry`s would block self-stop and turn this into an unbounded run.
- ❌ Lambert W, any mathlib upstreaming, any new target.
- ❌ Touching Curtis.

---

## Rules
- **No `sorry`/`admit` left at the end.** If a step resists, keep attacking it —
  the plan below is complete and elementary, so a stuck proof is a lemma-name or
  bookkeeping issue, not a math gap. Grind it.
- **Engine lives in a sibling, `Statement.lean` delegates.** Create
  `RealAnalysis/PowerTower/Engine.lean` (imports `Defs`); put the real proofs there
  as `tower_converges_engine` / `tower_diverges_engine`; then in `Statement.lean`
  replace each `:= by sorry` with `:= tower_converges_engine` (resp. `_diverges_`),
  and `import …PowerTower.Engine`. Mirror the Curtis `Engine`/`Statement` split.
- **Move `endpoint_fixed_point` to `Defs.lean`** (it's a fact about the constant and
  the engine needs it; `Engine` can't import `Statement`). Keep a reference to it in
  `Statement.lean`'s docstring; the theorem name stays the same, just relocated.
- **Verify lemma names against this repo's mathlib** (`v4.29.1`). The names below are
  ~90% right; fix any that don't resolve (the proof shape is the de-risked part).
- **Commit every green build** (from a real `lake build`). **DO NOT push.**
- Reference corpus for mathlib lemma names:
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

---

## Proof plan (elementary, no calculus)

Let `a n := tower x n`, so `a 0 = 1`, `a (n+1) = x ^ a n` (`tower_succ`). The two
proofs share a **monotone** sub-proof and a **no-fixed-point-above-threshold**
lemma. Put shared helpers in `Engine.lean`.

### Shared helper 1 — `log L ≤ L / e` for `L > 0`
The whole "max of `t^(1/t)` is `e^(1/e)`" fact, with no derivatives, straight from
`exp x ≥ x + 1`:
```lean
lemma log_le_div_e {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / Real.exp 1 := by
  have h := Real.add_one_le_exp (Real.log L - 1)       -- (log L - 1) + 1 ≤ exp (log L - 1)
  rw [Real.exp_sub, Real.exp_log hL] at h              -- exp(log L -1) = exp(log L)/exp 1 = L/exp 1
  linarith
```

### Shared helper 2 — a fixed point forces `x ≤ e^(1/e)`
If `x^L = L` with `L > 0` and `x > 0`, then `x ≤ eInvE`. (Take logs: `L·log x =
log L`, so `log x = log L / L ≤ (L/e)/L = 1/e`, then `exp` monotone.)
```lean
lemma base_le_eInvE {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (h : x ^ L = L) :
    x ≤ eInvE := by
  have hlog : L * Real.log x = Real.log L := by
    rw [← Real.log_rpow hx, h]                          -- log (x^L) = L * log x
  have hlogx : Real.log x ≤ 1 / Real.exp 1 := by
    have hd := log_le_div_e hL                          -- log L ≤ L / exp 1
    rw [← hlog] at hd                                   -- L*log x ≤ L/exp 1
    -- divide by L>0:  log x ≤ 1/exp 1
    rw [div_eq_mul_inv] at hd ⊢
    nlinarith [hd, hL, Real.exp_pos 1]                  -- or: cancel L; field_simp/​le_div_iff
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ Real.exp (1 / Real.exp 1) := Real.exp_le_exp.mpr hlogx
    _ = eInvE := rfl
```
(If `nlinarith` is fussy, derive `log x ≤ 1/exp 1` via `le_div_iff hL` /
`(mul_le_mul_left hL)` from `L*log x ≤ L*(1/exp 1)`.)

### Shared helper 3 — monotonicity (holds for `1 ≤ x`)
```lean
lemma tower_mono {x : ℝ} (hx : 1 ≤ x) : Monotone (tower x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa using hx          -- tower x 0 = 1 ≤ x = tower x 1
  | succ k ih =>
      rw [tower_succ, tower_succ]    -- x^(a k) ≤ x^(a (k+1))
      exact Real.rpow_le_rpow_of_exponent_le hx ih
```
(`monotone_nat_of_le_succ` needs `∀ n, a n ≤ a (n+1)`; prove that `∀ n` statement by
induction as above. Adjust if the induction shape needs `∀ n, a n ≤ a (n+1)` proved
as its own lemma first.)

### `tower_converges_engine` (`1 ≤ x ≤ eInvE`)
1. `hmono := tower_mono hx1`.
2. **Bounded by e:** `hbd : ∀ n, tower x n ≤ exp 1` by induction:
   - `n=0`: `tower x 0 = 1 ≤ exp 1` via `Real.one_le_exp (by norm_num)`.
   - `n+1`: `x^(a n) ≤ x^(exp 1) ≤ eInvE^(exp 1) = exp 1`:
     `Real.rpow_le_rpow_of_exponent_le hx1 (ih)` then
     `Real.rpow_le_rpow (by linarith) hx2 (Real.exp_pos 1).le` then `endpoint_fixed_point`.
3. `hbdd : BddAbove (Set.range (tower x)) := ⟨exp 1, by rintro _ ⟨n,rfl⟩; exact hbd n⟩`.
4. `L := ⨆ n, tower x n`; `hL := tendsto_atTop_ciSup hmono hbdd : Tendsto (tower x) atTop (𝓝 L)`.
5. **`x ^ L = L`:**
   - `hshift : Tendsto (fun n => tower x (n+1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)`.
   - `hrpow : Tendsto (fun n => x ^ tower x n) atTop (𝓝 (x ^ L)) :=`
     `Tendsto.rpow tendsto_const_nhds hL (Or.inl (by positivity))`  -- x ≠ 0 (x ≥ 1)
   - `(fun n => tower x (n+1)) = (fun n => x ^ tower x n)` by `funext; rw [tower_succ]`.
   - `tendsto_nhds_unique hshift (this ▸ hrpow)` gives `L = x ^ L`; take `.symm`.
6. **`1 ≤ L`:** `le_ciSup hbdd 0` gives `tower x 0 ≤ L`, and `tower x 0 = 1`.
7. **`L ≤ exp 1`:** `ciSup_le hbd`.
8. `exact ⟨L, hL, ⟨x^L=L⟩, ⟨1≤L⟩, ⟨L≤exp 1⟩⟩`.

### `tower_diverges_engine` (`eInvE < x`)
Here `x > eInvE > 1`. Strategy: monotone + **unbounded** ⇒ `atTop`. Unbounded by
contradiction with the no-fixed-point lemma — NO δ-gap calculus needed.
1. `hx1 : 1 ≤ x := le_of_lt (lt_trans one_lt_eInvE hx)` — you'll need `1 < eInvE`
   (`eInvE = exp(1/exp 1) > exp 0 = 1` since `1/exp 1 > 0`: `Real.one_lt_exp_iff` /
   `Real.exp_lt_exp` + `Real.exp_zero`). Prove a small `one_lt_eInvE` helper.
2. `hmono := tower_mono hx1`.
3. **Unbounded:** `hub : ∀ C, ∃ n, C ≤ tower x n`. Suppose not, i.e. `BddAbove (range)`.
   Then by the SAME steps 4–6 of converges (you can factor a
   `monotone_bdd_has_fixedpoint` helper returning `∃ L, Tendsto ∧ x^L=L ∧ 1≤L`),
   get a fixed point `L ≥ 1 > 0` with `x ^ L = L`. Then `base_le_eInvE` gives
   `x ≤ eInvE`, contradicting `eInvE < x`. So unbounded.
   - Cleanly: prove `¬ BddAbove (Set.range (tower x))`, then unbounded follows
     (`not_bddAbove_iff` on ℝ).
4. **Monotone + unbounded ⇒ atTop:** `tendsto_atTop_atTop_of_monotone hmono hub`
   (or `Monotone.tendsto_atTop_atTop`; or `tendsto_atTop_atTop.2`). Find the exact
   mathlib name; the hypothesis is `∀ b, ∃ n, b ≤ f n`.

### After both engines compile
- Wire `Statement.lean` to delegate (`:= tower_converges_engine` etc.), rebuild green.
- `#print axioms tower_converges_iff` and `#print axioms tower_converges` must be
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. Same for `_diverges`.
- Refresh `RealAnalysis/PowerTower/README.md` Status to DONE, and the top-level
  `README.md` table row (Scaffold → PROVED).

---

## Completion = stop condition (`--allow-stop` is armed)

On **ANY lap** (you need NOT wait for a review/reflect lap), as soon as ALL hold,
certify completion and self-stop — don't keep churning:
- `tower_converges` and `tower_diverges` are PROVED (delegating to the engine),
  `src/` is sorry-free, `lake build` green;
- `#print axioms` on `tower_converges`, `tower_diverges`, `tower_converges_iff` is
  the pure trust base (no `sorryAx`, no custom axioms, no `native_decide`);
- the lower half is correctly NOT started.

Then write your synthesis + refresh `HANDOFF.md`, commit, and:
```
printf 'source=lap\nreason=power-tower upper half complete (tower_converges + tower_diverges proved, axiom-clean)\n' > "$LEAN_STOP_SENTINEL"
```
then end the turn. If a `sorry` lingers, do NOT stop — finish it. This is a small,
fully-specified run; expect to finish in 1–3 grind laps + a review lap.
