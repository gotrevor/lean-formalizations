# DIRECTION — read FIRST (operator directive, 2026-09-04, Trevor via Ren)

## 🎯 THE OBJECTIVE: the Catalan salvage — `src/LeanFormalizations/NumberTheory/Catalan/`

Zhi-Wei Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1 (3 Sep 2026), claims
`G = Σ (-1)^k/(2k+1)^2 ∉ ℚ`.  **The proof is wrong**: a 2-adic bookkeeping error kills §3–§9
(`papers/sun-2026-catalan-irrationality.md` — read it once; the PDF sits beside it).  This thread
builds the machine-checked **conjecture graph** around what survives.  The product is the graph;
the unit of progress is one green node, one green edge (a wiring theorem), or one probe-refuted
node.  Report what the mathematics *says*; the axiom audit is a check, never a headline.

- 🟢 **Node A — Theorem 2.1** (`residual_rank`, engine `resid_rank`): the `(S+3) × S` weighted
  residual matrix has full column rank.  The one clean, correct, self-contained object in the
  paper — proved here for **any** sequence satisfying the recurrence `T_m + T_{m+1} = 1/(2m+1)^2`
  (`IsTailSeq`), then instantiated at the real tails.  ⚠️ The paper's own proof has two index
  slips (expansion base `T_i` vs `T_{i+1}`; a `k = 0` term that is not a polynomial) — the repair
  and the full proof plan are in `Residual.lean`'s header.  **Discharge it.**
- 🟢 **Node B — the 2-adic no-go** (`two_pow_padicValNat_bigF_dvd_NB`,
  `padicValNat_two_bigF_ge`, headline `sun_ledger_impossible`): under `G = a/q` the paper's own
  integer `N_B` is divisible by `2^{v₂(F_B)}` with `v₂(F_B) ≥ B(2B−1) − 2B(⌊log₂ 2B⌋+1)`, and
  some row set makes it nonzero, so `|N_B| → ∞` where Theorem 9.1 needs `|N_B| → 0`.  This is
  the **signpost** (a kernel-checked negation of the refuted route, so nobody re-argues §9).
  It consumes Node A over `ℚ` (Corollary 2.1 gives the nonzero minor).  **Discharge it.**
- 🔴 **Sink — `Irrational catalanConst`.  NOT a target.  Nothing here proves it; no lap may
  claim, imply, or headline it.  Catalan's constant remains open.**
- 🌙 **Frontier question** (Phase 2, only after A and B are green): *what is the weakest open
  node on any path from A to the sink?*

## Phase 1 — the grind (laps start here)

**Frozen statements, guarded BY NAME** (also enforced by the host's `--require-decls`; do not
rename, weaken, generalise-into-restriction, or delete):
`tail`, `catalanConst`, `wtail`, `tail_add_tail_succ` (Tails.lean) · `normaliser`, `IsTailSeq`,
`resid`, `resid_rank` (Residual.lean) · `fakeTail`, `bigF`, `normaliserProd`, `qhat`, `NB`,
`two_pow_padicValNat_bigF_dvd_NB`, `padicValNat_two_bigF_ge` (TwoAdic.lean) · `residual_rank`,
`sun_ledger_impossible`, `fakeTail_eq_tail_of_catalan_eq` (Statement.lean).
If a frozen statement is *wrong* (the planted scaffold was hand-checked, not machine-checked, so
this can happen), FIX it: the fix plus the reason go in the commit message and the HANDOFF, and
the lap says so loudly.  Never route around a wrong statement silently.

**Order** (each is one coherent green checkpoint — commit each; a lap that lands one is a
successful lap):
1. `Tails.lean`: `summable_tailTerm` → `tail_add_tail_succ` → `tail_eq_catalan_sub_partialSum`
   (then `tail_pos`, `tail_lt` if cheap; they are anchors, not on the path).
2. `Residual.lean`, in this order: `IsTailSeq.shift` → `alt_choose_sum_eval_eq_zero` →
   `exists_poly_of_alt_sums_eq_zero` → `no_rational_solution` → **`resid_mulVec_eq_zero`** (the
   crux).  Decompose the crux into NAMED sub-lemmas following the header plan (`D_λ`, `P_λ`,
   the polynomial `K`, its `4B+1` zeros, `deg K ≤ 4B`).  Raising the `sorry` count by splitting
   one fat leaf into named leaves IS progress; a lap succeeds by advancing the crux.
3. `TwoAdic.lean`: `odd_den_mul_fakeTail` → `odd_den_smul_resid` → `odd_den_det` →
   `two_pow_padicValNat_bigF_dvd_NB` → `padicValNat_two_bigF_ge`.
4. `Statement.lean`: `exists_row_set_det_ne_zero` → `fakeTail_eq_tail_of_catalan_eq` →
   `sun_ledger_impossible`.
Steps 1, 3 and 4a are independent of step 2 — if the crux stalls, land those and come back.

**Before the hard part of any lap: commit a compiling skeleton with named `sorry` leaves.**  A lap
that dies with nothing committed loses the hour whatever killed it (an output-token cap kills a
lap the same way a spent window does, and no model switch helps).

## Phase 1 — GREEN (2026-09-04, one lap, merged to `main`)

All seven headlines axiom-clean; every frozen statement char-identical to the scaffold.  Record:
`HANDOFF-2026-09-04-catalan-phase1-green.md`.

## Phase 2 — the moonshot (review laps own this)

### ☠️ Killed thread: N1 alone (2026-09-04, host, `papers/sun-2026-catalan-twoadic-check.py ledger`)

The fake-rational probe was the wrong instrument for the real place (with `G = a/q` the "tails"
do not decay).  With `G` **formal**, `det R[A,J]` is a degree-`≤S` polynomial `P_A(G) ∈ ℚ[G]`
(interpolated exactly); `y_A := P_A/∏_{i<N}Π_i`; `Δ_B` := lcm of `y_A`'s coefficient denominators
(so `Δ_B q^S y_A(a/q) ∈ ℤ` for **every** `a/q`, F_B-free by construction, `v₂(Δ_B) = 0`); and
`|y_A(G)|` at the true `G`, 4000 digits.  Then, minimised over `A`:

    log10|N_B| = log10 Δ_B + log10|y_A(G)|  ≈  +3.4·S·B   and GROWING at every (B,S) tested
    (S=2: 12.8 → 91.0 for B=3..14; S=3: 30.9 → 142.9 for B=4..14).
    Real-place decay ≈ −7.4 B² (log10) against an integerizer ≈ +7.9 B²; both are B², the
    difference is ~ S·B.  No constant fixes this; the construction loses at the odd primes / ∞
    once the 2-adic F_B is removed.

Verdict: **Sun's construction (weights `1/(2m+1)`, normaliser `Π_i`) does not produce small
integer forms, with or without `F_B`.**  N1 is refuted as a repair; N2 (even normaliser) is moot
for the same reason unless it also shrinks `Δ_B` by ~S·B in the log, which nothing suggests.
Re-run: `uv run --with mpmath python3 papers/sun-2026-catalan-twoadic-check.py ledger 14 2`.

### Phase 3 (proposed, awaiting Trevor) — the generic frame, ready for any v2

Everything a v2 (or any Apéry/Nesterenko-style attempt on `G`) needs, stated for a **generic
weight family** so a new construction drops into slots rather than restarting:
- **W (wiring, cheap)**: `irrational_of_small_integer_forms` — if for every `a/q` some `B` gives an
  integer `N_B(a,q) ≠ 0` with `|N_B| < 1`, then `Irrational G`.  The sink edge, once.
- **D (real place)**: the Beta identity `Σ_i (−1)^i C(n,i)/(x+i) = n!/∏_{i≤n}(x+i)` and from it a
  closed form + explicit bound for `Σ_i (−1)^i C(n,i) W_i u_{i+j}` for a generic polynomial
  weight family `W_i`.  Real analysis + combinatorics; the reusable engine.
- **E (integrality)**: for a generic weight family that covers the tail denominators, the entries
  of `R` lie in `(1/Δ)ℤ + (1/Δ)ℤ·G` with `Δ` explicit; hence `det R[A,J] ∈ (1/Δ^S)ℤ[G]`.
- **Frontier Prop** (never a Lean discharge): `∃` weight family with D-bound + E-bound `→ −∞`.
  That is the open problem restated honestly.  For Sun's weights the probe above says NO.
Discharging W, D, E is real Lean work (a lap or two); the payoff is speed of independent
verification when a v2 lands, not a proof of irrationality.

### The original Phase 2 text (kept for provenance)

Sun's stages 3–5 die for a *structural* reason: the `2B` monomial reference columns `i^r` make
the finite-difference transform triangular with pivots `r!`, planting `F_B = ∏_{r<2B} r!`
(`2^{2B²}` of 2-power) in the integer, against a normaliser `∏Π_i` that is entirely odd.  Any
"patch" must change the *construction*, not a constant.  Two levers, each a candidate node:
- **N1 (binomial completion)**: with reference columns `C(i, r)` the transform is unitriangular,
  so the analogue of (3.4) is `det Ã_B = ± det R[A,J]` with NO `F_B` — a true, cheap linear-algebra
  statement.  It removes `F_B` from the 2-adic ledger *and* from the real one, so the real-place
  size of the new integer `N'_B := num(q^S det R[A,J]/∏Π_i)` is the open question.
- **N2 (an even normaliser)**: replace `Π_i` by a family with 2-power content while keeping the
  polynomial-divisibility that Theorem 2.1's proof needs (`(2(i+k)+1)^2 ∣ Π_i` for `1 ≤ k ≤ S`).
**Discipline — paths before roads.**  A Phase-2 node is a `def … : Prop` with a provenance
docstring, an odds estimate, and a **numeric refutation probe** run FIRST:
`papers/sun-2026-catalan-twoadic-check.py` already prints, for a fake `G = a/q`, both the paper's
`N_B` and the `F_B`-free `N'_B` (valuations and digit counts); extend it for N2.  A node whose
probe says the integer *grows* with `B` is refuted — record that as progress (a killed-thread
entry), do not build a road to it.  No asymptotic ledger is to be attempted in Lean.  Do not
propose Lean discharges for Phase-2 nodes; the deliverable there is the stated `Prop` + probe
result + the next story.

## Lane discipline
- Work ONLY in `src/LeanFormalizations/NumberTheory/Catalan/`.  New files get wired into
  `src/LeanFormalizations.lean` (the lib builds only what is reachable from that root).
- **DO NOT TOUCH** any other thread (`Transcendence/`, `Constructible/`, `Curtis/`, `PowerTower/`,
  `Logic/`, `Combinatorics/`, `Kakeya2D/`, `PrimeNumberTheorem/`).  Read them for technique.
- No `axiom`, ever.  `decide +kernel` before `native_decide`; `native_decide` must not touch a
  headline's axiom path.  A disclosed `sorry` in `src/` is a checkpoint; a bare axiom is not.
- Goal end-state for every headline: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
  Run it when you close a real leaf; mention the tier only if it fails.

## Rules (same as every autonomous run here)
- **Commit every green build** from a real `lake build` you saw succeed.  **NEVER push** (the host
  pushes).  Never claim green you didn't see.  Work on the `catalan` branch.
- Toolchain `v4.31.0`, mathlib `v4.31.0`.  Verify lemma names against THIS repo's mathlib
  (`.lake/packages/mathlib`).  `push_neg` is deprecated → `push Not at h`.
- **Reference corpus** (cross-lap memory, NOT auto-loaded):
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` — `ls` it at lap start and
  `grep -rl <keyword>` it before re-deriving any tactic/API friction.
- Blocked needing the open web?  First check `ON-LINE-FINDINGS-*.md`; else append a dated, specific
  item to `ON-LINE-REQUEST.md` and continue on another leaf.  Do not block.
- Keep `HANDOFF.md` current (thin pointer) and write a dated `HANDOFF-<date>-<desc>.md` at lap end;
  on the governor's budget signal, `/handoff` and end the lap.

## NOT a stop condition
No self-stop until Phase 1 is green and axiom-clean.  Do NOT stop because a leaf landed, "to take
stock", or because the crux is hard.  Trevor ends the run.
