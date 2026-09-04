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

### ☠️ Killed thread: Path 1 positive forms from the EMN motive (2026-09-04, host, `papers/catalan-emn-search.py`)

Eskandari–Murty–Nemoto (arXiv:2510.20648) give `I(F,t) = ∫_Δ F/(1−x²−y²)^{t+1} = a + bG` for
σ-invariant `F` with `x^{2⌈t/2⌉}y^{2⌈t/2⌉} | F`.  Their construction was made exact and general
here (every branch validated to 30 digits against quadrature).  The only non-Dirichlet-trivial
search is over **positive** forms `F = σ-orbit-sum(h²)`, where `I(F,t) = cᵀ(A + BG)c` is an exact
quadratic form and the minimisation is an SVP (LLL).  Scan `N ≤ 20`, `0 ≤ t ≤ 6`: best
`log10(D·I) ≈ −1.16` (`N=16–18, t=3`), never trending to `−∞`; per degree the integral shrinks
like `≈ 10^{−0.35}` (≈ `2^{−1}`) while the exact integerizer grows like `≈ 10^{+0.5}` — the same
factor-of-4-per-degree gap the authors computed from their uniform bound (Remark 8.3.4).  LLL beats
the best single monomial square by ≤ 1 order of magnitude, not exponentially.  Limits: `N ≤ 20`,
float64 LLL (dims ≤ 66).  Positivity via SOS is sufficient, not necessary; a signed family needs a
*proof* of decay (Padé/hypergeometric), which is Path 3's world.  Re-run:
`./papers/catalan-emn-search.py validate && ./papers/catalan-emn-search.py scan 20 6`.

### Phase 3 — ACTIVE (authorized by Trevor 2026-09-04, "dig in!") — the generic frame

**File: `Frame.lean`** (wired into `src/LeanFormalizations.lean`; module docstring carries a
proof plan per leaf; every statement below was hand-derived AND numerically checked before
freezing — D5 to 55 digits, E1 exactly).  The payoff is being the fastest independent verifier
of whatever v2 lands, not a proof of irrationality: **the sink stays a non-target**, `SmallForms`
is a `def … : Prop` and must never become a theorem (the host probe says it is false for these
weights).

**Frozen statements, guarded BY NAME** (host `--require-decls` on `Frame.lean`; do not rename,
weaken, generalise-into-restriction, or delete — if one is WRONG, fix it loudly, per Phase 1):
`irrational_of_forms` · `alt_choose_sum_inv_eq` · `alt_choose_sum_inv_sq_eq` ·
`alt_choose_sum_div_sq` · `redPi` · `resid_tail_eq` · `oddLcm` · `resid_fakeTail_den` ·
`det_resid_fakeTail_den` · `abs_det_ge_of_rational` · `SmallForms` ·
`catalan_irrational_of_smallForms`.

**Order** (each a green checkpoint — commit each):
1. **W**: `irrational_of_forms` (cheap; `Int.one_le_abs` against `Tendsto … (𝓝 0)`).
2. **E**: `oddLcm_pos` → `odd_dvd_oddLcm` → `resid_fakeTail_den` → `det_resid_fakeTail_den` →
   `abs_det_ge_of_rational` → **`catalan_irrational_of_smallForms`** (the sink edge; consumes E3
   + `fakeTail_eq_tail_of_catalan_eq` + `RingHom.map_det`).  Landing the sink edge is the lap's
   headline: it makes "the ledger is the only missing thing, and E3 is its floor" kernel-checked.
3. **D**: `alt_choose_sum_inv_eq` → `alt_choose_sum_inv_sq_eq` → `lin_dvd_bigPi` /
   `redPi_mul_lin` / `natDegree_redPi_le` → `alt_choose_sum_div_sq` → **`resid_tail_eq`**
   (the real-place engine; the swap of `Σ_i` with `∑'_r` is the only analysis).
Steps 1–2 and 3 are independent; if D stalls, land W+E and come back.  Decomposing a fat leaf
into named sub-lemmas is progress.  **No asymptotic estimate is to be attempted in Lean** — the
bound on the RHS of `resid_tail_eq` is a probe question, not a Lean question.

**Before the hard part of any lap: commit a compiling skeleton with named `sorry` leaves.**

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

## Phase 4 — ACTIVE (planted 2026-09-04) — the nearest TRUE theorem: one of β(2),…,β(20) is irrational

**Lane**: *formalizing a known result* (not moonshot).  Directory
`src/LeanFormalizations/NumberTheory/DirichletBeta/`.  Scaffold planted and green; eight `sorry`
leaves remain, and **the headline is already wired**: `Statement.lean` is proof-complete, so
closing the leaves closes the theorem with no further design work.

**The theorem** (Rivoal–Zudilin 2003, Math. Ann. **326** 705–721 / Zudilin 2019 arXiv:1804.09922 §2,
made elementary in the pattern of his SIGMA 2018 odd-zeta paper `papers/zudilin-2018-odd-zeta-elementary.txt`):

    exists_even_beta_irrational : ∃ i ∈ Icc 1 10, Irrational (dirichletBeta (2 * i))

i.e. **at least one of β(2), β(4), …, β(20) is irrational**.  `β(2) = G`, so
`catalan_or_higher_beta_irrational` restates it as "`G` is irrational, or one of β(4),…,β(20) is".
⚠️ This does **not** claim `G ∉ ℚ`; every disjunct is individually open.  Nobody has formalized any
result of this type (reservoir + mathlib swept 2026-09-04).

**The ledger** (`s = 21`, `n` even, `d_n = lcm(1..n) = Nat.lcmUpto n`):

    Rval s n u = 2^{6n}(n!)^{s-3}(3n+1+2u)·(u+3n)!/u! / ∏_{j=0}^{n}((2(n+1+u+j)-1)/2)^s
    rForm s n  = Σ_{u≥0} (-1)^{n+u+1} Rval s n u                       ( = r_n, Zudilin's linear form )
    d_n^21·r_n = A_0 + Σ_{i=1}^{10} A_i β(2i),  A_i ∈ ℤ                (N2)
    r_n < 0                                                            (N3, the crux)
    |r_n| ≤ e^{-21.3 n},   d_n ≤ e^{1.01 n}                            (N4, N5)
    ⇒ |d_n^21 r_n| ≤ e^{(21·1.01 − 21.3)n} = e^{-0.09n} → 0, a nonzero integer form → contradiction.

True rates: `lim|r_n|^{1/n} = e^{-21.657}` and `d_n^{1/n} → e`, so `21 < 21.657` closes with
`0.657/n` to spare; the frozen constants `-21.3` and `1.01` spend part of that margin to keep the
bounds coarse.  **Do not tighten them** — any pair with `21·c₅ < −c₄` works, and the slack is what
makes N4/N5 elementary.

**Frozen names** (guard by name; the shapes are the contract):
- `Beta.lean` — `dirichletBeta`, `summable_betaTerm`, `beta_two_eq_catalanConst`
- `Rational.lean` — `Rval`, `rForm`, `Rval_pos`, `summable_Rval`
- `LinearForm.lean` — `dn`, **`exists_int_combination`** (N2)
- `Integral.lean` — **`rForm_neg`** (N3, the crux), `rForm_ne_zero`
- `Bound.lean` — **`abs_rForm_le_exp`** (N4)
- `Lcm.lean` — **`dn_le_exp`** (N5)
- `Statement.lean` — `exists_irrational_of_forms` (W', proved), `exists_even_beta_irrational`
  (proved from the leaves), `catalan_or_higher_beta_irrational` (proved)

**Order of attack** (easiest first; each is independent):
1. **N5 `dn_le_exp`** — nearly free: `Chebyshev.psi_eq_log_lcmUpto` (mathlib) + `WeakPNT''`
   (`PrimeNumberTheoremAnd.Consequences`) give `log d_n / n → 1`.
2. **`summable_betaTerm`, `beta_two_eq_catalanConst`** — routine; `Catalan/Tails.lean` has the
   summability pattern and `catalanConst = tail 0` is definitionally the same series.
3. **`Rval_pos`, `summable_Rval`** — positivity is `positivity` once the factorials are unfolded;
   summability from the `u^{3n+1−s(n+1)} ≤ u^{-2}` decay.
4. **N2 `exists_int_combination`** — the arithmetic grind: partial fractions of `R_n`, SIGMA
   Lemma 1 integrality `d_n^{s−i}a_{i,k} ∈ ℤ`, odd-`i` vanishing from `R_n(−t−n) = R_n(t)`.
   Only the *existential* is frozen, so any route is fair.
5. **N4 `abs_rForm_le_exp`** — bound `|r_n|` by `poly(n)·max_u|Rval 21 n u|` (legitimate: the
   ledger probe shows max-term rate = exact rate), then explicit factorial/Stirling bounds.
6. **N3 `rForm_neg`** — the crux: the `s`-fold Beta integral
   (`integral_fintype_prod_eq_prod`, binomial series of `(1−T)/(1+T)^{3n+2}`).  Sign convention
   `r_n = −C_n·∫` is **verified numerically** — do not re-derive it from scratch.

**Every frozen statement was validated numerically before planting**, on exactly the hypothesis
range it states (`Odd s`, `Even n`, `3 ≤ s`) — the Phase 3 `E1` lesson.  Probes:
`papers/catalan-beta-validate.py` (integrality, decomposition, the integral at `s=3,n=2`),
`papers/catalan-beta-ledger.py` (rates, odd `s` from 7 to 41 at `n=40`),
`papers/catalan-beta-rval-check.py` (the shifted `Rval` against the source `R_n(ν−½)`: termwise
**exact**).  ⚠️ If a lap finds a frozen statement FALSE, say so loudly and stop that leaf — that
is a result, not a failure (Phase 3 found `E1` false and it was the most valuable thing the lap did).

## NOT a stop condition
Do NOT stop because a leaf landed, "to take stock", or because N3 is hard.  Closing N5 or the
`Beta.lean` pair is a lap's worth of progress on its own.  Trevor ends the run.

## Lane discipline
- Work ONLY in `src/LeanFormalizations/NumberTheory/DirichletBeta/` (Phase 4, the live lane) and
  `src/LeanFormalizations/NumberTheory/Catalan/` (Phases 1–3, green — read, don't churn).  New files get wired into
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
No self-stop until every `sorry` in `src/LeanFormalizations/NumberTheory/DirichletBeta/` is closed
and `exists_even_beta_irrational` is axiom-clean.  Do NOT stop because a leaf landed, "to take
stock", or because N3 is hard.  Trevor ends the run.
