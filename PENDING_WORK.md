# PENDING_WORK — lean-formalizations

## 🧘 Reflection — 2026-06-19 (lap 8, deep-reflection lap)

*Altitude pass over the whole expedition. Read STATUS/HANDOFF/PENDING/DIRECTION + git log; re-ran
`#print axioms` on all 12 headlines (every one = bare trust base, 0 math axioms) and re-audited the
growth-theory statements against the math (all faithful). This section is the lap's primary output.*

### Direction call: **SOUND — KEEP GOING.**
The expedition's destination (DIRECTION.md: build the mathlib-only growth theory behind Kirby–Paris,
"`goodsteinLength` grows like `f_{ε₀}`") is **right and substantially achieved**. What's DONE and
axiom-clean: **A1–A4** (fast-growing growth theory incl. `f_{ε₀}` domination, the Kirby–Paris growth
gap); **B1–B3** (Hardy hierarchy); **C1, C2** (the `toOrdinal ↔ ONote.repr` bridge + the Goodstein
descent on `ONote`); and **C3 — the Cichoń identity `goodsteinLength m = H_{seqONote m 0}(2) − 2`**,
whose borrowing crux `hstep_oadd_one_zero` (the heart of Cichoń's theorem) was genuinely discharged.
That is a coherent, novel, mathlib-PR-shaped body of formalization that did not exist anywhere. The
lap-over-lap record is **real forward motion, not circling**: C3 closed (lap 5) → headline reduced to
sub-fact (ii) (lap 6) → sub-fact (ii) at `o=1` + recursion machinery (lap 7).

The honest realistic endpoint: this is an *unbounded* expedition with no finish line. The valuable
artifact already exists; the ONE remaining headline — **diagonal domination `f_o(m) ≤ goodsteinLength
m + 2` for every fixed `o`** — is a genuine multi-lap crux (Cichoń's *lower* bound proper). It is
**not axiomatizable** (anti-smuggling: it *is* the growth content), so it stays a disclosed open
crux, kept off the `sorry` path by stating only the partial results actually proved. Keep banging.

### KEEP doing
- Attacking the **diagonal domination headline** via the reduction already machine-checked in lap 6
  (`goodstein_dominates_of_index` / `goodstein_dominates_of_index_le`): the headline ⟺ **sub-fact
  (ii)** = "the Goodstein descent stays `≥ ω^o` for `≥ m` steps." This reduction is correct and the
  norm-budget obstruction is resolved (`norm_seqONote_le`). Both natural routes (direct count; via
  the Cichoń identity + telescope to a high-budget step) provably collapse to sub-fact (ii) — it is
  irreducible (lap-6 analysis), so this IS the crux.
- Anti-vacuity `native_decide` anchors on every new computable lemma; `#print axioms` on every
  closed theorem; thin faithful headline statements. (All currently in good shape.)

### STOP doing
- **Stop producing further *non-diagonal* lower-bound refinements as the headline lap output.** The
  super-linear → NON-ELEMENTARY ladder (`fastGrowing_ofNat_log_le_goodsteinLength`) is a *complete,
  bankable* result — `goodsteinLength` outgrows every elementary function, proved clean. But it gives
  `f_n` at argument `~log₂ m`, NOT the diagonal `f_n(m)`; pushing it further (to multiply-recursive,
  to `f_ω`, etc.) would **simulate progress without advancing sub-fact (ii)**. That is the fixation
  trap to avoid: don't bag another non-diagonal leaf and call the lap a win.

### Single highest-value next target: **the `o=2` diagonal `f_2(m) ≤ goodsteinLength m + 2`.**
Reasoning: it is the **smallest open instance of the headline** (`o=1` is done), it is concrete and
checkable, and cracking it *forces* building the **steps-between-drops base case** — the technique
that then generalizes to all `o`. Concretely, via `fastGrowing_step_le_goodsteinLength` at a step
`j ≈ m`, the goal needs `(oadd 2 1 0).repr = ω² ≤ (seqONote m j).repr` at a step with budget `j+2 ≥
m`, i.e. **the leading CNF exponent stays `≥ 2` for `≥ m` steps** — equivalently a *super-polynomial
value lower bound* `goodsteinSeq m j ≥ (j+2)²` sustained to `j ≈ m`. The whole gap is the budget
`log₂ m → m`: lap 7's `omega_opow_le_seqONote_repr` already gives `≥ ω²` but only for `j ≤ log₂ m − 2`
(the per-step `leadExp drops ≤ 1` rate bound telescoped from `L₀ = log₂ m`). The truth is leadExp
drops are *rare* — the number of steps between consecutive drops of the leading exponent from level
`E` to `E−1` is itself a Goodstein length of the sub-structure (`≫ m`). The first concrete sub-lemma:
a `dropTime`-style count showing leadExp `≥ 2` persists for `≥ m` steps (induction mirroring
`hardy_oadd_iter`). **Feed Aristotle** a bounded, self-contained carve of this (a slot is free).

*Detailed attack notes for sub-fact (ii) / the steps-between-drops recursion are in the lap-6/lap-7
sections below — unchanged and still the operative plan.*

---

## 🎯 ACTIVE FRONTIER (refreshed 2026-06-19 lap 2 — A4 CLOSED)

**Section A (growth theory of `ONote.fastGrowing`) is COMPLETE + axiom-clean.** A1
(`le_fastGrowing`), A2 (`fastGrowing_monotone`), A3 (`fastGrowing_bachmann_reach`), **A4
(`fastGrowing_lt_fastGrowingε₀`)** all proved. The A4 engine (`Domination.lean`): CNF `norm`,
`lt_fundamentalSequence_of_norm_le` (key cofinality bound), `reaches_of_lt` (general
reachability), `osucc` + strict step. General index monotonicity `fastGrowing_le_of_lt` /
`hardy_le_of_lt` added. `Logic/FastGrowing/*` is sorry-free.

### C2 — the semantic bridge `toOrdinal` ↔ `ONote.repr`  ✅ DONE (2026-06-19 lap 2)
`Logic/Goodstein/Growth.lean` (axiom-clean): `toONote b n` (the computable notation),
`repr_toONote : (toONote b n).repr = toOrdinal b n`, `toONote_NF`, and the descent on `ONote`:
`seqONote m k := toONote (k+2) (goodsteinSeq m k)`, `repr_seqONote = Engine.seqOrd m k`, and
**`seqONote_lt`** (`goodsteinSeq m k ≠ 0 ⟹ seqONote m (k+1) < seqONote m k`). The Goodstein
ε₀-descent now lives on the same `ONote` as the fast-growing growth theory.

### ✅ C3 — `goodsteinLength m = H_{seqONote m 0}(2) − 2`  (the Cichoń identity) — **DONE 2026-06-19 lap 5**
**FULLY PROVED + axiom-clean.** The lone disclosed `sorry` `hstep_oadd_one_zero` (the borrowing
predecessor of `ω^E` — the heart of Cichoń's theorem) is discharged. `goodsteinLength_eq_hardy`,
`hstep_toONote`, `hstep_oadd_one_zero` all have `#print axioms = [propext, Classical.choice,
Quot.sound]`. The close-out used the `Good`/`Canon` frontier invariant (base-`(b+1)` canonical
with ≤1 coeff `=b+1` at the active frontier): `canon_repr`/`canon_round_trip` (round-trip through
`evalNat` via the engine's `toOrdinal` strict monotonicity), `Canon_pred` (a `Good` successor's
predecessor is `Canon`), `Good_fundSeq` (limit descent preserves `Good`), and the general
`hstep_pred_pow` (WF recursion on `repr E`). `src/` is now sorry-free.

### ✅ Hardy ↔ fastGrowing BRIDGE — **DONE 2026-06-19 lap 5** (`Logic/Goodstein/Domination.lean`)
`fastGrowing_le_hardy_pow : NF α → fastGrowing α n ≤ hardy (oadd α 1 0) n` (`f_α ≤ H_{ω^α}`,
**matching args**), axiom-clean. Engine: `hardy_split` (`H_{ω^e·c+R}=H_{ω^e·c}∘H_R` for NF — the
NF condition `repr R < ω^(repr e)` IS the no-absorption side condition, sidestepping general
`ONote.add` additivity); `hardy_oadd_iter` (iteration law `H_{ω^e·(k+1)}=(H_{ω^e})^[k+1]`, via
`hardy_oadd_coeff_step_ne` + the lap-4 `fundSeq_oadd_coeff`); `hardy_finite`, `iterate_le_iterate`,
`succ_iterate`. Also `toOrdinal_two_cofinal` (`∀ NF β, ∃ N, repr β < toOrdinal 2 N`; via
`toOrdinal_pow` building ω-towers). All `#print axioms`-clean; native_decide anchors present.

### ✅ LAP 7 (2026-06-19) — `f_1` DOMINATED unconditionally + the recursion skeleton formalized

Six axiom-clean commits in `Goodstein/Domination.lean`. The growth attack moved from "fully
blocked on sub-fact (ii)" to "level `o = 1` CLOSED + the per-step recursion machinery built":

1. **Growth engine (`bump_gt`):** `b ≤ n → n + 1 ≤ bump b n` — one bump strictly grows a value
   above its base (leading power `b^L ↦ (b+1)^{bump b L} > b^L`). The first real growth fact.
2. **`goodsteinSeq_ge_init`:** `k + 1 ≤ m → m ≤ goodsteinSeq m k` — the value stays `≥ m` for the
   first `m` steps (non-decrease while `≥` base). ⟹ **`omega_le_seqONote_repr`:** the descent
   ordinal stays `≥ ω` for `~m` steps = **sub-fact (ii) at `o = 1`**.
3. **`goodstein_dominates_of_index_le`** (generalized reduction: any telescope step `j`, non-strict
   index, equality ⟹ `rfl`) ⟹ **`fastGrowing_one_le_goodsteinLength`**: `goodsteinLength`
   dominates `f_1` for every `m ≥ 2`, via the full Cichoń pipeline (NOT `native_decide`).
4. **`two_mul_sub_one_le_goodsteinLength`:** `goodsteinLength m ≥ 2m − 1` (value drops by `≤ 1`/step
   — `goodsteinSeq_sub_le` — from the `≥ m` plateau). Beats the old linear `≥ m`.
5. **Recursion skeleton (the path to `o ≥ 2`):** `log_bump` (`log_{b+1}(bump b n) = bump b(log_b n)`
   — *the leading exponent bumps itself*); `log_le_log_pred_succ` (a decrement lowers `Nat.log` by
   `≤ 1`); **`leadExp_drop_le_one`** (leading CNF exponent `L_k` drops by `≤ 1`/step) and
   **`leadExp_ge_of_base_le`** (`L_k` non-decreasing while `L_k ≥ base k`). The full per-step local
   structure of the leading-exponent descent.
6. **Telescope + ordinal bridge:** `leadExp_ge_sub` (`L_i ≥ log₂ m − i`, telescoping
   `leadExp_drop_le_one`); `opow_toOrdinal_log_le` (`ω^(L_i ordinal) ≤ seqOrd`); `opow_le_seqONote_repr`
   (`L_i ≥ k`, `k < base i` ⟹ `ω^k ≤ seqOrd`); **`omega_opow_le_seqONote_repr`** — the descent
   ordinal stays `≥ ω^k` for the first `log₂ m − k` steps (generalizes the `o=1` ordinal bound to
   every `k`). The `seqOrd ≥ ω^k` machinery is now fully built; the ONLY gap to sub-fact (ii) at
   `o = k` is upgrading the step-range from `log₂ m` to `m` — i.e. the steps-between-drops recursion.
7. **CAPSTONE — `goodsteinLength` is SUPER-LINEAR:** `fastGrowing_step_le_goodsteinLength` (the
   non-diagonal reduction: `seqOrd ≥ ω^o` at step `j` ⟹ `f_o(j+2) ≤ goodsteinLength m + 2`, no
   diagonal budget) instantiated at `o=2`, `j=log₂ m − 2` ⟹ **`fastGrowing_two_log_le_goodsteinLength`**:
   `f_2(log₂ m) ≤ goodsteinLength m + 2`, i.e. `goodsteinLength m ≳ m·log₂ m`. First proof it beats
   the polynomial regime. **✅ DONE — generalized to all `n`: `goodsteinLength` is NON-ELEMENTARY.**
   `fastGrowing_ofNat_log_le_goodsteinLength`: `fastGrowing (ofNat n) (L − n + 2) ≤ goodsteinLength
   m + 2` for `1 ≤ m`, `2n ≤ L = log₂ m` (helpers `norm_ofNat`, `ONote.repr_ofNat`, `(ofNat n).NF =
   inferInstance`). The budget is `L − n + 2` not `L` (leadExp ≥ n and budget trade off). Taking
   `n ≈ L/2` gives `goodsteinLength m ≥ f_{L/2}(L/2 + 2)` — a tower of height `~log₂ m`, so
   `goodsteinLength` outgrows every elementary function. Axiom-clean.

   **THE ONE REMAINING DEEP CRUX — the diagonal `f_n(m)` (true domination, the headline):** the gap
   is entirely the budget `L − n → m` (we have `f_n` at argument `~log m`; the headline wants
   argument `m`). This needs the descent to keep `leadExp ≥ n` for `≥ m` steps (not just `~log m`),
   i.e. the **steps-between-leading-exponent-drops = sub-Goodstein-length recursion**. All the local
   machinery (`leadExp_drop_le_one`, `leadExp_ge_of_base_le`, `log_bump`, the ordinal bridges) is the
   running start; the recursion itself (induction on the leading exponent mirroring `hardy_oadd_iter`)
   is the genuine multi-lap obligation.

**THE SHARPENED CRUX (what remains for `o ≥ 2`, i.e. the headline):** the per-step facts give only
a **`log m`-step** guarantee that `L_k ≥ 2` (rate-bound `drop ≤ 1`/step from `L_0 = log_2 m`; and
`leadExp_ge` only holds while `L_k ≥ base k = k+2`, i.e. `k ≲ log m`). The TRUTH is that `L_k`
*drops are RARE*: **the number of steps between consecutive drops of `L_k` from level `E` to `E−1`
is itself a Goodstein length of the sub-structure at level `E`** (astronomically `≫ m`). Formalizing
"steps-between-drops = sub-Goodstein-length" is the genuine recursive heart of Cichoń's lower bound
— the one remaining deep, multi-lap obligation. Concretely: define the drop-time function and prove
a recursion `dropTime(E) ≥` (Goodstein length at level `E−1`), then `L_k ≥ 2` for `≥ m` steps
follows. The local skeleton (lap 7) is the running start; next lap, attack the steps-between-drops
recursion (likely an induction on the leading exponent mirroring `hardy_oadd_iter`).

### 🎯 NEXT CRUX (refreshed 2026-06-19 lap 6): headline REDUCED to one descent-count fact

**Lap-6 result — the headline is now a machine-checked reduction to a single deep fact, and the
budget obstruction is RESOLVED.** Three axiom-clean additions in `Goodstein/Domination.lean`:

1. **`goodstein_dominates_of_index`** — the full Cichoń assembly, verified:
   `o.NF → norm o ≤ m → oadd o 1 0 < seqONote m m → fastGrowing o m ≤ goodsteinLength m + 2`.
   Chain (all banked): telescope at `j=m` (valid by `le_goodsteinLength`) + `hardy_seqONote_zero`
   give `goodsteinLength m + 2 = H_{seqONote m m}(m+2)`; `hardy_le_of_lt` (budget OK at `m+2`)
   lifts `H_{oadd o 1 0}(m+2) ≤ H_{seqONote m m}(m+2)`; bridge `fastGrowing_le_hardy_pow` +
   `fastGrowing_monotone`. **The ONLY open input is the index hypothesis `hidx`.**
2. **`norm_toONote_lt` / `norm_seqONote_le`** — `norm (seqONote m j) ≤ j+1` (a base-`(j+2)`
   numeral has all digits `< j+2`). ⟹ **the Hardy budget `norm ≤ argument` is AUTOMATIC at the
   telescope step `j+2`.** The old "norm obstruction" only ever bit at the *fixed* argument 2;
   evaluated on the descent at step `j+2` it is free, in BOTH comparison directions.
3. **`goodstein_dominates_or_hardy_bound`** (unconditional dichotomy) — for `norm o ≤ m`, EITHER
   `fastGrowing o m ≤ goodsteinLength m + 2` (A, dominates) OR
   `goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m+2)` (B, length Hardy-bounded). Proof: trichotomy
   of `seqONote m m` vs `oadd o 1 0`, budget free both ways.

**⟹ THE HEADLINE ⟺ "branch (B) is eventually empty" ⟺ sub-fact (ii) below.** Nothing else is
missing. native_decide anchors witness the inequality for `o∈{0,1}, m∈{2,3}` (computable regime).

**THE ONE REMAINING DEEP FACT — sub-fact (ii), `oadd o 1 0 < seqONote m m` for large `m`:**
the Goodstein descent stays above `ω^o` for at least `m` steps. Equivalent forms: (a) the drop
time `j*(m) = max{j : seqONote m j > oadd o 1 0}` satisfies `j*(m) ≥ m`; (b) branch (B) fails for
large `m`; (c) `goodsteinLength m + 2 > H_{ω^o}(m+2)` eventually.

**Why it is irreducible (lap-6 analysis — do NOT re-try these dead ends):**
- *Leading-exponent antitone is FREE and USELESS:* for ordinals `α<β ⟹ leadExp α ≤ leadExp β`
  (else `ω^{leadExp α} > β > α ≥ ω^{leadExp α}`), so "leading exp non-increasing on the descent"
  is just a corollary of the strict descent — it gives no step-COUNT.
- *The dichotomy cannot be bootstrapped from the linear bound:* branch (B) gives
  `goodsteinLength m + 2 ≤ H_{ω^o}(m+2)`; combined with `goodsteinLength m ≥ m` only yields
  `m+2 ≤ H_{ω^o}(m+2)` (always true). To kill (B) you need `goodsteinLength m` ABOVE `H_{ω^o}(m+2)`
  — i.e. a **super-linear lower bound on `goodsteinLength`**, which is the growth content itself.
- *`j*(m) → ∞` is provable but too weak:* for fixed `K`, `seqONote m K > oadd o 1 0` for large `m`
  (since `goodsteinSeq m K → ∞` as `m→∞` by bump-monotonicity, and `toOrdinal (K+2)` is cofinal),
  so `j*(m) ≥ K` eventually. But this only gives `f_o(K+2) ≤ goodsteinLength m + 2` (constant LHS)
  ⟹ `goodsteinLength → ∞`, NOT `f_o(m) ≤ goodsteinLength m`. The diagonal `j*(m) ≥ m` is the gap.

**Concrete next-lap attack (the genuine deep content):** a super-linear lower bound on
`goodsteinSeq m j` / on the descent ordinal. The real recursive structure: within one
leading-CNF-level the number of steps is itself a Hardy value (astronomically `>` 1 per level),
so the descent spends `≫ m` steps before the leading exponent falls below `repr o`. Formalizing
"steps-per-CNF-level" is Cichoń's lower bound proper — likely needs an induction on `o` mirroring
`f_{o+1} = f_o`-iterate, or a direct recursive count of `goodsteinLength` restricted to a
threshold. Multi-lap; decompose, checkpoint with a `sorry` only on the count itself.

**OLDER framing (lap 5) — superseded by the lap-6 reduction above but kept for the math:**
The identity gives `goodsteinLength m = H_{toONote 2 m}(2) − 2`; the headline (DIRECTION.md C3) is
"**`goodsteinLength` eventually dominates every `fastGrowing o`**". The diagonal `H_{toONote 2 m}(2)`
has a large *index* but the **argument is fixed at 2**.
**⚠ KEY OBSTRUCTION (found lap 5, the reason this is harder than it looks):** `hardy_le_of_lt`
carries a budget hypothesis `norm α ≤ x`, and Hardy index-monotonicity GENUINELY FAILS at small
fixed argument — measured: `H_ω(2)=5 < H_5(2)=7` although `ω > 5`. So you CANNOT dominate
`H_{toONote 2 m}(2)` by comparing it (via `hardy_le_of_lt`) to a big-coefficient notation like
`ω^o+(m+2)` at arg 2 (its `norm = m+2 > 2`). The naive arg-2 comparison is mathematically WRONG.

**Budget-aware attack paths (next laps):**
1. **Via fastGrowingε₀ + A4.** Relate `goodsteinLength m` to `fastGrowingε₀ m`, then A4
   (`fastGrowing_lt_fastGrowingε₀`, already proved) dominates every `f_o`. Needs the deep half of
   Cichoń: climb the index using the budget the descent itself provides (the bridge `f_α ≤ H_{ω^α}`
   at matching args is the easy half; the missing half converts index-size to argument-size).
2. **Hardy budget-climb.** `H_α(n+k) = H_{α+k}(n)` (finite additive shift — have `hardy_split` +
   `hardy_finite`). Apply `hardy_le_of_lt` only at points along the descent where `norm ≤ arg`
   already holds (the budget grows as the descent proceeds). Trace where the norm budget unlocks.
3. **The `H_{ω^α}=f_α`-style matching-budget correspondence** (the genuine "B4 trap"): mathlib's
   `ω[n]=n+1` shifts the classical identity (`H_ω(n)=2n+1` vs `f_1(n)=2n`; `H_{ω²}(2)=23` vs
   `f_2(2)=8`, not a constant shift). The one-sided `f_α ≤ H_{ω^α}` is done; a reverse bound
   `H_{ω^α}(n) ≤ f_{α+1}(n)` (matching args) would let the diagonal be squeezed.
Bank: bridge + cofinality are the prerequisites; this is a multi-lap crux.

**🔑 THE CONCRETE ENABLER (found lap 5) — the telescope unlocks the budget.** Already proved:
`hardy_seqONote_telescope : j ≤ goodsteinLength m → H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`.
Combined with `hardy_seqONote_zero`: **`goodsteinLength m + 2 = H_{seqONote m j}(j+2)` for ALL
`j ≤ goodsteinLength m`** — so we may evaluate the invariant at a HIGH-budget step `j+2` where
`norm` becomes available. Sketch to finish the headline `f_o(m) ≤ goodsteinLength m + 2`:
- pick `j` with budget `j+2 ≥ max(m, norm(oadd o 1 0))` and `j ≤ goodsteinLength m`;
- `H_{seqONote m j}(j+2) ≥ H_{oadd o 1 0}(j+2)` by `hardy_le_of_lt` (NOW norm-valid: `norm(ω^o)
  ≤ j+2`) **provided `oadd o 1 0 ≤ seqONote m j`** (index lower bound);
- `H_{oadd o 1 0}(j+2) ≥ f_o(j+2) ≥ f_o(m)` by the bridge + `fastGrowing_monotone` (need `j+2 ≥ m`).
**Sub-facts:**
  (i) ✅ **DONE lap 5** — `le_goodsteinLength : m ≤ goodsteinLength m` (`Domination.lean`, via
      `le_bump`+`goodsteinSeq_ge_sub`, axiom-clean). So any `j ≤ m` is a valid telescope step.
  (ii) **the real remaining depth — needs a STRONG term lower bound, NOT the linear one.**
       ⚠ Checked lap 5: at `j = m-2` (budget `m`), `goodsteinSeq m (m-2) ≥ m-(m-2) = 2` only, so
       `seqONote m (m-2)` reads as `finite 2` (repr 2) — FAR below `ω^o`. The linear bound (i) is
       insufficient for the index. **The sweet-spot tension:** small `j` ⇒ huge index but small
       budget (`< m`, bridge needs arg `≥ m`); large `j` ⇒ big budget but tiny index. The needed
       index bound `oadd o 1 0 ≤ seqONote m j` at a `j` with budget `≥ m` requires
       `goodsteinSeq m j ≥ (j+2)^(big)` — a **super-exponential** Goodstein-term lower bound (the
       term IS astronomically large early on). That strong term bound is essentially the growth
       content itself; it is the genuine deep crux. Next-lap target: prove a super-linear lower
       bound on `goodsteinSeq m j` for `j` in the early/middle range (e.g. via `bump b n ≥ n+...`
       or tracking the leading CNF term across steps), enough that `seqONote m j ≥ ω^o` at a
       budget-`≥m` step.

**OLD (pre-2026-06-19-lap5) C3 close-out notes — kept for reference, now all DONE:**
The whole C3 chain was built and the headline held modulo a single isolated lemma. Identity
(native_decide-confirmed): `hardy (seqONote m 0) 2 = goodsteinLength m + 2`. Done across laps 3–5:
- **Intrinsic Hardy machinery** (`FastGrowing/Hardy.lean`, axiom-clean): `hstep` (budget-
  incrementing Hardy step on `ONote`), `hardy_hstep : o≠0 → H_o(n)=H_{hstep o n}(n+1)`,
  `fundamentalSequence_inr_ne_zero`, `hstep_oadd_tail` (peel leading `oadd` term).
- **C3 assembly** (`Goodstein/Growth.lean`): `hstep_seqONote`, `hardy_seqONote_step` (per-step
  invariance), `hardy_seqONote_telescope`, `hardy_seqONote_zero`, `goodsteinLength_eq_hardy`
  (HEADLINE). Helpers `toONote_bump`, `toONote_oadd`, `toONote_single`,
  `fundamentalSequence_oadd_zero_zero`, `hstep_oadd_zero_zero`.
- **The crux `hstep_toONote`** (`hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`): strong
  induction on `p = c·b^L + r`. PROVED: `r≠0` (tail recursion via `hstep_oadd_tail` + IH +
  `toONote_oadd`/`toONote_bump`) and `r=0 ∧ L=0` (finite, `hstep_oadd_zero_zero`).

**THE LONE OPEN CORE: `hstep_oadd_one_zero` (general `L≥1`, `c=1`)** — predecessor of `ω^E`,
`E = toONote b L`. Target: `hstep (oadd (toONote b L) 1 0) b = toONote (b+1) ((b+1)^(bump b L) − 1)`.

**DONE 2026-06-19 lap 4 (4 commits) — crux narrowed `r=0,L≥1` ⟶ this single `c=1` lemma:**
1. **Lemma A (coefficient peel) — PROVED.** `hstep_oadd_coeff` (+ `fundSeq_oadd_coeff`): for
   `E≠0, c≥2`, `hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The `r=0,L≥1`
   branch of `hstep_toONote` is now FULLY PROVED modulo `hstep_oadd_one_zero` (c=1).
2. **Lemma B finite base case — PROVED.** `hstep_oadd_one_zero_finite`: `E = finite(d+1)`,
   `d≤b`, gives `(b+1)^(d+1)−1`. Validates the whole recursion engine end-to-end.
3. **Recursion primitives — PROVED.** `hstep_oadd_one_of_succ`/`_of_limit` (descent on
   `oadd E 1 0`), `fundSeq_oadd_one_of_succ`/`_of_limit`, `hstep_finite_pred`, `fundSeq_finite_succ`.
4. **`evalNat` linchpin — PROVED.** `evalNat b o` (= `repr o` read as base-`(b+1)` numeral);
   `evalNat_toONote : evalNat b (toONote b L) = bump b L`. The general answer is
   `toONote (b+1) ((b+1)^(evalNat b E) − 1)`.

**Remaining (next lap): the general recursion.** WF recursion on `repr E`:
- **Limit case CLEAN** (no reconstruction): `hstep_oadd_one_of_limit` → IH on `f b`, closes via
  `evalNat (f b) = evalNat E` (identity `evalNat_fundSeq`, TODO — at the fixed index `b`).
- **Successor case** needs `evalNat E = evalNat E' + 1` (`evalNat_succ`, TODO) AND the
  reconstruction `toONote (b+1) (evalNat E') = E'` for `E' = pred E`. Reconstruction is the
  real wall: it holds for base-`(b+1)`-CNF `E'` but the descent's `f b` introduces coefficient
  `b+1` (at index `b`). KEY OBSERVATION: that `b+1` is always immediately peeled by
  `hstep_oadd_coeff`, and `pred` of a reachable successor keeps coefficients `< b+1` at the
  decremented position — so a **coefficient-bound invariant** (≤ b+1, with the b+1 only where
  peelable) makes reconstruction go through. Formalize that invariant + the two `evalNat`
  identities, then the WF recursion closes `hstep_oadd_one_zero`.
3. **Aristotle: job `77c99f0e`** still RUNNING on the (pre-narrowing) general borrowing goal —
   if it returns a full proof, it subsumes everything; VERIFY + `#print axioms` before porting.

### Domination corollary (after the C3 identity closes)
With `goodsteinLength_eq_hardy` + A4 (`fastGrowing_lt_fastGrowingε₀`) + `hardy_le_of_lt`, derive
`goodsteinLength` eventually outgrows every `fastGrowing o`; then a thin audit-surface headline.

### B ladder (Hardy) — lower priority
B2/B3 done. **B4** (`H_{ω^α}=f_α`) is a trap under mathlib's `ω[n]=n+1` (measured: not a
constant shift, `H_{ω^2}(2)=23 ≠ f_2(2)+1=9`). Needs a reformulated statement; long-horizon.

---

## 🔭 OPEN-ITEM INVENTORY (refreshed 2026-06-17, operator directive)

`src/` is **100% axiom-free** (0 custom axioms, 0 `sorry`/`admit`; `lake build` green, 8274
jobs). Three threads are COMPLETE + axiom-clean — **do not reopen**: Curtis 1990
(no-Frobenius-formula), π/e-transcendence + squaring-the-circle (the `hermite_lindemann` axiom
was discharged + deleted 2026-06-16), and constructible numbers / Wantzel (full iff + 5 classical
impossibilities). Completion records below.

### ✅ COMPLETE (2026-06-18) — power-tower SHARP `iff` (the `0 < x < e^(-e)` divergence)
**DONE, axiom-clean.** The operator-directed target of the 2026-06-17 `DIRECTION.md` is
finished. `EngineLower.tower_diverges_lower` (`0<x<e^(-e) ⟹ ¬∃L`) + the headline
`Statement.tower_converges_iff_full` (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`) are
both proved; `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The proof followed
the planned route exactly: `fixedpoint_exists` (IVT fixed point `y`), `log_fixedpoint_lt_neg_one`
(the repelling seed `x<e^(-e) ⟹ log y < -1` — by contradiction, `log y ≥ -1 ⟹ y ≥ 1/e ⟹
-ye ≤ -1`, no `v·e^v` monotonicity lemma needed), `strict_two_cycle_exists` (IVT on `g-id`
both sides of `y`, where `g'>1` on a neighbourhood from continuity of `g'` + `g'(y)=(log y)²>1`),
and the even/odd-trapping bound (`a(2n) ≥ γ₀ > β₀ ≥ a(2n+1)`) ⟹ distinct limits ⟹ no limit.
The subsequence construction is now the shared `tower_subseq_limits` (used by both directions).
The Lóczi §3 reference was NOT needed (no `ON-LINE-REQUEST` filed).

### ✅ COMPLETE (2026-06-16) — π/e-transcendence, axiom-clean, `hermite_lindemann` DELETED
`Transcendence.transcendental_pi` proved from first principles, axiom-clean;
`squaring_the_circle_impossible_uncond` rewired to it; the cited axiom deleted → repo
math-axiom count = **0**. Assembly: `ETranscendental.lean` (`e_transcendental`, the Hermite
assembly of `exp_polynomial_approx`) → `PiLindemann.lean` (combinatorial reduction + non-monic
analytic engine) → `MonicRootSums.lean` (fact (a) `sum_aeval_roots_int`, Aristotle `9a19f72e`)
→ `SubsetSumEsymm.lean` (fact (b) `subsetSum_esymm_rational`, fundamental theorem of symmetric
polynomials, Aristotle `b7252abe`) → `PiTranscendental.lean`. Both Aristotle proofs independently
kernel-verified. (For the *alternative* path not taken — adopting mathlib PR #28013 on a future
bump — see `archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`.)


## ✅ COMPLETE (2026-06-14, operator-bounded run): Curtis verification hardening

All four items in `DIRECTION.md` are built, green, sorry-free, axiom-clean
(commits `ea89147`, `0498df8`). Every optional stretch part was also done:

1. ✅ `Boundary.n2_polynomial_relation_exists` — Sylvester hypersurface; n=2/n=3 line.
2. ✅ three new Lemma-2 anchors (⟨3,7,11⟩, ⟨3,13,14⟩, ⟨5,11,23⟩, one also direct) +
   ✅ stretch `frobeniusNumber_6_9_20` (McNugget 43, outside Curtis's family).
3. ✅ `symmetric_guess_not_a_formula` (worked) + ✅ stretch `no_single_polynomial_formula`.
4. ✅ `Curtis/FINDINGS.md` + fixed stale docstrings in `Engine.lean` / `Curtis/README.md`.

Run self-stopped on completion per `DIRECTION.md` (sentinel written). The PARKED targets
below remain Trevor's call for a future, separately-scoped run.

---

## ✅ COMPLETE (2026-06-14, power-tower LOWER half run)

Mandatory `tower_converges_of_mem` (convergence on the FULL Euler interval
`[e^(-e), e^(1/e)]`) is PROVED and **fully axiom-clean** (`[propext,
Classical.choice, Quot.sound]`). The lower-bound crux `two_cycle_collapse` (no
nontrivial 2-cycle of `t↦x^t` for `x ≥ e^(-e)`) is **machine-checked, no axiom** —
via the slope bound `g'(t) ≤ |log x|/e ≤ 1` (`EngineLower.lean`): contraction +
Banach for `x > e^(-e)`, antitone-on-interval for the boundary `x = e^(-e)`.
(The DIRECTION's "subtract the tangent-line inequalities" sketch is mathematically
invalid; the derivative/slope bound is the correct mechanism.)

### Sharp `iff` lower direction (`0 < x < e^(-e)` diverges) — NOW THE ACTIVE TARGET
`tower_converges_iff_full` was omitted as a stretch on the 6-14 run (the convergence half
`tower_converges_of_mem` + `tower_diverges` shipped; the lower divergence requires a *genuine
attracting 2-cycle*, multi-lap real analysis). **As of 2026-06-17 it is the directed goal —
see `DIRECTION.md` and "THE ONE ACTIVE ITEM" at the top.** NO `sorry` was ever left here.

---

## ✅ COMPLETE (2026-06-15): P1 Layer 1 — constructible-numbers algebraic core + all three classical impossibilities

`Geometry/Constructible/` — **PROVED, axiom-clean** (`[propext, Classical.choice,
Quot.sound]` on every headline). Exactly the Layer-1 plan below, and then some:
- `IsSqrtTower` / `IsConstructible` on `IntermediateField ℚ ℝ`; engine
  `IsSqrtTower.finrank_eq_pow_two` (degree `2ⁿ`) via tower law + quadratic step.
- **Doubling the cube**: `cbrt2_not_constructible` (`minpoly ℚ ∛2 = X³−2`,
  Kummer-irreducible; `[ℚ(∛2):ℚ]=3`).
- **Trisecting 60°**: `cos20_not_constructible` (triple-angle ⟹ `2cos20°` root of the
  monic `X³−3X−1`, irreducible by integral-root theorem; degree 3).
- **Squaring the circle**: `squaring_the_circle_impossible (hπ : Transcendental ℚ π)`
  via `IsConstructible.isAlgebraic`. Conditional on `π`-transcendence (mathlib gap).
- Constructibles form a **subfield closed under √** (`IsSqrtTower.sup_exists` +
  `IsConstructible.{add,sub,mul,neg,inv,sqrt}`, `isConstructible_ratCast`).

### ✅ DONE (2026-06-16): P1 Layer 2 + the full converse — Wantzel as an iff
The geometric faithfulness layer is COMPLETE and axiom-clean, and then some:
- `ConstructiblePoint : ℝ×ℝ → Prop` (inductive: `{(0,0),(1,0)}` closed under
  line∩line / line∩circle / circle∩circle). `ConstructiblePoint.isConstructible_coords`
  proves geometry ⟹ algebra via `line_meet_line` / `line_meet_circle` /
  `circle_meet_circle` (`ConstructiblePoint.lean`).
- **Converse** (`Converse.lean`): `AxisConstructible` closed under `+,−,·,⁻¹,/,√` by
  explicit compass constructions; tower induction `isSqrtTower_le_axisField` gives
  algebra ⟹ geometry. Headline `isConstructible_iff_constructiblePoint`.
- Geometric impossibility headlines (`cbrt2_point_not_constructible`,
  `heptagon_point_not_constructible`); positive `isConstructible_cos_pi_div_five`
  (pentagon); heptagon added (`Heptagon.lean`, 5th classical instance).

### ✅ DONE (2026-06-16): squaring-the-circle is now UNCONDITIONAL
`squaring_the_circle_impossible_uncond` no longer takes a hypothesis — it is wired to the
axiom-clean `Transcendence.transcendental_pi` (full Lindemann assembly; see the π completion
record at the top). The "multi-year wall" was discharged from first principles. No axiom remains.

### ✅ DONE (2026-06-16): regular heptagon / 7-gon
`Heptagon.lean` — `twoCosHept_not_constructible`, axiom-clean. Minpoly `X³+X²−2X−1`
derived from `cos(4θ)=cos(3θ)` at `θ=2π/7` (factor out the `c=1` root).

## 🅿️ PARKED — future runs, Trevor's call (NOT this run; do not start)

Preserved for a future, separately-scoped run. These are genuine extensions but are
**explicitly out of scope now** — do NOT treat them as "open frontier" when deciding to stop.

### P2. Upstream Curtis to `Mathlib.NumberTheory.FrobeniusNumber`
mathlib has the n=2 Chicken-McNugget theorem and notes it stops at n=2; Curtis's n=3
impossibility is the natural sequel. Needs a mathlib style pass (drop the bespoke
`IsAdmissible`/audit framing for an idiomatic statement) and an AI-contribution-policy check
(reference corpus: `2026-06-07-mathlib-ai-contribution-policy.md`). Web/CLA-gated.

### P3. Sharpen the "not algebraic" framing
State explicitly: `(s₁,s₂,s₃,g)` lies on no proper hypersurface of ℂ⁴ (graph Zariski-dense).
A short repackaging of `no_polynomial_relation`. (Item 4 of the active run *documents* this;
P3 would be a full theorem-level statement — defer.)

---

## Lemma2.lean lint warnings — LEAVE THEM
The unused-variable warnings on `lemma2`'s hypotheses (`h1,h2,h3,hk_hi,hr_hi`) are the
*mathematical* hypotheses of Curtis's Lemma 2, kept for the audit surface even though this
proof path doesn't consume all of them. Do not strip them. The two unused-simp-arg warnings
are inside Aristotle-verified tactic blocks — not worth the regression risk to touch.

## Aristotle
Nothing genuinely open → Aristotle correctly idle. The old Lemma-1 job (`80d9166c`) is
OBSOLETE (the proof needs no Lemma 1). Do not feed redundant cross-confirms. The verification
items 1–4 are all elementary and do NOT need Aristotle.
