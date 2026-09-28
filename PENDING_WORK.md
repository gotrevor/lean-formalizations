# PENDING_WORK — lean-formalizations

## 🔭 PHASE 9 IN PROGRESS (2026-09-28) — `Dubickas2022` (Lemma 6) narrowed to the CZ dichotomy
The open `sorry`s in `src/` are deliberate and are the active crux, both in
`NumberTheory/Transcendence/DubickasNoSubspace.lean`:

* `corvajaZannier_dichotomy` — CZ 2004 main theorem, p. 177 (= Dubickas's Lemma 3).  **The wall**:
  the only `p`-adic-Subspace-Theorem step in the whole repo's Dubickas thread.
* `corvajaZannier_lemma4` — CZ 2004, Lemma 4.  **Not** subspace-strength: a valuation/trace
  argument in `ℚ(α)`; mathlib has `IsDedekindDomain.HeightOneSpectrum` + the number-field trace.
  **Attack this one next.**  The `d = 2` Newton-polygon analysis is written out in
  `PROBE-DUBICKAS-NOSUBSPACE.md`; its `hsmall` hypothesis (every conjugate inside the unit disc or
  of modulus `α`) is already proved at the call site, so a future proof may assume it.
  `ON-LINE-REQUEST.md` (2026-09-28) asks for CZ's own statements/proof before anything lands in
  `Literature/`.  Prerequisites for it that are now **proved** in the same file: `tracePowSum`
  (`= Tr_{ℚ(α)/ℚ}(α^N)`, the power sum over all conjugates), `tracePowSum_rat` (it is rational),
  `tracePowSum_recurrence` (`Σ_{k ≤ d} p_k U_(N+k) = 0` — the linear recurrence the valuation
  argument runs on) and `isIntegral_int_iff_minpoly_den` (the integrality bridge: `α` is an
  algebraic integer iff the coefficients of `minpoly ℚ α` have denominator 1 — the shape in which
  Lemma 4's conclusion arrives).  And the **non-archimedean core of the no-tie case is now proved**:
  `no_bounded_den_of_unique_max_valuation` — in any number field `L`, if one conjugate `z`
  strictly dominates the others at a prime `v` and `v z > 1`, then `q(z^N + Σ_w w^N)` cannot be a
  rational integer for infinitely many `N` (ultrametric equality ⇒ `v = v q · (v z)^N`, unbounded,
  while integers have valuation `≤ 1`); supporting `exists_one_lt_mul_pow`,
  `valuation_multiset_sum_lt`.  **(a) The bridge is now BUILT** (2026-09-28, fourth lap): `conjField α`
  (`adjoin ℚ ((minpoly ℚ α).rootSet ℂ)`) is a `NumberField` by *global* instances, `conjMultiset α`
  is the conjugate multiset there (via `Multiset.pmap` — no `Splits`/`aroots_map` needed),
  `conjMultiset_pow_sum_coe` pushes its power sums down to `tracePowSum`,
  `exists_valuation_one_lt` is the contrapositive of
  `HeightOneSpectrum.mem_integers_of_valuation_le_one`, and **`exists_tie_of_bounded_den`** (proved,
  axiom-clean) concludes: *if `q U_N ∈ ℤ` for infinitely many `N` and `α` is not an algebraic
  integer, then at some prime `v` two **distinct** conjugates share the maximal valuation, which
  is `> 1`.*  **(b) The tie case is therefore the entire residual, and it is now purely local**:
  with the dominant conjugates written `z u_i` (`u_i` a `v`-unit), the hypothesis forces
  `v(Σ_i u_i^N) → 0` along the infinite index set, and one must produce a root-of-unity ratio
  `u_i/u_j` (`p`-adic Skolem–Mahler–Lech).  **That reduction is now DONE too** (`false_of_bounded_den_of_nondegenerate`,
  `isIntegral_of_bounded_den_of_nondegenerate`): Lemma 4's first branch is proved whenever no two
  distinct conjugates of `α` share a power, modulo the **one** local leaf
  `valuation_sum_unit_pow_nondegenerate` (units `u_i`, `k ≥ 2`, no `u_i^l = u_j^l` ⇒ `v(Σ u_i^N)`
  cannot decay geometrically along an infinite exponent set).  **Next attack, ranked:**
  (1) the leaf — classical route is Strassmann's theorem on `ℤ_p` (mathlib has **no** Strassmann /
  `p`-adic Weierstrass preparation: that is the concrete prerequisite to build; for `N = 2^n` the
  tower-growth contradiction is easy once Strassmann is available);
  (2) the **degenerate** branch, which is the other genuine gap — `w^l = w'^l` for distinct
  conjugates gives only `deg(α^l) < deg α` (a descent), and the descent cannot be iterated because
  the exponent set becomes `{N | l N ∈ S}`; CZ's own argument for their `α^l ∈ ℚ` branch is what
  `ON-LINE-REQUEST.md` asks for.

`exists_pisot_pow_pseudoPisot_core` is *proved* from exactly those two: Dubickas's Lemma 5 (both
branches), the `deg α^N ≤ deg α` bound and the "trace eventually nonzero" step are all formalized
(`isPisot_of_pseudoPisotMul`, `otherConj_eq_zero_of_pow_rat`, `eq_rat_of_otherConj_eq_zero`,
`card_otherConj_pow_le`).

**Advance this lap.**  Lemma 6 = Dubickas's Lemma 3 (Corvaja–Zannier's main theorem, subspace) ∨
Lemma 5 (elementary, given CZ's Lemma 4).  The *whole* rational-power case is now unconditional
from `Ridout1957`: new `Diophantine.mahler_mul_of_ridout1957` (Mahler 1957 II **with a positive
integer multiplier**, needed because our approximants are half-integers), then
`exists_pisot_pow_of_rat` / `exists_pisot_pow_of_pow_rat`.  So the residual core may assume
`α^(2^a) ∉ ℚ` for every `a`.

**Refuted this lap** (do not retry): the archimedean Liouville/norm route (it only re-derives
`M(α) ≥ α`, vacuous), and the Böttcher/Mahler-method route (`Φ_c` is not of Mahler-method shape).
Even *degree 1* is Mahler's `‖q(3/2)ⁿ‖` problem, which is why `Ridout1957` was needed there.

**Next attack:** state `CorvajaZannier2004` (pseudo-Pisot dichotomy, their p. 177) — proposal
written out in `PROBE-DUBICKAS-NOSUBSPACE.md`, *not* yet in `Literature/` per DIRECTION — and
split the core into that `Prop` + CZ Lemma 4 + Dubickas Lemma 5.  `hD` stays on the
`Dubickas.lean` headlines until the core is closed; never route a headline through the `sorry`.

## 🏁 THE FRONTIER IS OTHERWISE HYPOTHESES, NOT SORRIES (2026-09-28)
Apart from the phase-9 crux above, `src/` has **no `sorry`, no `admit`, no declared `axiom`**, and every headline is
`[propext, Classical.choice, Quot.sound]`.  So there is no leaf work left: the only fidelity debt
is the *literature hypotheses* carried by the conditional headlines.  Ranked (see
`DIRECTION.md` → CURRENT DIRECTIVE for the binding order):

| hypothesis | carried by | bucket | next prerequisite |
|---|---|---|---|
| `Dubickas2022` (his Lemma 6) | `Transcendence.Dubickas.{transcendental_growth_of_monic_quadratic,theorem1,oeis_constants}` | 🟠 generational | Corvaja–Zannier 2004 ⇒ `p`-adic Subspace Theorem (Schlickewei). mathlib has **nothing**. Chip a prerequisite: heights / places of a number field, or a Roth-shaped statement in the `Literature/Diophantine` idiom. |
| `BakerHarmanPintz2001`, `Matomaki2007` | `Mills.{transcendental_of_four_le,transcendental_or_pisot,irrational_of_ridout}` | 🟡 project-scale | primes in short intervals `[x, x+x^0.525]`; needs a sieve/zero-density layer mathlib lacks. |
| `PrimeBetweenCubesFrom` (Ingham) | `Mills.exists_least_of_primeBetweenCubes` | 🟡 project-scale | `θ(x+x^c)−θ(x) > 0` for `c > 5/8`; the PNTAnd dep is the natural home. |
| `Dubickas2022PisotGap` (his Lemma 8) | **nothing on the headline path any more** — only the paper-faithful `DubickasPisot.c_eq_zero_or_two`, kept for the audit trail | — | DISCHARGED-BY-BYPASS 2026-09-28: `c_eq_zero_or_two_noGap` gets the same conclusion without it. |
| `Ridout1957`, `Ridout1958` | `Diophantine.{mahler_of_ridout1957,ridoutSUnitDen_of_ridout1957,roth_of_ridout1958}` | 🟡 project-scale | same Subspace-Theorem family as Lemma 6; the *edges* off them are already proved (phase 5). |

Non-hypothesis frontiers still registered: **Saito Remark 4.4** (degree-3 Pisot, `Mills/`),
**Catalan phase 2** (probe-first, never claim `G ∉ ℚ`), **no-three-in-line all-`N` `(3/2−ε)N`**
(needs a prime in `[(1−ε)N/2, N/2]`), **Goodstein B4 at limit levels**.

## ✅ Dubickas 2022 phase 8 COMPLETE (2026-09-28) — Lemma 8 dropped, degree-uniform
`c_eq_zero_or_two_noGap` is proved from `Dubickas2022` alone for **every** degree, so
`hG : Dubickas2022PisotGap` is gone from all three `Dubickas.lean` headlines and from
`Comparator/Dubickas/Challenge.lean` (`scripts/comparator-probe Dubickas` → identical).
Route + file map: `PROBE-DUBICKAS-NOGAP.md`.  The decisive reframing: the exact recursion identity
`c = 2 βᴺ S_N + S_N² − S_(2N)` *is* the statement that `E₂(βᴺ's conjugates) = c/2` is **constant**
along the Graeffe tower, and eventual constancy of `E₂` alone forces `c/2 ∈ {0,1}` (via the
parity-weight induction + the `b`-recursion with finite support).  Lemma 8 was only ever supplying a
*lower* bound on `|S_N|`; nothing in the new route wants one.  Nothing to reopen.

## ✅ Dubickas 2022 phase 7 COMPLETE (2026-09-27) — `NumberTheory/Transcendence/` sorry-free, axiom-clean
`transcendental_growth_of_monic_quadratic`, `theorem1`, `oeis_constants` all
`[propext, Classical.choice, Quot.sound]`.  See `HANDOFF-2026-09-27-dubickas-phase7-complete.md`.
Nothing to reopen.  The crux that made it tractable: for `d = 2, a₀ = 1` the recursion is EXACT
(`y_{n+1} = y_n² − c`), so Lemmas 7/10 are unnecessary and (17)/(18) reduce to `c ∈ {0, 2}`; the
degree collapse is `Mills.pisot_degree_bound` at `μ = 1`.

## 🔢 Catalan salvage (branch `catalan`, 2026-09-04) — Phase 3 GREEN (all of Catalan/ sorry-free)
- **Done (lap 2, 2026-09-04):** `Frame.lean` 14/14 leaves, axiom-clean; sink edge
  `catalan_irrational_of_smallForms` kernel-checked.  E1/E2 statements corrected (`S ≤ B` added;
  frozen form refuted by exact probe at `B=0, S=7`).  See `HANDOFF-2026-09-04-catalan-phase3-green.md`.
- **Open (not a Lean question):** `SmallForms` is a `Prop`, numerically false for Sun's weights.
  A corrected construction would replace `resid`/`oddLcm` and re-run the ledger probe.

### (older) Phase 1 GREEN
- **Done:** Theorem 2.1 (`residual_rank`) and the 2-adic no-go (`sun_ledger_impossible`), all
  axiom-clean; see `HANDOFF-2026-09-04-catalan-phase1-green.md`.
- **Open (Phase 2, probe-first, no Lean discharges):** the frontier question — weakest open node on
  a path from A to the sink `Irrational catalanConst`.  N1 (`F_B`-free `N'_B` via binomial reference
  columns): extend `papers/sun-2026-catalan-twoadic-check.py` to report the real-place growth of
  `N'_B` in `B`; N2 (even normaliser): extend the probe first.  A node whose probe says the integer
  grows with `B` is refuted — record that, build no road.
- **⚠️ Nothing in the repo claims Catalan's constant is irrational.**


## 🎉 lap 14 — DONE: HJSW `3(p−1)` no-three-in-line COMPLETE & axiom-clean (`three_mul_pred_le_maxNoThreeInLine`)

The per-prime HJSW headline is **fully machine-checked** (commit `cd5a8ce`, trust base only). Found and
fixed the false lap-13 construction (below), built the genuine half-band pinwheel, and proved the
cross-class slope-`±1` diagonal crux (`pinwheel_diagonal_false`) across all 4 families. ITEM 1 below is
**CLOSED**. **Next frontier = the all-`N` `(3/2−ε)N` corollary** (needs PNT-grade primes near `N/2`;
Bertrand alone gives only ratio `3/4`). See STATUS.md → Short-term. Also minor: `p=2` witness to drop
the `Odd p` hypothesis.

## 🚨 lap 14 (HISTORY) — the lap-13 `pinwheel` construction was FALSE; rewrote to the real HJSW half-band form

**Brute-force discovery (2026-06-19 lap 14):** the lap-13 `Pinwheel.lean` construction — single
hyperbola, four `{0,p}²` translates per residue class, drop ONE corner (keep 3) — is **NOT
no-three-in-line for ANY drop rule**. Verified exhaustively (`/tmp/brute.py`): INFEASIBLE for `p=7`
(all `k`), `p=5` (`k∈{2,3}`). Root cause: the symmetric `{0,p}²` corner layout couples each class to a
`+1`-line partner AND a `−1`-line partner simultaneously, forcing it to break BOTH its `+1` and `−1`
diagonal with a single drop — impossible. So **`pinwheel_exists_noThree` as lap-13 stated it is FALSE**
(a `sorry` on a false statement is a landmine — it could be "closed" by any soundness slip).

**The fix = the genuine HJSW construction with the half-band shift.** The x-translate DIRECTION depends
on the half-band: a left-half class (`a ≤ h=(p−1)/2`) uses columns `{a, a+p}`, a right-half class uses
`{a−p, a}` — then a global `+h` shift lands everything in `[0,2p)`. The dropped corner is in the OUTER
column, opposite `b`'s band. Verified no-three + `card=3(p−1)` + grid `⊂[0,2p)²` for all primes `p≤17`,
all `k` (`/tmp/hjsw.py`). The reflection/general lemmas in `HyperbolaLine.lean` are UNAFFECTED (pure
ZMod p) and are reused verbatim. The no-three proof: slopes 0/∞ safe (residue-uniqueness); slope ±1 via
the σ-reflection — the partner class's three points sit on lines offset by exactly `±p` from the
diagonal, so none lands on it. THIS is the real, now-TRUE crux. See `Pinwheel.lean` rewrite (lap 14).

## 🧭 lap 13 — NO-THREE-IN-LINE: HJSW `3(p−1)` covering UNBLOCKED + scaffolded; crux narrowed to slope-±1 incidence (⚠️ construction was FALSE — see lap-14 note above)

**Findings harvested** (`archive/findings/ON-LINE-FINDINGS-2026-06-19-hjsw-3n2-construction.md`): the
real HJSW construction is a **12-of-16-block "pinwheel"** carved from a single hyperbola `H(k,p)` over
`2p×2p`, NOT stacked arcs. Grid side `N=2p`, `|N_set|=3(p−1)`. Crux is a slope-only argument.

**Done + committed this lap (build 🟢 8299 jobs, all axiom-clean — ONE disclosed crux `sorry`):**
- `HyperbolaLine.lean` (NEW) — **`hyperbola_line_two_congruent`** (the general HJSW Lemma: any
  collinear triple of the full hyperbola `xy≡k` has two CONGRUENT points; determinant collapse ported
  to arbitrary lattice points) + residue/x-residue forms. Plus **both reflection lemmas (HJSW Thm 2
  Step 2)**: `hyperbola_slope_one_reflection` (slope +1 ⇒ the two classes are anti-diagonal reflections
  `r'=−s, s'=−r`, `r·r'=−k`) and `hyperbola_slope_neg_one_reflection` (slope −1 ⇒ main-diagonal
  reflection `r'=s, s'=r`, `r·r'=k`). Pure ZMod p Vieta.
- `Pinwheel.lean` (NEW) — the construction, drop-rule-parametrized (`drop : ℕ → Fin 4` = which of the
  4 corners of each residue class to discard). **`pinwheel_card = 3(p−1)`** and **`pinwheel_grid ⊆
  [0,2p)²`** proved for ANY drop (mechanical, axiom-clean). **`pinCorner_not_collinear`** (3 distinct
  corners of one class are never collinear, `det3=±p²`) discharges the same-class no-three subcase.
  Headline `three_mul_pred_le_maxNoThreeInLine : 3(p−1) ≤ maxNoThreeInLine(2p)` STATED, reduced to the
  one crux below.

### ✅ CLOSED ITEM 1 — the no-three crux. DONE lap 14 (`pinwheel_noThree`, axiom-clean). Text below is HISTORY.
### OPEN ITEM 1 (HISTORY) — `pinwheel_exists_noThree` (the branch HEADLINE crux). STATUS: narrowed, unblocked.
The lone disclosed `sorry`: ∃ a drop-rule making the pinwheel no-three-collinear. **KEY STRUCTURE
(documented in `Pinwheel.lean`):** slopes 0/∞ are AUTOMATICALLY safe (each row/column residue belongs
to a unique class ⇒ ≤2 points), and the general Lemma reduces any collinear triple to "two congruent
(same class) + a third". The same-class subcase is killed by `pinCorner_not_collinear`. **So the crux
is ONLY the cross-class slope-±1 incidence:** choose `drop` so that each class's surviving ±1 diagonal
extends through no kept corner of the OTHER class on that line (the two classes are σ-reflections, by
the Step-2 lemmas already proved). Three attack paths:
1. **Define the HJSW family drop-rule + finish the slope-±1 incidence.** Drop-rule = family of residue
   `(x-half, y-half)` per findings §1.4–1.5 (in [0,2p)² frame: translate the centered HJSW pinwheel).
   Then the no-three proof: apply `hyperbola_line_two_congruent`, case on which corner-pair the two
   congruent points form (slope 0/∞/±1), discharge 0/∞ (unique-class — needs a small "same-y ⇒ same
   x-residue" lemma, ≈ `hyperbolaY_inj_residue` already in `Hyperbola.lean`) and same-class
   (`pinCorner_not_collinear`), then the ±1 case via the reflection lemmas + the family assignment
   forcing complementary slope-families (so only ONE of the two σ-paired classes keeps the on-line
   diagonal). The genuine remaining content; finite once the drop-rule is pinned.
2. **First prove the two reduction lemmas as standalone `Pinwheel` theorems** (slope-0/∞ ⇒ ≤2 pinwheel
   points on the line; the same-class one is done) to convert the monolithic `sorry` into a single
   narrow "±1 cross-class incidence" `sorry` — cheaper checkpoint, sets up path 1.
3. **Per-prime → all-N corollary** (independent, bankable): once item 1 lands, `(3/2−ε)N ≤
   maxNoThreeInLine N` for all large N via mathlib's PNT (pick prime `p≈N/2`); or state headline only
   at `N=2p`.

### OPEN ITEM 2 — Goodstein general limit-α B4 `H_{ω^α}(n)+1 = f_{α[n]}(n+1)`. STATUS: open, marginal.
Pattern proven at `ω^ω` (`hardy_omega_pow_omega`); finite-k done (`hardy_omega_pow_ofNat`). The
charter headline (`grows like f_{ε₀}`) is already delivered, so this is a sharpening. Three paths:
1. **Well-founded induction on α** with a non-uniform RHS index (succ vs limit α split): limit case
   peels `(ω^α)[n]=ω^{α[n]}` (brick `fundamentalSequence_omega_pow_limit`) → B4 at smaller `α[n]`;
   succ case is finite-B4's step via `hardy_oadd_coeff`. Fiddly; NB Hardy.lean edits re-run ~4–5 min
   `native_decide`.
2. **Next concrete level only** — B4 at `ω^{ω+1}` or `ω^{ω·2}` (specific limits past `ω^ω`),
   mirroring the `ω^ω` proof; cheaper, incremental.
3. **Inequality sandwich** instead of the exact (succ/limit-uniform) identity, if the exact form
   stays awkward.

### OPEN ITEM 3 — Goodstein strict domination (remove the `+2`). STATUS: open.
`f_o(m) ≤ goodsteinLength m + 2` → tighten. The `+2` is the Cichoń `H(2)−2` offset; A3 index
monotonicity is now CLOSED (`fastGrowing_bachmann_reach`), so the old "A3-hard" blocker is gone.
Paths: (1) trace where `+2` enters `GrowthStatement`/`TowerDomination` and see if a sharper seed
bound removes it; (2) prove a strict variant on a cofinal subsequence; (3) leave as-is (the
two-sided headline already holds with `+2`).

---

## 🎉🎉🎉 lap 11 — CICHOŃ'S LOWER BOUND COMPLETE TO ε₀: f_o(m) ≤ goodsteinLength m + 2 for EVERY o < ε₀

**Done + committed (`4856b9a` tower spine, `9b1e779` full ε₀); build 🟢 (8294 jobs).** New file
`src/LeanFormalizations/Logic/Goodstein/TowerDomination.lean`. The diagonal lower-bound headline —
the genuine Cichoń growth content — is now **complete for every ordinal below ε₀**:
- **`goodsteinLength_eventually_dominates_fastGrowing`** (`o.NF → ∃ N, ∀ m≥N, f_o(m) ≤ goodsteinLength m + 2`).
- `fastGrowing_towerO_le_goodsteinLength` (every tower level `ω↑↑k`); explicit threshold
  `goodsteinLength_dominates_fastGrowing_towerO` (`m ≥ towerN k (2^16+k)`).
- `fastGrowing_le_goodsteinLength_of_repr_le_tower` (any `o` with `repr o ≤ ω↑↑k`).

**The two general engines (each subsumes lap-10's per-level closures):**
1. **General length bootstrap** `two_mul_le_goodsteinLength_iter`: `goodsteinLength((log₂)^[k] m) ≥ 2m`
   for ALL `k`. The lap-10 worry ("needs `f_{ω^ω}`-strength deep-seed bound") was **FALSE** — the
   already-proved `o=ω` domination is strong enough at every depth. Carrier: the clean finite-level
   tower bound `towerN_le_fastGrowing` (`f_{k+2}(t) ≥ towerN(k+1)(t+1)`, induction on `k` via
   `f_{n+1}=(f_n)^[·]` + iterate-monotone), composed with `f_ω(t)=f_{t+1}(t) ≥ f_{k+2}(t)`. Plus the
   tower upper bound on the seed `succ_le_towerN_log_iter` (`m+1 ≤ towerN k ((log₂)^[k] m + 1)`).
2. **General ordinal bridge** `omegaTower_succ_le_seqONote_repr`: descent `≥ ω↑↑(k+1)` from the
   `k`-fold leading exponent in the large regime. Pure `toOrdinal` induction `omegaTower_le_toOrdinal`.
3. **Tower cofinality in ε₀** `exists_repr_lt_omegaTower` (axiom-clean): every NF `ONote` has
   `repr < ω↑↑k` for some `k` (structural induction + additive principality of `ω^·`). This is what
   lifts the tower-spine result to ALL of ε₀.

Crux discharged via the self-similarity tower `iterLeadExp_dominates` read at a fixed index
(`logSeq_iterate_apply`) feeding `n_le_goodsteinSeq` the bootstrap length bound. `#print axioms`:
trust base + finite-base-case `native_decide` (engines fully clean); no sorry.

**UPPER bound also landed this lap (two-sided "grows like f_{ε₀}" COMPLETE):**
- `hardy_le_fastGrowing` (`Logic/FastGrowing/Hardy.lean`, axiom-clean): `hardy o n ≤ fastGrowing o n`
  for `n≥2` — Hardy never outruns fast-growing at the same ordinal index (well-founded recursion on
  the notation; successor case `H_a(n+1) ≤ f_a(n+1) ≤ f_a(f_a n) = (f_a)^[2]n ≤ (f_a)^[n]n`).
- `goodsteinLength_le_fastGrowing_ordinal` (`GrowthStatement.lean`, **fully axiom-clean**, no
  native_decide): `goodsteinLength m + 2 ≤ f_{o_m}(2)` (`o_m = seqONote m 0`). Immediate from the
  Cichoń identity `hardy_seqONote_zero` + `hardy_le_fastGrowing`.
- C3 audit surface `GrowthStatement.lean` + faithfulness anchor `fastGrowingε₀_eq_towerO` (our
  `towerO` IS mathlib's ε₀ fundamental sequence: `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`).

### 🎯 NEXT FRONTIER — B4 (`H_{ω^α} = f_α`), the last charter ladder item — WALL MAPPED (lap 11)
The two-sided growth theorem is DONE; the charter ladder A–C is complete. The remaining explicit
charter target is **B4: the classical identity `H_{ω^α} = f_α`** (flagged "long-horizon trap under
mathlib's `ω[n]=n+1`"). **Lap 11 reconnaissance (measured with `native_decide`/`#eval`) pinned the
exact behavior — record before re-attacking:**

- **The offset is `+1`, and the clean form is `H_{ω^α}(n) + 1 = f_α(n+1)`.** MEASURED and CONFIRMED at
  α = 0, 1, 2 (finite):
  - α=0: `H_{ω^0}(n)=H_1(n)=n+1`, `f_0(n+1)=n+2` → `H+1 = f_0(n+1)` ✓.
  - α=1: `H_ω(n)=2n+1`, `f_1(n+1)=2n+2` → `2n+1+1 = 2n+2` ✓.
  - α=2: `H_{ω^2}(n) = 2^{n+1}(n+1)−1 = f_2(n+1)−1` ✓ (e.g. n=2: H=23, f_2(3)=24).
- **BUT THE CLEAN FORM IS FALSE AT LIMIT α.** MEASURED at α=ω (i.e. `ω^ω`): `H_{ω^ω}(1)+1 = 8` while
  `f_ω(2) = 2048` — NOT equal. Root cause (from the induction): for limit α with fund. seq. `q`,
  `H_{ω^α}(n) = H_{ω^{q n}}(n)` (index `n`) but `f_α(n+1) = f_{q(n+1)}(n+1)` (index `n+1`) — the
  `ω[n]=n+1` shift makes the two pick DIFFERENT tower levels (`q n` vs `q(n+1)`). So the naive offset
  identity does NOT generalize past successor exponents. This IS the charter's "trap."
- **Consequences / correct next attack:**
  - A *restricted* B4 `H_{ω^k}(n)+1 = f_k(n+1)` for FINITE k (α = ofNat k) is TRUE (measured) and is a
    legitimate bankable target — but even its successor step `k→k+1` needs the **coefficient lemma**
    `H_{ω^β·j}(n) = (H_{ω^β})^[j](n)` (since `(ω^{k+1})[n] = ω^k·(n+1)`). **This coefficient lemma is
    MEASURED+VERIFIED true** (lap 11: `H_{ω·2}=(H_ω)^[2]`, `H_{ω·3}=(H_ω)^[3]` exact). Its proof (by
    induction on j) needs, in the step, `H_{ω^β·(j-1)+(ω^β)[n]}(n) = H_{ω^β·(j-1)}(H_{ω^β}(n))` — i.e.
    the **Hardy additive law `H_{α+γ}(n) = H_α(H_γ(n))` for non-absorbing γ** (γ's CNF terms `≤` α's
    trailing term). NOTE the absorption caveat: the *general* `H_{α+β}=H_α∘H_β` is FALSE
    (`1+ω=ω` ⇒ `H_{1+ω}=H_ω` but `H_1∘H_ω ≠ H_ω`); only the non-absorbing form holds.
  - **ROOT BRICK = the non-absorbing Hardy additive law — ✅ DONE (lap 11, `5bf832f`, axiom-clean):**
    `hardy_oadd_tail (a m b n) : hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)` in
    `Logic/FastGrowing/Hardy.lean`. Tail-peeling by well-founded recursion on `b`; no ONote-addition
    machinery needed (the fund-seq def at `Notation.lean:922` already acts on the tail).
  - **✅ DONE (lap 11, `6a63e12`, all axiom-clean):** the coefficient lemma `hardy_oadd_coeff`
    (`H_{ω^β·j}=(H_{ω^β})^[j]`, β≠0) via `hardy_oadd_coeff_step`; the transfer `iterate_offset`; and
    **FINITE B4 `hardy_omega_pow_ofNat`: `H_{ω^k}(n)+1 = f_k(n+1)`** for every finite k. All in
    `Logic/FastGrowing/Hardy.lean`, with a `native_decide` anti-vacuity anchor (`H_{ω^2}(2)+1=24=f_2(3)`).
  - **B4 at LIMIT α — first limit DONE (`558e5bd`):** `hardy_omega_pow_omega`:
    `H_{ω^ω}(n)+1 = f_{n+1}(n+1)` (axiom-clean). The clean `H_{ω^α}(n)+1=f_α(n+1)` is FALSE at limit α
    (`H_{ω^ω}(1)+1=8≠f_ω(2)=2048`); the TRUE limit form reads off the fund seq: `(ω^ω)[n]=ω^{n+1}` ⇒
    `H_{ω^ω}(n)=H_{ω^{n+1}}(n) = f_{n+1}(n+1)−1` by finite B4. **General limit-α pattern (next lap if
    wanted):** `H_{ω^α}(n)+1 = f_{α[n]}(n+1)` for limit α (same `(ω^α)[n]=ω^{α[n]}` peel + finite/IH);
    a uniform B4 statement is non-uniform across succ/limit α — provable but fiddly, and the charter
    "grows like `f_{ε₀}`" is already delivered by finite B4 + the two-sided growth theorem.
  - For limit α, do NOT chase the clean identity (false). The honest general statement is likely an
    *inequality* sandwich or a statement along the successor-α cofinal subsequence only.
  - `hardy_le_fastGrowing` (lap 11, axiom-clean) already gives the `≤`-at-same-index half generally.
**Optional sharpenings** (lower priority): strict domination removing the `+2` (needs general index
monotonicity = A3-hard); a single ε₀ capstone via `ε₀ = sup_o repr o` (presentation).

---

## 🎉🎉 lap 10 — CLIMBED THE LIMIT LEVELS: o=ω, o=ω^j (all finite j), o=ω^ω all CLOSED
### (SUPERSEDED by lap 11's general `TowerDomination.lean` — kept for the engine writeup)

**Done + committed (`ca30077`, `69550cd`, `df89a28`, `1278df6`, `1fb59f8`); build 🟢 (8293 jobs).**
In one lap the diagonal domination `f_o(m) ≤ goodsteinLength m + 2` went from finite-`o`-only to
**every `o` up to `ω^ω`**, all unconditional + machine-checked:
- `fastGrowing_omega_le_goodsteinLength` (o=ω, m≥2^16) — `DominationOmega.lean`.
- `fastGrowing_omega_pow_le_goodsteinLength` (o=ω^j, all finite j≥1).
- `fastGrowing_omega_pow_omega_le_goodsteinLength` (o=ω^ω).

**The two engines (reusable):**
1. **The self-similarity TOWER** (`GoodsteinLike.lean`, axiom-clean): `GoodsteinLike a` (the Goodstein
   lower-bound recursion); `goodsteinLike_logSeq` (leading exponent of a Goodstein-like seq is
   Goodstein-like); `iterLeadExp_dominates m j` (the `j`-fold iterated leading exponent dominates
   `goodsteinSeq ((log₂)^[j] m)`). This is the precise self-reference: level-`j` leadExp ≥ a Goodstein
   value seeded at the `j`-fold log of `m`.
2. **The length BOOTSTRAP** (`two_mul_le_goodsteinLength_loglog`): `goodsteinLength ((log₂)^[2] m) ≥ 2m`,
   proved by bootstrapping `o=ω` against itself — `goodsteinLength t ≥ f_ω(t)−2 = f_{t+1}(t)−2 ≥
   f_3(t)−2 ≥ 2^{2^t·t}−2 ≥ 2(m+1)−2` (`fastGrowing_omega_eq` + `fastGrowing_ofNat_mono` +
   `two_pow_le_fastGrowing_ofNat_three`). The `f_ω` length bound is *tower-strength* — that's what
   lifts the leading exponent into the LARGE regime at the deep seed.

**Ordinal bridges built (`DominationOmega.lean`):** `omega_omega_le_seqONote_repr` (ω^ω from leadExp≥base),
`opow_le_toOrdinal` + `omega_pow_pow_le_seqONote_repr` (ω^{ω^j} from secondLeadExp≥j),
`omega_omega_le_toOrdinal` + `omega_pow_omega_le_seqONote_repr` (ω^{ω^ω} from secondLeadExp≥base).

### 🎯 NEXT FRONTIER — the FULL tower up to ε₀ (`ω^{ω^ω}`, …, `ε₀`)
The pattern is now self-propelling and should be made GENERAL (one induction, not per-level):
  - **General ordinal bridge:** `descent ≥ ω^β` from `β ≤ toOrdinal (base i) (leadExp_i)` (have the
    pieces: `opow_le_toOrdinal`, `omega_omega_le_toOrdinal`, `opow_toOrdinal_log_le`). Induct on
    ω-tower height `k` to get `descent ≥ ω↑↑(k+1)` from the `k`-th leadExp in the large regime.
  - **General length bootstrap:** `goodsteinLength ((log₂)^[k] m) ≥ 2m` by induction on `k`, using the
    previous level's domination as the length bound. The recursive crux is a fastGrowing lower bound
    `f_{tower_{k-1}}(t) ≥ 2m` — iterate `two_pow_le_fastGrowing_ofNat_three`/index-monotonicity. THIS
    is the genuinely hard recursive piece; everything else is mechanical.
  - Concrete next rung if not general: **o = ω^{ω^ω}** needs the THIRD leadExp in large regime, hence
    `goodsteinLength ((log₂)^[3] m) ≥ 2m` — bootstrap `o=ω^ω` (already proved) at the triple-log seed.
  - Good Aristotle candidate: the recursive fastGrowing lower bound (bounded, self-contained).

---

## 🎉 lap 9 — DIAGONAL DOMINATION CLOSED for all finite levels (the 8-lap crux)

**Done + committed (`da05776`, `9b186a8`); build 🟢 (8291 jobs).** The headline open problem —
`f_o(m) ≤ goodsteinLength m + 2` (sub-fact (ii), Cichoń's lower bound) — is **PROVED for every finite
`o`**: `fastGrowing_ofNat_le_goodsteinLength (16 ≤ m) (n+1 ≤ log₂ m)` and the qualitative
`goodsteinLength_dominates_fastGrowing_ofNat : ∀ n, ∃ N, ∀ m ≥ N, f_n(m) ≤ goodsteinLength m + 2`.

**The winning idea (what 8 laps were missing): SELF-SIMILARITY.** The leading-exponent sequence
`L_k = log_{base k}(G_k)` is itself a Goodstein-like descent (`L_{k+1} ≥ bump(base k) L_k − 1`,
`leadExp_step_ge`), so it **dominates the genuine Goodstein sequence seeded at `log₂ m`**
(`leadExp_ge_goodsteinSeq_log`, using `bump_mono` via the `toOrdinal` bridge). This converts "leadExp
stays `≥ n` for `m` steps" into "`goodsteinLength(log₂ m) ≥ m + n`" — one scale down. A strong
induction (`goodsteinLength_exp_lower`, step `exp_le_goodsteinLength_step`) makes the exponential
length bound `goodsteinLength m ≥ 2^{m+1}+m` **reproduce itself** at each scale; it bottoms out at the
finite computational base cases `goodsteinLength M ≥ 2^{M+1}+M` (`4≤M<16`) discharged by the
tail-recursive evaluator `gpos` under `native_decide`. General `o` from the small-regime termination
law (`goodsteinLength_le_of_small` → `n_le_goodsteinSeq`). Engine axiom-clean; unconditional closures
carry `Lean.ofReduceBool` (finite base computation).

### ❌ SUPERSEDED — do NOT pursue
- **The `ppCount` sparsity bound `ppCount m m ≤ log₂ m − 2`** (lap-8 "next brick"). The self-similarity
  recursion is a cleaner, COMPLETE route to the same `o=2` (and all finite `o`); the sparsity bound is
  no longer needed. `ppCount` + `leadExp_ge_sub_ppCount` remain in `Domination.lean` as harmless
  characterization lemmas but are off the closing path. Don't re-attack the sparsity bound.

### 🎯 NEXT FRONTIER — transfinite `o`, starting `o = ω` (toward `f_{ε₀}`)
The finite-`o` diagonal is closed. The expedition's destination (`goodsteinLength ~ f_{ε₀}`) now needs
**limit ordinals**. The smallest open instance: `f_ω(m) ≤ goodsteinLength m + 2`.

**The precise crux.** `f_ω` needs the descent ordinal `≥ ω^ω = (oadd ω 1 0).repr` at step `j ≈ m`,
i.e. `toOrdinal(base j)(G_j) ≥ ω^ω`. Since `toOrdinal b v = ω^(toOrdinal b (log_b v))·c + …`, this
requires `toOrdinal(base j)(leadExp_j) ≥ ω`, i.e. **`leadExp_j ≥ base j` at `j ≈ m`** — the leading
exponent must stay in the LARGE regime (`≥ base`) for `~m` steps, not just `≥ n`. Via self-similarity
`leadExp_k ≥ goodsteinSeq(log₂ m) k`, this needs the *lower* sequence's VALUE `≥ base k = k+2` at
`k ≈ m` — i.e. the lower Goodstein sequence (seed `log₂ m`) is itself still in its large regime at step
`m`. That is one more recursion of the SAME self-similarity (the lower sequence's leadExp dominates
`goodsteinSeq(log₂ log₂ m)`, …). Attack paths:
  (a) **Iterate self-similarity.** Generalize `leadExp_ge_goodsteinSeq_log` to a 2-level statement:
      `leadExp_k(m) ≥ goodsteinSeq(log₂ m) k`, and the value `goodsteinSeq(log₂ m) k ≥ base k` while
      `goodsteinSeq(log₂ m)` is in ITS large regime — bounded below by a length bound on
      `log₂ log₂ m`. Likely needs an `ω`-level analog of `goodsteinLength_exp_lower` (a doubly-iterated
      length bound). This is the natural continuation and reuses every brick built this lap.
  (b) **Direct CNF-height tracking.** Define a "second-level leading exponent" (the log of the leading
      exponent) and show it stays `≥ 2` for `~m` steps by the same self-similarity one level up. `ω^ω`
      ⟺ the CNF has a term `ω^(ω^0·c)` with the inner exponent ≥ ω, i.e. height-2 CNF persists.
  (c) **Bound `goodsteinLength m` below by `f_ω(m)` through the Cichoń identity** (`goodsteinLength m =
      H_{seqONote m 0}(2) − 2`, already proved) + a Hardy/`H_{ω^ω}` lower bound — may be cleaner than
      the leadExp route for limit levels. Cross-check against the `Logic/FastGrowing/Hardy` API.

Realistic: `o=ω` is a genuine multi-lap tier (the limit-ordinal half of Cichoń). Route (a) is the
most direct reuse of the lap-9 machinery; START there. Do NOT axiomatize — it IS the growth content.

---

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

**Lap-8 proof progress (committed, axiom-clean):** the **per-step leading-exponent characterization**
is now COMPLETE, which is the prerequisite below the `dropTime` count:
- `log_bump_pred_of_not_pow` — at a NON-pure-power step (`b^{log_b n} < n`), the leading exponent is
  exactly preserved: `log_{b+1}(bump b n − 1) = bump b (log_b n)` (the `−1` is absorbed by lower terms).
- `log_bump_pred_of_pow` — at a pure power (`n = b^{log_b n}`, `log_b n ≥ 1`), it drops by EXACTLY one:
  `log_{b+1}(bump b n − 1) = bump b (log_b n) − 1` (the `−1` borrows from the top).
- `leadExp_ge_of_not_pow` — **unconditional non-decrease off pure powers** (no `≥ base` cap, unlike
  `leadExp_ge_of_base_le`): `L_k ≤ L_{k+1}` at every non-pure-power step. This is the lemma that, once
  paired with a bound on the number of pure-power events, lifts the `log₂ m`-step guarantee to `m` steps.
- `bump_eq_of_lt` (`bump b n = n` for `n < b`) + `leadExp_small_nonincreasing` — **the leadExp
  trajectory is now FULLY characterized**: it GROWS while `L_k ≥ base k` (large regime, `bump_gt`),
  then is **NON-INCREASING once `L_k < base k`** (small regime — off pure powers `bump` fixes the
  single-digit exponent, at pure powers it drops by 1). The `o = 2` difficulty lives entirely in the
  small regime; `leadExp_small_nonincreasing` is the tool for a value/quadratic-plateau induction there.
So the leading exponent bumps-itself/grows everywhere except at the **rare pure-power "borrow" events**.
- `ppCount m k` (new `def`) + `leadExp_ge_sub_ppCount` (the **sharpened telescope**):
  `log₂ m ≤ leadExp_k + ppCount m k` — the leading-exponent deficit is bounded by the *number of
  pure-power steps*, not the step index (sharper than `leadExp_ge_sub`).

**⟹ THE DIAGONAL CRUX IS NOW REDUCED TO ONE SPARSITY BOUND.** Since `ppCount` is monotone, the
implication is clean and CORRECT: **`ppCount m m ≤ log₂ m − 2` ⟹ `leadExp_k ≥ 2` for all `k ≤ m`**
⟹ `seqONote m (m−2) ≥ ω²` ⟹ `f_2(m) ≤ goodsteinLength m + 2` (via `fastGrowing_step_le_goodsteinLength`;
general `o` analogously with `ppCount m m ≤ log₂ m − o`). The sparsity hypothesis is *plausibly true*
(pure-power hits `G_i = (i+2)^e` are extremely sparse among the astronomically-large early terms) but
proving it rigorously **IS** the deep steps-between-drops content — the genuine remaining obligation.
**Next brick = the sparsity bound** `ppCount m m ≤ log₂ m − 2` (or its general-`o` form); cleanest
Aristotle carve too. ⚠ NOTE the telescope gives a LOWER bound on `ppCount` (`ppCount k ≥ log₂ m −
leadExp_k`), NOT the upper bound we need — so the sparsity bound is a genuinely separate fact. Routes:
(a) **bound the count directly** — show pure-power hits `G_i = (i+2)^e` among `i ≤ m` are `≤ log₂ m −
2`; since `G_i` is astronomically large and exact powers of base `i+2` are extremely sparse, this is
plausibly true (likely `O(1)` hits for large `m`), but proving it is the deep content. (b) **bypass
`ppCount` and lower-bound the value directly**: prove `G_k ≥ (k+2)²` for `k ≤ m` (⟺ `leadExp_k ≥ 2`)
by a quadratic-plateau induction — the difficulty is the same (it breaks at pure powers, where `G`
dips just below the square), but the per-step lemmas now characterize exactly those break points.
*(Do NOT claim "leadExp stays ≥ base for m steps" — that is FALSE; `leadExp ≥ base i = i+2` fails once
`i > log₂ m − 2`. The early large regime lasts only `~log₂ m` steps; the depth is the small regime.)*

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

## 🔭 OPEN-ITEM INVENTORY (refreshed 2026-06-17)

`src/` declares **no custom axioms** and has no `sorry`/`admit` (`lake build` green, 8274
jobs at the time of writing). Note this is not the same as "axiom-free": the Goodstein growth
closures carry `native_decide` artifacts, as `STATUS.md` records. Three threads are COMPLETE + axiom-clean — **do not reopen**: Curtis 1990
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

### 🧹 Deferred one-liner: a stale docstring in `PiLindemann.lean`

`PiLindemann.lean:48` still describes its two missing ingredients as "the isolated remaining crux
toward discharging `hermite_lindemann` at `π` (equivalently, adopting mathlib PR #28013 on the next
bump)".  **Both ingredients were supplied and the axiom was discharged and deleted** — verified
2026-09-04 by `#print axioms`: `transcendental_pi_axiomClean` and
`squaring_the_circle_impossible_uncond` are both `[propext, Classical.choice, Quot.sound]`.  The
docstring is a recorded plan that outlived the problem it solved, and it reads as an open TODO.
Rewrite it to describe what the file *does*.  Deferred only because editing a `.lean` file mid-run
contends with the treadmill's `lake` lock; it is a comment change, no proof content.

Same check settled the vendoring question: mathlib `v4.31.0` already ships
`NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` (`exp_polynomial_approx`, which this
repo uses), and `Analysis/Real/Pi/Irrational.lean` already has `irrational_pi`.  PR #28013 is still
OPEN (checked 2026-09-04, updated that same day) and its remaining files supply the *general*
Lindemann–Weierstrass theorem, which this repo does not need for `π`.  **Nothing to vendor.**


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

## Mills lane, phase 2 — COMPLETE (2026-09-27)

`src/LeanFormalizations/NumberTheory/Mills/` is **sorry-free and axiom-clean**.  Both phase-2
targets landed: `lower_bound_of_RH` (Caldwell–Cheng 2005 + `Schoenfeld1976`) and `irrational`
(Saito 2024 + `BakerHarmanPintz2001`/`Matomaki2007`/`Mahler1957`).  Every headline reports
`[propext, Classical.choice, Quot.sound]`.

Nothing is parked.  The literature `Prop`s in `Literature/Primes.lean` are the only remaining
debt, and discharging one (Schoenfeld under RH, BHP, Matomäki) is a research project in its own
right — a legitimate future lane, not a hole in this one.

## 2026-09-27 — Mills phase 6, lap 1: Saito Lemma 4.1 crux decomposed

`Mills/SaitoPisot.lean` (new). Attacked the route-decisive half of Saito Thm 1.5 first,
decoupled from the §3 `c`-generalisation grind: **`pisot_degree_bound`** is Saito's Claim
`(ℓ−1)·μ ≤ 1` for a Pisot `β` whose other-conjugate power sums decay like `β^(−μn)`.
It is PROVED from two named algebraic-number leaves. Proved along the way:
`le_of_pow_le_const_mul_pow` (Saito's "take k → ∞": `Mⁿ n^(−λ) ≤ K ρⁿ` ⇒ `M ≤ ρ`, via
`isLittleO_pow_const_const_pow_of_one_lt` after `n^λ ≤ n^⌈λ⌉₊`), `conjMax_pow_card_le`,
`Multiset.prod_le_pow_card_of_le`.

Open leaves (both standard ANT, neither Mills-specific):
1. `pisot_conjPowSum_add_mem_int` : `βⁿ + Σ_{j≥2} β_jⁿ ∈ ℤ` (trace of an algebraic integer).
   Route: `Algebra.trace_eq_sum_embeddings` over `ℚ⟮β⟯` + `Algebra.isIntegral_trace`.
2. `pisot_one_le_prod_norm` : `1 ≤ β·∏_{j≥2}|β_j|` = `|minpoly.coeff 0|` ≥ 1, via
   `minpoly.isIntegrallyClosed_eq_field_fractions` (ℚ-minpoly is the ℤ-minpoly mapped) and
   `prod_roots_eq_coeff_zero_of_monic_of_splits`.

**UPDATE (same lap): BOTH LEAVES PROVED.** `SaitoPisot.lean` is sorry-free and axiom-clean.
**Next attack**: the `b ≥ 5` arithmetic
(`μ = bθ_b ≥ 11/8 > 1`, `ℓ ≥ 2` ⇒ contradiction ⇒ Thm 1.1 modulo the §3 `c`-generalisation).
The §3 `c`-general Lemmas 3.5/3.6/3.8/3.9 (a known-shape generalisation of `Irrational.lean`)
are deliberately *later*: effort, not uncertainty.

### Same lap, later: the `c`-general §3 existence chain is DONE

* `Mills/BasicC.lean` — nested-interval construction for any `c ≥ 2`, sorry-free.
* `Mills/SaitoGeneral.lean` — `pow_succ_ge_add_mul` (binomial gap bound),
  `primeBetweenPows_of_BHP` (BHP ⇒ a prime in `(nᶜ,(n+1)ᶜ)` for `c ≥ 3`; the window fits because
  `21c/40 ≤ c−1` for `c ≥ 40/19`), `exists_millsC_of_BHP`, `exists_leastC_of_exists`
  (lower bound `2^(1/c)` replaces the hand-computed `5/4`), `exists_leastMillsC_of_BHP`.
* **`exists_minMillsC_of_BHP` is PROVED and axiom-clean** — the first of the three phase-6
  sorries is closed.

Remaining in `Mills/Transcendental.lean`: `transcendental_of_four_le`, `transcendental_or_pisot`.
Next attack: the `c`-general Saito Lemmas 3.5/3.6/3.8/3.9 supplying `pisot_degree_bound`'s
`hdecay` hypothesis (generalise `Irrational.lean`'s `mdigit`/`saito_lemma36/38/39`), then the
`b ≥ 5` arithmetic (`μ = bθ_b = 19c/40 − 1 ≥ 11/8 > 1` with `ℓ ≥ 2` contradicts the Claim).

### Same lap, later still: Saito Lemma 4.1 (case `μ > 1`) is COMPLETE

`Mills/SaitoLemma41.lean` — `transcendental_of_decay`, sorry-free and axiom-clean:

> If `A > 1`, `c ≥ 2`, `μ > 1`, `K > 0`, `|A^(cᵏ) − round(A^(cᵏ))| ≤ K·A^(−μcᵏ)` for all large
> `k`, and no `A^(cᵐ)` (`m ≥ 1`) is an integer, then `A` is transcendental.

Both branches of `Dubickas2022` are discharged: the separation branch by `ε := μ log A / 2`, the
Pisot branch by `pisot_degree_bound` + `card_otherConj_add_one` + `pisot_two_le_natDegree`.
Key design note: `le_of_pow_le_const_mul_pow` and `pisot_degree_bound` take `∃ᶠ`, not `∀ᶠ`,
because the decay for `β = A^(c^(m+1))` is only available along `n = c^j`.

**All that now separates Theorem 1.1 (`c ≥ 5`) from a proof is the §3 decay hypothesis**, i.e.
the `c`-general Saito Lemmas 3.5/3.6/3.8/3.9. For `c = 4` (and `c = 3`) one additionally needs
Lemmas 4.2/4.3, since there `μ = 19c/40 − 1 = 9/10 < 1` and the Claim only forces `ℓ = 2`.

**Next attack**: `c`-general Lemma 3.5 (`p_k^c < p_{k+1} < (p_k+1)^c − 1`) and Lemma 3.6
(minimality via Matomäki), generalising `Irrational.lean`. Lemma 3.6 is the long one.

### Same lap, final state: Theorem 1.1 for `c ≥ 5` reduced to ONE deep lemma

`Mills/SaitoDigits.lean` (new): `mdigitC`, Lemma 3.5 both halves, `le_add_rpow_of_pow_le`
(the (3.19) Bernoulli expansion), `decay_of_lemma36C`, `millsC_not_intCast`,
`transcendentalC_of_five_le`. All axiom-clean except for the one named `sorry`.

**The three remaining open obligations in `Mills/` are now exactly:**

1. `saito_lemma36C` (`SaitoDigits.lean:113`) — Saito Lemma 3.6 for general `c`, the Matomäki
   minimality step. The `c = 3` case IS proved (`saito_lemma36` in `Irrational.lean`, ~200
   lines); this is that argument with `3 → c` (`Rich`, `saito_lemma38`, `rich_chain`,
   `Chain.exists_shifted_of_chain` all generalise; Lemma 3.8's exponent `2/3` becomes `(c−1)/c`).
   **This is the whole remaining content of Theorem 1.1 for `c ≥ 5`.**
2. `transcendental_of_four_le`, the `c = 4` branch (`Transcendental.lean:70`) — needs Saito
   Lemmas 4.2 (`t_k = p_k`) and 4.3 (no degree-2 Pisot power), because there `μ = 9/10 < 1`
   and `pisot_degree_bound` only yields `ℓ = 2`. Lemma 4.3's `b = 4` case is the short one:
   `d_k` even ⇒ `β₂^(d_k) > 0` ⇒ `p_k = β₁^d + β₂^d > β₁^d = ξ^(C_k) ≥ p_k`.
3. `transcendental_or_pisot` (`Transcendental.lean:79`) — Theorem 1.2; same machinery at
   `c = 3` (`μ = 17/40`), where the Claim leaves `ℓ ∈ {2,3}` and Lemma 4.3's `b = 3` case
   (`p_k³ = p_{k+1} + 3x₁x₂p_k` ⇒ `p_k ∣ p_{k+1}`) kills `ℓ = 2`.

**Next attack**: item 2's Lemma 4.2/4.3 machinery (short, and shared by items 2 and 3), then
item 1 (long but mechanical).

### Same lap: THEOREM 1.1 IS COMPLETE (modulo `saito_lemma36C`)

`transcendental_of_four_le` is proved for **all** `c ≥ 4`. `#print axioms` shows `sorryAx`
solely from `saito_lemma36C`; every other ingredient is clean.

* `c ≥ 5`: `μ = 19c/40 − 1 > 1`, Lemma 4.1's Claim closes outright.
* `c = 4`: `μ = 9/10`, so the Claim forces `card (otherConj) = 1`, i.e. degree exactly 2 —
  killed by `not_pisot_two_of_even` (`Mills/SaitoDegreeTwo.lean`), axiom-clean.

The `c = 4` argument came out shorter than Saito's: **Lemma 4.2 is not needed as a separate
step.** With `n = cʲ` even, `wⁿ > 0`, so the integer `t = βⁿ + wⁿ` exceeds `βⁿ`, hence
`t ≥ ⌊βⁿ⌋ + 1` and `wⁿ = t − βⁿ > 1/2` as soon as `frac(βⁿ) < 1/2` — contradicting `|w| < 1`
directly. No `t_k = p_k` identification is required.
Also new and reusable: `exists_real_conj_of_natDegree_two` — a degree-2 Pisot number's other
conjugate is the *real* number `t₁ − β`, with no field theory (the `n = 1` trace over a
singleton multiset IS the conjugate), and `eventually_rpow_neg_lt`.

**Two obligations remain in `Mills/`:**
1. `saito_lemma36C` (`SaitoDigits.lean:114`) — general-`c` Matomäki minimality. Gates BOTH
   remaining items. The `c = 3` case is proved in `Irrational.lean`; this is `3 → c`.
2. `transcendental_or_pisot` (`Transcendental.lean:79`) — Theorem 1.2. At `c = 3`, `μ = 17/40`,
   so the Claim gives `card ≤ 40/17`, i.e. `card ∈ {1,2}` (degree 2 or 3). Degree 2 needs
   Lemma 4.3's `b = 3` case: `t_{3n} = t_n³ − 3(βw)ⁿ t_n` with `βw ∈ ℤ` gives `p_k ∣ p_{k+1}`,
   impossible for distinct primes. Degree 3 is Saito's open Remark 4.4 — it is the *disjunct*,
   so Theorem 1.2 needs only the degree-2 kill plus `IsPisot` + `natDegree = 3` extraction.
   **Prerequisite to add: `βw = (minpoly ℤ β).coeff 0 ∈ ℤ`** (extract from the proof of
   `pisot_one_le_prod_norm`, which already computes `Q.eval 0` both ways).

### 2026-09-27 — Mills phase 6 COMPLETE: Saito Theorems 1.1 and 1.2 are axiom-clean

`src/LeanFormalizations/NumberTheory/Mills/` is **sorry-free** again, and all three phase-6
headline theorems in `Mills/Transcendental.lean` report only
`[propext, Classical.choice, Quot.sound]`:

| theorem | content |
|---|---|
| `exists_minMillsC_of_BHP` | `ξ_c` exists for every integer `c ≥ 3` (Saito Cor 3.4) |
| `transcendental_of_four_le` | **Theorem 1.1**: `ξ_c` transcendental for every `c ≥ 4` |
| `transcendental_or_pisot` | **Theorem 1.2**: `ξ₃` transcendental, or some `ξ₃^(3^m)` is Pisot of degree 3 |

Two laps' worth of work, both landed here:

**`saito_lemma36C`** (Lemma 3.6 for general `c`) is proved, via two new sorry-free files:

* `ChainC.lean` — `exists_shifted_of_chainC`, `Chain.lean`'s shifted nested-interval engine for
  any `c ≥ 2`.
* `SaitoRich.lean` — `RichC`, the inner exponent `γ = 1 − 1/c` (`etaC`), and `saito_lemma38C`
  (Lemma 3.8 for general `c`).

The design point: at `c = 3` the inner Matomäki exponent and the outer window exponent coincide
(both `2/3`), so `Irrational.lean` could use one symbol.  Separating them is exactly what makes
the `c`-general lemma instantiable twice — at `η = 21/40` (window from Baker–Harman–Pintz) and at
`η = 1 − 1/c` (window from the previous chain step).  Since `2/3 − γ ≤ 0` for `c ≥ 3`, Matomäki's
count `D x^(2/3−γ)` collapses to the bare constant `D`.

Two elementary ingredients replaced the analytic estimates Saito leaves implicit:
`(1 + 1/(2c))^c ≤ 17/10` (from `1+t ≤ exp t` and `exp(1/2)² = e < 2.89`), which keeps the
window's `c`-th powers inside `[Xᶜ, 2Xᶜ]`; and `(u+1)ᶜ ≥ uᶜ + 2u^(c−1) + u^(c−2)` (split off
`(u+1)²` — no binomial theorem), which gives both the disjointness of the Matomäki windows and
the upper half of the chain condition.

**Theorem 1.2** then needed only Lemma 4.3 at `b = 3`, now `not_pisot_two_of_cube` in
`SaitoDegreeTwo.lean`.  The mechanism is the Dickson/Newton identity

    t_{3n} = t_n³ − 3 Pⁿ t_n,     t_n = βⁿ + wⁿ ∈ ℤ,  P = βw ∈ ℤ,

so `t_n ∣ t_{3n}`; along `n = 3ʲ` both are **digits of `A`**, hence primes, and
`t_{3n} > t_n³ > t_n` — a prime properly dividing a prime.  The missing prerequisite `βw ∈ ℤ` is
`pisot_two_prod_mem_int` (`βw = ∏(−root) = Q(0) = (minpoly ℤ β).coeff 0`, the same computation as
`pisot_one_le_prod_norm` but keeping the value instead of its modulus).  With `μ = 17/40` the
Claim gives `card ≤ 40/17 < 3`, so degree is 2 or 3; degree 2 dies, degree 3 *is* the disjunct
(Saito's open Remark 4.4).

Gotchas this lap: `gcongr` cannot discharge the `0 ≤ log(pᶜ)` side goal of a div-monotonicity
step — use `div_le_div_of_nonneg_right` with an explicit `Real.log_nonneg`.  `Nat.cast_sub` takes
`(R := ℝ)`, not `(α := ℝ)`.  A `set ... with h` does **not** fold occurrences created later by
`refine`, so re-`rw [← h]` before `omega`.  A transient `failed to open file ... .ir: Bad file
descriptor` from the mathlib build tree is spurious; rerun `lake build`.
