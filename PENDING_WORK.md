# PENDING_WORK — no-three-in-line / HJSW frontier (branch `ntl-hjsw`)

## ⭐ 2026-06-19 (review lap) — ACTIVE FRONTIER: general-`N` constant `3/4 → 5/4 → 3/2`

**State.** All headlines proven & axiom-clean (kernel-verified). The open obligation is the
general-`N` lower *constant*: HJSW's theorem is `3N/2 − o(N)` for *all* large `N`, but the formalized
general-`N` bound is only `3/4` (`maxNoThreeInLine_ge_three_quarters`, Bertrand-limited). Lifting it is
genuine 🟡 debt. `PrimeGap.lean` now holds the scaffold + the Chebyshev lower-bound infrastructure (all axiom-clean
except `nagura_prime`):
- `maxNoThreeInLine_ge_of_two_mul_prime_le` (interface) + `maxNoThreeInLine_mono`.
- `maxNoThreeInLine_ge_five_fourths` (`3⌊5N/12⌋ ≤ max N`, `N≥60`) — **wired**, payoff ready.
- `nagura_prime` (prime in `(n,6n/5]`, `n≥25`) — the **disclosed-`sorry` crux**.
- `centralBinom_dvd_lcm_Icc`, `four_pow_lt_mul_lcm` (`4ⁿ<n·lcm(1..2n)`) — ℕ Chebyshev lower bound. ✅
- `factorization_finset_lcm`, `primePow_dvd_lcm_Icc_iff` (`pᵏ ∣ lcm(1..N) ⟺ pᵏ ≤ N`). ✅
- `log_lcm_Icc_eq_psi` (`log(lcm(1..N)) = ψ N`, the von Mangoldt ↔ lcm bridge). ✅ **DONE this lap.**
- `psi_lower` (`n·log4 − log n < ψ(2n)`) + `theta_lower` (`… − 2√(2n)·log(2n) < θ(2n)`). ✅ **The
  Chebyshev θ LOWER bound mathlib was missing — built from scratch this lap, axiom-clean.**

**The crux `nagura_prime` — remaining work (the θ-lower infra is now DONE):**
1. **The precise tuned numerical inequality (PRIMARY).** ⚠️⚠️ DEFINITIVE FINDING (computed this lap —
   do NOT chase the crude path): the crude elementary Chebyshev bounds are **provably insufficient** for
   `6/5`. With `theta_lower` (`θ(x) ≳ (log4/2)x`) + crude upper (`θ(x) ≤ log4·x`), the central-binomial
   split gives, under "no prime in `(n,6n/5]`",
   `C(2n,n) ≤ (2n)^√(2n)·4^(2n/3)·∏_{6n/5<p≤2n}p ≤ (2n)^√(2n)·4^(2n/3)·4^(2n−3n/5) = (2n)^√(2n)·4^(31n/15)`,
   and `31/15 ≈ 2.07 > 1`, so it does **not** contradict `4ⁿ ≤ n·C(2n,n)`. (`θ(x) ≳ 0.69x` is the best
   *elementary* lower constant — lcm/central-binom cap it at `log4/2`; the true `θ(x)~x` needs PNT.)
   So Nagura's `6/5` genuinely requires the **precise tuned numerical inequality** — the analogue of
   mathlib's `bertrand_main_inequality` (`Mathlib/NumberTheory/Bertrand.lean:126`) re-derived for ratio
   `6/5` and valid for `n ≥ N₀`, with `n ∈ [25, N₀)` by `decide`/explicit prime list. That is a real
   analytic computation — the genuine multi-lap content, best started fresh. The factorization split
   (sharpen `centralBinom_factorization_small`/`centralBinom_le_of_no_bertrand_prime` to keep the
   `(6n/5,2n]` primes) is the mechanical scaffolding around it.
2. **Aristotle.** Job `1644a603` (`aris-nagura`) grinding the self-contained statement. Harvest when
   IDLE: download, kernel-verify, `#print axioms`, port.
3. **Weaker explicit rung.** Any ratio `c<2` with a provable gap gives constant `3/(2c) > 3/4`. Same
   factorization obstruction, just looser numerics.

**Reusable spinoffs (PR-worthy to mathlib):** `factorization_finset_lcm`, `primePow_dvd_lcm_Icc_iff`,
`log_lcm_Icc_eq_psi`, `psi_lower`, `theta_lower` are all general Chebyshev/lcm facts mathlib lacks.

**Faithfulness (carry-over):** Aristotle `72891d77` (independent NL→Lean of the headline) finished
(IDLE) but its `show`/`download` 500 server-side this lap — retry next lap; not load-bearing.

---

## 📋 2026-06-19 (earlier) — FULL INVENTORY (per how-to-get-unblocked.md)
**Open `sorry` in `src/`: 0.** **Custom `axiom` declarations in `src/`: 0.** Verified by
`grep -rnE '^[[:space:]]*axiom '` (only a docstring word-wrap hit) and `grep -rnw sorry` (only
comments). Every headline `#print axioms = [propext, Classical.choice, Quot.sound]`. This is a
genuinely empty inventory, not a fixation on one blocked thread — the hard crux was *solved* this lap.

**The only non-formalizable thing left in NTL is the open Main Conjecture.** Future *formalizable*
directions, three paths each (none required; all optional next-lap menu):
1. **Sharper general-`N` constant (`3/4 → 3/2`).** (a) Formalize Nagura's theorem (prime in
   `(n, 1.2n]`, n≥25) → constant `≈1.25`; (b) formalize a Baker–Harman–Pintz-style gap → `→3/2`;
   (c) reformulate to only claim the bound at `N=2p` (already done — `hjsw_lower_bound`). Paths
   (a)/(b) are real prime-gap infrastructure projects (mathlib lacks them), not quick laps.
2. **Faithfulness audit.** (a) Harvest Aristotle `72891d77` (independent NL→Lean of the headline) and
   diff its `no-three-collinear`/box/card encoding vs `Statement.lean`; (b) add `native_decide`
   anchors for the construction at more primes (LOW value — `shearSel_noThree` is already proven ∀p,
   so anchors add nothing the kernel didn't); (c) hand-audit `Defs.lean` against the literature def.
   Path (a) is the genuine one.
3. **Strengthen the construction itself (toward 2N).** (a) Search for a base of size `> p` reaching
   `> 3(p-1)`; (b) two-curve / union constructions (prior laps found single-curve caps); (c) port a
   published `(2-ε)N` construction if one exists. Open research; (a)/(b) need exhaustive search first.

## ✅✅ 2026-06-19 (later) — NOTHING OPEN. HJSW COMPLETE.
`shearSel_cross_diag` (the lone `sorry`) is **PROVEN** ⇒ `hjsw_lower` is fully proven, axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Discharged via `shear_diag_partner`/`shear_anti_partner`
(curve-factoring → partner relation → drop tie-break). Promoted to `Statement.lean`
(`hjsw_lower_bound`, `maxNoThreeInLine_ge_three_quarters` = general-`N` `3N/4` via Bertrand).
**Zero `sorry` in the repo.** The only remaining item in the no-three-in-line problem is the
**Main Conjecture (open math)** — not a formalizable proof. The (now historical) attack-path
inventory below is preserved for context. See `HANDOFF-2026-06-19-0728.md` for techniques + the
optional next-lap menu (faithfulness cross-check / sharper general-`N` via prime gaps / cosmetic
polish). Do NOT re-open the items below — they are solved.

---

Inventory of open items + attack paths (per `how-to-get-unblocked.md`). Refreshed 2026-06-19 (lap N+1).
(This isolated clone's focus is solely the HJSW frontier; the main-branch threads — Curtis,
power-tower, constructibles, transcendence, Goodstein — are complete & axiom-clean, recorded in
`STATUS.md` and git history. Do not reopen them here.)

## ⭐⭐ 2026-06-19 UPDATE — THE CONSTRUCTION CRUX IS CRACKED (closed-form rule found)

The open combinatorial crux (the lift-selection rule) is **SOLVED**. A closed-form rule for the
sheared hyperbola was found and verified (exact integer determinant: card, distinct, grid, NoThree)
for EVERY prime `3 ≤ p ≤ 109`. See `SELECTION-RULE-FOUND.md`. Construction:
> drop the pole column `pl=(p−1)/2`; for every other column `(r,s)=(x,(2x+1)⁻¹)` keep 3 of 4 lifts,
> dropping the corner nearest the grid centre `dropped=(r+p·[r≤pl], s+p·[s≤pl])`.

**Lean status now** (`Hyperbola.lean`, all green except one sorry):
- `shearSel p` defined (general, computable); `shearSel_card = 3(p−1)` and `shearSel_grid ⊆ 2p×2p`
  proven **axiom-clean**.
- `hjsw_lower` rewritten to assemble `card + grid + shearSel_noThree` — so the headline `sorry` is
  now the SINGLE lemma `shearSel_noThree : NoThreeCollinear (shearSel p)`.
- Bricks proven axiom-clean: `shear_two_ne` (2x+1 unit off pole), `shear_curve` ((2x+1)·y=1 mod p),
  `shearY_lt`. Plus the full geometry toolkit from prior laps.
- `Anchors.lean` native_decide-certifies `NoThreeCollinear (shearSel p)` at p=7,11,13.
- Aristotle job `1c2a55b7` (`aris-hjsw-shear`) running the pure-arithmetic form
  (`shearSel_decNoThree`: every distinct triple has `detZ ≠ 0`) — self-contained, no reals.

## The ONLY open item (as of latest commit)

**`shearSel_cross_diag`** (`Hyperbola.lean`) — the lone `sorry`, the irreducible slope-`±1` core.
The entire tower is machine-checked above it:
`hjsw_lower` ⟸ `shearSel_noThree` ⟸ `shearSel_intdet` ⟸ `shearSel_two_lifts_line` ⟸
`shearSel_cross_column` ⟸ `shearSel_cross_diag`, with `shearSel_card`, `shearSel_grid`,
`shearSel_mem_curve`, `shearSel_share_residue`, `shear_curve`, `shearY_injective`,
`shearSel_{y,x}res_of_{x,y}res`, `lift_triple_noncollinear` all axiom-clean — AND the slope-`0`/`∞`
cross-column cases now discharged inside `shearSel_cross_column`.

`shearSel_cross_diag`: `P,Q` two kept lifts of one column differing in BOTH coordinates (so a
diagonal `{A,D}` or antidiagonal `{B,C}` slope-`±1` pair), `R` a kept lift of a DIFFERENT column —
never collinear. This is the genuine HJSW combinatorial heart.

**Proof plan for `shearSel_cross_diag`:** `P,Q` differ by `p` in both coords (by
`coord_diff_of_residue_eq`), so they are the diagonal `{A,D}` (line `Y−X = sₐ−a`, slope `+1`) or
antidiagonal `{B,C}` (line `Y+X = sₐ+a+p`, slope `−1`) pair of column `a`. Both being kept pins the
drop: diagonal kept ⟺ `a,sₐ` opposite sides of `pl` (dropped corner `B`/`C`); antidiagonal kept ⟺
same side. `R` on that line ⇒ `R.2−R.1 = sₐ−a` (resp `R.2+R.1 = sₐ+a+p`) as integers ⇒
`s_c−c ≡ sₐ−a (mod p)` with `c` the slope-`±1` partner column (an explicit Möbius relation via the
curve `(2x+1)y≡1`). The contradiction: the corner of column `c` that lands on this line is exactly
`c`'s DROPPED corner (so `R` cannot be a kept lift there) — unless `c=a`. Formalize by extracting
columns from `mem_shearKept`, casing the 4 corners of each, and the `shearDrop` if-conditions +
`intCoord_diff_factor`. Aristotle job `1c2a55b7` is grinding the superset `shearSel_intdet`; if it
returns without the counting, resubmit the tighter `shearSel_cross_diag`.

### (superseded) earlier plan — reduction → 4 line-counts:
   - Each P,Q,R ∈ `shearSel p` is a kept lift of a column; for x≠pl, `shear_curve` puts its residue
     on `(2x+1)y=1`. Apply `shear_hyperbola_lift_share_residue` ⇒ two share a residue ⇒ same column
     (first coord <2p determines column mod p). If all three same column ⇒ `lift_triple_noncollinear`
     kills it. Else two-in-a-column + one other ⇒ line slope ∈ {0,∞,±1}.
   - slope 0 / ∞: impossible because `shearY` is **injective** (need a `shearY_injective` lemma:
     `2x+1` injective on `[0,p)`-residues, inverse injective) ⇒ distinct rows AND columns ⇒ each
     integer row/column has ≤2 points.
   - slope ±1: the closed-form drop rule guarantees ≤2 per slope-±1 integer line. This is the genuine
     remaining content — reduce to modular arithmetic via `coord_diff_of_residue_eq` /
     `intCoord_diff_factor`. (Diagonal pair kept ⟺ r,s opposite sides of pl; antidiagonal pair kept
     ⟺ same side — so each column doubly-loads exactly one slope-±1 line, and no two columns collide.)

Single-crux target ⇒ "broaden" mostly means *broaden the attack on this crux*.

## Reduction toolkit shipped this lap (axiom-clean, `Hyperbola.lean`)
The geometric half of any lift-based HJSW proof is now done:
- `collinear_imp_modp_det_zero` — **construction-agnostic**: real-collinear grid points ⇒ their
  residues' `2×2` determinant vanishes in `ZMod p` (ℤ→ZMod p is a ring hom). Works for ANY base.
- `hyperbola_collinear_zmod` — mod-`p` Vandermonde core over the field `ZMod p`.
- `hyperbola_lift_collinear_share_residue` — real-collinear triple of hyperbola-lifts ⇒ two share a
  residue mod `p` (= two lifts of one base point). Reduces no-three to a slope-`±1` condition.
- `coord_diff_of_residue_eq` — two grid coords in `[0,2p)` congruent mod `p` differ by `0` or `p`.

**What remains for the headline = purely combinatorial:** choose which lifts to keep so that no
slope-`±1` line carries 3 chosen points. (Slope `0`/`∞` are automatically safe when the base has
distinct x- and y-residues; only slope `±1` is dangerous.)

## NEW structural result this lap (rigorous + computationally confirmed)
**Uniform "3 of the 4 lifts of a single modular hyperbola `xy ≡ k`" reaches `3(p−1)` iff `p = 5`.**
Proof sketch (k = 1; recorded in `ON-LINE-REQUEST.md`): the only collinear triples are
"2 diagonal lifts of `P_a` + 1 of its slope-`+1` partner `P_{−a⁻¹}`" (line `y = x + (a⁻¹−a)`) or the
anti-diagonal analogue with the slope-`−1` partner `P_{a⁻¹}`. Avoiding a triple forces **both**
endpoints of each collision pair to drop a (anti-)diagonal lift; but a base point sits in one
slope-`+1` pair AND one slope-`−1` pair, so it must drop a diagonal **and** an anti-diagonal lift —
two drops — while 3-of-4 drops only **one**. The only escape is an involution fixed point: the
slope-`−1` constraint is void when `a² = k` (partner = self, line has only 2 points), the slope-`+1`
constraint void when `a² = −k`. For `p = 5` **every** `a ∈ {1,2,3,4}` is a fixed point of one
involution (`a²=1`: a=1,4; `a²=−1`: a=2,3), so all points are singly-constrained ⇒ feasible. For
every other prime ≥ 7 some base point is doubly-constrained ⇒ infeasible.
Verified: `test(5)=True`, `test(7)=False` by exhaustive `4^(p−1)` search.

**Stronger (from prior lap, still holds):** even *non-uniform* single-hyperbola lifts cap at `≤ 17`
at `p=7` (min hitting set of the collinear-triple hypergraph is `≥ 7`). And this lap's probe
confirms **no** structured single base reaches the count at `p=7`: hyperbola `xy=k` (all k),
rotated hyperbola `y²−x²=c`, circle `x²+y²=c`, monomial graphs `y=x^m` (m coprime to p−1),
translated hyperbola `(x+1)(y+1)=k`, parabola `y=x²` — all `< 18`. (`p=5` hits are small-case
coincidences, explained by the iff above.)

**Bottom line (corrected later this lap):** the prior conclusion "need ≥2 curves" was an artifact
of only ever testing the **|B| = p−1** plain hyperbola + uniform 3-of-4. A single base of size
**|B| = p** DOES work — see the breakthrough below.

## ⭐ BREAKTHROUGH this lap — the SHEARED HYPERBOLA construction (|B| = p, validated p=7,11,13)
A fresh exhaustive scan over "one-point-per-column, distinct-rows" bases (graphs of permutations
`f : Z_p → Z_p`) found **984 of 5040** such bases at `p=7` whose 4-lift union contains an 18-point
no-3-collinear set. Among the *uniformly-defined* (all-`p`) families, **Möbius / conic bases work**.
The cleanest:

> **`base = { (x, (2x+1)⁻¹ mod p) : x ∈ Z_p }`** — the sheared hyperbola `y·(2x+1) ≡ 1 (mod p)`,
> with the pole `x = −2⁻¹` mapped to `0`. `|B| = p`. Its `4p` lifts into `[0,2p)²` contain a
> `3(p−1)`-point no-3-collinear subset. **Verified REACH at p = 7, 11, 13** (and others:
> `(a,b,c,d) ∈ {(0,1,2,1),(0,1,4,2),(1,1,2,4),(2,3,1,3),(2,1,4,0)}` all reach p=7,11,13).

Why the shear matters: the plain hyperbola `xy≡1` (|B|=p−1) caps at 17 because every base point is
over-constrained by its slope-`±1` partners (the iff-p=5 result). The shear `x ↦ 2x+1`
**redistributes** the slope-`±1` collisions (the lift structure is NOT shear-invariant — lifts are
tied to the `2p×2p` grid), and the extra pole point (`|B|` goes p−1 → p) relieves the deficit.
NB: plain hyperbola + origin (`xy=1 ∪ {(0,0)}`) does NOT work — the shear is essential.

Still open: the lift **selection rule is non-uniform** (a found p=7 selection keeps 3,2,3,1,3,4,3
lifts across the 7 base points; uniform 3-of-4 = 21 pts does NOT exist for ANY of the winning bases
`(0,1,2,1),(0,1,4,2),(1,1,2,4),(2,3,1,3),(2,1,4,0)`). So the count is intrinsically `3(p−1) = 3p−3`,
a **deficit of 3** below "3 per base point" — and a *closed-form* selection rule is not yet pinned.

**Collision-graph structure of the sheared base (for the rule search):** classify base points by
`y−x mod p` (slope-`+1` classes) and `y+x mod p` (slope-`−1`). At `p≡1 (mod 4)` (e.g. p=13) all
classes have size ≤2 (clean); at `p≡3 (mod 4)` (p=7,11) there is a **size-3 class** on each side —
those are where the deficit/over-constraint concentrates. A character-only rule
(keep-set by `χ(2x+1) ∈ {+1,−1,0}`) does NOT work (tested p=7,11). The rule must use the
collision-class structure, likely splitting on `p mod 4` and the size-3 classes. **This is the heart
of the HJSW combinatorics** — the realistic next-lap target (or await Aristotle `083292d5` / paper).

## Three attack paths for `hjsw_lower`

### Path A — get the real construction from the HJSW 1975 paper (filed; network-blocked)
`ON-LINE-REQUEST.md` asks for the explicit point set + cross-curve non-collinearity proof, now
sharpened with the over-constraint analysis (so the fulfiller knows exactly what to extract).
When `ON-LINE-FINDINGS-*.md` lands: build the candidate set, validate via `native_decide (decNoThree …)`
at p=5,7,11,13, port to a clean `def`, prove using the reduction toolkit (the new content is then
just the slope-`±1` combinatorics, the geometry being discharged). Highest-confidence path.

### Path B — ⭐ PRIMARY now: pin down the sheared-hyperbola selection rule, then prove
The base is found (sheared hyperbola, above). The remaining work is the **lift-selection rule** +
the general proof. Concrete next steps:
1. **Find a closed-form selection** for `base = {(x,(2x+1)⁻¹)}`: search for a selection of `3(p−1)`
   lifts that is *symmetric* (e.g. invariant under an involution of the base, or given by a simple
   per-`x` rule on the residue/quadratic-character of `2x+1`) and validate at p=7,11,13,17. The
   hitting-set found arbitrary selections; we need a *rule*. Try: keep lifts by a rule depending on
   `χ(2x+1)` (quadratic character) and the slope-`±1` partner structure of the sheared base.
2. **Generalize the non-collinearity proof**: the reduction toolkit (`collinear_imp_modp_det_zero`)
   already handles cross-residue triples for ANY base; `shear_hyperbola_lift_share_residue` does the
   sheared base. Two clean geometric pieces remain (both provable now, independent of the selection
   rule, good warm-up lemmas):
   (i) **`lift_triple_noncollinear`** (the same-base-point case) — ✅ **DONE this lap, axiom-clean**
       (`Hyperbola.lean`): 3 distinct grid points in `[0,2p)²` pairwise congruent mod `p` are never
       collinear (3 distinct corners of a `p×p` rectangle ⇒ integer det `= ±p² ≠ 0`; via
       `intCoord_diff_factor` + `decide` on the `{0,1}`-determinant). **So the GEOMETRY is COMPLETE**:
       cross-base triples → impossible (`*_lift_share_residue`); same-base triples → impossible
       (`lift_triple_noncollinear`). The only open obligation is now purely combinatorial.
   (ii) Remaining: a **capstone** `NoThree S ⟸ (residues on base) ∧ (no slope-±1 cross-base triple)`
       (assembly of the two proven cases — straightforward but has 3-fold pair symmetry), and the
       **selection rule** that discharges the slope-`±1` condition (reduce it to arithmetic via
       `coord_diff_of_residue_eq`). The selection rule is the sole research crux left.
3. Validate any candidate rule via `native_decide (decNoThree …)` at p=5,7,11,13 before the proof.
Fallback: if no clean rule emerges, the Aristotle job (`083292d5`, self-contained HJSW) may return
a construction to port.

### Path C — special-case ladder (partial, native-certified) while A/B mature
Verified witness ladder p=5,7,11,13 (`hjsw_lower_{five,seven,eleven,thirteen}`, native_decide, OFF
headline). Extend to p=17,19 only if a lap needs filler; do NOT generalize to the headline.

## Done this lap
Reduction toolkit (4 axiom-clean lemmas); over-constraint theorem (3-of-4 iff p=5, proven +
verified); computational wall map; **the sheared-hyperbola breakthrough** (a uniformly-defined
|B|=p base reaching 3(p−1) at p=7,11,13, overturning the prior "need ≥2 curves" belief); submitted
the self-contained HJSW to Aristotle (`083292d5`). **Next lap:** Path B step 1 — find a closed-form
selection rule for the sheared hyperbola (validate p=7,11,13,17), then prove via the toolkit. Also
check `aristotle list` for `083292d5` and any `ON-LINE-FINDINGS-*.md`.
