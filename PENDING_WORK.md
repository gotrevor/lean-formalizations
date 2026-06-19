# PENDING_WORK — no-three-in-line / HJSW frontier (branch `ntl-hjsw`)

Inventory of open items + attack paths (per `how-to-get-unblocked.md`). Refreshed 2026-06-19 (lap N+1).
(This isolated clone's focus is solely the HJSW frontier; the main-branch threads — Curtis,
power-tower, constructibles, transcendence, Goodstein — are complete & axiom-clean, recorded in
`STATUS.md` and git history. Do not reopen them here.)

## Open items (full `#print axioms` + `grep sorry` sweep of `src/.../NoThreeInLine/`)

1. **`hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)`** (`Hyperbola.lean`) — the ONLY open `sorry`.
   The covering count of the HJSW `3N/2` lower bound. Everything else is proven & axiom-clean:
   2N upper bound, Erdős Θ(N), hyperbola-arc non-collinearity, the **reduction toolkit** (new this
   lap, see below), the decidable `det3=0 ⟺ Collinear` certificate, and native-decide witnesses at
   p = 5, 7, 11, 13.

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
   (i) **`lift_triple_noncollinear`** (the same-base-point case): 3 *distinct* grid points in
       `[0,2p)²` pairwise congruent mod `p` in both coords are never collinear (they are 3 distinct
       corners of a `p×p` rectangle ⇒ integer det `= ±p² ≠ 0`). Proof route: cast det to ℤ, write
       each coord as `residue + p·(coord/p)` with `coord/p ∈ {0,1}` (use `coord_diff_of_residue_eq`),
       factor out `p²`, then `decide` the `{−1,0,1}`-determinant is nonzero given the 3 corners are
       distinct. With this + `share_residue`, the FULL geometry reduces to a single clean capstone
       `NoThree S ⟸ (residues on base) ∧ (no slope-±1 cross-base triple)`.
   (ii) the slope-`±1` triples (two lifts of one base point + a third) are killed by the selection
       rule, reduced to arithmetic via `coord_diff_of_residue_eq`.
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
