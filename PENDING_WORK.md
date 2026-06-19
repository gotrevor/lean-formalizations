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

**Bottom line:** HJSW is **not** any single algebraic base's 4-lift union, nor (from prior lap) a
2-curve hyperbola-lift union. The construction must be genuinely cleverer (non-uniform lifts across
a specific multi-curve / non-conic base, navigating the over-constraint above — likely exploiting
the fixed points and a global cycle structure on the slope-`±1` collision graph). **Need the paper.**

## Three attack paths for `hjsw_lower`

### Path A — get the real construction from the HJSW 1975 paper (filed; network-blocked)
`ON-LINE-REQUEST.md` asks for the explicit point set + cross-curve non-collinearity proof, now
sharpened with the over-constraint analysis (so the fulfiller knows exactly what to extract).
When `ON-LINE-FINDINGS-*.md` lands: build the candidate set, validate via `native_decide (decNoThree …)`
at p=5,7,11,13, port to a clean `def`, prove using the reduction toolkit (the new content is then
just the slope-`±1` combinatorics, the geometry being discharged). Highest-confidence path.

### Path B — original construction, guided by the structure above
The over-constraint analysis says: model the slope-`±1` collision graph (vertices = base points;
S+ edge `a—(−a⁻¹)`, S− edge `a—a⁻¹`; 2-regular ⇒ disjoint alternating cycles + involution
fixed-point self-loops) and find a lift-assignment (some points keep all 4 lifts, some keep 2)
totalling `3(p−1)` with `#KEEP4 = (p−1)/2`, respecting "each S+ edge has an all-anti endpoint, each
S− edge has an all-diag endpoint." Feasibility hinges on the fixed points relieving the cycle.
Next experiment: solve this CSP computationally for p = 7, 11, 13 (it is small: 2-regular graph,
3 types per vertex); if a consistent assignment exists, decode the rule and prove it via the
reduction toolkit. If the CSP is **infeasible** for one hyperbola, a 2nd curve must supply fillers —
then the base is a 2-hyperbola union and the reduction needs the union's mod-`p` non-collinearity.

### Path C — special-case ladder (partial, native-certified) while A/B mature
Verified witness ladder p=5,7,11,13 (`hjsw_lower_{five,seven,eleven,thirteen}`, native_decide, OFF
headline). Extend to p=17,19 only if a lap needs filler; do NOT generalize to the headline.

## Done this lap
Reduction toolkit (4 axiom-clean lemmas); over-constraint theorem (3-of-4 iff p=5, proven +
verified); computational wall map (all single structured bases fail at p=7). **Next lap:** act on
findings (A) the moment they land; else execute Path B's CSP solve for the lift-assignment.
