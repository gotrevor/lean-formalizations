# PENDING_WORK — Curtis 1990 engine

> Read `DIRECTION.md` first. The crux is `substCurve_eq_zero`; everything else is
> `sorryAx` until it closes and is NOT a deliverable.

## ⚖️ FEASIBILITY VERDICT (2026-06-14) — crux appears REACHABLE, no confirmed wall
Assessment of `substCurve_eq_zero` against current mathlib (v4.29.1):
- **Lemma 1 (Dirichlet + Farey witness)** — riskiest pole. mathlib HAS Dirichlet. The
  only candidate gap is **Farey adjacency** (`|rs−qt|=1` for consecutive Farey fractions,
  existing near any real α). mathlib has Stern–Brocot / continued-fraction machinery, so
  this is *probably* buildable, but I have NOT yet confirmed a ready lemma — this is the
  open feasibility question. OUT TO ARISTOTLE (`80d9166c`); its result will sharpen the verdict.
- **Limit argument** — no wall seen. All ingredients are in mathlib
  (`homogeneousComponent`, `sum_homogeneousComponent`, `IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`,
  `Polynomial.eq_zero_of_infinite_isRoot`, `Filter.Tendsto`). A multi-lemma analysis build,
  but mechanical. Buildable now, independent of Lemma 1.
- **Net:** NO confirmed wall → do NOT park Curtis. The crux is a real but apparently
  reachable multi-lap build. Next lap should SPIKE it (build the limit argument + harvest/port
  Lemma 1) and update this verdict — especially the Farey-adjacency question, the one
  genuine unknown.

---

Headline theorem `no_polynomial_relation` (spine machine-checked) reduces to ONE
remaining `sorry` — **the crux** — which is still `sorryAx` and gates every headline.

## DONE this far (all axiom-clean modulo the one open sorry)
- `no_finite_polynomial_formula` — corollary (`F = ∏(fᵢ − Y)`).
- `no_polynomial_relation_engine` — spine + final contradiction + good-prime selection.
- `finite_specCurve_eq_zero` — bad-prime set finite (finSuccEquiv → roots over a domain).
- `half_le_totalDegree` — **Step B, the entire degree-counting finish** (root-counting
  via `finSuccEquiv ∘ rename (finRotate 3)`, distinct `linForm p k`, `card_roots'`,
  `degreeOf_le_totalDegree`, `totalDegree_aeval_le`).
- `Curtis.Lemma2.lemma2` — **Curtis's Lemma 2** (Brauer–Shockley value), via Aristotle,
  re-verified in our kernel.

## THE ONE OPEN SORRY — `substCurve_eq_zero` (Step A) — DEEP
Goal: `F` vanishes on the graph ⟹ each `substCurve F p k = 0` (k = 2..(p-1)/2+1).
Two remaining inputs:

1. **Lemma 1** (Dirichlet primes in AP + Farey adjacency) — **OUT TO ARISTOTLE**
   (job `80d9166c-a0af-4717-978b-98bda8c0af50`, prompt
   `tools/aristotle/curtis-lemma1-prompt.txt`). Statement: for `α>0`, `ε>0`, prime `p`,
   residues `i,j` coprime to `p`, there are `x` prime, `y` with `x≡i`, `y≡j (mod p)`,
   `gcd(x,y)=1`, `|α − y/x| < ε`. On return: verify in-kernel + `#print axioms`, port to
   a sibling `Lemma1.lean`.

2. **The limit argument** (replaces Curtis's projective homogenization with elementary
   analysis): `G := substCurve F p k`-style 2-var polynomial vanishes at `(xₙ,yₙ)` with
   `yₙ/xₙ → α` irrational, `xₙ → ∞` ⟹ its leading form `G_D(1,α)=0` for every irrational
   `α` in an interval ⟹ `G_D(1,T) ≡ 0` (infinitely many roots, `Polynomial.eq_zero_of_infinite_isRoot`)
   ⟹ `G_D = 0` ⟹ `G = 0`. Independent of Lemmas 1/2; can be built against their statements.

### Assembling `substCurve_eq_zero` once 1 & 2 land
For fixed prime `p>2` and `k` in range, and an irrational `α ∈ (p−k, p−k+1)`:
- Lemma 1 (with `i=1`, `j=p−k+1`) gives admissible `(p, xₙ, yₙ)` with the right residues,
  `xₙ` prime, `gcd=1`, `yₙ/xₙ → α`. Admissibility of `(p,xₙ,yₙ) ∈ A`: `p<xₙ<yₙ` (large n),
  both prime, `p∤yₙ` (since `yₙ ≡ p−k+1 ≢ 0`), `xₙ∤yₙ` (gcd 1, `xₙ>1`).
- Lemma 2 gives `g⟨p,xₙ,yₙ⟩ = (k−2)xₙ + yₙ − p`, so `substCurve F p k` evaluated at
  `(xₙ,yₙ)` equals `eval (graph point) F = 0` (hypothesis `hF`).
- The limit argument then forces `substCurve F p k = 0`.
  (Verify Lemma 2's hypotheses hold: `2<p<xₙ<yₙ`, `2≤k≤(p-1)/2+1` ⇒ `2k≤p+1`,
  `(p−k)xₙ < yₙ < (p−k+1)xₙ` from `yₙ/xₙ → α ∈ (p−k,p−k+1)`, congruences from Lemma 1.)

## Attack-path summary (pick one per lap)
- **A: harvest Aristotle Lemma 1** (`80d9166c`) when it returns; verify + port.
- **B: the limit argument** — independent; build it now against the Lemma 1/2 statements.
- **C: assemble `substCurve_eq_zero`** once A & B land → closes the last sorry, full theorem.
