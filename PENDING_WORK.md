# PENDING_WORK — lean-formalizations

## 🎯 ACTIVE TARGET (chosen 2026-06-14 review lap): Compass-and-straightedge impossibility

**Why this target.** Curtis 1990 is verified complete & axiom-clean (below). Its only
leftovers are Trevor's-call (mathlib upstream) or trivial (Zariski repackaging). The
umbrella's job is no-formula / impossibility meta-theorems; mathlib already has Liouville,
Lindemann–Weierstrass, and Abel–Ruffini, but **constructible-number theory is absent**
(mathlib's `Constructible.lean` is all topology/spectra). So: formalize the impossibility
of doubling the cube (and, cheaply later, trisection / regular n-gons / squaring the circle).

**Layer 1 — algebraic core (attack THIS lap; aim axiom-clean).** Three viable encodings:
1. *(preferred)* Tower predicate. `inductive IsSqrtTower : IntermediateField ℚ ℝ → Prop`
   with `base : IsSqrtTower ⊥` and `step K a (hK) (ha : a*a ∈ K) :
   IsSqrtTower ((IntermediateField.adjoin K {a}).restrictScalars ℚ)`. Define
   `Constructible (x:ℝ) := ∃ K, IsSqrtTower K ∧ x ∈ K`. Prove
   `IsSqrtTower K → ∃ n, Module.finrank ℚ K = 2^n` by induction:
   - base: `IntermediateField.finrank_bot = 1 = 2^0`.
   - step: tower law `Module.finrank_mul_finrank ℚ K K⟮a⟯` (LinearAlgebra/Dimension/Free)
     × `adjoin.finrank` (= `(minpoly K a).natDegree`, with `a` integral via monic
     `X² - C(a*a)`) which is `≤ 2` and `≥ 1` ⟹ `∈ {1,2}` ⟹ `2^0` or `2^1`.
   Then `[ℚ(a):ℚ] ∣ finrank ℚ K` ⟹ power of 2.
2. *(faithfulness anchor)* the field+sqrt closure `inductive Constructible` (rat/add/neg/
   mul/inv/sqrt) — most recognizable "constructible number" def; prove it implies (1).
3. *(witness)* `∛2`: `c := (2:ℝ)^(1/3:ℝ)`, `c^3 = 2` via rpow; `X³ - 2` irreducible over ℚ
   (Eisenstein at 2: `Polynomial.IsEisensteinAt.irreducible`; OR `X_pow_sub_C` Kummer
   results). ⟹ `minpoly ℚ c = X³-2`, `[ℚ(c):ℚ] = 3`, and `¬∃n, 3 = 2^n` ⟹ not constructible
   ⟹ cube cannot be doubled (side `∛2` from unit side).

**Layer 2 — the hard wall (multi-lap; this is the crux to bang on going forward).** A
faithful *geometric* definition: points constructible from {(0,0),(1,0)} by repeated
line∩line, line∩circle, circle∩circle, and the bridge **geometric ⟹ coordinates lie in a
quadratic tower** (line∩line stays in F; the others solve a degree-≤2 equation over F).
This is the real impossibility-grade theorem; Layer 1 alone proves "∛2 not in a sqrt tower".

**Files (to create):** `src/LeanFormalizations/Geometry/Constructible/{Defs,Tower,Doubling,
Statement}.lean` (mirror Curtis's audit-surface + engine split). Keep `Statement.lean` the
faithful audit surface.

---

## ✅ DONE (2026-06-14) — Curtis 1990 is COMPLETE and axiom-clean

The crux `substCurve_eq_zero` (Step A — the binary gate from `DIRECTION.md`) is
**closed**. Both headline theorems are machine-checked and axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
custom axioms anywhere in the repo):

- `no_polynomial_relation` — Curtis's theorem (Frobenius number of a triple is
  not algebraic over its generators).
- `no_finite_polynomial_formula` — the ℂ corollary.
- `no_finite_polynomial_formula_of_algebra` / `_int` / `_rat` — coefficients in
  any ℂ-algebra; in particular **no integer / rational polynomial formula**.
- `Anchors.lean` — faithfulness witnesses (`⟨3,7,8⟩`, Frobenius number `5`,
  proved directly *and* reproduced by Lemma 2).

### How the crux was closed (the key insight)
Curtis's **Lemma 1** (Dirichlet + Farey adjacency, to manufacture a *converging*
sequence of *coprime* points) and his projective/limit argument turned out to be
**unnecessary**. `IsAdmissible` and `Lemma2` never need `gcd(x,y)=1` — only `p∤y`
and `x∤y`. So fix ONE prime `x ≡ 1 (mod p)`, `x > p·(D+1)` (`D=F.totalDegree`):
the interval `((p−k)x,(p−k+1)x)` has length `x`, so it holds no multiple of `x`
(`x∤y` free) and `≥ D+1` residues `y ≡ p−k+1 (mod p)`. Each `(p,x,y)` is admissible
with Frobenius number `(k−2)x+y−p` (Lemma 2) → `G=substCurve F p k` vanishes there.
`D+1` such primes (Dirichlet, `Nat.exists_prime_gt_modEq_one`) give a `(D+1)²`
grid of zeros; `grid_vanish` (double univariate root-counting + `MvPolynomial.funext`)
forces `G=0`. New machinery in `GridVanish.lean` + `eval_substCurve_eq` in `Engine.lean`.

---

## NEXT TARGETS (pick one per lap; all genuine extensions, none blocked)

### A. The `n ≥ 3` generalization (completes the paper's title) — PRIME TARGET
Curtis's title is "for `n ≥ 3`". We proved `n = 3`. The reduction: an
`n`-generator formula restricted to tuples whose extra generators are redundant
(lie in `⟨s₁,s₂,s₃⟩`, e.g. `s₄ := s₁+s₂`, …) yields a 3-variable formula computing
the same Frobenius number on admissible triples → contradiction with
`no_finite_polynomial_formula`. Plan:
1. Decide the faithful Lean statement: `∀ n ≥ 3, ¬ ∃ formula in MvPolynomial (Fin n) ℂ …`
   over an `n`-admissible family. Define the family so the reduction is clean (the
   simplest: require the tuple to *contain* an admissible triple in its first 3
   slots with the rest in the generated semigroup, so the semigroup = the triple's).
2. Build the reduction map: given the `n`-formula `f`, substitute
   `X₄ := P₄(X₁,X₂,X₃), …` (fixed polynomials landing in the semigroup) to get a
   3-variable formula; show it computes `g` on admissible triples.
3. Apply `no_finite_polynomial_formula`. Risk: getting the "redundant generators
   keep the semigroup AND admissibility" bookkeeping right. Medium-size lap.

### B. Upstream to mathlib (Curtis's natural home)
`Mathlib.NumberTheory.FrobeniusNumber` has the `n=2` Chicken-McNugget theorem and
explains it stops at `n=2`. Curtis's `n=3` impossibility is the natural sequel.
Would need: mathlib naming/style pass, dropping the bespoke `IsAdmissible`/audit
framing for a mathlib-idiomatic statement, and a contribution-policy check
(reference corpus: `2026-06-07-mathlib-ai-contribution-policy.md`).

### C. Sharpen the "not algebraic" framing
State explicitly as: the point `(s₁,s₂,s₃,g)` lies on no proper hypersurface of
`ℂ⁴` — i.e. the graph is Zariski-dense. A short repackaging of `no_polynomial_relation`.

## Lemma2.lean lint warnings — LEAVE THEM
The unused-variable warnings on `lemma2`'s hypotheses (`h1,h2,h3,hk_hi,hr_hi`) are
the *mathematical* hypotheses of Curtis's Lemma 2, kept for the audit surface even
though this proof path doesn't consume all of them. Do not strip them. The two
unused-simp-arg warnings are inside Aristotle-verified tactic blocks — not worth
the regression risk to touch.

## Aristotle
Nothing genuinely open → Aristotle correctly idle. The old Lemma-1 job
(`80d9166c`) is OBSOLETE (the new proof needs no Lemma 1). Do not feed redundant
cross-confirms. Only re-engage when a new OPEN lemma exists (e.g. an `n≥3`
sub-lemma).
