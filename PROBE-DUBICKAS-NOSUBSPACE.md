# PROBE — Dubickas Theorem 1 without Lemma 6 (phase 9)

**Status (2026-09-28, eighth lap): the residual is TWO named Corvaja–Zannier statements.**  The
rational-power case is unconditional (from `Ridout1957`); CZ's **Lemma 4 is proved outright, with no
escape branch, for every multiplicatively-closed exponent set** (Newton's identities kill every tie
size — see the eighth-lap section); and the *only* remaining strength is CZ's main theorem (his
Lemma 3), the `p`-adic Subspace Theorem, plus the *density* of the index set it produces.

After phase 8, the three ⚓ OEIS-linked headlines in
`NumberTheory/Transcendence/Dubickas.lean` rest on a single hypothesis, `Dubickas2022`
(Dubickas's Lemma 6, from Corvaja–Zannier 2004 via the `p`-adic Subspace Theorem).  It is
consumed exactly once, in `exists_pisot_pow` (`DubickasPisot.lean`), at `q = 2`, `s_n = 2ⁿ`.

## What Lemma 6 actually is

Dubickas (2022), p. 574–575, builds Lemma 6 out of three cited pieces:

| his label | content | strength |
|---|---|---|
| Lemma 3 | Corvaja–Zannier's main theorem (Acta Math. 193 (2004), p. 177) at `δ = 1`, `u = α^(s_n)`, `Γ = {α^t}`: if `q α^(s_n)` is **pseudo-Pisot** for only finitely many `n`, then `‖q α^(s_n)‖ ≥ (1−ε)^(s_n)` eventually | **`p`-adic Subspace Theorem** (Schlickewei) |
| Lemma 4 | CZ's Lemma 4: if the trace of `q_n α^(s_n)` is a nonzero integer and `log q_n = o(n)`, then `α` is an `ℓ`-th root of a rational or an algebraic integer | number-theoretic, *not* subspace |
| Lemma 5 | pseudo-Pisot infinitely often ⇒ some `α^(s_m)` is Pisot | elementary, given Lemma 4 |

Lemma 6 = Lemma 3 ∨ Lemma 5.  **All of the subspace strength sits in Lemma 3.**

## What this lap closed, unconditionally

`DubickasNoSubspace.lean` (all sorry-free unless marked):

* `Diophantine.mahler_mul_of_ridout1957` (in `NumberTheory/Diophantine/Edges.lean`) —
  **Mahler (1957 II) with a positive integer multiplier**: for `u > v ≥ 2` coprime and `q ∈ ℕ`,
  `‖q (u/v)ⁿ‖ > e^(−εn)` for all large `n`, derived from `Ridout1957` by Mahler's §3 route with
  `ϑ = q`, `c = 2q`, `p = round(q αⁿ)·vⁿ`, `Q = uⁿ`.  (`Literature.Mahler1957` is the `q = 1`
  case Saito quotes; Dubickas's §2 remark needs the multiplier, and so do we, because our
  approximants are half-integers: `‖2α^(2ⁿ)‖` small does **not** bound `‖α^(2ⁿ)‖`.)
* `round_dist_le_of_bnd` — the hypotheses `2 y_n ∈ ℤ`, `|y_n − α^(2ⁿ)| ≤ C α^(−2ⁿ)` say exactly
  `‖2 α^(2ⁿ)‖ ≤ e^(−(log α / 2) 2ⁿ)` for large `n`.
* `isPisot_of_rat_den_one` — a rational integer `> 1` is Pisot (linear minimal polynomial, so no
  other conjugates to bound).
* `exists_pisot_pow_of_rat`, `exists_pisot_pow_of_pow_rat` — **if `α^(2^a)` is rational for some
  `a`, the conclusion of Lemma 6 holds with no hypothesis beyond `Ridout1957`.**  This is exactly
  the route Dubickas sketches in his §2 for Wagner–Ziegler's Theorem 1.
* `exists_pisot_pow_noD (hR : Ridout1957)` — reduces the full statement to the one residual:

## The decomposition now in `src/` (second lap)

`exists_pisot_pow_pseudoPisot_core` is **proved** from exactly two named literature leaves, and
nothing else:

| leaf | strength | status |
|---|---|---|
| `corvajaZannier_dichotomy` (CZ main thm p. 177 = Dubickas Lemma 3) | `p`-adic Subspace Theorem | `sorry` — the wall |
| `corvajaZannier_lemma4` (CZ Lemma 4) | valuations/traces in `ℚ(α)`, **not** subspace | `sorry` — next lap |

Everything between them is elementary and formalized: `IsPseudoPisotMul` (pseudo-Pisot for `qβ`,
phrased through `β`'s conjugates — the conjugates of `qβ` are `q` times `β`'s and
`trace(qβ) = q·trace β`), `isPisot_of_pseudoPisotMul` (Lemma 5's algebraic-integer branch: `‖qw‖<1`
and `q ≥ 1` give `‖w‖<1`), `otherConj_eq_zero_of_pow_rat` + `eq_rat_of_otherConj_eq_zero` (Lemma 5's
root-of-a-rational branch: if `β^l ∈ ℚ` then *every* conjugate has modulus `β > 1`, so pseudo-Pisot
forces `β ∈ ℚ`, which `hnr` forbids), `card_otherConj_pow_le` (`deg α^N ≤ deg α`, uniformly in `N`,
via `minpoly.natDegree_le` over `ℚ⟮α⟯`), and the derivation — Dubickas's "we may assume the trace is
nonzero" — that `trace(2α^(2ⁿ)) ≠ 0` once `α^(2ⁿ) > deg α`, since the other conjugates contribute
less than `card/2`.

## The obstruction, precisely

The residual, `corvajaZannier_dichotomy`:

> `α > 1` algebraic, `q ≥ 1`, `s` strictly monotone: if `q α^(s n)` is pseudo-Pisot for only
> finitely many `n`, then `‖q α^(s n)‖ > e^(−ε s n)` eventually.

Why the elementary tools do not reach it:

1. **Archimedean Liouville/Roth is vacuous here.**  Put `θ_N = 2α^N − k_N` with
   `k_N = 2y_n`, `N = 2ⁿ`.  If `α` is an algebraic integer, `∏_σ σ(θ_N) ∈ ℤ ∖ {0}`, so
   `∏_{σ≠1}|k_N − 2σ(α)^N| ≥ 2^{−d}/|θ_N| ≥ α^N/(2^d C)`.  That is a **lower** bound on the
   conjugate product, i.e. precisely the inequality `M(α) ≥ α` that holds for every algebraic
   number; it carries no information.  Getting an **upper** bound on that product is the same as
   knowing the conjugates are small — what we are trying to prove.  Roth/Ridout applied to `α^N`
   likewise only says `H(α^N) ≳ α^N`.  This kills the first lead in the file header.
2. **Degree 1 is already Mahler's problem.**  For `α = p/q` non-integral, the product formula
   gives only `|θ_N| ≥ 1/(2q^N)`, which is *weaker* than the hypothesis `|θ_N| ≤ 2Cα^{−N}`
   exactly when `p < q²` — e.g. `α = 3/2`, where the required statement is Mahler's problem on
   `‖q(3/2)ⁿ‖`.  So even the rational case is not elementary; it is closed above **only** because
   this repo has `Ridout1957 ⇒ Mahler1957` as a theorem (phase 5) and the same route gives the
   multiplier form.  Sparse exponents `N = 2ⁿ` are also why Pisot's classical
   `∑‖λβⁿ‖² < ∞ ⇒ β` Pisot theorem is unavailable: it needs *all* `n`.
3. **The Böttcher/Mahler-method lead (second lead in the file header) is refuted.**
   `α = Φ_c(y_0)` with `Φ_c ∘ f = Φ_c²`, `f(z) = z² − c`.  Mahler's method needs a functional
   equation `F(z^p) = R(z, F(z))` with `R` rational; conjugating `f` to `z ↦ z²` is what `Φ_c`
   itself does, and `Φ_c` is not algebraic, so no Mahler-method transcendence criterion
   (Nishioka's included) applies.  Nothing was gained over the dynamical formulation.

## The smallest literature `Prop` that closes it (proposal — deliberately *not* stated in `Literature/`)

Two candidates, in increasing generality; either one suffices and both are strictly more
canonical than `Dubickas2022`, because they are the *published* statements rather than Dubickas's
packaging of them.

1. **`CorvajaZannier2004` (his Lemma 3) — recommended.**  With a `def IsPseudoPisot (z : ℂ)`
   (`1 < ‖z‖`, all other conjugates in the open unit disc, `trace z ∈ ℤ`):
   for `α > 1` algebraic, `q : ℕ` positive, `s : ℕ → ℕ` strictly monotone, if
   `{n | IsPseudoPisot (q α^(s n))}` is finite then `∀ 0 < ε < 1, ∃ n₀, ∀ n ≥ n₀,
   (1 − ε)^(s n) ≤ ‖q α^(s n)‖`.  This is CZ 2004, main theorem, p. 177, at `δ = 1`,
   `u = α^(s n)`, `Γ = {α^t}`.  Deriving `exists_pisot_pow_pseudoPisot_core` from it then needs
   CZ's Lemma 4 + Dubickas's Lemma 5 (elementary; Lemma 5's rational-root branch is the `v = 1`
   argument we already formalized in `exists_pisot_pow_of_rat`).
2. **`SchlickeweiSubspace` — the `p`-adic Subspace Theorem** itself (Schlickewei 1977), in the
   `Literature/Diophantine` idiom (finitely many `S`-unit-scaled solutions of a linear-form
   inequality lie in finitely many proper subspaces).  Strictly deeper, reusable by the Catalan
   and Mills threads, but CZ 2004 → our core is then a multi-lap formalization of its own.

A third, narrower option worth recording: our situation has an **exact recursion**
`y_{n+1} = y_n² − c`, hence `2α^{2^n}δ_n → c` (so `y_n = α^{2ⁿ} + c/(2α^{2ⁿ}) + O(α^{−3·2ⁿ})`).
Nothing in the obstruction above is improved by it: the conjugate sequences `σ(δ_n)` satisfy the
same recursion, which is an identity, not new information at the non-archimedean places.

## Recommended next step (updated after the decomposition lap)

`corvajaZannier_lemma4` is the one that can be attacked *without* the subspace theorem: if `α` is
not an algebraic integer, some prime `𝔭` of `ℚ(α)` has `v_𝔭(α) < 0`, and `trace(q α^(s n)) ∈ ℤ`
forces `v_𝔭` of a sum of `n`-th powers to stay `≥ 0`; a unique conjugate of minimal valuation gives
`v_𝔭(trace) = n·v_𝔭(α) + v_𝔭(q) → −∞`, a contradiction, and the tie case (all conjugates sharing
the valuation pattern at every place) is exactly the `α^l ∈ ℚ` branch.  mathlib has
`IsDedekindDomain.HeightOneSpectrum` valuations and the number-field trace, so this is a real
multi-lap target rather than a wall.  Close it before touching Lemma 3.

### The Lemma-4 attack, worked out for `d = 2` (2026-09-28, third lap)

Let `P = a₀X² + a₁X + a₂ ∈ ℤ[X]` be primitive irreducible with roots `α > 1` and `α'`, and
`u_N = α^N + α'^N = Tr(α^N) ∈ ℚ`.  Suppose `2 u_N ∈ ℤ` for infinitely many `N` and `p ∣ a₀`.
Write `v = v_p`, `s = u_1 = −a₁/a₀`, `t = αα' = a₂/a₀`.  Primitivity gives
`min(v a₀, v a₁, v a₂) = 0`, so `v a₀ ≥ 1` forces `min(v a₁, v a₂) = 0`.

* If `v a₂ = 0` then `v t = −v a₀ < 0`, so some root has negative valuation.
  * **Distinct root valuations** (`2 v s < v t`, i.e. the Newton polygon has two slopes):
    `v(u_N) = N · v(r₁)` with `v(r₁) = v s < 0`, so `v(2u_N) → −∞` — contradiction after finitely
    many `N`.  No cancellation is possible.
  * **Equal root valuations** (`v r₁ = v r₂ = v t / 2 < 0`): `u_N = r₁^N (1 + ρ^N)` with `ρ = r₂/r₁`
    a unit, so `v(u_N) = N v t / 2 + v(1 + ρ^N)`.  Infinitely many `N` with `v(u_N) ≥ −1` forces
    `v(1 + ρ^N) ≥ −1 − N v t / 2 → ∞`.  If `1 + ρ^N = 0` for two exponents then `ρ` is a root of
    unity, `α' = ζ α`, and `α^l ∈ ℚ` — **this is exactly Lemma 4's second branch** (witness:
    `2X² − 3`, `α = √(3/2)`, `u_N = 0` for every odd `N`, `α² = 3/2 ∈ ℚ`).  Ruling out the
    "unbounded but never exact" case is a small `p`-adic Skolem–Mahler–Lech step.
* If `v a₂ ≥ 1` then `v a₁ = 0`; then `v s = −v a₀ < 0` and `v t ≥ 1 − v a₀ > 2 v s`, so the
  Newton polygon has two distinct slopes and the first bullet applies.

So for `d = 2` the only obstruction to a fully elementary proof is the unit-ratio step, and the
tie case is the source of the root-of-a-rational branch — a good sign that CZ's Lemma 4 is *not*
subspace-strength.  What Lean needs: `ℚ_p`, the Newton polygon (or just the quadratic formula in a
ramified quadratic extension), and `v(2u_N) ≥ 0`.  A faithful `ON-LINE-REQUEST` for CZ's own proof
is filed (2026-09-28) so the next lap can follow their argument instead of this reconstruction.

**The no-tie case is formalized, and the bridge to it as well (see the fourth-lap section below)** (2026-09-28): `no_bounded_den_of_unique_max_valuation` is the
whole ultrametric argument for an arbitrary number field — `v(z^N + Σ_w w^N) = (v z)^N` when `z`
strictly dominates, versus `v ≤ (v q)⁻¹` from `q U_N ∈ ℤ`.  It needs no archimedean input and no
hypothesis beyond the unique-maximum.  What remains is the bridge (splitting field of `minpoly ℚ α`
inside `ℂ` as a `NumberField`, `tracePowSum` transferred into it, dominating prime from
`HeightOneSpectrum.mem_integers_of_valuation_le_one`) and the tie case.

**Prerequisites now proved** (so the remaining Lemma-4 work is *only* the `p`-adic core):
`tracePowSum α N = Σ_w w^N = Tr_{ℚ(α)/ℚ}(α^N)`, `tracePowSum_rat` (rational),
`tracePowSum_recurrence` (`Σ_{k ≤ d} p_k U_(N+k) = 0`, each conjugate contributing `w^N p(w) = 0`),
`isIntegral_int_iff_minpoly_den` (`IsIntegral ℤ α ↔ every `minpoly ℚ α` coefficient has denominator
`1`, via `Polynomial.lifts_and_natDegree_eq_and_monic`).  Multiplying the recurrence by a common
denominator `D` gives the integer recurrence whose leading coefficient is `D`; `D = 1` is exactly
integrality, and a prime `p ∣ D` is exactly a prime at which some conjugate has negative valuation.

**Already free in our application** (proved earlier, so any future proof of Lemma 4 may assume it):
every conjugate `w` of `α` satisfies `‖w‖ < 1` or `‖w‖ = α` — `aroots_pow_mem` (conjugates of a
power are powers of conjugates, via `(minpoly ℚ (α^N)).comp (X^N)`), `norm_lt_one_of_pseudoPisotMul`,
`norm_eq_of_pow_eq`.  The `‖w‖ = α` case means `w = ζα` with `ζ^N = 1`.

### The bridge is BUILT; the residual of Lemma 4 is exactly its tie case (2026-09-28, fourth lap)

`conjField α` (= `IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet ℂ)`) is a `NumberField`
*unconditionally* — for transcendental `α`, `minpoly ℚ α = 0` and the root set is empty — so the
instances `conjField.finiteDimensional` / `conjField.numberField` are global, and the handoff's
"`haveI` inside the proof" worry is gone.  `conjMultiset α` is the conjugate multiset inside it,
built by `Multiset.pmap` from `(minpoly ℚ α).aroots ℂ` (no `Splits`/`aroots_map` needed), and
`conjMultiset_pow_sum_coe` says its power sums push down to `tracePowSum α N`.

On top of that, **`exists_tie_of_bounded_den` is proved and axiom-clean**:

> if `q · U_N ∈ ℤ` for infinitely many `N` and `α` is **not** an algebraic integer, then there is a
> prime `v` of `conjField α` and two *distinct* conjugates `z ≠ w` with
> `v z = v w = max_y v y > 1`.

(Route: `¬IsIntegral ℤ α ⇒ ∃ v, v α > 1` by the contrapositive of
`HeightOneSpectrum.mem_integers_of_valuation_le_one`; take `z` of maximal valuation, so `v z > 1`;
if the maximum were unique, `no_bounded_den_of_unique_max_valuation` gives `False`.)

So CZ's Lemma 4 is now reduced to a **purely local** statement.  Write the dominant conjugates as
`z u_i` with `u_i ∈ O_v^*`, `u_1 = 1`, `k = |W| ≥ 2`.  Then
`U_N = z^N (Σ_{i≤k} u_i^N + ε_N)` with `v ε_N = (v ε)^N → 0`, and `v U_N ≤ (v q)^{-1}` forces
`v(Σ_i u_i^N) → 0` along the infinite index set, i.e. the `v`-adic valuation of a sum of `N`-th
powers of units tends to `+∞`.  The needed conclusion is that some `u_i/u_j` is a root of unity —
a `p`-adic Skolem–Mahler–Lech step.  Two concrete handles for the next lap:

* **Compactness.** `(O_v^*)^k` is compact, so `(u_i^{N_j})_j` has a convergent subnet, whose limit
  `(c_i)` lies in the closure of the procyclic group generated by `(u_i)` and satisfies
  `Σ_i c_i = 0`.  That is a genuine multiplicative relation; turning it into a root of unity needs
  the structure of the closure.
* **Sparse exponents are an advantage, not an obstacle, here.**  Our application only needs
  `N = 2^n`.  For each `m`, `h = |(O_v/π^m)^*|` is finite and `n ↦ 2^n mod h` is *eventually
  periodic*, so `Σ_i u_i^{2^n} mod π^m` is eventually periodic in `n`; the infinitely many `n` in
  the index set then pin its value to `0` on a whole residue class.  A version of Lemma 4 special
  to `N = 2^n` may therefore be much cheaper than the general one, and it is all the headline needs.

Also worth recording: the archimedean input `hsmall` does **not** help with ties — ties are a
non-archimedean phenomenon, and `2X² − 3` (`α = √(3/2)`, `U_N = 0` for odd `N`) shows the tie case
is genuinely nonvacuous.

### The tie case is reduced to ONE local leaf; Lemma 4 is proved in the nondegenerate case (fifth lap)

`false_of_bounded_den_of_nondegenerate` (proved) handles **both** halves at the level of an
arbitrary number field.  Split the conjugate multiset `R` at a prime `v` into the dominant part
`W = {w : v w = V}` (`V = max`, `> 1`) and the rest.  If `|W| = 1` this is
`no_bounded_den_of_unique_max_valuation`.  If `|W| ≥ 2`, normalize: `U = {w / z : w ∈ W}` are
`v`-units, and

    v(Σ_{u ∈ U} u^N) = v(Σ_W w^N) / V^N ≤ max((v q)⁻¹, r₀^N) / V^N ≤ B · r^N,
    r = max(V⁻¹, r₀/V) < 1,  B = max((v q)⁻¹, 1),  r₀ = max_{w ∉ W} v w < V.

So the entire residual of CZ's Lemma 4 is the local leaf

> **`valuation_sum_unit_pow_nondegenerate`** — units `u_1, …, u_k` (`k ≥ 2`) at a prime `v`, no two
> of which satisfy `u_i^l = u_j^l`, cannot have `v(Σ_i u_i^N) ≤ B r^N` (`r < 1`) along an infinite
> set of exponents `N`.

and at the level of `α` this yields **`isIntegral_of_bounded_den_of_nondegenerate`** (proved modulo
that leaf): *if no two distinct conjugates of `α` share a power, bounded denominators of the trace
power sums along an infinite exponent set make `α` an algebraic integer.*

**Proof sketch for the leaf** (the next real target; mathlib is missing the input): pass to an
arithmetic progression `N = r + h t` with `u_i^h ∈ 1 + π^m`, `m > 1/(p−1)`.  Then
`t ↦ Σ_i u_i^r (u_i^h)^t` is a convergent `p`-adic power series on `ℤ_p`, not identically zero by
nondegeneracy, so **Strassmann's theorem** gives finitely many zeros `t_1, …, t_s ∈ ℤ_p` and
`ord_v(Σ_i u_i^N) ≤ C + Σ_j ord_p(t − t_j)`.  Geometric decay forces `ord_p(t − t_j) ≳ c t`, hence
`p^{c t} ∣ t' − t` for two exponents in the set, so the exponent set must grow at least like a
**tower**.  For `N = 2^n` (all the headline needs) consecutive `t` roughly double, which is far
below `p^{c t}` — contradiction.  **mathlib has no Strassmann theorem / `p`-adic Weierstrass
preparation**; that is the concrete prerequisite to build (or to request as a `Literature` `Prop`).

**The degenerate branch is now the other gap, and it is a genuine gap, not laziness.**  From
`w^l = w'^l` for distinct conjugates one gets only `deg(α^l) < deg α` (the fibre of `w ↦ w^l` over
`α^l` has `≥ 2` elements, and every fibre has size `[ℚ(α):ℚ(α^l)]`) — a *descent*.  It cannot be
iterated naively: the hypothesis for `α^l` needs infinitely many `N` with `l N ∈ S`, and for
`S ⊆ {2^n}` that already fails unless `l` is a power of `2`.  CZ's own proof of the `α^l ∈ ℚ`
branch is therefore the thing to read (`ON-LINE-REQUEST.md`, filed 2026-09-28, still unanswered).

### Sixth lap: the sparse-index obstruction, and the archimedean constraint that answers it

**Correction to the fifth lap's optimism.**  The Strassmann route bounds
`ord_v(Σ_i u_i^N) ≤ C + Σ_j ord_p(t − t_j)`, and geometric decay then forces
`p^{c t} ∣ t' − t` for consecutive members of the index set — i.e. the index set must grow at least
like a **tower**.  `{2^n : n ∈ S}` with `S` merely infinite is *not* excluded (`S = {2^j}` gives
`{2^(2^j)}`, a tower).  So even with Strassmann in hand the leaf does **not** close for an arbitrary
infinite index set: it closes for index sets of at most exponential growth, e.g. a cofinite one.
The same objection kills the cheap `k = 2` case (`Σ = u_1^N(1 + ρ^N)`, where the elementary bound
`ord_v(ρ^M − 1) ≤ C + e·log_p M` — from the order of `ρ` in `(O_v/π^m)^*` growing like `p^{m/e}` —
needs exactly the same non-sparseness).  Recording this because it is the reason CZ may well need
subspace strength for Lemma 4 too; `ON-LINE-REQUEST.md` asks for their proof.

**The answer: the index set can be made cofinite, at the price of "near-integer".**  New in `src/`
(proved, axiom-clean): `tracePowSum_near_int` and `tracePowSum_den_grows`.  Once **one** pseudo-Pisot
exponent `n₁` exists, every conjugate `w` of `α` either satisfies `w^(2^n₁) = α^(2^n₁)` — and then
`w^(2^n) = α^(2^n)` for *every* `n ≥ n₁` — or has `‖w‖ < 1`.  Hence for **all** large `n`

    2 U_(2^n) = k (2 α^(2^n)) + O(ρ^(2^n)) = k (2 y_n) + O(α^(−2^n)) + O(ρ^(2^n)),

with `k ≥ 1` the number of collapsing conjugates and `2 y_n ∈ ℤ`.  So `2 U_(2^n)` is within
`C₂ r^(2^n)` (`r = max(α⁻¹, ρ) < 1`) of a rational integer for every large `n`, and therefore

> **either `2 U_(2^n) ∈ ℤ`, or its denominator is `≥ (C₂ r^(2^n))⁻¹ ≍ α^(2^n)`.**

**The constraint this yields.**  Combine with the valuation side: if `α` is not an algebraic integer
and at some prime the dominant conjugate valuation is *unique*, then `ord_v(U_N) = N·ord_v(z)`
exactly, so the denominator of `U_N` is `≍ D_v^N` with `D_v = p^{(−ord_v z)/e_v} > 1` — and
Liouville (`one_div_den_le_dist_int`) forces `D_v ≥ α`.  That is a genuine quantitative constraint
obtained with **no** Diophantine input, and it is the first thing in this thread that bites on `α`
itself.  Whether `D_v < α` can be forced (it would close the no-tie case outright) is the next
question; note `D = ∏_p D_p ≤ a₀` and `D_v ≥ α` therefore implies `a₀ ≥ α`, i.e.
`M(α) ≥ α^(k+1)` — no contradiction yet, since nothing bounds the Mahler measure of `α` a priori.

**A bypass that was examined and refuted.**  `c_eq_zero_or_two_uncond` does **not** need `β` to be
an algebraic integer for most of the chain: `base_bound_of_eFull_two`, the whole `bb`/`qq` analysis
and the terminal `eq_zero_or_one_of_bRec_finite_support` use only `β > 1`, `β` algebraic, all other
conjugates inside the unit disc, and `e_n ≡ 0` past `deg β − 1`.  Integrality enters at exactly one
point: `pisot_conjPowSum_add_mem_int` in `exists_pisot_trace_ident`, to identify `y_(m+j)` with
`Tr(β^(2^j))`.  For that, `den(Tr β^N) ≪ β^N` suffices — strictly weaker than integrality.  But it
is **not** free: `9X² − 18X + 2` has the root `β = 1 + √7/3 ≈ 1.8819`, whose other conjugate is
`≈ 0.118` and whose trace is `2 ∈ ℤ` — a genuine pseudo-Pisot number — and `3` splits in `ℚ(√7)`,
so `ord_3(Tr β^N) = −N` and `den(Tr β^N) = 3^N ≫ β^N`.  Pseudo-Pisot alone therefore does not give
the denominator bound; the hypothesis "integral trace for infinitely many `N`" must be used.

### Seventh lap: the double tie CLOSES elementarily — the residual is sparsity, not `p`-adic analysis

The Graeffe identity, read through `v`, does what Strassmann was wanted for.  For `v`-units
`u₁, u₂`,

    2 (u₁ u₂)^N = (u₁^N + u₂^N)² − (u₁^(2N) + u₂^(2N)),

and the left side has valuation **exactly** `v 2` — a fixed nonzero quantity.  So the two power sums
at `N` and `2N` cannot both be highly divisible.  Proved and axiom-clean in `src/`:
`valuation_two_le_of_two_unit_pow_sums`, `false_of_two_unit_pow_sums_small`,
`valuation_sum_unit_pow_card_two` (the leaf's own shape, for `card U = 2`), plus the `ℤₘ₀` helper
`exists_mul_pow_lt`.  **No nondegeneracy hypothesis is needed.**

The same collapse handles a tie of any size `k`, as soon as the exponent set is closed under
multiplication by `1, …, k`: with `x_i = u_i^N`, Newton's identities `j e_j = Σ_i (−1)^(i−1) e_(j−i) p_i`
and `ord_v(p_i) = ord_v(Σ x_i^i) = ord_v(S_(iN)) ≥ cN − C` give, by induction on `j`,
`ord_v(j! e_j) ≥ cN − C`; at `j = k` this says `ord_v(k! ∏_i u_i^N) ≥ cN − C → ∞` while `∏ u_i` is a
unit — contradiction.  (Consistency check: `α = √(3/2)` has `U_N = 0` for odd `N` but
`U_(2M) = 2(3/2)^M`, so the hypothesis *fails* on a doubling-closed set, as it must.)

**So the obstruction has moved, and it is now a single sharp statement**: the exponent set
`{2^n : n ∈ S}` is only known to be *infinite*, and neither the Newton/Graeffe collapse nor
Strassmann applies to an arbitrarily sparse set.  Closing CZ's Lemma 4 for our application therefore
needs one of:

1. **`S` cofinite (or of bounded gaps / closed under doubling).**  `S` is the pseudo-Pisot index set
   produced by CZ's *Lemma 3*; nothing in the current derivation makes it dense.  If Lemma 3 can be
   made to deliver a cofinite `S` (its conclusion is "for all large `n`" in the *other* branch, so
   this is a question about how the two branches are split), Lemma 4 becomes elementary **and the
   whole tie problem disappears**.  ⟵ *this is the most promising next attack.*
2. bounded denominators at exponents `N, 2N, …, kN` — i.e. near-integrality at exponents that are
   not powers of `2`, which the archimedean input does not supply (`y_n` exists only at `2^n`).
3. subspace strength.

Note also that `tracePowSum_den_grows` (sixth lap) gives a *cofinite* statement of the near-integer
kind, so route 1 is not hopeless: the archimedean side is already cofinite; it is the *arithmetic*
(exact-integer) side that is sparse.

### Eighth lap: the degenerate branch of Lemma 4 is an ARTIFACT — Newton kills every tie size

The `k = 2` Graeffe collapse generalizes to arbitrary tie size, and the generalization is *shorter*
than the special case.  New in `src/`, all axiom-clean:

* `valuation_natCast_le_one`, `valuation_multiset_prod_eq_one`, `valuation_finset_sum_le`,
  `valuation_esymm_le_one`, `multiset_esymm_card` — the local toolkit.
* **`valuation_factorial_mul_esymm_le`** — for a multiset `x` of `v`-units with `|x| = k`, if
  `v(p_l(x)) ≤ ε` for every `1 ≤ l ≤ k` then `v(j! · e_j(x)) ≤ ε` for every `1 ≤ j ≤ k`.
  *No induction is needed*: multiply Newton's identity
  `j e_j = (−1)^(j+1) Σ_{i<j} (−1)^i e_i p_(j−i)` (mathlib-free, from the repo's
  `multiset_mul_esymm_eq_sum`) through by `(j−1)!`; each summand is then
  `(something of valuation ≤ 1) · p_(j−i)`, because `i! ∣ (j−1)!` is not even required — `v(m!) ≤ 1`
  and `v(e_i) ≤ 1` hold separately for *every* integer `m` and every `i`.
* **`valuation_sum_unit_pow_mulClosed`** — hence: `v`-units `u_1, …, u_k` (`k ≥ 1`) and an infinite
  exponent set closed under multiplication by `1, …, k` cannot have `v(Σ_i u_i^N) ≤ B r^N`, `r < 1`.
  At `j = k`, `e_k(x) = (∏ u_i)^N` is a unit, so the left side is the **fixed nonzero** `v(k!)`.
  **No nondegeneracy hypothesis, and `k = 1` (the no-tie case) is included.**
* **`false_of_bounded_den_mulClosed` / `isIntegral_of_bounded_den_mulClosed`** — so CZ's Lemma 4
  holds for a multiplicatively-closed exponent set **with no escape branch at all**: the conclusion
  is `IsIntegral ℤ α`, not `IsIntegral ℤ α ∨ ∃ l, α^l ∈ ℚ`.  The old disclosed leaf
  `valuation_sum_unit_pow_nondegenerate` is **deleted** (superseded), taking `src/` from three
  disclosed `sorry`s to **two**, both now named published statements of Corvaja–Zannier.

**What this settles conceptually.**  The `α^l ∈ ℚ` branch of CZ's Lemma 4 is *not* an intrinsic
feature of the local analysis; it is exactly what an exponent set that is **not** closed under
multiplication buys.  The canonical witness confirms it: `α = √(3/2)` has `U_N = 0` for every odd
`N` (so the hypothesis holds on the odds) but `U_(2M) = 2(3/2)^M` has denominator `2^M` (so it fails
on any doubling-closed set).  Consequently **the entire residual of Lemma 4 is now the DENSITY of
the index set produced by CZ's Lemma 3** — a single, sharply stated question, with no `p`-adic
analysis left in it (Strassmann is not needed anywhere; the earlier laps' Strassmann plan is
obsolete).

**The remaining inequality.**  `D α` is an algebraic integer for some positive integer `D` (`D ∣ a₀`),
so `den(U_N) ∣ D^N`.  Pair that *upper* bound with the proved `tracePowSum_near_int` (for all large
`n`, `2 U_(2^n)` is within `C r^(2^n)` of an integer, `r = max(α⁻¹, ρ)`) and `one_div_den_le_dist_int`:
for every large `n`, either `2 U_(2^n) ∈ ℤ` or `(D r)^(2^n) ≥ 1/(2C)`.  Hence

> **if `D · max(α⁻¹, ρ) < 1` then `2 U_(2^n) ∈ ℤ` for every large `n`** — the index set is cofinite,
> so it is multiplicatively closed, so `isIntegral_of_bounded_den_mulClosed` applies and `D = 1`.

So the *whole* obstruction is now the inequality `D ≥ min(α, ρ⁻¹)`, i.e. a lower bound on the
Mahler measure `M(α) = D' α^k` of a growth constant.  Nothing bounds `M(α)` a priori (the
pseudo-Pisot number `β = 1 + √7/3`, root of `9X² − 18X + 2`, has `D = 3`, `α ≈ 1.88`, `ρ ≈ 0.118`),
which is one more independent confirmation that the missing strength lives in Lemma 3.

### Eighth lap, part 2: the denominator CEILING, the cofiniteness dichotomy, and the `ζ₃` witness

All proved and axiom-clean in `src/`:

* `isIntegral_multiset_sum`, **`exists_common_integral_multiple`** — one positive integer `D` with
  `D w` an algebraic integer for *every* conjugate `w` of `α`.  (`conjField α` is a `NumberField`, so
  mathlib's `exists_integral_multiples ℤ ℚ` supplies all the multipliers at once.)
* **`exists_tracePowSum_den_dvd`** — hence `den(U_N) ∣ D^N`: `D^N U_N = Σ_w (D w)^N` is a sum of
  algebraic integers and is rational, so it is a rational integer.  *This is the upper bound the
  sixth lap was missing; it had only the lower bound `den ≍ D_v^N`.*
* **`tracePowSum_int_of_near_int_of_den_lt`** — the **cofiniteness dichotomy**.  If `2 U_(2^n)` is
  within `C₂ r^(2^n)` of a rational integer for all large `n` (what `tracePowSum_near_int` gives once
  one pseudo-Pisot exponent exists) and `D r < 1`, then `2 U_(2^n)` is *exactly* a rational integer
  for **every** large `n`.  Liouville (`one_div_den_le_dist_int`) versus the ceiling: the two can
  only coexist if `(D r)^(2^n) ≥ 1/(2C₂)`.
* `false_of_bounded_den_tie_le` — Lemma 4's local step refined so that the exponent set need only be
  closed under multiplication by `1, …, K` where `K` bounds the **tie size** at `v`
  (`false_of_bounded_den_mulClosed` is the case `K = |R|`).  At `K = 2` that is *doubling closure*.
* **`isIntegral_of_tie_le_two_of_den_lt`** (the capstone) — if `D r < 1` **and** the dominant
  conjugate valuation is attained at most twice at every prime, then `α` **is** an algebraic integer.
  Equivalently: a non-integral growth constant must have `D ≥ r⁻¹ = min(α, ρ⁻¹)` **or** a triple tie
  at some prime.

**The `ζ₃` witness — why doubling closure cannot be pushed past tie size 2.**  Take a prime `v` whose
local field contains `ζ₃` and set `u_i = ζ₃^i c` (`i = 0, 1, 2`) for a unit `c`.  Then
`Σ_i u_i^N = c^N Σ_i ζ₃^{iN} = 0` whenever `3 ∤ N` — in particular for **every** `N = 2^n`.  So the
`k = 3` tie survives an exponent set that is merely closed under doubling, and it is killed only by
an exponent `3N` (where the sum is `3c^{3N}`, a unit times `3`).  This is a *definitive* refutation
of the seventh lap's hope that doubling closure might suffice in general, and it pins the requirement
to closure under multiplication by `1, …, k` exactly.  Note also that the witness is degenerate
(`u_1^3 = u_2^3`, so `w^3 = w'^3` for two conjugates): the surviving case is precisely
Corvaja–Zannier's `α^l ∈ ℚ` branch, and the descent it offers is useless here because `{N | 3N ∈ S}`
is empty for `S ⊆ {2^n}`.

**State of the residual after this lap.**  For a non-integral growth constant `α`, at least one of:

1. `D ≥ min(α, ρ⁻¹)` — a lower bound on the Mahler measure that nothing currently supplies
   (`9X² − 18X + 2` shows pseudo-Pisot-ness alone does not forbid it);
2. some prime of `conjField α` carries a **triple** tie of dominant valuations, i.e. a non-`2`-power
   root of unity among the conjugate ratios (CZ's degenerate branch, whose descent is blocked by the
   sparsity of `{2^n}`);
3. the pseudo-Pisot index set `S` produced by CZ's Lemma 3 is sparse — which is what makes 1 and 2
   unresolvable and is therefore the single remaining question.

## Earlier recommendation (still valid for Lemma 3)

Do **not** take option 2 first.  Option 1 splits the residual into one subspace-strength `Prop`
plus two genuinely elementary lemmas (CZ Lemma 4, Dubickas Lemma 5), which is the same shape that
made phase 5 (`Ridout1957 ⇒ Mahler1957`) and phase 8 (Lemma 8 elimination) work.  The `hD` on the
`Dubickas.lean` headlines cannot be dropped until the core is closed; it must not be routed
through a `sorry`.
