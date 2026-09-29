# HANDOFF 2026-09-29 — phase 24 COMPLETE: weakest hypotheses, what follows from Conjecture 1

`NumberTheory/Transcendence/WeakSchanuel.lean` is **sorry-free**; all five frozen statements are
machine-checked and `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

| statement | route |
|---|---|
| `gelfondSchneider_of_algIndepLogs` | `λ = (log a, b log a)`; Conj 1 makes them alg. indep., but `λ₂ ∈ ℚ̄(λ₁)` |
| `baker1966_of_algIndepLogs` | pass to a `ℚ`-basis of `span ℚ (range ℓ)` (`logSubmodule`), then `eq_zero_of_algebraicIndependent_linear` over `ℚ̄` |
| `algebraicIndependent_log_primes_of_algIndepLogs` | direct; unique factorisation gives `ℚ`-independence |
| `algebraicIndependent_pi_log_primes_of_algIndepLogs` | `iπ` is a log of `−1`; trade `iπ` for `π` by trdeg |
| `strongFourExponentials_of_algIndepLogs` | `StrongSix.strongSix` at `Fin 2 × Fin 2` + the new `AffTwo.constRatioTwo` |

## The flagged item resolved

The strong-four-exponentials row was marked "Ren, about 70% confident, not checked against a
source". **It is correct.**  The only genuine obstruction was that Roy's derivation argument
(`AffineRankOne.const_ratio`) needs *three* columns — it works by forcing the three `Pⱼ` into a
two-dimensional space, which is vacuous with two.  New route, in the `AffTwo` section:

* `sym_coeff` — from `A·D = B·C` for affine forms `aff a b = a + ∑ bₖXₖ`, apply `pderiv k`,
  `pderiv l` and `eval 0` to get `AᵢD_j + A_jDᵢ = BᵢC_j + B_jCᵢ` on coefficient vectors
  `cv a b = Fin.cons a b`.
* `exists_minor_ne` — `A, B` linearly independent gives `p, q` with `A p B q − A q B p ≠ 0`.
* `eq_smul_of_sym` — with `f v = α v p + β v q` chosen so `f A = 0`, `f B = 1`, the identity at
  `(p, ·)` and `(q, ·)` gives `f A·D_j + A_j·f D = f B·C_j + B_j·f C`; combining at `j = p, q`
  gives `2 f A f D = 2 f B f C`, so `f C = 0` (char 0), so `C_j = (f D)·A_j`.
* `constRatioTwo` — the polynomial-level wrapper.

**Schanuel is never used.**  `strongSix` touches `hS` only through
`algebraicIndependent_of_exp_isAlgebraic`, so the whole of Roy's strong six exponentials
theorem is *also* a consequence of Conjecture 1 alone — worth recording in the fact graph.

## Reusable by-products

* `AffTwo.eq_smul_of_sym` — pure linear algebra: `A⊙D = B⊙C` + `A,B` independent ⟹ `C ∈ K·A`.
  This is unique factorisation of a rank-one symmetric tensor, done without a UFD.
* `logSubmodule` — the logarithms of algebraic numbers as a `ℚ`-submodule of `ℂ`, and
  `isAlgebraic_exp_rat_mul`, `isAlgebraic_exp_of_mem_span`.
* `exists_rat_basis` — a finite family of complex numbers in a `ℚ`-basis of its own span,
  with the basis elements certified to lie in the span (`exists_rat_coords` in
  `StructuralRank.lean` does not expose independence or membership).

## Next

Run `scripts/fact-graph`.  Uncovered Waldschmidt-2023 items remain: Leopoldt §2 and Conj 7
(Roy's equivalent of Schanuel).  The observation above (Conj 1 ⇒ strong *six* exponentials,
not just four) is a one-line new edge that the graph should carry.

## Addendum (same lap): Conj 1 ⇒ strong SIX exponentials

`strongSix_of_algIndepLogs` is now a theorem, not a remark.  `StrongSix.strongSix` touches
`hS : SchanuelConjecture` in exactly one place — `algebraicIndependent_of_exp_isAlgebraic hS μ
hμli hμexp`, which is `AlgIndepLogsConjecture` applied verbatim — so the whole of Roy's theorem
rests on the weaker hypothesis.  Axiom-clean.  The fact graph carries the edge.

## Addendum 2: the vacuous `SixExponentials` edge, repaired

`ExponentialsKnown.lean`'s header flags that the only "strong ⇒ six exponentials" edge in the
repo, `sixExponentials_of_strongOverQ`, has a hypothesis machine-refuted as FALSE
(`not_strongSixExponentialsOverQ`), so the edge is vacuous.  It is now replaced by a real one.

Two things had to be got right, and both are recorded as theorems rather than prose:

1. **Strong four exponentials does not imply four exponentials.**  The strong forms hypothesise
   `ℚ̄`-linear independence; the four/six exponentials statements supply only `ℚ`-linear
   independence.  When `x` is `ℚ`-independent but `ℚ̄`-dependent, `x₁ = c·x₀` with `c` algebraic
   irrational, and "all `exp (xᵢyⱼ)` algebraic" says `exp ℓ` and `exp (c·ℓ)` are both algebraic
   at `ℓ = x₀y₀ ≠ 0` — Gelfond–Schneider, which no strong-exponentials hypothesis supplies.
   Hence `fourExponentials_of_strongFour_of_gs` carries `hGS` as a second hypothesis.
2. **Strong SIX is the wrong hypothesis for this repair.**  The degenerate `y` case cannot be
   fed back to strong six: a `ℚ̄`-dependent triple need not contain a `ℚ̄`-independent pair.
   Strong four is the right input — if no pair of the `yⱼ` is `ℚ̄`-independent then they are all
   `ℚ̄`-multiples of `y₀`, which is again the Gelfond–Schneider case.

`sixExponentials_of_algIndepLogs` then discharges both hypotheses from Conjecture 1
(`strongFourExponentials_of_algIndepLogs` and `not_isAlgebraic_exp_mul_of_algIndepLogs`, the
branch-free complex Gelfond–Schneider).  Axiom-clean.  New leaves: `exists_algebraic_ratio`,
`mem_logAlgSpan_of_exp_isAlgebraic`, `sixExponentials_of_fourExponentials`.

## Addendum 3: ⚠️ `Literature.SixExponentialsShifted` is FALSE — a second dropped overbar

Found while trying to route `Conjecture 1 ⇒ FiveExponentials` through the repo's existing
`ExponentialsKnown.fiveExponentials_of_shifted`.  The degenerate-case analysis would not close,
and the reason is that the hypothesis `Prop` is false.  `not_sixExponentialsShifted` is the
kernel-checked refutation.

**Witness.**  `x = (1, √2)` and `y = (1, √2, i)`, each `ℚ`-linearly independent (the second is
the repo's `linearIndependent_one_sqrt_two_I`, already on hand from the earlier refutation),
with the shifts taken to be `βᵢⱼ := xᵢyⱼ` — legitimate, since `x` and `y` consist of algebraic
numbers, so the products are algebraic.  Then all six `exp (xᵢyⱼ − βᵢⱼ) = exp 0 = 1`.

**Root cause: identical to `StrongSixExponentialsOverQ`** (refuted earlier the same day) — a
`ℚ̄` whose overbar `pdftotext` dropped.  Waldschmidt 1988 Cor. 2.1 asks for `x` and `y`
independent over the *algebraic* numbers; over `ℚ̄` the pair `1, √2` is dependent, which is
exactly what kills the witness.  That makes two instances of the same transcription failure in
`Literature/ExponentialsKnown.lean`; the KB gotcha `pdftotext-drops-overbars` is doing real work
and every remaining `LinearIndependent ℚ` in a "strong"/"shifted" statement deserves an audit.

**Fact-graph consequence.**  `sixExponentials_of_shifted` and `fiveExponentials_of_shifted`
stay valid implications but now have a hypothesis known to be unsatisfiable, exactly like
`sixExponentials_of_strongOverQ`.  So **there is no live route to `FiveExponentials` in the
repo at present** — the one that looked live was resting on a false `Prop`.  Repairing the
frozen statement (`LinearIndependent ℚ` ⟶ independence over `integralClosure ℚ ℂ`) is an
operator decision; once repaired, the natural route is strong four + Gelfond–Schneider, as in
addendum 2.

## Addendum 4: `FiveExponentials` route restored, and its honest hypothesis set

Addendum 3 left the repo with no live route to `FiveExponentials`.
`fiveExponentials_of_algIndepLogs` supplies one; `FiveExponentials` itself is *not* vulnerable
to the addendum-3 trick (it is about `exp` of the products, not of shifted products, and
Hermite–Lindemann already kills the all-algebraic configuration).

The shape of `ExponentialsKnown.fiveExponentials_of_shifted_of_baker` is kept — put
`y₃ = γ/x₁`, so `x₀y₃ = γx₀/x₁` is the fifth number and `x₁y₃ = γ` — but "shifted six
exponentials" is replaced by the **membership** form: if all five numbers are
non-transcendental then every one of the six `xᵢyⱼ`, `j ∈ {0,1,3}`, lies in `𝓛̃`, five because
they are logarithms and the sixth because `𝓛̃ ⊇ ℚ̄`.  That is the hypothesis of strong six
exponentials, with no shifts anywhere — which is how the false `SixExponentialsShifted` gets
cut out of the route entirely.

Three degenerate cases remain, and they are three different theorems, which is why
`fiveExponentials_of_strongSix_of_baker_of_gs` carries three hypotheses:

| degenerate case | what closes it |
|---|---|
| `x` is `ℚ̄`-dependent | Gelfond–Schneider |
| `y₀, y₁` are `ℚ̄`-dependent | Gelfond–Schneider |
| `y₃ ∈ ℚ̄·y₀ + ℚ̄·y₁` | `Baker1966` — `γ ≠ 0` algebraic equals a `ℚ̄`-combination of the logarithms `x₁y₀, x₁y₁` |

**Sharper than the old route in the third case.**  With only `ℚ`-independence available that
case needed `BakerTwoLogs` (rational coefficients); the `ℚ̄`-degenerate case produces
*algebraic* coefficients, so full `Baker1966` is what is actually required.  All three
hypotheses are discharged from Conjecture 1 (`strongSix_of_algIndepLogs`,
`baker1966_of_algIndepLogs`, `not_isAlgebraic_exp_mul_of_algIndepLogs`).

Gotcha worth keeping: `linearIndependent_finSnoc` needs a `DivisionRing`, so the snoc/span step
has to run over `algebraicClosure ℚ ℂ` (an `IntermediateField`, hence a field) and be
transported to the `integralClosure ℚ ℂ` of the frozen statements by defeq — the same trick
`StrongSix.strongSix` uses.  Also: this proof needs `maxHeartbeats 2000000`.

## Addendum 5: the repaired shifted statement, and the overbar audit

`Literature/` is frozen, so the false `SixExponentialsShifted` cannot be edited from here.  What
*can* be supplied is the proof of its repaired form, so the operator's fix is a one-line swap:
`sixExponentialsShifted_bar_of_algIndepLogs` is `SixExponentialsShifted` with `ℚ`-linear
independence corrected to `ℚ̄`, derived from Conjecture 1.  Short proof — `exp (xᵢyⱼ − βᵢⱼ)`
algebraic makes `xᵢyⱼ = βᵢⱼ + ℓᵢⱼ` an algebraic number plus a logarithm, hence a member of `𝓛̃`,
so the shifts vanish into the definition of `𝓛̃` and strong six applies unchanged.  Same move
that let addendum 4 route around the false statement.

### Overbar audit (owed after two bugs in one file) — CLEAN

Every remaining `LinearIndependent ℚ` in `Literature/` checked against its source:

| file | statement | verdict |
|---|---|---|
| `Exponentials.lean` | `FourExponentialsConjecture`, `SixExponentials` | genuinely `ℚ` ✓ |
| `Schanuel.lean` | `SchanuelConjecture` | genuinely `ℚ` ✓ |
| `Waldschmidt2023.lean` | `AlgIndepLogsConjecture`, `BakerHomogeneous` | genuinely `ℚ` ✓ |
| `StructuralRank.lean` | `IsStructRank` (basis of the span) | genuinely `ℚ` ✓ |
| `Ax1971.lean` | `Ax1971` | genuinely `ℚ` ✓ |
| `Roy2001.lean` | `RoyConjecture` | genuinely `ℚ` ✓ |

The failure mode is specific to statements *about* `𝓛̃` — the "strong" and "shifted" family —
where the source writes `ℚ̄` and the plain statements write `ℚ`.  Both instances lived in
`ExponentialsKnown.lean` and are now refuted in the kernel
(`not_strongSixExponentialsOverQ`, `not_sixExponentialsShifted`).

## Addendum 6: a hard limit on the rank consequence of Conjecture 1

`StructuralRank.rank_eq_structRank_of_algIndepLogs` gives `rk M = r_str,ℚ(M)` from Conjecture 1
for matrices of **logarithms**.  The natural next question — does it extend to entries in `𝓛̃`,
where the strong exponentials statements live and where Roy's conjecture is usually posed? —
has answer **no**, and the obstruction is *unconditional*.  `not_rank_eq_structRank_of_mem_logAlgSpan`
is the kernel-checked refutation, so this is a wall, not an open problem.

The witness contains no logarithm at all.  `𝓛̃ ⊇ ℚ̄`, and algebraic numbers are `ℚ`-linearly
rich:

* `M = !![1, √2; √2, 2] = (1, √2)ᵀ(1, √2)` has rank `1` (`rank_sqrt_two_example`);
* a `ℚ`-basis of the span of its entries is `(1, √2)`, so the generic matrix is
  `!![X₀, X₁; X₁, 2X₀]`, of determinant `2X₀² − X₁² ≠ 0`, giving `r_str,ℚ(M) = 2`
  (`structRank_sqrt_two_example`).

So `IsLogMatrix` (entries are logarithms, not members of `𝓛̃`) is **sharp** in the frozen
statement, and Definition 1's `K = ℚ` is load-bearing: over `𝓛̃` the structural rank has to be
taken over `ℚ̄`, because `ℚ̄`-scalars are invisible to a `ℚ`-basis.  For `2×2` matrices the
correct `ℚ̄`-statement is exactly `strongFourExponentials_of_algIndepLogs`, via
`AffTwo.constRatioTwo`.

This also records why the *converse* half of Roy's equivalence (rank conjecture ⇒ Conjecture 1)
was not attempted this lap: the determinantal route needs matrices of affine-linear forms
(Valiant), whose constant entries are not logarithms — `exp c` is transcendental for rational
`c ≠ 0` — so it cannot be run against `IsLogMatrix`, and the `𝓛̃` version where constants are
available is the one just refuted for `K = ℚ`.  A correct converse would need `r_str` over `ℚ̄`,
which the frozen `IsStructRank` does not provide.
