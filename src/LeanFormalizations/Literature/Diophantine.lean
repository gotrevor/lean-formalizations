/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature inputs: rational approximation to algebraic numbers

Statements only (see `Literature/Primes.lean` for the rules: faithful or weaker, cited, never an
`axiom`).  These are the bedrock under a large part of irrationality/transcendence theory; this
repo does not prove them.

* `Roth1955` — Thue–Siegel–Roth, exactly as in the Encyclopedia of Mathematics entry.
* `Ridout1958` — Ridout's Theorem 1, the `p`-adic Roth theorem, stated from the paper.
* `Ridout1957SUnitDen` — the classical corollary of Ridout's *1957* paper (denominators built
  from a fixed finite set of primes, exponent `1 + δ`).  The full 1957 two-sided form is not
  stated as its own `Prop`; `Ridout1957 → Ridout1957SUnitDen` is an edge.
* `Ridout1957` — Ridout's 1957 Theorem, stated from the paper.  Mahler derives `Mahler1957`
  from it (Mahler 1957, §3).
* `Stephan2026Ridout` — Ridout's theorem as machine-checked by R. Stephan (Lean 4, 2026),
  verbatim; waits only on a toolchain match to be discharged.
* `Stephan2026Subspace` — Stephan's Subspace Theorem with several places (Schlickewei form),
  verbatim, same status.
* `Stephan2026CZMain`, `Stephan2026CZLemma4` — Corvaja–Zannier 2004's Main Theorem and
  (strengthened) Lemma 4 as machine-checked by Stephan, verbatim, same status.

Wiring edges (proved in `NumberTheory/Diophantine/Edges.lean`): `Ridout1957 → Mahler1957`,
`Ridout1957 → Ridout1957SUnitDen`, `Ridout1958 → Roth1955`.
⚠️ `Mahler1957` does NOT come from `Ridout1958`: Mahler (1957, §3) derives it from Ridout's
*other* paper, *Rational approximations to algebraic numbers*, Mathematika **4** (1957),
125–131 (doi:10.1112/s0025579300001182) — the two-sided `S`-unit form with exponent
`γ > α + β` (Mahler's Theorem 3).  The 1958 theorem only reaches exponent `> 2`, too weak for
Mahler's application.
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- **Thue–Siegel–Roth (Roth 1955).**  For an irrational algebraic real `α` and `δ > 0`, only
finitely many rationals `p/q` (in lowest terms, `q > 0`) satisfy `|α − p/q| < 1/q^(2+δ)`.

K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika **2** (1955), 1–20.
Statement as in Encyclopedia of Mathematics, "Thue–Siegel–Roth theorem". -/
def Roth1955 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → Irrational α → ∀ δ > (0 : ℝ),
    {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + δ)}.Finite

/-- **Ridout (1957), special case: `S`-unit denominators.**  For an irrational algebraic real
`α`, a finite set `S` of primes and `δ > 0`, only finitely many rationals whose (lowest-terms)
denominator has all prime factors in `S` satisfy `|α − p/q| < 1/q^(1+δ)`.

The case "numerator unrestricted, denominator an `S`-unit" (`α = 1`, `β = 0`, `q* = 1` in the
two-sided form Mahler (1957, Theorem 3) quotes), so it is implied by Ridout's theorem.

D. Ridout, *Rational approximations to algebraic numbers*, Mathematika **4** (1957), 125–131. -/
def Ridout1957SUnitDen : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → Irrational α → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    ∀ δ > (0 : ℝ),
      {r : ℚ | (∀ p ∈ r.den.primeFactors, p ∈ S) ∧ |α - r| < 1 / (r.den : ℝ) ^ (1 + δ)}.Finite

/-- Lets `ℚ_[p]` be formed for a bundled prime `p : Nat.Primes`. -/
instance factPrimeOfPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **Ridout (1958), Theorem 1 — the `p`-adic Thue–Siegel–Roth theorem**, as stated in the
paper.  Let `f ∈ ℤ[X]` have degree `≥ 2`, a real root `ξ`, and for each of the distinct primes
`p₁, …, p_t` a `p_r`-adic root `ξ_r`.  For `κ > 2` only finitely many coprime `(h, q)` with
`q > 0` satisfy
`min(1, |ξ − h/q|) · ∏_r min(1, |q ξ_r − h|_{p_r}) ≤ max(|h|, |q|)^(−κ)`.
(Ridout notes the `p`-adic factors are `|q ξ_r − h|`, not `|ξ_r − h/q|`.)

D. Ridout, *The `p`-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **5**
(1958), 40–48, Theorem 1 (p. 40).  Local-only full text (gitignored):
`papers/ridout-1958-p-adic-roth.{pdf,txt}`. -/
def Ridout1958 : Prop :=
  ∀ (f : Polynomial ℤ), 2 ≤ f.natDegree →
  ∀ ξ : ℝ, Polynomial.aeval ξ f = 0 →
  ∀ (t : ℕ) (P : Fin t → Nat.Primes), Function.Injective P →
  ∀ ξp : (r : Fin t) → ℚ_[(P r : ℕ)], (∀ r, Polynomial.aeval (ξp r) f = 0) →
  ∀ κ > (2 : ℝ),
    {x : ℤ × ℤ | 0 < x.2 ∧ IsCoprime x.1 x.2 ∧
      min 1 |ξ - (x.1 : ℝ) / x.2| *
          ∏ r, min 1 ‖((x.2 : ℚ_[(P r : ℕ)]) * ξp r - x.1)‖ ≤
        (max |x.1| |x.2| : ℝ) ^ (-κ)}.Finite

/-- **Ridout (1957), Theorem** — Roth with `S`-unit restrictions, the exponent `2` lowered to
`μ + ν`.  Let `α ≠ 0` be algebraic, `P₁…P_s, Q₁…Q_t` distinct primes, `0 ≤ μ, ν ≤ 1`, `c > 0`.
Restrict to `p = p* · (product of powers of the Pᵢ)`, `q = q* · (product of powers of the Qⱼ)`
with `0 < |p*| ≤ c p^μ`, `0 < q* ≤ c q^ν`.  If `κ > μ + ν`, then `0 < |α − p/q| < q^(−κ)` has
only finitely many solutions `(p, q)`.

Stated for `p, q > 0` (Ridout writes `p^μ`, so `p > 0` is implicit); restricting the solution
set only weakens the statement.  "Distinct primes" is `Disjoint P Q` plus primality.

D. Ridout, *Rational approximations to algebraic numbers*, Mathematika **4** (1957), 125–131,
the Theorem on p. 125.  Local-only full text (gitignored):
`papers/ridout-1957-rational-approximations.{pdf,txt}`. -/
def Ridout1957 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → α ≠ 0 →
  ∀ P Q : Finset ℕ, (∀ r ∈ P, r.Prime) → (∀ r ∈ Q, r.Prime) → Disjoint P Q →
  ∀ μ ν c κ : ℝ, 0 ≤ μ → μ ≤ 1 → 0 ≤ ν → ν ≤ 1 → 0 < c → μ + ν < κ →
    {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧
      (∃ ps a : ℕ, x.1 = ps * a ∧ (∀ r ∈ a.primeFactors, r ∈ P) ∧
        0 < ps ∧ (ps : ℝ) ≤ c * (x.1 : ℝ) ^ μ) ∧
      (∃ qs b : ℕ, x.2 = qs * b ∧ (∀ r ∈ b.primeFactors, r ∈ Q) ∧
        0 < qs ∧ (qs : ℝ) ≤ c * (x.2 : ℝ) ^ ν) ∧
      0 < |α - (x.1 : ℝ) / x.2| ∧ |α - (x.1 : ℝ) / x.2| < 1 / (x.2 : ℝ) ^ κ}.Finite

/-- **Ridout's theorem, as formalized by Ralf Stephan (2026)** — a *machine-checked* input, not
a paper one.  For a real algebraic `ξ`, finite sets `S₁`, `S₂` of primes and `ε > 0`, only
finitely many rationals `β = p/q` (lowest terms) satisfy
`|ξ − p/q| · ∏_{l ∈ S₁} |p|_l · ∏_{l ∈ S₂} |q|_l ≤ max(|p|, q)^(−2−ε)`.

Verbatim `Rat.finite_setOf_ridout`, R. Stephan, *Subspace-Theorems*,
https://github.com/rwst/Subspace-Theorems at `ce289c64054c8ffcfb6fd37d5881312c6a5d577d`
(2026-09-28), `DiophantineApproximation/Ridout.lean:188`, statement also in
`Challenge/DiophantineApproximation/Ridout.lean` (comparator-certified per its `COMPARATOR.md`).
Proved there sorry-free on Lean `v4.35.0-rc3`; this repo is on an older toolchain, so it enters
as a `Prop` until the toolchains meet, then gets discharged by `require`-ing a fork at a SHA
(see `PROBE-ROTH.md`).  Implies `Roth1955` (`S₁ = S₂ = ∅`), `Ridout1957SUnitDen` and
`Mahler1957` (`NumberTheory/Diophantine/StephanEdges.lean`). -/
def Stephan2026Ridout : Prop :=
  ∀ {ξ : ℝ}, IsAlgebraic ℚ ξ → ∀ (S₁ S₂ : Finset Nat.Primes) {ε : ℝ}, 0 < ε →
    {β : ℚ | |ξ - (β : ℝ)| * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite

/-- R. Stephan's `approxProd` (verbatim, `Challenge/DiophantineApproximation/ApproxProd.lean` at
`ce289c64`): `∏_{v ∈ S} ∏_i |L_{v,i}(x)|_v / max_j |x_j|_v`, archimedean factors raised to the
place's multiplicity.  Only needed to state `Stephan2026Subspace`. -/
noncomputable def approxProd {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] {ι : Type*} [Fintype ι]
    (Sinf : Finset (NumberField.InfinitePlace K)) (Sfin : Finset (NumberField.FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Module.Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
    ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

/-- **Schmidt's Subspace Theorem with finitely many places (Schlickewei's form, coefficients in
`K`), as formalized by Ralf Stephan (2026)**, machine-checked, verbatim up to the universe of `K`
and `ι`.  For linearly independent linear forms `L_{v,1..n}` at each place `v ∈ S`, the nonzero
`x ∈ Kⁿ` with `∏_{v∈S} ∏_i |L_{v,i}(x)|_v / |x|_v ≤ H(x)^(−n−ε)` lie in finitely many proper
subspaces.  This is the form Corvaja–Zannier (2004) use ("[S, Theorem 1D′]").

`NumberField.exists_finset_submodule_of_approxProd_le`, R. Stephan, *Subspace-Theorems*,
https://github.com/rwst/Subspace-Theorems at `ce289c64054c8ffcfb6fd37d5881312c6a5d577d`,
`Challenge/DiophantineApproximation/SubspaceTheorem.lean:54` (COMPARATOR.md item 6.2).  Enters as a
`Prop` until the toolchains meet (`PROBE-ROTH.md`). -/
def Stephan2026Subspace : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [Nontrivial ι]
    (Sinf : Finset (NumberField.InfinitePlace K)) (Sfin : Finset (NumberField.FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)),
    (∀ v ∈ Sinf, LinearIndependent K (L v.1)) → (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ {ε : ℝ}, 0 < ε →
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin (fun v ↦ v) L x ≤
          Height.mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W

open Classical IntermediateField in
/-- Mathlib's `NumberField.absMulHeight₁` (absolute multiplicative Weil height), copied verbatim
from mathlib `v4.33.x` `Mathlib/NumberTheory/Height/NumberField.lean`, because this repo's mathlib
predates it.  Only needed to state `Stephan2026CZMain`; delete on the next mathlib bump and use
mathlib's. -/
noncomputable def absMulHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : ℝ :=
  if hx : IsIntegral ℚ x then
    haveI : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField ℚ⟮x⟯ := {}
    (Height.mulHeight₁ (AdjoinSimple.gen ℚ x)) ^ (Module.finrank ℚ ℚ⟮x⟯ : ℝ)⁻¹
  else 1

/-- Stephan's pseudo-Pisot predicate (verbatim, `CorvajaZannier2004/PseudoPisot.lean`):
`|α| > 1`, algebraic, every other conjugate inside the unit disc, integral trace.  CZ 2004 p. 2. -/
def IsPseudoPisot (α : ℝ) : Prop :=
  1 < |α| ∧ IsAlgebraic ℚ α ∧ (∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ (α : ℂ) → ‖z‖ < 1) ∧
    ∃ n : ℤ, ((minpoly ℚ α).aroots ℂ).sum = n

open IntermediateField Module in
/-- **Corvaja–Zannier (2004), Main Theorem, as formalized by Ralf Stephan (2026)**, verbatim up to
universes.  For a finitely generated group `Γ` of real algebraic units, algebraic `δ ≠ 0` and
`ε > 0`, only finitely many `(q, u) ∈ ℤ × Γ` have `|δqu| > 1`, `δqu` not pseudo-Pisot and
`0 < ‖δqu‖ < H(u)^(−ε) |q|^(−[ℚ(u):ℚ]−ε)`.

`finite_setOf_not_isPseudoPisot`, R. Stephan, *Subspace-Theorems* at `ce289c64`,
`CorvajaZannier2004/MainTheorem.lean:251`, challenge `ChallengeCorvajaZannier2004.lean:128`
(comparator lane `corvaja-zannier-2004`).  P. Corvaja, U. Zannier, Acta Math. 193 (2004), 175–191. -/
def Stephan2026CZMain : Prop :=
  ∀ {Γ : Subgroup ℝˣ}, Γ.FG → (∀ u ∈ Γ, IsAlgebraic ℚ (u : ℝ)) →
    ∀ {δ : ℝ}, IsAlgebraic ℚ δ → δ ≠ 0 → ∀ {ε : ℝ}, 0 < ε →
    {p : ℤ × Γ | 1 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ)| ∧
      ¬ IsPseudoPisot (δ * p.1 * ((p.2 : ℝˣ) : ℝ)) ∧
      0 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| ∧
      |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| <
        absMulHeight₁ ((p.2 : ℝˣ) : ℝ) ^ (-ε) *
          |(p.1 : ℝ)| ^ (-(finrank ℚ ℚ⟮((p.2 : ℝˣ) : ℝ)⟯ : ℝ) - ε)}.Finite

open Filter Topology IntermediateField in
/-- **Corvaja–Zannier (2004), Lemma 4, in the stronger form Stephan proves** (the `α^h ∈ ℚ`
alternative never occurs): if `Tr_{ℚ(α)/ℚ}(q_n αⁿ) ∈ ℤ ∖ {0}` along an infinite `Ξ` with
`log q_n = o(n)`, then `α` is an algebraic integer.

`isIntegral_of_trace_mul_pow`, R. Stephan, *Subspace-Theorems* at `ce289c64`,
`CorvajaZannier2004/IntegralPowerSums.lean:368`, challenge `ChallengeCorvajaZannier2004.lean:107`. -/
def Stephan2026CZLemma4 : Prop :=
  ∀ {α : ℂ}, IsAlgebraic ℚ α → ∀ {Ξ : Set ℕ}, Ξ.Infinite → ∀ {q : ℕ → ℕ}, (∀ n ∈ Ξ, 0 < q n) →
    Tendsto (fun n : ℕ ↦ Real.log (q n) / n) (atTop ⊓ 𝓟 Ξ) (𝓝 0) →
    (∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧ Algebra.trace ℚ ℚ⟮α⟯ (q n * AdjoinSimple.gen ℚ α ^ n) = t) →
    IsIntegral ℤ α

end LeanFormalizations.Literature
