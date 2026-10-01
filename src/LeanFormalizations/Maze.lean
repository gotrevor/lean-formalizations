/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# `Maze.lean`: the routes we have walked and closed, as Lean data

Borrowed from `normal-numbers` (`NormalNumbers/Maze.lean`).  Trevor, 2026-09-29, after the Wright
probe: *"If there any way to formalize this failure, so that we don't try it again w/out a new
idea?"*

Each row is a route this repo walked and closed or parked.  Its `reopenIf` field names the
**new idea** that would justify walking it again.  If your idea is not that idea, the row
already answers it.  Rows are never deleted: if a route reopens, the row stays and gains a note.

## How to use it

1. Before planting a phase, match the idea against `Verdict`.  Each constructor's doc comment
   carries the tell.
2. Grep `register` for the object you are about to touch.

## The three tiers

* `Tier.kernel`: the verdict is a **theorem in this build**, named in `anchor`.
* `Tier.frozen`: the obstruction is a precise `def … : Prop` named in `anchor`, not yet proved.
  A frozen row claims a *statement*, never a truth value.
* `Tier.cited`: the verdict lives in the `evidence` prose and file.  This is the weakest tier and
  is not machine-checked.

`anchor` is a double-backtick name literal, so renaming or deleting the anchored declaration
breaks this file.  That is the point.
-/
import LeanFormalizations.Literature.GelfondSchneider
import LeanFormalizations.NumberTheory.Mills.Wright

namespace LeanFormalizations.Maze

open LeanFormalizations.Literature LeanFormalizations.Mills

/-- How strongly a row's verdict is checked. -/
inductive Tier
  | kernel
  | frozen
  | cited
  deriving DecidableEq, Repr

/-- Why a route closed.  Each constructor's docstring gives the tell to recognise it early. -/
inductive Verdict
  /-- **No common field.**  The Mills / Saito / Saito–Takeda engine needs algebraicity of the
  constant to *propagate* along the iteration (`A ↦ A^c` keeps every iterate in one number field
  of bounded degree), so that Pisot, Liouville or Subspace tools can act.  Tell: the iterated map
  is not a power map (towers, `2^x`, `e^x`): algebraicity dies after one step. -/
  | noCommonField
  /-- **Gap-bound limited.**  The argument closes only with a prime-gap bound stronger than
  anything known, even under RH.  Tell: the final inequality compares a gap exponent with a
  constant coming from BHP / Matomäki / CMS. -/
  | gapBoundLimited
  /-- **Superseded.**  Someone else has formalized it; reuse through a Literature `Prop` and later
  a `require`d fork.  Tell: a peer repo's *tree*, not just its headline table, contains it. -/
  | superseded
  /-- **No consumer.**  It fills a hole nothing downstream needs, since we are not publishing
  (and OEIS is out).  Tell: the only thing it unblocks is a sorry count. -/
  | noConsumer
  /-- **Needs a new idea.**  A genuinely open problem with no mechanism in hand.  Tell: the
  literature's own authors state it as open and list no plan. -/
  | needsNewIdea
  deriving DecidableEq, Repr

/-- One walked route. -/
structure Row where
  route : String
  verdict : Verdict
  tier : Tier
  /-- The declaration that pins the verdict (kernel or frozen tiers), or `none` for cited. -/
  anchor : Option Lean.Name
  /-- Where the argument lives. -/
  evidence : String
  /-- The new idea that would justify reopening this route. -/
  reopenIf : String

/-! ## Frozen obstructions -/

/-- **The Wright tower leaves every number field at level 2.**  If `ω` is rational but not an
integer, then `2 ^ ω` is algebraic and irrational, so Gelfond–Schneider makes
`tower ω 2 = 2 ^ 2 ^ ω` transcendental.  This is why no Mills-type argument (which needs *every*
iterate algebraic in a fixed field) can prove the least Wright constant irrational.  Nothing is
known at level 3: `2 ^ x` for transcendental `x` may be algebraic, as far as current theory
can say (Schanuel's conjecture would settle it).  The least constant is not an integer, since
`1 < ω_min < log₂ 3` (`PROBE-WRIGHT.md`), so the hypothesis `q.den ≠ 1` is the relevant case. -/
def WrightLevelTwoTranscendental : Prop :=
  GelfondSchneider1934 → ∀ q : ℚ, q.den ≠ 1 → Transcendental ℚ (tower (q : ℝ) 2)

/-! ## The register -/

/-- Every walked route, newest last. -/
def register : List Row := [
  { route := "Dubickas 2022 Lemma 6 without the Subspace Theorem (phase 9)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-DUBICKAS-NOSUBSPACE.md: the wall is Corvaja–Zannier's main theorem \
      (p-adic Subspace) plus sparsity of {2^n}"
    reopenIf := "an elementary substitute for the p-adic Subspace Theorem on sparse exponent sets" },
  { route := "Prove Corvaja–Zannier 2004 from Stephan's Subspace Theorem (phase 13)"
    verdict := .superseded, tier := .cited, anchor := none
    evidence := "rwst/Subspace-Theorems has CorvajaZannier2004/ (whole paper); PROBE-ROTH.md"
    reopenIf := "never; discharge Literature.Stephan2026CZMain by requiring a fork" },
  { route := "Derive Dubickas2022 from Stephan's CZ statements (phase 13b)"
    verdict := .noConsumer, tier := .cited, anchor := none
    evidence := "DIRECTION.md phase 13b, parked a0e1bf4"
    reopenIf := "a downstream theorem we want that needs Dubickas2022 discharged" },
  { route := "Lower Saito 2025's thresholds (the 17/23, 17/40 exponents; ξ over 2^k)"
    verdict := .gapBoundLimited, tier := .cited, anchor := none
    evidence := "PROBE-MILLS-TRANSCENDENCE.md: the 40/19 ratio comes straight from BHP"
    reopenIf := "a prime-gap exponent below Baker–Harman–Pintz 0.525" },
  { route := "Unconditional transcendence of Mills' constant (totally real cubic Pisot case)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-MILLS-TRANSCENDENCE.md; Saito arXiv:2508.16068 Thms 1.7-1.8"
    reopenIf := "a mechanism excluding |β₃| < -β₂ ≤ min(|β₃|^(17/23), β^(-17/40)) without RH" },
  { route := "Irrationality of the least Wright constant ω ≈ 1.2516476 (new-math #2)"
    verdict := .noCommonField, tier := .frozen, anchor := some ``WrightLevelTwoTranscendental
    evidence := "PROBE-WRIGHT.md; scripts/wright-least.py"
    reopenIf := "control of frac(2^x) along a transcendental orbit, a transcendence measure \
      for 2^(2^(a/b)), or a proof that uses minimality (the greedy prime chain) directly" },
  { route := "Transcendence of Copeland–Erdős via consecutive primes in AP (Mahler/Ridout blocks)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-COPELAND-ERDOS.md: Ridout needs block length ≍ digit offset ≍ 10^k; \
      consecutive-prime APs give O(k log k) digits even under Cramér"
    reopenIf := "a prime-sequence block whose digit length is a positive fraction of its offset, \
      or a criterion accepting approximation quality 1 + o(1)" },
  { route := "Burn down the six residual mod-3 classes left by phase 29 (Mills 3-adic)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "FINDING-MILLS-3ADIC.md: in the residual classes p_m ≡ ±1 mod 3^(m+1), the \
      conjugates' 3-parts differ, so the modulus-is-the-prime trick is silent; \
      small-prime covering removes density → 1 of cubics, not all"
    reopenIf := "an argument that uses the Pisot/size structure (Saito's (1.3)) together with \
      the 3-adic constraint, or a covering theorem valid for every cubic Pisot number" },
  { route := "Saito arXiv:2504.14968 Problem 1.7 (non-reversible R with ⌊α^R(n)⌋ composite i.o. \
      for every Pisot α) via the phase-32 prime-as-modulus trick"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-SAITO-FIBONACCI.md § Problem 1.7; scripts/saito-problem17-probe.py: the floor \
      is a trace (Frobenius-invariant), so it converges c-adically; R = 2^n+3^n leaves 2/32 classes \
      mod 4 and 6/486 mod 9"
    reopenIf := "an exponent sequence under which tr C^R(n) has non-±1 limit points for EVERY \
      Pisot C, or a covering theorem valid for every Pisot number" },
  { route := "F(c^n) + h composite i.o. at SPLIT primes c (c ≡ ±1 mod 5) via the prime-modulus filter"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "SWEEP-PRIME-MODULUS.md: one c-adic limit point; survivor h looks non-integral \
      numerically (c = 11..41) but no proof that the limit is not an integer.  CLOSED 2026-09-30 \
      by a different route, phase 37 FibonacciAllPrimes.fib_prime_pow_add_not_prime_all: the exact \
      composition F((2j+1)N) = Φ_j(F N) turns the congruences into an equality, avoiding \
      non-integrality altogether"
    reopenIf := "an algebraic proof that lim F(c^n) (= (ω(φ)-ω(ψ))/√5 in ℤ_c) is not ±1 - h for any \
      integer h, e.g. via a polynomial it satisfies with no suitable integer root" },
  { route := "Mills residual classes via local (splitting-type) filters: covering, projective, \
      and the Kronecker lemma (a split prime T_j = 2 mod 3 recurs, so tau = -1 forces (D/p_k) = -1)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-MILLS-RESIDUAL.md §3, §5: the filters hold for EVERY eventually-prime trace \
      sequence, so they burn down density but cannot separate Mills from its siblings; tau = -1 \
      classes lose cyclic K outright and every tested (1.3) example; tau = +1 with S3 K has no \
      abelian filter at all ({1, transpositions} surjects onto C2).  Not Fermat-blocked: every \
      explicit residual cubic (184,513 (1.3) Pisot β, 2.4M tau = -1 cubics) dies to a certificate \
      at q <= 47, while Fermat has none structurally; the block is uniformity (conjecture LC).  \
      Corrected 2026-10-01 (§7): for unit β with 3-adic rate c_j = 1, the paired-root lemma also \
      removes transpositions, so (D/T_j) = +1 is a Jacobi filter there"
    reopenIf := "a proof that every cubic with Tr β = 2 mod 3 has a covering prime or a Kronecker \
      hit on its eventual cycle mod |D| (Saito Problem 1.1 for those classes), or a non-abelian \
      (Kummer) condition at the Mills primes that is forced, not merely probable" },
  { route := "Mills residual classes via least-ness beyond ε = 0 (the prime-free gaps (T_j³, T_(j+1)))"
    verdict := .gapBoundLimited, tier := .cited, anchor := none
    evidence := "PROBE-MILLS-RESIDUAL.md §1, §4: least-ness is exactly the prime-free interval \
      [(y-|s|)³, y³) of length x^θ, θ ∈ (1/2, 21/40]; it is the only lever separating Mills from \
      S1-S3 (all 89 local survivors in the (1.3) census fail it at once), but zero-density counts \
      cells and cannot pick out one cell per scale"
    reopenIf := "a coupling of primality of T = Tr β^(3^j) with the interval (T³, T_(j+1)), or a \
      prime-gap exponent below 21/40 at cubes of Pisot traces" },
  { route := "Mills hard core (tau = +1, S3) via the cube classes of the roots at p = T_j (Kummer data)"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "PROBE-MILLS-RESIDUAL.md §7: a Frobenius-conjugate root pair shares one cube class, \
      so (1)(2) at T_j with v_3(T_j - 1) = j + 1 and N(β) a cube recurs (48/48, control 6/24); unit \
      c = 1 cubics then get a Jacobi certificate (436/442 killed alone).  Left: c >= 2 (mod-9/27 \
      condition on f) or non-cube norm, where the cube classes at T_j match random primes \
      (hard-core 60 1 4 2: 30/46 vs control 28/46); the symbol lives in a non-abelian Kummer \
      field and p = Tr β^(3^j) gives no generator of the prime"
    reopenIf := "a law forcing the cubic residue symbol of β at the primes dividing Tr β^(3^j), \
      e.g. an explicit generator of such a prime; or LC" }
]

end LeanFormalizations.Maze
