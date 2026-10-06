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
import LeanFormalizations.NumberTheory.Erdos385.FunctionField
import LeanFormalizations.NumberTheory.Erdos385.Graph
import LeanFormalizations.NumberTheory.Erdos385.Hyperbola
import LeanFormalizations.NumberTheory.Erdos385.Remainder
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.ZeroDetect
import LeanFormalizations.NumberTheory.Mills.PairedRoot
import LeanFormalizations.NumberTheory.Mills.SaitoTypeB
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBTheta
import LeanFormalizations.NumberTheory.Mills.DecayDegreeFour
import LeanFormalizations.NumberTheory.Mills.ShiftRigidityUnipotent
import LeanFormalizations.NumberTheory.Mills.EvenRTimesThree
import LeanFormalizations.NumberTheory.ErdosDyadic

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
      at q <= 47, while Fermat has none structurally; the block is uniformity (conjecture LC, \
      stated as PairedRoot.LocalCertificates).  \
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
    evidence := "PROBE-MILLS-RESIDUAL.md §7; statements (sorry, believed 97%) in \
      NumberTheory/Mills/PairedRoot.lean: a Frobenius-conjugate root pair shares one cube class, \
      so (1)(2) at T_j with v_3(T_j - 1) = j + 1 and N(β) a cube recurs (48/48, control 6/24); unit \
      c = 1 cubics then get a Jacobi certificate (436/442 killed alone).  Left: c >= 2 (mod-9/27 \
      condition on f) or non-cube norm, where the cube classes at T_j match random primes \
      (hard-core 60 1 4 2: 30/46 vs control 28/46); the symbol lives in a non-abelian Kummer \
      field and p = Tr β^(3^j) gives no generator of the prime"
    reopenIf := "a law forcing the cubic residue symbol of β at the primes dividing Tr β^(3^j), \
      e.g. an explicit generator of such a prime; or LC" },
  { route := "Erdős #385 over F_q[T], large q (Sawin's analogue; witness depth m for q ≥ q₀(k, m))"
    verdict := .superseded, tier := .frozen
    anchor := some ``LeanFormalizations.Literature.BBR2015Thm23TwoFactor
    evidence := "DOOR-FF-ERDOS-385.md, LIT-ERDOS-385.md §1: a one-line corollary of BBR \
      arXiv:1302.0625 Thm 2.3 (edge Erdos385.ffWitness_of_BBR).  The (i) analogue is even \
      trivial once q > deg f (Erdos385.ffGood_of_natDegree_lt_card), since a bad f satisfies \
      T^q - T ∣ f (Erdos385.X_pow_card_sub_X_dvd_of_not_ffGood)"
    reopenIf := "never as new math; prove the edge only if a downstream theorem consumes it" },
  { route := "Erdős #385 over F_q[T], fixed q, n → ∞ (testing whether Siegel zeroes are the only enemy)"
    verdict := .gapBoundLimited, tier := .frozen
    anchor := some ``LeanFormalizations.Literature.Gorodetsky2018Thm11
    evidence := "DOOR-FF-ERDOS-385.md; LIT-ERDOS-385.md §1: Weil RH and Gorodetsky Thm 1.1 reach \
      only h > n/2, #385 needs two factors of degree > h, so h < n/2; Sawin (Tao blog comments, \
      2024-08-22) showed GRH alone falls short.  No Siegel zeroes over F_q[T], yet the square-root \
      barrier remains.  scripts/erdos385-ff-probe.py: bad f over F_2 up to degree 16, none 17..25"
    reopenIf := "a fixed-q short-interval estimate below the square root for prime-type \
      factorization functions, or Sawin–Shusterman-style special-q geometric input applied to \
      two-large-factor types in every I(f, h), h < n/2" },
  { route := "Erdős #385 by a sieve-only argument (arbitrary interval, arbitrary classes)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Erdos385.SieveOnlySibling
    evidence := "Tao 2024-08-19 post; FGKMT arXiv:1412.5029 eq. (1.2) (Literature.FGKMT2018Eq12, \
      edge Erdos385.sieveOnlySibling_of_FGKMT): one class per prime ≤ h covers an arbitrary \
      interval of length h, so the sibling statement a sieve-only proof would establish is false"
    reopenIf := "an input that uses that the classes are 0 mod p at the specific location n, \
      e.g. parity-breaking Type II information on [n - h, n]" },
  { route := "Erdős #385 for every n via sieve or multiplicative methods (one scale at a time)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Literature.Granville2022Cor1
    evidence := "Tao 2024-08-19 post; Granville arXiv:2010.01211 Cor. 1: with infinitely many \
      Siegel zeroes the classes 0 mod p, p ≤ √y, leave o(y / log y) survivors in some intervals \
      (Literature.OneScaleSieveEnemy).  Even RH gives semiprime gaps no better than √x log x"
    reopenIf := "a parity breakthrough that at minimum excludes Siegel zeroes, or a cross-scale \
      coupling that makes one n good at some scale (see the repulsion row)" },
  { route := "Erdős #385 via repulsion between scales (Tao's loophole, door 3)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Erdos385.CrossScaleRepulsion
    evidence := "DOOR-EXCEPTIONAL-ERDOS-385.md Part B, scripts/erdos385-bad-structure.py: no signal \
      (85%).  Carriers at different scales are independent within residue classes; the joint \
      failure 'no carrier with p ≤ 512' is 23× the product of the marginals (conspiracy, not \
      repulsion).  Edge Erdos385.eventually_not_bad_of_crossScaleRepulsion"
    reopenIf := "a mechanism by which an empty scale forces a carrier at another scale that \
      survives the positive cross-scale coupling seen in the data" },
  { route := "Erdős #385(i) for every n via prime pairs on the strip pq < n < pq + p \
      (Erdos385.HyperbolaPrimePairs, edges eventually_not_bad_of_hyperbolaPrimePairs, \
      erdos430_of_hyperbolaPrimePairs)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Erdos385.HyperbolaPrimePairs
    evidence := "Hyperbola.lean header: near p ≈ √n, ⌊n/p⌋ = 2A + c(p) − p, so the statement is \
      binary Goldbach with p in a window of length ≍ n^{1/4}.  The Dirichlet-polynomial bound for \
      the strip count in a window of length ≍ √n is ∫|P Q| ≤ (∫|P|²∫|Q|²)^{1/2} ≍ 1/log n against a \
      main term ≍ 1/log² n, and the L² norms are sharp even under RH, so no hypothesis on zeros \
      alone closes it.  Data (scripts/erdos385-hyperbola-probe.py): W(n) = 0 last at 267689 ≤ 10^8, \
      min W = 27 on [10^7, 10^8)"
    reopenIf := "pointwise cancellation in the Type II × Type II term near the diagonal \
      (Σ α_a β_b γ_c δ_d 1[ab = ⌊n/(cd)⌋]), i.e. a binary-problem mechanism; the curved range \
      p ≪ √n needs ⌊n/p⌋ p-rough, which the sieve-only row already blocks" },
  { route := "Erdős #385(i) by witnesses with three or more prime factors (a 'ternary escape' \
      from the binary prime-pair problem)"
    verdict := .needsNewIdea, tier := .cited
    anchor := some ``LeanFormalizations.Erdos385.good_iff_exists_prime_floor
    evidence := "By Erdos385.good_iff_exists_prime_floor a witness with least prime p is \
      p ⌊n/p⌋, inside a window of length p.  With k factors of size n^{1/k} the window is n^{1/k} \
      and the Mellin height n^{1−1/k} exceeds each factor's length n^{1/k}, so for k ≥ 3 the \
      pointwise Hölder/mean-value bound loses a power of n (k = 3: ∫|P|³ ≫ n^{1/6}): more \
      variables shrink the window faster than they add freedom.  The widest window, √n, is \
      the two-prime case (Erdos385.HyperbolaPrimePairs), which is binary"
    reopenIf := "a witness family whose window is not bounded by its least prime factor, or \
      a pointwise mechanism for two primes near a hyperbola (open even for ⌊p^c⌋, where only \
      almost-prime values are known)" },
  { route := "Erdős #385(i), #430, #463 from binary Goldbach alone (no gap control)"
    verdict := .needsNewIdea, tier := .cited
    anchor := some ``LeanFormalizations.Erdos385.GoldbachWindow
    evidence := "Goldbach supplies one representation N = p + q per N and says nothing about \
      which; an adversarial choice (least p, gap ≈ N) puts pq = p(N − p) within p of a given n \
      only by accident.  The proved reductions (Erdos385.hyperbolaPrimePairs_of_goldbachWindow, \
      Erdos385.ees_of_goldbachWindow, Erdos385.erdos463_of_goldbachWindow) need the gap q − p \
      in a prescribed window of length ≍ √N, i.e. Erdos385.GoldbachWindow, which is stronger \
      than Goldbach.  The minimal-gap form (q − p ≪ log² N) pins the gap near 0 and does not help"
    reopenIf := "a transfer from additive representations to the multiplicative strip that \
      survives an adversarial choice of representation, or Goldbach with gap control" },
  { route := "Linear sieve s > 2 (phase E5) from ONE Buchstab step on Selberg's Λ² upper bound"
    verdict := .needsNewIdea, tier := .cited, anchor := none
    evidence := "scripts/linear-sieve-onestep.py: S(z) = N − Σ_{p<z} S(A_p, p) with Selberg's \
      F_S(t) = e^γ / ∫_0^{t/2} ρ gives f₁(s) < 0 for s ≤ 2.05 (control: JR f(s) = 2e^γ log(s−1)/s \
      > 0 there).  Selberg is sharp only for t ≤ 2; the loss for t > 3 costs a constant, and the \
      margin at s = 2 + ε is O(ε).  E5 uses the full JR comparison instead (LinearSieve.lean)"
    reopenIf := "an upper bound matching Jurkat–Richert's F(t) for all t > 1 without iteration" },
  { route := "Erdős #385 E9b: NearOneLargeValues (large values ≪ T^{Bη^{3/2}} log^C T for EVERY \
      C^∞ weight) from NearOneZeroDensity + Richert (nearOneLargeValues_of_density)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Erdos385.SlowMellinWeight
    evidence := "PowerSaving/ZeroDetect.lean header (2026-10-01 review lap): the local explicit \
      formula localises a large value to a zero within L of t, L = where the weight's Mellin tail \
      drops below P^{−η}.  A weight with Mellin decay exp(−(log u)²) gives L = exp(√(η log P)), and \
      one zero at β = 1 − η/2 (allowed by density and by VK for η ≫ (log P)^{−2/3}) yields more \
      large values than T^{Bη^{3/2}} when η ≪ (log P)^{−1/2}.  The headline now uses \
      LocalZeroDetect (window P^{η/3}), which LargeValueCount can afford"
    reopenIf := "a zero-free region 1 − β ≫ (log γ)^{−1/2} or better (beyond VK), or restricting \
      NearOneLargeValues to Gevrey weights (|mellin f(1+iu)| ≤ e^{−c|u|^α})" },
  { route := "Saito Type B (E+) from BHP + Dubickas 2022 Lemma 6 alone (phase 62: the frozen \
      SaitoTypeB.saitoTypeBLeast_holds / xi_shift_transcendental_classical)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Mills.SaitoTypeB.SparseNoCancel
    evidence := "Proved with Dubickas 2022 Lemma 8 added and ratios eventually ≥ 29/10 \
      (SaitoTypeB.saitoTypeBLeastEv_holds, SaitoTypeB.xi_shift_transcendental_classical'). \
      Lemma 8 (Baker) enters twice.  Case (II) (decay at every large k) can drop it for E+ by \
      the exact orbit n ↦ 3n − d (SaitoTypeB.conjPowSum_lower_of_recurrence).  Case (I) of \
      Saito Lemma 5.2 gives decay β^(−19n/10) only on an arbitrary sparse set; the norm of \
      β^n − Tr(β^n) bounds |S(n)| below only by β^(−(ℓ−1)n), useless for ℓ ≥ 3.  Matomäki is \
      needed for general C (chain steps with ratio < 40/19) but not for E+"
    reopenIf := "an elementary proof of SaitoTypeB.SparseNoCancel (or of the case-(I) degree \
      bound for the E+ orbit), or a competitor construction that avoids Saito's case (I)" },
  { route := "E+ from a short-interval exponent θ ∈ [5/9, 2/3) (phase 64a: the frozen \
      SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval, hence the Ingham 5/8 corollaries)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.Mills.SaitoTypeBTheta.ShiftPisotDegreeLeThree
    evidence := "SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval' proves E+ for θ < 5/9 \
      by the θ-parametric route (SaitoTypeBThetaParts.lean).  The prime input enters twice: the \
      chain step needs ratio c with θc ≤ c − 1 (fine up to θ < 2/3), and Saito (5.17) gives decay \
      μ < (1 − θ)·3 − 1 = 2 − 3θ.  The Baker-free degree bound is (ℓ − 1)μ ≤ 1, and the endgame \
      (e2_zero_of_nonrecord, not_natDegree_two, trace rigidity) is degree-3 only, so it needs \
      μ > 1/3, i.e. θ < 5/9.  Ingham's 5/8 lies above.  Control: decay alone cannot close it, \
      since quartic Pisot numbers have decay μ < 1/3 at every n \
      (DecayDegreeFour.decay_admits_degree_four, X⁴ − aX³ − 1)"
    reopenIf := "a proof of ShiftPisotDegreeLeThree for θ < 2/3 (exclude Pisot degree ≥ 4 for the \
      E+ orbit n ↦ 3n − d without Baker), or a degree-ℓ version of the non-record e₂ argument; it must use more than decay \
      (DecayDegreeFour.decay_admits_degree_four)" },
  { route := "Degree-≥4 shift trace rigidity by the cubic 3-adic/spectral mechanism alone (phase 65 \
      lap 2: ShiftRigidityDeg.shiftTraceRigidity_ge_four via window + Teichmüller limit + spectral \
      identity, generalised from ShiftRigidity.not_primeTraces)"
    verdict := .needsNewIdea, tier := .kernel
    anchor := some ``LeanFormalizations.Mills.ShiftRigidityUnipotent.unipotent_trace_congr
    evidence := "In degree 3 the cube class f ≡ (X − z)³ (mod 3) dies because tr ≡ 3z^m ≡ 0.  In \
      degree 4, f₀ = X⁴ − 4X³ − X + 1 ≡ (X − 1)⁴ is Pisot (β ≈ 4.046) with tr β^(−1) = 1, and \
      tr C^(3^n − 1) ≡ 1 (mod 3^(n−1)) for all n ≥ 2 (kernel-checked), so the window p² ≡ 1 and the \
      constant spectral vector u ≡ 1, ω = 1 are consistent: every 3-adic constraint holds.  47 such \
      (f, s) with |coeff| ≤ 9; each has a covering prime q ≤ 60, but no uniform reason.  Not only the \
      unipotent class: f₁ = X⁴ − 8X³ − 5X² + 6X + 3 ≡ X²(X − 1)² has tr C^(3^n − 1) ≡ −1 \
      (mod 3^(n+1)) (ShiftRigidityUnipotent.generic_trace_congr_le_nine), a non-constant spectral \
      solution u = (1,1,0,0) from a pair relation among reciprocal roots"
    reopenIf := "ShiftRigidityUnipotent.UnipotentCovering (a covering prime for every unipotent-class \
      Pisot), or any non-3-adic input on tr C^(3^n + s) in the class f ≡ (X ∓ 1)^ℓ (mod 3)" },
  { route := "Degree-≥4 generic leaf by the 3-adic route plus the q-power class kill (phase 65 lap 4: \
      f ≡ g^q (mod q) ⇒ q ∣ every trace, ShiftRigidityUnipotent.PowerClassKill; kills the lap-3 control \
      f₁ at q = 2, ShiftRigidityUnipotent.not_primeTraces_f₁)"
    verdict := .needsNewIdea, tier := .kernel
    anchor := some ``LeanFormalizations.Mills.ShiftRigidityUnipotent.C₂_trace_mod
    evidence := "In degree 4 the power class needs q ∣ 4, so only q = 2.  Scan (|cᵢ| ≤ 9, c₃ ∈ [−12, −3], \
      irreducible Pisot, not unipotent mod 3, not a square mod 2, s ∈ [−4, 4], n ≤ 11): two survivors, \
      both s = −1; f₂ = X⁴ − 5X³ − 8X² − 6X − 3 has tr C₂^(3^n − 1) ≡ −1 (mod 3^(n+1)) and tr C₂ = 5 \
      odd.  It dies only by a hit prime (7 ∣ tr C₂^(3^7 − 1), C₂_hit_seven)"
    reopenIf := "ShiftRigidityUnipotent.HitPrime (a prime dividing infinitely many orbit traces; \
      not_primeTraces_of_hitPrime closes both leaves from it), or a third input separating f₂" },
  { route := "ξ(r·3^k − 1) for even r below Saito's r ≥ 4.003·10¹⁴ by the Theorem E arithmetic route \
      (window + Teichmüller limit + Galois rigidity + cube-class congruence)"
    verdict := .needsNewIdea, tier := .kernel
    anchor := some ``LeanFormalizations.Mills.EvenRTimesThree.trace_congr_le_eight
    evidence := "For even r the limit points carry ζ_k^(r·3^m) and x ↦ x^r is not injective on the \
      Teichmüller roots, so f ≡ (X − 1)(X + 1)² (mod 3) survives.  Probe (|coeff| ≤ 12, r ∈ {2,4,8,10}, \
      n < 40): 164 cubic Pisot survivors of the window test.  X³ − 2X² − X − 1 has \
      tr C^(2·3^n − 1) ≡ −1 (mod 3^(n+2)) (kernel-linked range n ≤ 8, numerics to 15).  Every \
      survivor checked has small hit primes (here 2, 7, 13, 23)"
    reopenIf := "the cubic case of ShiftRigidityUnipotent.HitPrime along r·3^n − 1 (a prime dividing \
      infinitely many tr C^(r·3^n − 1)), or a non-3-adic input separating X³ − 2X² − X − 1" },
  { route := "Erdős #249 (∑ φ(n)/2^n) by CRT forcing 2^i ∣ φ(N+i), i ≤ M, so 2^M divides the scaled \
      tail V_(N+M) ≤ q(N+M+2) (Erdős's d(n) template)"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.ErdosDyadic.TotientForcingRoute
    evidence := "Bit-count: the block costs ≈ M²/2 bits of CRT conditions but the route needs N < 2^M, \
      only ≈ M bits (believed ErdosDyadic.not_totientForcingRoute, ~85%).  Control: passes for d(n) \
      (polylog coefficients, Erdős 1948).  φ = μ ∗ id (ErdosDyadic.totient_dyadic_eq_moebius) puts \
      Möbius arithmetic in any proof.  Cook (plectis-erdos 605b273) proves only φ(n) mod m"
    reopenIf := "a mechanism using Möbius cancellation in ∑ μ(n)/(2^n − 1)², or one that controls \
      φ(N+i) mod 2^i with fewer than log₂ N bits of conditions" },
  { route := "Erdős #251 (∑ p_n/2^n) via Tao's gap reduction plus Maynard/Erdős–Rankin windows whose \
      tuple elements are all ≡ 0 mod 2^R, forcing 2-adic valuations of consecutive gaps"
    verdict := .needsNewIdea, tier := .frozen
    anchor := some ``LeanFormalizations.ErdosDyadic.Cook2026GapPerturbation
    evidence := "Needs ≈ log₂ log x consecutive controlled gaps, but Maynard gives ≈ (ln k)/4, and the \
      gap after the window is uncontrolled.  Cook's perturbation (Prop 1.1) makes the gap series \
      rational while keeping eventual congruences and m-block laws for m = o(log log X), exactly the \
      scale where this route dies.  Reduction: ErdosDyadic.primes_dyadic_eq_two_add_gaps"
    reopenIf := "control of ≫ log log x consecutive prime gaps (e.g. a uniform prime k-tuples \
      hypothesis, cf. Johan Land's conditional result), or an input invisible to short-block statistics" },
  { route := "Erdős #1049 at t = 3/2 (Chowla) by 3-adic forcing 3^i ∣ τ(N+i) against integrality of \
      W_N = s·2^N·T_N"
    verdict := .needsNewIdea, tier := .kernel
    anchor := some ``LeanFormalizations.ErdosDyadic.three_halves_outside_cook_region
    evidence := "The 2^N scale swamps every forced 3^M (the Mahler 3/2 wall, irrationality-screen \
      column B).  The best rational-base criterion (ErdosDyadic.Cook2026RationalBase, from Zudilin \
      2004) needs log b/log a < 0.4057; 3/2 sits at 0.631"
    reopenIf := "a Padé/Hankel construction whose denominators do not grow like b^(n²), i.e. one \
      beating the Mahler 3/2 denominator wall" },
  { route := "Erdős #267 (∑ 1/F_(n_k), ratio gap 1 < c < 2) as a new target"
    verdict := .superseded, tier := .frozen
    anchor := some ``LeanFormalizations.ErdosDyadic.Snyder2026Erdos267
    evidence := "Snyder's Lean proof (2026-07-15, GPT 5.6, Z[φ]-lattice window comparison) kernel-checked \
      here 2026-10-05: Mathlib fabf563, standard axioms, statement faithful to FC erdos_267.  \
      Transcendence is Nguyen 2022 for c > 2, sharp at c = 2"
    reopenIf := "never for irrationality; the open neighbour is which lacunary sums with \
      1 < c ≤ 2 are algebraic (∑ 1/F_(2^k) is)" }
]

end LeanFormalizations.Maze
