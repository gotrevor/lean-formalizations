# Findings: state of `Transcendental ℚ Real.pi` in proof assistants

**Answers** the 2026-06-15 `ON-LINE-REQUEST.md` item ("State of `Transcendental ℚ Real.pi`
in proof assistants"), filed to make `squaring_the_circle_impossible` unconditional.

**Fulfilled by** a networked host session, 2026-06-15.
**Sources read:** mathlib4 GitHub (PR #28013 + the local v4.29.1 snapshot), Isabelle AFP
(`Hermite_Lindemann`, `Pi_Transcendental`), the Coq/Rocq Marelle project page +
Bernard–Bertot–Rideau–Strub papers, arXiv, Metamath 100.

---

## 0. ⚠️ Read this first — the lap already self-resolved the blocker

While this was being researched, the live lap committed **`67c4bb2`** ("π-transcendence via
Hermite–Lindemann: squaring-the-circle now unconditional mod one cited axiom"). It added
`src/LeanFormalizations/NumberTheory/Transcendence/HermiteLindemann.lean` with:

- `axiom hermite_lindemann {α : ℂ} (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) : Transcendental ℚ (Complex.exp α)`
- `theorem transcendental_pi : Transcendental ℚ Real.pi` (machine-checked Euler-identity reduction)
- and `squaring_the_circle_impossible_uncond` in `Geometry/Constructible/Statement.lean`.

**Independent verification of that reduction (by inspection — it is correct):** the proof is
the canonical π-transcendence-from-Hermite–Lindemann argument. `π` alg ⟹ `(π:ℂ)` alg ⟹
`i·π` alg (product with `i`, a root of `X²+1`) and `i·π ≠ 0`; Hermite–Lindemann ⟹
`exp(i·π)` transcendental; but `exp(π·i) = -1` (`Complex.exp_pi_mul_I`) is algebraic —
contradiction. This is exactly the reduction used by every cited formalization below (Eberl
derives π from "`iπ` algebraic ⟹ `e^{iπ}=-1` algebraic, contra Lindemann"). So the cited
`axiom hermite_lindemann` is a **faithful, genuinely-more-general narrowing**, not a leap.

The findings below are still useful for **(a)** swapping the axiom for a real mathlib theorem
when PR #28013 lands, and **(b)** the alternative "formalize it locally" paths in
`PENDING_WORK.md` (items A.2 / A.3).

---

## 1. Q1 — Is there an open mathlib PR/branch proving `Transcendental ℚ π` / `e`?

**YES. mathlib4 PR #28013 — "feat: Lindemann-Weierstrass Theorem"** is the live effort, and it
proves *exactly* what's needed (and far more).

- URL: <https://github.com/leanprover-community/mathlib4/pull/28013>
- Author: **astrainfinita** (= **Yuyang Zhao**, who wrote the `AnalyticalPart.lean` already in
  your snapshot). Continues the long-running original PR **#6718**.
- Status (as of 2026-06-15): **OPEN, not draft**, labels `awaiting-author`, `t-analysis`,
  `t-algebra`. Created 2025-08-05, last pushed 2026-05-29. `+1040 / −64`, 8 files. `mergeable:
  UNKNOWN`. Depends-chain (#18693, #29121, #36762, #37797, #37811) all checked off. So: alive
  but parked on the author addressing review — **not merged, no firm ETA.**

**Declarations it adds** (all in `Mathlib/NumberTheory/Transcendental/Lindemann/`):

| Declaration | Statement (paraphrased) |
|---|---|
| `transcendental_pi` | `Transcendental ℤ Real.pi` |
| `transcendental_e` | `Transcendental ℤ (Complex.exp 1)` |
| `transcendental_exp` | `a ≠ 0 → IsAlgebraic ℤ a → Transcendental ℤ (Complex.exp a)` ← **your `hermite_lindemann`, as a real theorem** |
| `transcendental_log` | `Complex.log u ≠ 0 → IsAlgebraic ℤ u → Transcendental ℤ (Complex.log u)` |
| `linearIndependent_exp` | full Baker form (lin-indep algebraic exponents ⟹ …) |
| `algebraicIndependent_exp` | the algebraic-independence corollary |

**File layout of the PR (the "bridge" you asked for):**
- `…/Lindemann/AnalyticalPart.lean` — already in your v4.29.1 snapshot (`exp_polynomial_approx`).
- `…/Lindemann/AlgebraicPart.lean` — **NEW**: the symmetric-function / Galois-conjugate
  "algebraic part" (the missing piece). Helper added to
  `Mathlib/RingTheory/MvPolynomial/Symmetric/Eval.lean` + `Mathlib/Data/Finsupp/Quotient.lean`.
- `…/Lindemann/Basic.lean` — **NEW**: assembles analytic + algebraic into
  `linearIndependent_exp` ⟹ `transcendental_exp` ⟹ `transcendental_e` / `transcendental_pi`.
- Also ticks the boxes in `docs/100.yaml` / `docs/1000.yaml` (Freek's "100 theorems": #30,
  transcendence of e/π).

**⚠️ over-ℤ vs over-ℚ gotcha (matters for swapping out your axiom):** the PR states everything
over **`ℤ`**; your file uses **`ℚ`**. They are equivalent (`ℚ = Frac ℤ`, char 0). Bridge
candidates already in your snapshot — verify the exact one when you wire it:
`transcendental_algebraMap_iff` (needs `Function.Injective (algebraMap ℤ ℚ)`, trivially true)
in `Mathlib/RingTheory/Algebraic/Basic.lean:324`, and `Transcendental.extendScalars`
(`Mathlib/RingTheory/Algebraic/Integral.lean`). Likewise `IsAlgebraic ℚ a ↔ IsAlgebraic ℤ a`
via `isAlgebraic_algebraMap_iff` (`…/Algebraic/Basic.lean:320`).

**Practical recommendation:** keep the cited-axiom file as-is for now (it's v4.29.1-safe and
audit-clean). When you next bump mathlib past the PR merge, delete `axiom hermite_lindemann`,
`import Mathlib.NumberTheory.Transcendental.Lindemann.Basic`, and either (i) re-prove
`transcendental_pi` by the same Euler reduction off the real `transcendental_exp`, or (ii) just
bridge mathlib's `transcendental_pi : Transcendental ℤ π` to `ℚ`. Either kills the axiom outright.

---

## 2. Q2 — Cleanest paper reference for the *algebraic part*

Two canonical expositions (each is the basis of a real formalization, so each is "known
formalizable"), plus a modern self-contained one:

1. **Niven, *Irrational Numbers* (Carus Math. Monograph 11, 1956), ch. on Lindemann–
   Weierstrass.** This is the version **Eberl's Isabelle proof "mostly follows"** — the cleanest
   route if you want π directly with minimal symmetric-function overhead.
2. **Baker, *Transcendental Number Theory* (CUP, 1975), Ch. 1.** The version the **Coq/Rocq
   proof follows** (Baker's β₁e^{α₁}+…+βₙe^{αₙ}=0 ⟹ all βᵢ=0 form). Best if you formalize the
   full Baker statement and get π/e as corollaries (matches PR #28013's structure too).
3. **arXiv:2306.14352, "A simple and self-contained proof for the Lindemann–Weierstrass
   theorem"** (2023) — modern, short, written to minimize prerequisites. Good cross-check.
4. Lecture-note level: Jeremy Booher, "Transcendental Numbers"
   (<https://people.clas.ufl.edu/jeremybooher/files/transcendence.pdf>); PlanetMath "proof of
   Lindemann–Weierstrass theorem and that e and π are transcendental".

The crux of the algebraic part (all three): from a hypothetical algebraic relation, pass to the
**Galois conjugates** of the algebraic exponents and symmetrize, producing a **nonzero rational
integer** whose absolute value is forced `< 1` by the analytic bound (`exp_polynomial_approx`)
— contradiction. mathlib's missing machinery is the symmetric-function bookkeeping over the
conjugates, which is precisely what PR #28013's `AlgebraicPart.lean` +
`MvPolynomial/Symmetric/Eval.lean` add.

---

## 3. Q3 — Existing formalizations in other systems (porting templates)

**Best template by far: Isabelle/HOL AFP.** Two entries by **Manuel Eberl**:
- **`Hermite_Lindemann`** — "The Hermite–Lindemann–Weierstraß Transcendence Theorem" (2021):
  <https://www.isa-afp.org/entries/Hermite_Lindemann.html>. Proves Baker's form, with
  corollaries: transcendence of **e and π**, and of `e^z`, `sin z`, `tan z` for nonzero
  algebraic `z`, and `ln z` for algebraic `z ≠ 0,1`. **8-module structure**; follows Baker's
  statement, deriving the classical Hermite–Lindemann as a consequence — *the same architecture
  as mathlib PR #28013*, so it's the closest 1:1 map. Proof outline PDF:
  <https://www.isa-afp.org/browser_info/current/AFP/Hermite_Lindemann/outline.pdf>.
- **`Pi_Transcendental`** — "The Transcendence of π" (2018):
  <https://www.isa-afp.org/entries/Pi_Transcendental.html>. Standalone, **follows Niven**,
  reuses the `e`-transcendence AFP entry. Smaller/simpler if you only want π — closest match to
  what you actually need.

**Coq / Rocq:** Bernard, Bertot, Rideau, Strub — full Lindemann–Weierstrass, follows Baker,
built on **Mathcomp** (algebra) + **Coquelicot** (analysis). Project page (with the dev):
<http://www-sop.inria.fr/marelle/lindemann/>. Papers: ITP 2017
(<https://inria.hal.science/hal-01647563/document>) and "Formal proofs of transcendence for e
and π …" (arXiv:1512.02791). Their key contribution = alternative forms of the **fundamental
theorem of symmetric polynomials** relating multivariate polys to conjugates of a univariate
poly — directly the lemma family mathlib still needs.

**HOL Light:** Bingham (2011) formalized **Hermite's proof that `e` is transcendental** (not π).
First machine-checked transcendence result; π was not done there.

**Metamath:** **no native transcendence of π or e** in set.mm (it has e/π *irrationality* only).
There is a HOL-Light→Metamath proof-conversion pipeline (Carneiro, arXiv:1412.8091) that *could*
in principle import Bingham's `e`-result, but no π-transcendence exists in Metamath. So Metamath
is not a useful template here.

**Adjacent (Lean 4, not L-W):** Karatarakis & Wiedijk, "A formalization of the Gelfond–Schneider
theorem" (arXiv:2603.24823, 2026) — Hilbert's 7th in Lean 4. Different theorem (α^β), no claimed
mathlib/L-W dependency, but confirms the Lean transcendence-theory ecosystem is active; worth a
glance for technique if you ever go the local-formalization route.

---

## 4. Bottom line / recommended next action

- The blocker is **already resolved** in-repo via the cited `hermite_lindemann` axiom + a
  correct Euler reduction (commit `67c4bb2`). Nothing urgent.
- To go **fully axiom-free**: the realistic path is **adopt mathlib PR #28013 on a mathlib bump**
  (it gives `transcendental_pi`/`transcendental_exp` outright) — not re-deriving the algebraic
  part yourself. Track #28013; it's `awaiting-author`, so watch for merge.
- If you do want to formalize a prerequisite locally before then (PENDING_WORK A.2), the
  accessible entry point remains **transcendence of `e` from `exp_polynomial_approx`** (no
  symmetric functions needed) — follow **Niven** (≈ Eberl's `Pi_Transcendental`/e-entry
  skeleton). Full π needs the symmetric-function-over-conjugates machinery (Baker / PR #28013's
  `AlgebraicPart.lean`).
