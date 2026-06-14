# DIRECTION — read FIRST (operator directive, 2026-06-14, Trevor via Ren)

## ⛔ THIS IS A BOUNDED RUN. Build items 1–4, then STOP.

Curtis 1990 is **COMPLETE and axiom-clean** (re-verified by real `#print axioms`
on all headlines — pure trust base, no `sorryAx`, no custom axioms). The math core
is **done and is not to be reopened or extended in this run.**

This run has exactly ONE job: **add independent verification / faithfulness
cross-checks** (items 1–4 below) that raise confidence the formalized *statements*
faithfully capture Curtis — the kind of external consistency checks you'd run on the
quadratic formula by plugging in cases where the answer is independently known.

**When items 1–4 are built (green + axiom-clean) — or honestly marked
omitted-as-intractable — and `src/` is sorry-free, you are DONE. STOP the treadmill**
(self-stop sentinel; see "Stop condition" at the bottom).

### Out of scope this run (DO NOT START — deferred to a future run, Trevor's call)
- ❌ Constructible-number / doubling-the-cube impossibility (the prior "next target").
- ❌ Upstreaming Curtis to mathlib.
- ❌ Any new theorem, problem, or target.
These are PARKED in `PENDING_WORK.md`. Do **not** treat them as "open frontier" when
deciding whether to stop. Trevor has explicitly scoped this run to 1–4 only. Continuing
past 1–4 is going OUT OF SCOPE, not diligence.

---

## Rules for this run

- **No `sorry`/`admit`, ever.** Every item below is provable by elementary means. If a
  sub-item turns out to cost more than its worth, **OMIT it** (delete the attempt, leave a
  one-line note in `PENDING_WORK.md`) — do **not** leave a `sorry`. A stray `sorry` blocks
  the self-stop and churns the run.
- **Order: certain-and-easy first, risky-optional last.** This is NOT a "hardest-first"
  run — the goal is a complete bundle of cross-checks, not resolving a feasibility gate.
  Do item 1, the mandatory part of item 2, item 3's worked example, and item 4 first
  (all easy + certain). Attempt the OPTIONAL parts (g(6,9,20) by hand, a general
  constructive corollary) only after, and omit if costly.
- **Keep `Statement.lean` the faithful audit surface.** New checks go in sibling files
  (suggested: `Curtis/Boundary.lean` for items 1+3; extend `Curtis/Anchors.lean` for
  item 2; docs for item 4). Each new theorem gets a docstring saying what it cross-checks
  and why it raises confidence.
- **Commit every green build** (verify from a real `lake build`). **DO NOT push** (host
  publishes). Standing repo rules in `HANDOFF.md` still apply.
- Reference corpus if you need mathlib lemma names:
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

---

## The four items

### 1. The n = 2 boundary check — MANDATORY, the single most convincing one
The entire content of Curtis is a boundary: **n = 2 HAS a closed formula (Sylvester,
g(a,b) = ab − a − b); n ≥ 3 does NOT.** Prove the n = 2 analog of `no_polynomial_relation`
is **true** — i.e. for two generators the graph DOES lie on a hypersurface — exhibiting
the explicit Sylvester polynomial. This demonstrates the theorem's teeth sit exactly at
the n=2 / n=3 line and is not a vacuous "no formula for anything" artifact.

Target (adjust names to taste; this is the shape):
```lean
/-- n = 2 boundary check: contrast with `no_polynomial_relation`. For TWO generators a
nonzero polynomial DOES vanish on the whole graph — the Frobenius number of a pair is
given by Sylvester's `ab − a − b`, so the 2-generator graph lies on the hypersurface
`X₀·X₁ − X₀ − X₁ − Y = 0`. Curtis's theorem is precisely that this becomes impossible at
n = 3. -/
theorem n2_polynomial_relation_exists :
    ∃ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 ∧
      ∀ a b g : ℕ, 1 < a → 1 < b → Nat.Coprime a b →
        FrobeniusNumber g {a, b} →
        eval ![(a : ℂ), (b : ℂ), (g : ℂ)] F = 0
```
- Witness `F = X 0 * X 1 - X 0 - X 1 - X 2`. Nonzero: its `X₀X₁` coefficient is `1`.
- Vanishing: mathlib's Sylvester result (`Mathlib.NumberTheory.FrobeniusNumber`, the
  coprime-pair theorem — find the exact name, likely `frobeniusNumber_pair`) gives the
  Frobenius number of `{a,b}` is `a*b - a - b`; `FrobeniusNumber` is an `IsGreatest`, hence
  unique, so `g = a*b - a - b`. Cast to ℂ (use `Nat.cast_sub`, valid since `ab ≥ a+b` for
  coprime `a,b > 1`) and the eval is `0`.

### 2. More numerical anchors against an independent computation — MANDATORY (core) + OPTIONAL (stretch)
The repo currently has ONE faithfulness anchor (`g(3,7,8)=5`, two ways). Add more
independent agreement between Curtis's Lemma 2 value formula `(k−2)·s₂ + s₃ − s₁` and
mathlib's independently-defined `FrobeniusNumber`. Each agreement is fresh evidence Lemma 2
is stated faithfully.
- **MANDATORY:** add **2–3 more Lemma-2 value anchors** at different `(s₁,s₂,s₃,k)` that
  satisfy `Lemma2.lemma2`'s hypotheses. For each, state the value `(k−2)s₂+s₃−s₁` and confirm
  `FrobeniusNumber` agrees (mirror `Anchors.frobeniusNumber_3_7_8_via_lemma2`). Bonus: prove
  that Frobenius number a SECOND way (directly, like `Anchors.frobeniusNumber_3_7_8`) for at
  least one of them.
- **OPTIONAL (stretch):** `FrobeniusNumber 43 {6,9,20}` — the Chicken-McNugget number (the
  Penn video already in `SOURCES.md`). ⟨6,9,20⟩ is NOT admissible (6 isn't prime), so this
  tests mathlib's `FrobeniusNumber` predicate *outside* Curtis's family — a different surface
  than the Lemma-2 anchors. Prove by hand (residue-cover mod 6, like anchor 2) or `decide`.
  Avoid `native_decide` if you can (keeps the repo's no-`ofReduceBool` cleanliness); if you
  must use it, note it in the docstring — it's a standalone anchor, so it can't touch any
  headline's axiom footprint. **Omit entirely if it costs more than ~one focused pass.**

### 3. Refute a named candidate formula — MANDATORY (worked example) + OPTIONAL (general)
- **MANDATORY:** make the abstract `¬∃` tangible with one concrete refuted guess. The natural
  "extend Sylvester symmetrically" candidate `s₁s₂ + s₂s₃ + s₁s₃ − s₁ − s₂ − s₃` already
  fails at ⟨3,7,8⟩: it evaluates to `21+56+24−18 = 83`, not `g = 5`. Formalize:
```lean
/-- A concrete witness that the natural symmetric degree-2 guess is NOT a Frobenius formula:
it already disagrees with the true value at the admissible triple ⟨3,7,8⟩ (gives 83, not 5). -/
theorem symmetric_guess_not_a_formula :
    ∃ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ ∧ FrobeniusNumber g {s₁, s₂, s₃} ∧
      eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)]
        (X 0 * X 1 + X 1 * X 2 + X 0 * X 2 - X 0 - X 1 - X 2) ≠ (g : ℂ)
```
  Witness `⟨3,7,8,5⟩` reusing the `Anchors` lemmas; the eval is `83 ≠ 5` by `norm_num`/`simp`.
  (Double-check the arithmetic in Lean — don't trust this comment's number.)
- **OPTIONAL (stretch):** a *constructive* corollary — given any candidate, an explicit
  admissible triple refutes it. This is essentially the contrapositive of the headline and is
  harder to state cleanly; attempt only if 1–4 are otherwise done, and OMIT (don't sorry) if
  it doesn't fall out.

### 4. Document the "free findings" + fix the stale docstrings — MANDATORY, easy
- State explicitly (in `Curtis/README.md` and/or a short `FINDINGS.md`) the two consequences
  the proof already gives, because each is a place a mis-reading could hide:
  1. **Stronger than "not polynomial" — "not algebraic":** the graph lies on no proper
     hypersurface of ℂ⁴ (Zariski-dense). The n=2 contrast (item 1) is the cleanest way to feel
     this — there the graph DOES lie on a hypersurface.
  2. **Sub-families still have formulas.** Arithmetic progressions ⟨a, a+d, …⟩ have a known
     closed Frobenius formula, and n=2 has Sylvester; Curtis forbids only a *single universal*
     formula over all triples. The Lean statement (`no_finite_polynomial_formula`, the "no
     finite menu covering ALL admissible triples" form) is correct and must not be misread as
     forbidding per-family formulas.
- **Fix the stale docstrings** (they currently mislead by describing the pre-completion
  scaffold state):
  - `Curtis/Engine.lean` module docstring (≈ lines 9, 11, 35) still says the main theorem is
    "currently `sorry`" / "disclosed sorrys". Update to reflect COMPLETE + axiom-clean.
  - `Curtis/README.md` (≈ line 8) says "`sorry` (statements first)" / "Proof: not started".
    Update to DONE.

---

## Completion = stop condition (allow-stop is armed on this run)

You are running with `--allow-stop`. On a **review/reflect lap**, once ALL of the following
hold, certify completion and self-stop (do NOT keep churning):
- items 1, the mandatory parts of 2 and 3, and 4 are built; optional parts are either done or
  explicitly omitted-with-a-note (omission is fine — they are stretch goals);
- `lake build` is green and `src/` is sorry-free (`#print axioms` on the headlines still clean,
  and the new check theorems are clean too);
- there is no remaining IN-SCOPE work (the parked targets do NOT count — they are deferred).

Then, per `lean-review-lap.md`'s completion exit: write your synthesis + refresh `HANDOFF.md`,
commit, and:
```
printf 'source=lap\nreason=verification-hardening run complete (Curtis cross-checks 1-4 built, axiom-clean)\n' > "$LEAN_STOP_SENTINEL"
```
then end the turn. If a `sorry` lingers or a mandatory item is missing, do NOT stop — finish it.
