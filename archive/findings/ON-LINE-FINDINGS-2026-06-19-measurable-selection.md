# ON-LINE-FINDINGS 2026-06-19 — measurable selection (`kakeya_borel_selection`)

**Answers:** `ON-LINE-REQUEST.md` UPDATE 6 (asks 1–3) + the recurring Davies-1971 ask (ask 4 across
updates). The lone remaining axiom of `davies_kakeya_2d` is the Kakeya-agnostic
`kakeya_borel_selection` (`Selection.lean`): a Borel `G ⊆ ℝ × Plane` with non-empty sections over
`θ ∈ [0,1]` admits an `AEMeasurable` selector. This is the **von Neumann / Jankov–von Neumann
measurable-selection theorem** (a.k.a. the *measurable section theorem* of Dellacherie–Meyer).

**Sources read this session:** the live mathlib v4.29.1 tree in `.lake` (exact decl audit);
`RemyDegenne/brownian-motion` `BrownianMotion/Choquet/*` in the local Reservoir mirror
(`~/src/reservoir/RemyDegenne/brownian-motion`, HEAD `fbe9ec1`); mathlib4 GitHub PR/issue search;
Wikipedia (Jankov–von Neumann; Kuratowski–Ryll-Nardzewski); Kechris *Classical DST* (for theorem
numbers). Faithfulness: declaration names + line numbers below were read directly, not recalled.

---

## ⭐ Bottom line (read this first)

1. **The theorem you need is ALREADY FORMALIZED in Lean** — not in mathlib, but in
   **`RemyDegenne/brownian-motion`, `BrownianMotion/Choquet/MeasurableSection.lean`**. The headline
   `MeasurableSet.exists_measurable_section_right_nnreal` is exactly the measurable section theorem,
   and it produces a selector of **`AEMeasurable` strength — precisely what `kakeya_borel_selection`
   asks for** (see §1). The whole missing DST layer (Choquet capacity, paving-analytic sets, the
   début theorem) is built there too. Confidence the statement matches your need: **90%**.

2. **mathlib's `AnalyticSet` API alone is NOT enough.** Your current von-Neumann-from-`AnalyticSet`
   route (commit `4fc11b2`, "proj of selection graph is analytic") is the right *start*, but the wall
   ahead is **Choquet capacitability** — "analytic sets are universally measurable" — which mathlib
   **does not have** (confirmed by grep, §2) and which is genuinely the hard core of any
   measurable-selection proof. brownian-motion supplies exactly that missing layer. So the choice is
   *port that layer* or *cite it as the boundary axiom* (§6). Do **not** expect to reconstruct it
   cheaply from the bare `AnalyticSet` API.

3. **The `ℝ²` → `ℝ≥0` reduction is a non-issue** — mathlib has every piece (§3). brownian-motion's
   selector targets `ℝ≥0` (its own `MeasurableSection.lean:484` TODO is literally "extend to standard
   Borel spaces"); you dissolve that with `PolishSpace.measurableEquivOfNotCountable : Plane ≃ᵐ ℝ≥0`.

4. **Restate the axiom to a.e. form — it is strictly what's used and what's provable** (§4). Your
   `kakeya_borel_selection` demands the *pointwise* `∀ θ ∈ [0,1], (θ, a θ) ∈ G`, but
   `kakeya_hausdorffContentBound_jvn` (`Selection.lean:166`) immediately drops it to `∀ᵐ` via
   `Filter.Eventually.of_forall`. Measurable-section theorems give the a.e. form, never pointwise.
   Weakening the axiom to a.e. costs nothing downstream and makes it *exactly* the brownian-motion
   lemma. **This is the single highest-leverage change.**

5. **The KRN "lighter route" (ask 3) is not a free win** (§5): KRN needs *closed* non-empty sections;
   your covered-length-`≥1` graph is Borel but not closed-valued, and the geometry doesn't hand you
   closed sections (closing up `S` breaks the lower bound). Measurable-section/capacitability is the
   genuinely-needed tool.

---

## §1 — The exact Lean theorem you need already exists (brownian-motion)

Repo: `RemyDegenne/brownian-motion` (GitHub `https://github.com/RemyDegenne/brownian-motion`), a
Rémy-Degenne mathlib-staging project. Files: `BrownianMotion/Choquet/{Capacity, AnalyticSet,
CompactSystem, CountableClosed, Debut, MeasurableSection}.lean` (~165 KB total). Local copy:
`~/src/reservoir/RemyDegenne/brownian-motion/`.

**The headline section theorem** (`MeasurableSection.lean:478`):

```lean
lemma _root_.MeasurableSet.exists_measurable_section_right_nnreal
    {s : Set (Ω × ℝ≥0)} (hs : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧ (∀ ω, τ ω ≠ ⊤ → (ω, (τ ω).untopA) ∈ s) ∧
      ∀ᵐ ω ∂μ, debut (Prod.swap '' s) 0 ω ≠ ⊤ ↔ τ ω ≠ ⊤
```

(There is also `_left_nnreal`, and `IsMeasurableAnalytic.*` / `IsPavingAnalytic.*` variants, lines
430–482.) In words: for a measurable `s ⊆ Ω × ℝ≥0` and a finite measure `μ`, there is a **measurable**
`τ` that selects a section point wherever `τ ω ≠ ⊤`, and **a.e. `ω`, `τ ω` is finite iff the section
over `ω` is non-empty** (the début / first-entry time is finite iff the section is hit).

**Why this is exactly `kakeya_borel_selection`** (instantiation sketch):
- `Ω := ℝ` (the direction parameter `θ`); `μ := volume.restrict (Set.Icc 0 1)` — **finite**, so
  `IsFiniteMeasure` holds. (Your downstream a.e. is wrt `(volume : Measure ℝ)`, and
  `ae_restrict_iff'` bridges `∀ᵐ θ ∂volume, θ∈Icc01 → P` ⟺ `∀ᵐ θ ∂(volume.restrict Icc01), P`.)
- Transport the selection target `Plane` to `ℝ≥0` by a measurable equivalence `e : Plane ≃ᵐ ℝ≥0`
  (§3). Then `G' := (id ×ᵐ e) '' G ⊆ ℝ × ℝ≥0` is `MeasurableSet` (measurable image under a
  measurable equiv).
- Your sections are non-empty for **every** `θ ∈ [0,1]` (`isKakeya_exists_aeCover`), so the début is
  finite there, so **a.e. `θ ∈ [0,1]`, `τ θ ≠ ⊤`**, hence `(θ, untopA (τ θ)) ∈ G'`.
- Set `a θ := e.symm (untopA (τ θ))` (and any default where `τ θ = ⊤`). Then `a` is **`Measurable`**
  (stronger than the required `AEMeasurable`), and **a.e. `θ ∈ [0,1]`, `(θ, a θ) ∈ G`**. ∎

So the brownian-motion theorem delivers the **a.e. form** of your selector (§4) end-to-end. The only
adaptation is the `Plane → ℝ≥0` transport (§3) and weakening your axiom's conclusion to a.e. (§4).

---

## §2 — What mathlib v4.29.1 has, and the precise gap (confirmed by grep)

**Has** (`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`): the full first-level analytic-set
API — `AnalyticSet`, `MeasurableSet.analyticSet` (Borel ⟹ analytic), `MeasurableSet.analyticSet_image`
(projection of a measurable set is analytic — this is what your `4fc11b2` uses),
`AnalyticSet.image_of_continuous(On)`, `AnalyticSet.iInter/iUnion`, `IsClosed.analyticSet`,
`AnalyticSet.measurablySeparable` (Lusin separation), `AnalyticSet.measurableSet_of_compl` (Suslin:
analytic + co-analytic ⟹ Borel), `borelSchroederBernstein`.

**Does NOT have** (grep over `Mathlib/MeasureTheory/` returned nothing):
- **universal / null measurability of analytic sets** (the Choquet capacitability theorem) — the one
  load-bearing fact. mathlib's only mention is the docstring line "any Borel set is analytic"; there
  is no converse-direction measurability of a general analytic set.
- **any measurable selection / uniformization** (no `measurable_selection`, no
  `RyllNardzewski`, no von Neumann selector).
- **Choquet capacity** machinery.

**mathlib4 PR search** (`gh search prs --repo leanprover-community/mathlib4`, queries: "measurable
section/selection", "Choquet capacity", "analytic universally measurable", "début", "paving
analytic", "IsPavingAnalytic"): **zero hits**. As of 2026-06-19 there is **no open or merged mathlib
PR** for this. The capacitability layer lives **only** in the brownian-motion staging repo (it is
needed there for the Doob–Meyer decomposition / début theorem). Treat "it'll land in mathlib soon" as
**not** something you can wait on or `lake exe cache get`.

**The minimal prerequisite chain** (this is the answer to ask 1 "which intermediate theorems are the
minimal prerequisites"), as realized in brownian-motion `Choquet/`:
1. `Capacity.lean` — Choquet `Capacity` structure (monotone, continuous-from-above on a paving);
   `Measure.capacity` turns a finite measure into a capacity.
2. `CompactSystem.lean` / `CountableClosed.lean` — the compact paving that drives capacitability.
3. `AnalyticSet.lean` — `IsPavingAnalytic` / `IsMeasurableAnalytic` (def: a set is measurably
   analytic if it is the projection of a measurable set, `IsMeasurableAnalytic s := …For ℝ s`,
   line ~1001), projections of analytic sets are analytic (lines 418/438), and **analytic sets are
   capacitable / measurable wrt the capacity's completion** (the Choquet theorem — this is the piece
   mathlib lacks).
4. `Debut.lean` — the début (first-entry) theorem: `debut s 0` is measurable; finite ⟺ section
   non-empty.
5. `MeasurableSection.lean` — iterate (the `sectionSeq` von-Neumann-derivative construction) to a
   measurable section a.e. on the non-empty-section set.

This **is** the Souslin-scheme / von-Neumann-derivative construction you asked for (ask 1), done in
Lean. Reading these five files is the fastest way to see the exact weights/inequalities.

---

## §3 — `Plane → ℝ≥0` reduction: mathlib has everything (ask 1, the target mismatch)

`Plane = EuclideanSpace ℝ (Fin 2)` is Polish and uncountable ⟹ a `StandardBorelSpace`; `ℝ≥0` is too.
mathlib gives the measurable equivalence directly:

- `PolishSpace.measurableEquivOfNotCountable` (`Polish/Basic.lean:58`): **any two uncountable standard
  Borel spaces are measurably equivalent** ⟹ `Plane ≃ᵐ ℝ≥0`. (Also `PolishSpace.Equiv.measurableEquiv`
  for equal-cardinality standard Borel spaces.)
- `EuclideanSpace.measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ)`
  (`MeasureTheory/Measure/Haar/InnerProductSpace.lean:124`) if you'd rather peel coordinates first.
- `MeasureTheory.exists_measurableEmbedding_real` / `embeddingReal`
  (`Polish/EmbeddingReal.lean:57,63`): a measurable embedding of any standard Borel space into `ℝ`
  (the lighter "embed, don't equiv" option).

So brownian-motion's `ℝ≥0`-only target (its `MeasurableSection.lean:484` TODO "extend to standard
Borel spaces. Need an Option type with measurable space") is **not** a blocker for you — compose its
theorem with `e : Plane ≃ᵐ ℝ≥0`. (`WithTop ℝ≥0` already plays the "Option" role on the target side;
the `untopA` you saw is the `⊤`-to-`0` collapse.) Confidence the instances resolve: **80%** — verify
`StandardBorelSpace (EuclideanSpace ℝ (Fin 2))` and `Nonempty`-uncountability discharge cleanly.

---

## §4 — Restate the axiom to a.e. form (highest-leverage change)

Your axiom (`Selection.lean:151`) concludes the **pointwise** `∀ θ ∈ Icc 0 1, (θ, a θ) ∈ G`. But
`kakeya_hausdorffContentBound_jvn` (`Selection.lean:163–166`) consumes it as:

```lean
exact ⟨a, ha, Filter.Eventually.of_forall (fun θ hθ => hcov' θ hθ)⟩
```

i.e. it **immediately discards** the pointwise strength and feeds the `∀ᵐ` form into
`kakeya_hausdorffContentBound_of_aeMeasurableSelection` (whose hypothesis, `Wiring.lean:206–208`, is
`∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Icc 0 1 → 1 ≤ …`). **Nothing downstream uses pointwise membership.**

Pointwise-for-all-θ selection from a Borel graph is genuinely *stronger* than the a.e. form and is the
part measurable-section theorems do **not** give (they leave a null exceptional set). So:

> **Recommended restatement** (keeps the headline honest *and* matches the standard theorem):
> ```lean
> axiom kakeya_borel_selection :
>     ∀ G : Set (ℝ × Plane), MeasurableSet G →
>       (∀ θ ∈ Set.Icc (0:ℝ) 1, ∃ p : Plane, (θ, p) ∈ G) →
>       ∃ a : ℝ → Plane, AEMeasurable a ∧
>         ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 1)), (θ, a θ) ∈ G
> ```
> Then `kakeya_borel_selection` is **verbatim** the measurable section theorem, and the
> `of_forall` in `kakeya_hausdorffContentBound_jvn` becomes a one-line `ae_restrict`/`Eventually`
> massage. (You'll also touch `kakeya_aeMeasurable_selection_of_jvn`'s `jvn` hypothesis the same way —
> it currently mirrors the pointwise form.)

This is a real **faithfulness upgrade**: the axiom becomes a named, published, *already-Lean-proved*
theorem rather than a bespoke pointwise statement that's quietly stronger than necessary.

---

## §5 — The KRN "lighter route" (ask 3): assessed, and why it isn't a shortcut

**KRN (Kuratowski–Ryll-Nardzewski, Kechris 12.13 / Srivastava 5.2.1):** a multifunction `ψ : Ω →
(closed non-empty subsets of a Polish `X`)` that is *weakly measurable* (`{ω : ψ(ω) ∩ U ≠ ∅}`
measurable for every open `U`) admits a measurable selector. Its proof is an **elementary successive-
approximation** (Castaing) argument — **no capacitability, no analytic sets** — so it would be *much*
lighter to formalize than the von Neumann route **if it applied**.

**It doesn't apply to your graph as built.** Your section is
`G_ae(θ) = {p : coveredLength_θ(p) ≥ 1}` with `coveredLength_θ(p) = vol{t∈[0,1] : p + t·dirθ ∈ F}`,
`F = ⋃ Cₙ` an Fσ cover. For Fσ `F`, `p ↦ coveredLength_θ(p)` is **measurable but neither upper- nor
lower-semicontinuous**, so `{p : coveredLength ≥ 1}` is **not closed** — KRN's closed-valued hypothesis
fails. And you cannot manufacture closed sections from the geometry: the only closed object in reach is
`closure S`, and selecting segments in `closure S` does **not** lower-bound `dimH S` (dimension is
monotone the wrong way: `dimH S ≤ dimH (closure S)`). The segments genuinely live in the
non-measurable `S`; the cover `F` is the most measurable structure available, and it's only Borel-
(not closed-) sectioned. **⟹ The Borel-section measurable-selection theorem (capacitability route) is
the genuinely-needed tool.** Confidence: **80%**.

**One alternative worth a look (selection-free), if you ever revisit the architecture:** the *Kakeya
maximal function* route takes, per direction, the **sup over base points** of covered length instead of
*selecting* one. For an **open** cover `F`, `p ↦ coveredLength_θ(p)` is **lower-semicontinuous**, so
`sup_p = sup` over a countable dense set `= measurable` — no selection theorem at all. This is how
Córdoba's `L²` argument is usually run. It needs the cover to be **open** (you currently reduce to
*closed* pieces), so it's a re-architecture, not a drop-in — but it would sidestep DST entirely.
Flagged as a **research direction**, not verified for your exact `IsKakeya` setup (confidence **55%**).

---

## §6 — Three concrete paths to discharge `kakeya_borel_selection`

- **(A) Port the brownian-motion `Choquet/` layer** (~6 files, ~165 KB) into this repo, then prove your
  axiom as a corollary via §1 + §3 + §4. *Pro:* fully axiom-free end state. *Con:* multi-lap; it's real
  DST (capacitability + début + the section iteration); **version-skew risk** — brownian-motion tracks
  a newer mathlib than your v4.29.1, so expect API drift to patch. Network-isolated box **cannot** add
  it as a git dependency, so this must be a *source port*, not a `require`.
- **(B) Keep an axiom, but make it the *named* theorem + cite the Lean proof** (recommended interim).
  Adopt the §4 a.e. restatement so the axiom is *verbatim* the measurable section theorem
  (Dellacherie–Meyer; Kechris 18.1/29.9 von Neumann selection), and add a docstring pointer to
  `RemyDegenne/brownian-motion` `MeasurableSection.lean:478`
  (`MeasurableSet.exists_measurable_section_right_nnreal`) as the existing Lean proof. This is exactly
  the `formal_proof using lean4 at "<url>"` link-out convention `formal-conjectures` already uses —
  a *named, externally-proved* axiom is far more defensible than the current bespoke one, and it's a
  genuine honesty win even before (A).
- **(C) Host-vendor the files in an online window.** When the box next has a host/online lap, the host
  can copy the brownian-motion `Choquet/*.lean` (MIT-licensed, mathlib-style) into the repo and adapt
  imports, turning (A) into a mostly-mechanical build-fix job for subsequent offline laps.

**Recommendation:** do **(B) now** (cheap, big faithfulness gain, unblocks the headline narrative),
then pursue **(A)** as the long pole. Your current `4fc11b2` "projection is analytic" work is reusable
toward (A) but stops at mathlib's ceiling (§2) — the next brick you'd hit, "analytic ⟹ universally
measurable," is the brownian-motion capacitability theorem, so harvest that rather than rebuild it.

---

## §7 — Davies 1971 (recurring ask 4): honest status

Could **not** retrieve Davies, *Some remarks on the Kakeya problem*, Proc. Camb. Phil. Soc. **69**
(1971), 417–421 in full this session (no open PDF; `WebFetch` summarizers refuse to transcribe paper
math). What I can say with the sources I have (confidence **50%**, treat as a lead not a fact):

- Davies' planar argument is usually described via **point–line duality** (a line `y = ax + b` ↔ the
  point `(a,b)`) plus a projection/`L²` estimate; modern treatments (Córdoba, Bourgain, Wolff,
  Mattila §22–23) run the **Córdoba `L²`** version — the route you already built. I found **no**
  evidence that Davies' duality *avoids* a measurable family of lines; the standard rigorous proofs
  **reduce to a compact/Borel Besicovitch set first**, where the direction→line map can be taken
  Borel by construction — i.e. they pay the measurability cost up front, exactly the cost your
  `kakeya_borel_selection` isolates.
- **Key correctness point for your general `IsKakeya`:** that compact-reduction does **not** transfer
  the lower bound back to a *non-measurable* `S` for free (`dimH S ≤ dimH(closure S)`), so the
  literature's "reduce to compact" is a *convenience for the compact statement*, not a way to dodge
  selection for the fully general set. Your decision to handle general `IsKakeya` via measurable
  selection is therefore **faithful to the actual difficulty**, and Davies-duality is **unlikely** to
  be a lighter path than the measurable-section theorem now that the latter exists in Lean. I'd
  **deprioritize** chasing Davies' original proof.

---

## Existing-formalization census (ask 2)

- **Lean:** ✅ **`RemyDegenne/brownian-motion` `Choquet/MeasurableSection.lean`** — the measurable
  section theorem (ℝ≥0 target) + the full capacitability layer. Directly portable (§6A). Also
  `sven-manthe/A-formalization-of-Borel-determinacy-in-Lean` has a `Choquet.lean` application (Borel
  determinacy ⟹ uniformization is a heavier alternative route; not needed here).
- **mathlib4:** ❌ nothing, no PR (§2).
- **Isabelle/AFP, Coq:** **not found.** Searches surfaced no AFP measurable-selection / measurable-
  projection entry and no Coq one. Isabelle/HOL-Analysis has descriptive-set-theory fragments but I
  could **not** confirm a measurable selection theorem there — treat as "none located," not "proven
  absent" (confidence **60%**).

---

### Sources
- mathlib v4.29.1 local tree (`.lake/packages/mathlib`): `Polish/Basic.lean`,
  `Polish/EmbeddingReal.lean`, `Measure/Haar/InnerProductSpace.lean` — decl audit.
- `RemyDegenne/brownian-motion` `BrownianMotion/Choquet/{Capacity,AnalyticSet,Debut,MeasurableSection}.lean`
  (local mirror; GitHub `https://github.com/RemyDegenne/brownian-motion`).
- Wikipedia: *Jankov–von Neumann uniformization theorem*; *Kuratowski and Ryll-Nardzewski measurable
  selection theorem*. Kechris, *Classical Descriptive Set Theory* (von Neumann selection 18.1/29.9;
  KRN 12.13; capacitability 29.7). Dellacherie–Meyer, *Probabilities and Potential*, the measurable
  section theorem.
- mathlib4 GitHub PR/issue search (no results for the section/capacitability machinery).
