# ON-LINE-REQUEST — networked host, please fulfil

Box has no general web. Append-only; date each item. A fulfiller commits
`ON-LINE-FINDINGS-<date>-<topic>.md`, deletes the answered item here, and removes this
file once nothing is open.

---

## 2026-06-19 — Córdoba/Davies planar-Kakeya Hausdorff (not just Minkowski) — cleanest write-up / formalization

**Context.** Branch `kakeya-davies`, proving `davies_kakeya_2d : KakeyaSetConjectureDim 2`
(planar Kakeya ⟹ Hausdorff dim 2). K1–K4 are done + axiom-clean: I have the **single-scale
Minkowski content bound** `vol(Sδ) ≳ 1/log(1/δ)` (Córdoba `L²`/Cauchy–Schwarz, file
`Kakeya2D/CordobaL2.lean`, lemma `volume_thickening_log_ge`). I've now reduced the remaining crux
(measure-free, via mathlib's `hausdorffMeasure_apply`) to a **Hausdorff content lower bound**:

> `∃ r>0, c>0 : every countable cover S ⊆ ⋃ₙ tₙ with diam(tₙ) ≤ r has ∑ₙ diam(tₙ)^d ≥ c`, for each `d<2`.

The obstruction is purely the **multi-scale** upgrade from Minkowski to Hausdorff: cover pieces can
be arbitrarily small, so single-scale bounds only bound the *count* of pieces, never `∑ diam^d`.

**What I need (any one suffices, most-useful first):**
1. The **cleanest fully-rigorous write-up** of the standard "Córdoba `L²` ⟹ Hausdorff dimension 2 for
   planar Kakeya/Besicovitch" argument — specifically the **dyadic double-pigeonhole** (over scales,
   then over directions) that reduces an arbitrary cover to a dominant scale, plus the **localized
   Córdoba count** at that scale (the `L²` bound for a tube family of *fractional* length covering a
   positive fraction of directions). Candidate sources: Wolff, *Recent work connected with the Kakeya
   problem* (1999 survey); Mattila, *Fourier Analysis and Hausdorff Dimension* (CUP 2015), Kakeya
   chapter; Bourgain–Demeter or Tao's blog/notes. I want the exact pigeonhole weights and the precise
   localized-`L²` statement, at a level of detail I can transcribe into Lean lemmas.
2. Davies' **original 1971 argument** (R. O. Davies, *Some remarks on the Kakeya problem*, Math. Proc.
   Camb. Phil. Soc. 69): is its projection/duality proof of dim = 2 *more elementary to formalize*
   than the Córdoba `L²` route I've built? If so, a clean statement of its key steps.
3. Any **existing Lean/Isabelle/Coq formalization** of a Kakeya Hausdorff-dimension lower bound (even
   partial) to port — e.g. in `google-deepmind/formal-conjectures` beyond the bare `sorry`, or
   elsewhere. (My defs mirror that repo verbatim, so a port would drop in.)
4. Whether current **mathlib** has, or has an open PR for, anything converting a *content/covering bound
   at all scales* into a Hausdorff-measure lower bound (a "Method I" / net-measure comparison, or a
   Frostman-measure *construction* — mathlib presently has only the spreading direction
   `Measure.le_hausdorffMeasure`). If such exists it could shortcut the whole pigeonhole.

This unblocks the lone remaining `sorry` `Engine.kakeya_hausdorffContentBound`; not blocking — I'll
keep building the reduction infrastructure (`Kakeya2D/Cover.lean`) and the localized-`L²` refactor
locally meanwhile.
