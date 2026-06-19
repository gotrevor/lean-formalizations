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

---

## 2026-06-19 (UPDATE — narrowed blocker: the net-scale circularity)

**All component lemmas are now built + axiom-clean** (this lap): both dyadic pigeonholes
(`Cover.exists_dominant_scale` over scales, `Cover.exists_global_dominant_scale` over a direction
net), the refined per-direction covered-length bound (`Cover.exists_pullback_cover`), the localized
Córdoba `L²` count for arbitrary covered sets (`CordobaL2.volume_thickening_sets_ge`), its numerator
(`TubeFractional.volume_thickening_covered_ge`: `vol(cthickening δ φ(A)) ≥ 2δ·vol(A)`), and the
**fully-assembled single-scale count** `CordobaL2.cordoba_cover_count`:

> at scale δ, net base pts `a k`, covered sets `A k ⊆ [0,1]`, container `P` with `φₖ(A k) ⊆ P`
>  ⟹ `(∑ₖ 2δ·vol(A k))² ≤ vol(cthickening δ P)·6πδ·2N(1+log N)`.

**The one remaining obstruction is a precise combinatorial-structure question — the net-scale
circularity.** The single-scale count needs the direction net to be `δ*`-separated with `N ≈ 1/δ*`,
where `δ* = 2^{-j*}` is the *dominant scale*. But `j*` is the OUTPUT of the pigeonhole, which needs
the net (its cardinality, the per-direction covered profiles `L k j`) as INPUT. The
`sum_overlap_le`/`cordoba_cover_count` machinery ties tube width = direction separation = `δ`, so a
single fixed net cannot serve all scales (a net of `N` directions is only `2^{-j}`-separated for
`j ≤ log₂ N`). Concretely I need ONE of:

1. The exact ordering/structure of the standard argument that breaks this circularity: do you
   (a) fix a fine net at scale `2^{-J}` (`N = 2^J`), find each direction's dominant scale `j(θ) ≤ J`
   via the scale-pigeonhole, group directions by `j(θ)` value to a dominant `j*` carrying `≳ N/poly`
   directions, then **thin** those to a `2^{-j*}`-separated subnet (≈ `2^{j*}` directions, one per
   angular cell) before applying the single-scale count — and crucially, why does the thinned subnet
   retain enough covered length per direction? Or (b) some cleaner route (e.g. summing the
   single-scale bound `M_j ≳ S_j²/poly(j)` over scales against `∑_j S_j ≥ N`)? I want the EXACT
   weights and the precise statement that closes `∑ ediam^d ≳ δ*^{-(2-d)}/poly ≥ c`.
2. The precise localized-`L²` / dominant-scale lemma as stated in Mattila (*Fourier Analysis and
   Hausdorff Dimension*, Kakeya chapter), Wolff (1999 survey), or Bourgain–Demeter — at transcription
   detail. My `cordoba_cover_count` is the single-scale brick; I need the cross-scale orchestration.

I have everything EXCEPT this orchestration. A clean statement of how the pigeonholes nest with the
net thinning would let me finish `kakeya_hausdorffContentBound` directly.
