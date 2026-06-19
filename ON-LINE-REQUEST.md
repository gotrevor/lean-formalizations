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

---

## 2026-06-19 (UPDATE 2 — the crux is now ONE crisp Lean axiom; here it is verbatim)

**Major narrowing this lap.** The ENTIRE planar Kakeya lower bound is now machine-checked *down to a
single combinatorial axiom*. `#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound,
kakeya_dominant_scale_count]` — no `sorryAx`. Everything else (Córdoba L², the single-scale content
brick `cover_content_per_scale`, the exponential-beats-poly constant `content_ratio_lower`, and the
full ENNReal assembly) is kernel-checked. The lone remaining obligation is exactly this axiom
(`Kakeya2D/Engine.lean`):

```
axiom kakeya_dominant_scale_count
    {S : Set Plane} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2)
    (t : ℕ → Set Plane) (hcov : S ⊆ ⋃ n, t n) (hr : ∀ n, Metric.ediam (t n) ≤ 1) :
    ∃ j : ℕ, ∃ (a : ℕ → Plane) (A : ℕ → Set ℝ),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, A k ⊆ Set.Icc (0 : ℝ) 1) ∧
      ∃ s : Finset ℕ,
        (∀ n ∈ s, Metric.ediam (t n) ≤ ENNReal.ofReal ((1/2:ℝ)^j)) ∧            -- pieces at scale ≤ 2⁻ʲ
        (∀ n ∈ s, ENNReal.ofReal ((1/2:ℝ)^(j+1)) ≤ Metric.ediam (t n)) ∧        -- ... and ≥ 2⁻⁽ʲ⁺¹⁾
        (∀ k, (fun u => a k + u • dir ((k:ℝ)*(1/2:ℝ)^j)) '' (A k) ⊆ ⋃ n ∈ s, t n) ∧  -- covered segs ⊆ pieces
        ENNReal.ofReal (1/(((j:ℝ)+1)*((j:ℝ)+2)))
          ≤ ∑ k ∈ Finset.range (2^j), ENNReal.ofReal (2*(1/2:ℝ)^j) * volume (A k)     -- covered-length ≳ 1/poly
```

**What it says in words.** For an arbitrary cover of a planar Kakeya set, there is a *dominant dyadic
scale* `j` such that, using the `N = 2ʲ` equally-spaced net directions `θ_k = k·2⁻ʲ`, a `1/poly(j)`
fraction of the net is covered (over length `∑ₖ vol(A k) ≳ N/poly`, encoded via the `2δ` numerator
`= 1/((j+1)(j+2))`) **by cover pieces that themselves live at scale `j`** (diam `∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]`).

**Why this is the genuine hard core (confirmed by re-derivation this lap).** This breaks the
"net-scale circularity": the count step (`cover_content_per_scale`/Córdoba) needs the directions
`δ*`-separated with `N ≈ 1/δ*` at the *dominant piece scale* `δ* = 2⁻ʲ`, but `j` is the pigeonhole's
*output*. A FIXED net at any scale provably fails: with the coarse `2⁻ᴶ⁰`-net you only get covered
length on `2ᴶ⁰` directions, but certifying enough fine (scale-`j*`) pieces needs `≈ 2^{j*}` directions
each substantially covered — and `2^{j*}` can be ≫ `2ᴶ⁰`. I verified BOTH the naive Cauchy–Schwarz
sum-over-scales AND the full-net LP minimisation **diverge to 0** under the constraint I could extract
(adversary concentrates covered length at one huge scale on the coarse directions). The resolution must
produce a `1/poly` fraction of the FULL net **at the dominant scale itself** — exactly what the axiom
asserts. The genuinely missing piece is the *net-thinning + covered-length-retention* combinatorial
lemma that yields this.

**What I still need (any one):**
1. The exact statement+proof of the dominant-scale / net-thinning step as it appears in a rigorous
   source (Wolff 1999 survey; Mattila *Fourier Analysis and Hausdorff Dimension*, Kakeya chapter;
   Bourgain–Demeter), at transcription detail — specifically: how does one extract, for the dominant
   scale `j*`, a definite fraction of the `2^{j*}`-direction net each covered `≳ 1/poly` at scale
   `2⁻ʲ*`, given only the per-direction covered-length budgets? The precise weights and the retention
   argument.
2. Equivalently: a clean proof that the multi-net LP (per-direction budgets `∑_{j'} b_θ^{(j')} ≥ 1`,
   objective `∑_{j'} S_{j'}² 2^{-j'd}/(1+j')` with `S_{j'} = ∑_{θ∈Θ_{j'}} b_θ^{(j')}` over the full
   `2⁻ʲ'`-net) is bounded below by a positive constant — or a counterexample showing more cover
   structure is needed.
3. Davies' original 1971 projection/duality argument if it sidesteps this entirely and is more
   formalization-tractable.

The building blocks the proof will plug into are ALL machine-checked already: `Cover.exists_dominant_scale`
(scale pigeonhole), `Cover.exists_global_dominant_scale` (direction pigeonhole),
`Cover.exists_pullback_cover` (per-direction covered length), `Cover.cover_content_per_scale`,
`Engine.content_ratio_lower`. Only the orchestration that assembles the axiom's witnesses remains.
