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

---

## UPDATE 3 (2026-06-19, retention lap) — net-thinning combinatorics SOLVED locally; now two narrower asks

The net-thinning + covered-length-retention lemma from UPDATE 2 is **now proven in Lean** (the
"shift average"): `NetThinning.lean`'s `exists_shift_ge` shows that decomposing the fine `2⁻ᴶ`-net
into the `2^{J-j*}` dyadic shifts of the `2⁻ʲ*`-subnet, SOME shift retains ≥ the full average of the
fine net's dominant-scale covered length — so the thinning loses nothing. (The earlier
"diverge to 0" dead ends were artifacts of trying to use the UNSHIFTED grid / a fixed net; the shift
average is the fix.) Combined with `one_le_tsum_volume_fiber_union` + the existing pigeonholes, the
orchestration is mathematically complete **modulo two narrower points below.** UPDATE 2's asks are
superseded by these.

**ASK 3a — is the UNSHIFTED-grid dominant-scale claim TRUE, or is the shift essential?**
Our cited axiom `kakeya_dominant_scale_count` asserts the *unshifted* net `dir(k·2⁻ʲ)` (`k<2ʲ`) is
covered length `≥ 1/poly(j)` at some scale `j`. The shift average only proves SOME base angle `θ₀`
works (net `dir(θ₀+k·2⁻ʲ)`). Question: does there exist a cover `{tₙ}` of a planar Kakeya set
(`ediam ≤ 1`) such that for EVERY dyadic scale `j`, the unshifted `2⁻ʲ`-grid directions are each
poorly covered (`∑_{k<2ʲ} covered-length(dir(k·2⁻ʲ) at scale j) < 1/((j+1)(j+2))`)? I.e. can an
adversary make every dyadic-rational direction be covered only at scales other than its own grid
scale? If YES (shift essential), our current axiom is possibly-false and we must restate to the
shifted form (we plan to). If NO (unshifted suffices), a citation/proof of that would let us keep the
simpler unshifted axiom. Either answer resolves a faithfulness question.

**ASK 3b — how does the rigorous literature handle the NON-MEASURABLE segment family?**
A general Kakeya set `S` (our `IsKakeya`: a unit segment in every direction, S possibly
non-measurable) gives a base-point function `θ ↦ a(θ)` that is a bare choice function — so
`θ ↦ (covered length of S's segment in direction θ at scale j)` need not be measurable, blocking a
CONTINUOUS shift-average `∫₀^{2⁻ʲ} (…) dα`. We sidestep this with a DISCRETE shift over a finite
`2ᴶ`-net (finitely many base points ⟹ no measurability needed). But this forces the dominant scale
`j* ≤ J` (we cap the scale fn at `J`), leaving a "Case B" residual (`j*=J`: the cover is dominated
by pieces finer than `2⁻ᴶ`). Question: in the standard proofs (Wolff lectures; Mattila §22–23;
Córdoba), how is the dominant-scale extraction made rigorous for an arbitrary (non-measurable)
Kakeya set — via a discrete net + Case-B argument like ours, via reduction to a Borel/compact
Besicovitch set, or via the maximal-function formulation that integrates over base points cleanly?
The exact handling of Case B (covered overwhelmingly by sub-resolution pieces) would let us close it.

Both asks are about the SAME final gap; either unblocks the discharge. The retention combinatorics
itself is done and needs nothing further.

---

## UPDATE 4 (2026-06-19, Case-A discharged lap) — the obstruction is now ISOLATED + sharpened

**Progress this lap (committed, `lake build` green, `#print axioms` verified):** the former
monolithic dominant-scale axiom `kakeya_dominant_scale_count` is **GONE**. `davies_kakeya_2d` now
reduces to `[propext, Classical.choice, Quot.sound, kakeya_subresolution_content]` — the new axiom is
the strictly-narrower **Case B residual**. The entire dominant-scale orchestration (fine net ⟶
`exists_dominant_shift` shift-pigeonhole ⟶ base-angle `cover_content_per_scale`) is now a machine-checked
proof for **Case A** (dominant dyadic scale `j < J`, the net resolution), including the finite/infinite
scale-`j`-fiber split. Only **Case B** (`j = J`: the cover dominated by pieces FINER than `2⁻ᴶ`) is
axiomatized.

**Sharpened obstruction (worked out this lap — please confirm/correct against the literature).**
I tried to close Case B by the multi-scale Córdoba `L²` sum with the *fixed* `2ᴶ`-net and found it
**provably diverges to 0 for `d > 1`** (the range that matters for `dim = 2`):

- Per sub-scale `j ≥ J`, the fixed `2ᴶ`-net Córdoba count gives `S_j² ≤ M_j · poly(J) · 2⁻ʲ · 2ᴶ`
  (`S_j` = aggregate scale-`j` covered length over the `2ᴶ` net, `M_j` = #scale-`j` pieces). Hence the
  content `Σ = ∑_j M_j 2⁻ʲᵈ ≥ (2⁻ᴶ/poly(J))·∑_{j≥J} S_j² 2^{j(1-d)}`.
- Minimizing `∑_{j≥J} S_j² 2^{j(1-d)}` s.t. `∑_{j≥J} S_j ≥ 2ᴶ⁻¹` (Case B: most length sub-resolution)
  gives min `= (2ᴶ⁻¹)² / ∑_{j≥J} 2^{j(d-1)}`. For `d>1` the denominator `∑_{j≥J} 2^{j(d-1)} = ∞`, so
  the bound is **0**. The adversary spreads covered length over unboundedly-fine scales; the coarse
  `2ᴶ`-net's count is too weak at fine scales (`M_j ≳ S_j² 2^{j-J}/poly`, the `2^{j-J}` doesn't pay).

So the single-fixed-net approach **cannot** close `d>1`. The correct count at sub-scale `j` needs the
**`2ʲ`-net (right resolution)** — `M_j ≳ S_j(j)²/poly(j)` — but then each scale uses a *different* net
and there is no obvious way to lower-bound a single cross-scale sum. (The shift-average solves exactly
ONE scale at its own resolution; Case B is precisely "no single scale dominates — mass at unboundedly
fine scales".)

**What I need (any one closes Case B / `kakeya_subresolution_content`):**
1. **The exact multi-scale combination** the rigorous Córdoba/Davies/Wolff proof uses to avoid the
   `d>1` divergence above — does it (a) use per-scale right-resolution nets with a specific
   convexity/Hölder that I'm missing, (b) argue by contradiction from `Σ < ∞ ⟹ M_j ≤ Σ·2^{jd}`
   (bounding the *number* of fine pieces) and derive a covering contradiction, or (c) reduce to a
   single scale via a Borel/compact reduction + dyadic maximal cubes? I want the precise inequality
   chain at transcription detail.
2. **Davies' original 1971 projection/duality proof** — does it sidestep the multi-scale Córdoba sum
   entirely (and is it more formalization-tractable)? A clean statement of its key steps. (Re-asking
   point 2 of the very first request with more urgency: this may be the path of least resistance.)
3. Any existing **Lean/Isabelle/Coq** formalization of a Kakeya Hausdorff lower bound to port.

Faithful Lean statement of the current residual (so a port drops in) — `kakeya_subresolution_content`
in `Kakeya2D/Engine.lean`: given `N = 2ᴶ` directions (base pts `a k`, measurable covered sets
`A k ⊆ [0,1]`, base angle `c`), a set `s` of cover pieces all with `ediam ≤ 2⁻ᴶ`, the containment
`(u ↦ a k + u·dir(c+k·2⁻ᴶ)) '' A k ⊆ ⋃_{n∈s} U_n`, and the numerator
`1/((J+1)(J+2)) ≤ ∑_{k<2ᴶ} 2·2⁻ᴶ·vol(A k)`, conclude `D⁻¹·cR ≤ ∑'_n ediam(U_n)^d` (`D = vol(unit disc)`).
