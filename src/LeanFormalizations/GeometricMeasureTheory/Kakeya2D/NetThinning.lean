/-
# Net thinning / shift-pigeonhole (the covered-length retention combinatorics)

The cross-scale orchestration of the planar Kakeya lower bound (the lone remaining obligation
`kakeya_dominant_scale_count`) hinges on a **covered-length retention** step: after the dyadic
pigeonholes deliver a *dominant scale* `j*` carrying a `≳ 1/poly(j*)` fraction of the aggregate
covered length over a *fine* `2⁻ᴶ`-net of directions, one must pass to a `2⁻ʲ*`-separated subnet
(`N ≈ 2^{j*}` directions, the resolution the localized Córdoba count needs) **without losing that
covered length** — the naive "one representative per cell" loses it, because the grid-aligned
representative may be poorly covered (an adversary concentrates the covered length off-grid).

The robust fix is a **shift average**. Decompose the fine index range `range (B·M)` (here
`B = 2^{J-j*}` = number of dyadic shifts, `M = 2^{j*}` = subnet size) into the `B` arithmetic
progressions `{β + B·i : i < M}`, one per shift `β < B`. The full covered length is the sum over
shifts of the per-shift subnet totals, so **some shift `β` captures at least the average** — a
`1/B`-fraction of the entire fine total. That shifted subnet (directions `β·2⁻ᴶ + i·2⁻ʲ*`, `i < M`,
which is `2⁻ʲ*`-separated) is the one fed to Córdoba.

This file proves the two purely-combinatorial bricks of that step, both `ℝ≥0∞`-valued and
`#print axioms`-clean:

* `sum_range_mul_eq_sum_shift` — the AP decomposition `∑_{k<B·M} L k = ∑_{β<B} ∑_{i<M} L(β+B·i)`;
* `exists_shift_ge` — the shift pigeonhole `∃ β<B, (∑_{k<B·M} L k) ≤ B · ∑_{i<M} L(β+B·i)`.

The geometric wiring (fine net ⟶ dominant scale ⟶ shifted subnet ⟶ Córdoba) consumes these.
Reference: the dominant-scale / shift-average argument is standard in the Córdoba/Davies planar
Kakeya literature (Wolff, *Lectures on Harmonic Analysis*; Mattila, *Fourier Analysis and Hausdorff
Dimension*, §22–23). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cover
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Arithmetic-progression decomposition of a range sum.** Splitting `{0,…,B·M−1}` by residue
`β = k mod B` and quotient `i = k div B` regroups any sum over `range (B·M)` into the `B` shifted
arithmetic progressions `{β + B·i : i < M}`:

  `∑_{k < B·M} L k = ∑_{β < B} ∑_{i < M} L (β + B·i)`.

Proven by the explicit bijection `range (B·M) ≃ range B ×ˢ range M`, `k ↦ (k % B, k / B)` with
inverse `(β, i) ↦ β + B·i` (`Finset.sum_nbij'`), then `Finset.sum_product'`. The shift-pigeonhole
`exists_shift_ge` reads a good shift `β` off this identity. -/
theorem sum_range_mul_eq_sum_shift (B M : ℕ) (L : ℕ → ℝ≥0∞) :
    ∑ k ∈ range (B * M), L k = ∑ β ∈ range B, ∑ i ∈ range M, L (β + B * i) := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp
  -- regroup the RHS double sum as a sum over the product finset
  rw [← Finset.sum_product']
  -- transport the LHS along `k ↦ (k % B, k / B)`
  refine Finset.sum_nbij' (fun k => (k % B, k / B)) (fun p => p.1 + B * p.2) ?_ ?_ ?_ ?_ ?_
  · -- `(k % B, k / B) ∈ range B ×ˢ range M`
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.mod_lt k hB, (Nat.div_lt_iff_lt_mul hB).mpr (by rwa [Nat.mul_comm M B])⟩
  · -- `β + B·i ∈ range (B·M)`
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hβ, hi⟩ := hp
    rw [Finset.mem_range]
    show p.1 + B * p.2 < B * M
    have hstep : B * (p.2 + 1) ≤ B * M := Nat.mul_le_mul_left B hi
    rw [Nat.mul_succ] at hstep
    omega
  · -- left inverse: `(k % B) + B·(k / B) = k`
    intro k _
    show k % B + B * (k / B) = k
    rw [Nat.mod_add_div]
  · -- right inverse: `((β + B·i) % B, (β + B·i) / B) = (β, i)`
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hβ, _⟩ := hp
    have hmod : (p.1 + B * p.2) % B = p.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ]
    have hdiv : (p.1 + B * p.2) / B = p.2 := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hβ, Nat.zero_add]
    show ((p.1 + B * p.2) % B, (p.1 + B * p.2) / B) = p
    rw [hmod, hdiv]
  · -- function agreement: `L k = L ((k % B) + B·(k / B))`
    intro k _
    show L k = L (k % B + B * (k / B))
    rw [Nat.mod_add_div]

/-- **Shift pigeonhole (covered-length retention).** For `B > 0` and any weights `L : ℕ → ℝ≥0∞`,
some shift `β < B` whose arithmetic progression `{β + B·i : i < M}` carries at least the average
fraction of the full range sum:

  `∃ β < B,  ∑_{k < B·M} L k  ≤  B · ∑_{i < M} L (β + B·i)`.

This is the heart of the net-thinning: with `L k` = covered length (at the dominant scale) of the
`k`-th *fine* direction, the LHS is the aggregate fine covered length `≥ 2ᴶ·scaleWeight j*`; the
chosen shift `β` then gives a `2⁻ʲ*`-separated subnet of `M = 2^{j*}` directions with covered
length `≥ 2^{j*}·scaleWeight j*` — exactly the numerator the localized Córdoba count needs, with
no covered length lost in the thinning. Proven from `sum_range_mul_eq_sum_shift` by taking the
shift maximizing the per-shift subnet total (`Finset.exists_max_image`, `Finset.sum_le_sum`). -/
theorem exists_shift_ge {B : ℕ} (hB : 0 < B) (M : ℕ) (L : ℕ → ℝ≥0∞) :
    ∃ β ∈ range B, (∑ k ∈ range (B * M), L k) ≤ (B : ℝ≥0∞) * ∑ i ∈ range M, L (β + B * i) := by
  rw [sum_range_mul_eq_sum_shift]
  set S : ℕ → ℝ≥0∞ := fun β => ∑ i ∈ range M, L (β + B * i) with hS
  obtain ⟨β₀, hβ₀, hmax⟩ :=
    Finset.exists_max_image (range B) S ⟨0, Finset.mem_range.mpr hB⟩
  refine ⟨β₀, hβ₀, ?_⟩
  calc ∑ β ∈ range B, S β
      ≤ ∑ _β ∈ range B, S β₀ := Finset.sum_le_sum (fun β hβ => hmax β hβ)
    _ = (range B).card • S β₀ := by rw [Finset.sum_const]
    _ = (B : ℝ≥0∞) * S β₀ := by rw [Finset.card_range, nsmul_eq_mul]

/-! ### Union-measure per-scale total (the localized-Córdoba numerator)

The Córdoba count needs, per net direction, the measure of the **covered set** `A k`
(`= vol{t : φₖ(t) ∈ some scale-`j` piece}`), i.e. the measure of a *union* of pullback pieces.
This differs from the per-scale *sum* `∑_{n} vol(Tₙ)` exposed by `exists_pullback_cover`: same-scale
cover pieces may overlap, so the sum overcounts and the genuine covered length is the union measure.
The dyadic pigeonhole therefore must run on the union measures `L k j = vol(⋃_{g n = j} Tₙ)`. The next
lemma supplies the per-direction hypothesis `1 ≤ ∑ⱼ L k j` (the input to the generic
`exists_global_dominant_scale`): the per-scale union measures total `≥` the measure of the full
union by countable subadditivity over scales. -/

/-- **Per-scale union measures total ≥ the full union measure.** For any scale function `g` and any
family `T : ℕ → Set ℝ`, grouping by scale and taking the union per scale loses no covering:
`vol(⋃ₙ Tₙ) ≤ ∑ⱼ vol(⋃_{n : g n = j} Tₙ)` (countable subadditivity over the scales `j`). In
particular a covered unit segment (`1 ≤ vol(⋃ₙ Tₙ)`) gives `1 ≤ ∑ⱼ vol(⋃_{g n = j} Tₙ)`, the
per-direction input the global dominant-scale pigeonhole consumes — now on the genuine covered
(union) length, not the overcounted sum. No measurability needed (`volume` is an outer measure). -/
theorem one_le_tsum_volume_fiber_union (g : ℕ → ℕ) {T : ℕ → Set ℝ}
    (h : 1 ≤ volume (⋃ n, T n)) :
    1 ≤ ∑' j : ℕ, volume (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n) := by
  refine le_trans h ?_
  have heq : (⋃ n, T n) = ⋃ j : ℕ, (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨g n, n, rfl, hn⟩
    · rintro ⟨_, n, rfl, hn⟩; exact ⟨n, hn⟩
  rw [heq]
  exact measure_iUnion_le _

/-! ### Geometric foundation: a measurable pullback cover from a closed-piece cover

The localized-Córdoba numerator needs the per-direction covered set `A k` to be **measurable** (the
Córdoba `L²` integrals are over measurable indicators). The raw pullback `Tₙ = φ⁻¹(Uₙ) ∩ [0,1]` is
measurable iff the cover piece `Uₙ` is (a general Kakeya cover piece may be non-measurable). The fix:
work with **closed** pieces — `IsClosed Uₙ` makes `φ⁻¹(Uₙ)` closed (`φ` continuous), hence the
pullback is measurable. In the discharge this is supplied by replacing each cover piece `tₙ` by its
closure `closure tₙ` (same `ediam`, still covering `S`), so the content bound is unaffected. This
brick packages the measurable pullback together with the forward containment `φ(Tₙ) ⊆ Uₙ` (the
geometric link to the container) and the union-measure bound `vol(⋃ₙ Tₙ) ≥ 1` (a covered unit
segment), the three facts the dominant-scale wiring consumes. -/

/-- **Measurable pullback cover (geometric foundation of the discharge).** A unit segment in
direction `v` covered by *closed* pieces `Uₙ` pulls back, along the unit-speed isometry
`φ : t ↦ a + t•v`, to measurable pieces `Tₙ = {t∈[0,1] : φ t ∈ Uₙ}` with `φ(Tₙ) ⊆ Uₙ` and
`vol(⋃ₙ Tₙ) ≥ 1`. Measurability (vs. the raw `exists_pullback_cover`) comes from `Uₙ` closed +
`φ` continuous; the forward containment and union bound are what `exists_dominant_shift` (via
`one_le_tsum_volume_fiber_union`) and the base-angle Córdoba count consume. -/
theorem exists_measurable_pullback_cover {a v : Plane} (hv : ‖v‖ = 1) {U : ℕ → Set Plane}
    (hU : ∀ n, IsClosed (U n)) (hcov : affineSegment ℝ a (a + v) ⊆ ⋃ n, U n) :
    ∃ T : ℕ → Set ℝ, (∀ n, MeasurableSet (T n)) ∧ (∀ n, T n ⊆ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, (fun t => a + t • v) '' (T n) ⊆ U n) ∧ 1 ≤ volume (⋃ n, T n) := by
  set φ : ℝ → Plane := fun t => a + t • v with hφ
  have hφcont : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  set T : ℕ → Set ℝ := fun n => Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' (U n) with hT
  refine ⟨T, ?_, fun n => Set.inter_subset_left, ?_, ?_⟩
  · exact fun n => measurableSet_Icc.inter ((hU n).preimage hφcont).measurableSet
  · -- forward containment `φ(Tₙ) ⊆ Uₙ`
    intro n y hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ht.2
  · -- `1 = vol[0,1] ≤ vol(⋃ₙ Tₙ)`
    have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ n, T n := by
      intro t ht
      have hmem : φ t ∈ affineSegment ℝ a (a + v) := by
        rw [affineSegment_eq]; exact ⟨t, ht, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hmem)
      exact Set.mem_iUnion.mpr ⟨n, ht, hn⟩
    calc (1 : ℝ≥0∞) = volume (Set.Icc (0 : ℝ) 1) := by
            rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
      _ ≤ volume (⋃ n, T n) := measure_mono hcover

/-! ### The combinatorial core, assembled: fine net ⟶ dominant scale ⟶ shifted subnet

Packaging the two pigeonholes with the shift average into the single statement the geometric wiring
consumes. Inputs: per-direction per-scale covered-length profiles `L k j` over a *fine* net of `2ᴶ`
directions, each fully covered (`1 ≤ ∑ⱼ L k j`), with the profiles **capped at scale `J`**
(`L k j = 0` for `j > J` — automatic when the scale function is `min(scale, J)`). Output: a dominant
scale `j ≤ J` and a shift `β < 2^{J-j}` whose `2⁻ʲ`-separated subnet of `2ʲ` directions
`{β + 2^{J-j}·i : i < 2ʲ}` carries aggregate covered length `≥ 2ʲ·scaleWeight j` — exactly the
localized-Córdoba numerator (`∑ᵢ 2δ·vol(Aᵢ) ≥ 2·scaleWeight j = 1/((j+1)(j+2))` at `δ = 2⁻ʲ`). -/

/-- **Dominant-scale extraction with shift (combinatorial core of the discharge).** From fine-net
covered-length profiles `L` (each direction covered: `1 ≤ ∑ⱼ L k j`; capped: `L k j = 0` for `j>J`),
the two pigeonholes + the shift average produce a dominant scale `j ≤ J` and a shift `β < 2^{J-j}`
with `2ʲ·scaleWeight j ≤ ∑ᵢ L (β + 2^{J-j}·i) j`. The geometric wiring supplies
`L k j = vol(⋃_{g n=j} Tₙᵏ)` (`one_le_tsum_volume_fiber_union` gives `1 ≤ ∑ⱼ L k j`); the output
subnet is `2⁻ʲ`-separated with retained covered length, ready for the base-angle Córdoba count. -/
theorem exists_dominant_shift {J : ℕ} (L : ℕ → ℕ → ℝ≥0∞)
    (hsupp : ∀ k j, J < j → L k j = 0)
    (hL : ∀ k ∈ range (2 ^ J), 1 ≤ ∑' j, L k j) :
    ∃ j, j ≤ J ∧ ∃ β ∈ range (2 ^ (J - j)),
      ((2 ^ j : ℕ) : ℝ≥0∞) * scaleWeight j
        ≤ ∑ i ∈ range (2 ^ j), L (β + 2 ^ (J - j) * i) j := by
  have h2J : 0 < 2 ^ J := pow_pos (by norm_num) J
  -- global dominant scale over the fine net `s = range (2ᴶ)`
  obtain ⟨j, hj⟩ := exists_global_dominant_scale (s := range (2 ^ J))
    ⟨0, Finset.mem_range.mpr h2J⟩ L hL
  rw [Finset.card_range] at hj
  have hswpos : scaleWeight j ≠ 0 := by
    rw [scaleWeight]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  -- the dominant scale is `≤ J` (the profile vanishes above `J`, so a positive total forces `j ≤ J`)
  have hjJ : j ≤ J := by
    by_contra hlt
    push_neg at hlt
    have hzero : ∑ k ∈ range (2 ^ J), L k j = 0 :=
      Finset.sum_eq_zero (fun k _ => hsupp k j hlt)
    rw [hzero] at hj
    rcases mul_eq_zero.mp (le_antisymm hj (zero_le _)) with h | h
    · exact absurd h (by exact_mod_cast h2J.ne')
    · exact hswpos h
  -- shift pigeonhole at the dominant scale
  obtain ⟨β, hβ, hshift⟩ :=
    exists_shift_ge (B := 2 ^ (J - j)) (pow_pos (by norm_num) _) (2 ^ j) (fun k => L k j)
  have hpow : 2 ^ (J - j) * 2 ^ j = 2 ^ J := by rw [← pow_add, Nat.sub_add_cancel hjJ]
  rw [hpow] at hshift
  refine ⟨j, hjJ, β, hβ, ?_⟩
  have hB0 : ((2 ^ (J - j) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos (by norm_num) (J - j)).ne'
  have hBtop : ((2 ^ (J - j) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcast : ((2 ^ J : ℕ) : ℝ≥0∞) = ((2 ^ (J - j) : ℕ) : ℝ≥0∞) * ((2 ^ j : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, hpow]
  refine (ENNReal.mul_le_mul_left hB0 hBtop).mp ?_
  calc ((2 ^ (J - j) : ℕ) : ℝ≥0∞) * (((2 ^ j : ℕ) : ℝ≥0∞) * scaleWeight j)
      = ((2 ^ J : ℕ) : ℝ≥0∞) * scaleWeight j := by rw [hcast]; ring
    _ ≤ ∑ k ∈ range (2 ^ J), L k j := hj
    _ ≤ ((2 ^ (J - j) : ℕ) : ℝ≥0∞) * ∑ i ∈ range (2 ^ j), L (β + 2 ^ (J - j) * i) j := hshift

/-! ### Dyadic scale of a length

The cover pieces are grouped by their dyadic scale `j` (diameter `∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]`). `dyadicIdx ρ`
is the index `j` of a real length `ρ`; the two bounds `dyadicIdx_le` / `lt_dyadicIdx` certify the
window for `0 < ρ ≤ 1`. The headline assembly takes `g n = min (dyadicIdx (ediam Uₙ).toReal) J`
(capped at the net resolution `J`); on the dominant-scale fiber `{g n = j}` with `j < J` these
bounds give the `ediam` window `cover_content_per_scale` needs. -/

/-- The dyadic scale index of a length `ρ`: the `j` with `ρ ∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]` when `0 < ρ ≤ 1`
(`⌊log₂(1/ρ)⌋`). -/
noncomputable def dyadicIdx (ρ : ℝ) : ℕ := ⌊Real.logb 2 ρ⁻¹⌋₊

/-- The two-sided dyadic window: for `0 < ρ ≤ 1` and `j = dyadicIdx ρ`, one has
`2⁻⁽ʲ⁺¹⁾ < ρ ≤ 2⁻ʲ`. (`⌊log₂(1/ρ)⌋ ≤ log₂(1/ρ) < ⌊⌋+1`, exponentiated base `2 > 1`.) -/
theorem dyadicIdx_window {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    (1 / 2 : ℝ) ^ (dyadicIdx ρ + 1) < ρ ∧ ρ ≤ (1 / 2 : ℝ) ^ dyadicIdx ρ := by
  have hinvpos : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr h0
  have hinv : (1 : ℝ) ≤ ρ⁻¹ := one_le_inv_iff₀.mpr ⟨h0, h1⟩
  set x : ℝ := Real.logb 2 ρ⁻¹ with hx
  have hx0 : 0 ≤ x := Real.logb_nonneg (by norm_num) hinv
  set j : ℕ := dyadicIdx ρ with hj
  have hjx : (j : ℝ) ≤ x := Nat.floor_le hx0
  have hxj : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
  have hpow : (2 : ℝ) ^ x = ρ⁻¹ := Real.rpow_logb (by norm_num) (by norm_num) hinvpos
  have hhalf : ∀ m : ℕ, (1 / 2 : ℝ) ^ m = ((2 : ℝ) ^ m)⁻¹ := fun m => by
    rw [one_div, inv_pow]
  constructor
  · -- `2⁻⁽ʲ⁺¹⁾ < ρ` from `ρ⁻¹ = 2^x < 2^(j+1)`
    have hlt : (2 : ℝ) ^ x < (2 : ℝ) ^ ((j : ℝ) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxj
    rw [hpow] at hlt
    have hcast : (2 : ℝ) ^ ((j : ℝ) + 1) = (2 : ℝ) ^ (j + 1) := by
      rw [← Real.rpow_natCast (2 : ℝ) (j + 1)]; push_cast; ring_nf
    rw [hcast] at hlt
    rw [hhalf]
    have h2j1 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
    rw [inv_lt_comm₀ h2j1 h0]
    exact hlt
  · -- `ρ ≤ 2⁻ʲ` from `2^j ≤ 2^x = ρ⁻¹`
    have hle : (2 : ℝ) ^ (j : ℝ) ≤ (2 : ℝ) ^ x :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hjx
    rw [hpow] at hle
    have hcast : (2 : ℝ) ^ (j : ℝ) = (2 : ℝ) ^ j := Real.rpow_natCast (2 : ℝ) j
    rw [hcast] at hle
    rw [hhalf]
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    rw [le_inv_comm₀ h0 h2j]
    exact hle

/-! ### Case A: dominant scale genuinely *at* the net resolution — the content contribution

`caseA_content` is the reusable "single dominant scale ⟹ Hausdorff content" step, generalized to a
**base angle `c`** (the shift output of `exists_dominant_shift`) and a **finite fiber `s`** of cover
pieces genuinely at scale `j` (diameter `∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]`). It folds the base-angle Córdoba count
`cover_content_per_scale` with the exponential-beats-polynomial constant `cR` (supplied by the caller
as `content_ratio_lower`) and the covered-length numerator `1/((j+1)(j+2))` (supplied by the shift
pigeonhole) into the content lower bound `D⁻¹·cR ≤ ∑_{n∈s} ediam(Uₙ)^d ≤ ∑'ₙ ediam(Uₙ)^d`.

This is exactly the downstream of the (now discarded) unshifted axiom, lifted to the shifted net so
the proven net-thinning bricks discharge it. The only thing it does *not* cover is the sub-resolution
case `j = J` (the cover dominated by pieces finer than the net) — see the headline assembly. -/

/-- **Case-A content contribution (base-angle, finite-fiber).** Given the shift output of
`exists_dominant_shift` — a dominant scale `j`, base angle `c`, covered sets `A k` over the
`2ʲ`-direction subnet, a finite set `s` of scale-`j` cover pieces with `φₖ(A k) ⊆ ⋃_{n∈s} Uₙ`, the
diameter window `2⁻⁽ʲ⁺¹⁾ ≤ ediam(Uₙ) ≤ 2⁻ʲ` on `s`, and the covered-length numerator
`1/((j+1)(j+2)) ≤ ∑ₖ 2·2⁻ʲ·vol(A k)` — the localized Córdoba count plus the uniform constant `cR`
yield `D⁻¹·cR ≤ ∑'ₙ ediam(Uₙ)^d` (with `D = vol(unit disc)`). The constant `cR` and its
exponential-beats-poly property `hcR` come from `content_ratio_lower`; supplying them as hypotheses
keeps the same `cR` shared with the headline's other branch. -/
theorem caseA_content {d : ℝ} (hd : 0 ≤ d)
    {cR : ℝ} (hcRpos : 0 < cR)
    (hcR : ∀ j : ℕ, cR * (4 * (1 / 4 : ℝ) ^ j) * (12 * Real.pi * (1 + (j : ℝ) * Real.log 2))
        ≤ (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d)
    (j : ℕ) (c : ℝ) (a : ℕ → Plane) (A : ℕ → Set ℝ)
    (hAmeas : ∀ k, MeasurableSet (A k)) (hA01 : ∀ k, A k ⊆ Set.Icc (0 : ℝ) 1)
    (U : ℕ → Set Plane) (s : Finset ℕ)
    (hediam_hi : ∀ n ∈ s, Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j))
    (hediam_lo : ∀ n ∈ s, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ≤ Metric.ediam (U n))
    (hscov : ∀ k, (fun u => a k + u • dir (c + (k : ℝ) * (1 / 2 : ℝ) ^ j)) '' (A k) ⊆ ⋃ n ∈ s, U n)
    (hnum : ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
        ≤ ∑ k ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A k)) :
    (volume (Metric.closedBall (0 : Plane) 1))⁻¹ * ENNReal.ofReal cR
      ≤ ∑' n, Metric.ediam (U n) ^ d := by
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  have hps := cover_content_per_scale (δ := (1 / 2 : ℝ) ^ j) (ρ := (1 / 2 : ℝ) ^ j) (N := 2 ^ j)
    (η := ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)))
    (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    (by rw [Nat.cast_pow, ← mul_pow]; norm_num) a A hAmeas hA01 c s U hediam_hi
    hscov hd hediam_lo
  rw [← hD] at hps
  set C0 : ℝ≥0∞ := ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2) * D
      * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
        * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))) with hC0def
  have hsq : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 from by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have hW1 : ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2 = 4 * (1 / 4 : ℝ) ^ j := by
    rw [show (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ j from by ring, mul_pow, hsq]
    norm_num
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hW2 : 6 * Real.pi * (1 / 2 : ℝ) ^ j
      * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))
      = 12 * Real.pi * (1 + (j : ℝ) * Real.log 2) := by
    rw [hcast, Real.log_pow,
      show 6 * Real.pi * (1 / 2 : ℝ) ^ j * (2 * (2 : ℝ) ^ j * (1 + (j : ℝ) * Real.log 2))
        = 12 * Real.pi * ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * (1 + (j : ℝ) * Real.log 2) from by ring,
      show (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 from by rw [← mul_pow]; norm_num]
    ring
  have hKEYreal : cR * (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2)
        * (6 * Real.pi * (1 / 2 : ℝ) ^ j
          * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))
      ≤ (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d := by
    rw [hW1, hW2]; exact hcR j
  have hW2pos : 0 < 6 * Real.pi * (1 / 2 : ℝ) ^ j
      * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))) := by
    rw [hW2]
    have hp : (0 : ℝ) < 1 + (j : ℝ) * Real.log 2 := by
      have h := mul_nonneg (Nat.cast_nonneg j) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      linarith
    exact mul_pos (by positivity) hp
  have hC0pos : C0 ≠ 0 := by
    rw [hC0def]
    exact mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hDpos.ne')
      (ENNReal.ofReal_pos.mpr hW2pos).ne'
  have hC0top : C0 ≠ ⊤ := by
    rw [hC0def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDtop) ENNReal.ofReal_ne_top
  have hLHS : (D⁻¹ * ENNReal.ofReal cR) * C0
      = ENNReal.ofReal (cR * ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2
        * (6 * Real.pi * (1 / 2 : ℝ) ^ j
          * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) := by
    rw [hC0def,
      show (D⁻¹ * ENNReal.ofReal cR) * (ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2) * D
          * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
            * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))))
        = (D⁻¹ * D) * (ENNReal.ofReal cR
            * ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2)
            * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
              * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) from by ring,
      ENNReal.inv_mul_cancel hDpos.ne' hDtop, one_mul,
      ← ENNReal.ofReal_mul hcRpos.le, ← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.mul_le_mul_iff_left hC0pos hC0top]
  calc (D⁻¹ * ENNReal.ofReal cR) * C0
      = ENNReal.ofReal (cR * ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2
          * (6 * Real.pi * (1 / 2 : ℝ) ^ j
            * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) := hLHS
    _ ≤ ENNReal.ofReal ((1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d) :=
        ENNReal.ofReal_le_ofReal hKEYreal
    _ = (ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) ^ 2
        * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1))) ^ d := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1))]
    _ ≤ (∑ k ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A k)) ^ 2
          * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1))) ^ d := by gcongr
    _ ≤ (∑ n ∈ s, Metric.ediam (U n) ^ d) * C0 := hps
    _ ≤ (∑' n, Metric.ediam (U n) ^ d) * C0 := mul_le_mul_right' (ENNReal.sum_le_tsum s) C0

end LeanFormalizations.Kakeya2D
