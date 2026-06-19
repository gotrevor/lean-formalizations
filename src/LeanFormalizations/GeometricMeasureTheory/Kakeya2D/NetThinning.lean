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

end LeanFormalizations.Kakeya2D
