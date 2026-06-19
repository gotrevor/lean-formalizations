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

open Finset
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

end LeanFormalizations.Kakeya2D
