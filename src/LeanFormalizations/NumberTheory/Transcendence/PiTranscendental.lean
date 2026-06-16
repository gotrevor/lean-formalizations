/-
# Transcendence of `π` — unconditional, fully machine-checked

The capstone: `Transcendental ℚ Real.pi`, axiom-clean. Combines
`MonicRootSums.transcendental_pi_of_subsetSumEsymm` (the full Lindemann conjugate-machinery
assembly at `α = iπ`) with `SubsetSumEsymm.subsetSum_esymm_rational` (the fundamental
theorem of symmetric polynomials applied to the subset-sums) — its sole remaining input.

Every step from "`π` algebraic ⟹ `False`" is machine-checked here; `#print axioms` is the
bare trust base `[propext, Classical.choice, Quot.sound]` — **no math axiom**. This discharges
the `α = iπ` instance of `HermiteLindemann.hermite_lindemann`, so squaring-the-circle is now
provably impossible with no transcendence hypothesis and no cited axiom (see
`transcendental_pi` here vs. the conditional `Constructible.squaring_the_circle_impossible`).
-/
import LeanFormalizations.NumberTheory.Transcendence.MonicRootSums
import LeanFormalizations.NumberTheory.Transcendence.SubsetSumEsymm

namespace LeanFormalizations.Transcendence

/-- **Transcendence of `π`** over `ℚ` (Lindemann, 1882) — fully machine-checked, axiom-clean.
Assembled from the conjugate machinery (`transcendental_pi_of_subsetSumEsymm`) and the
fundamental theorem of symmetric polynomials (`subsetSum_esymm_rational`). `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. -/
theorem transcendental_pi_axiomClean : Transcendental ℚ Real.pi :=
  transcendental_pi_of_subsetSumEsymm
    (fun n θ G hG hr j => subsetSum_esymm_rational n θ G hG hr j)

end LeanFormalizations.Transcendence
