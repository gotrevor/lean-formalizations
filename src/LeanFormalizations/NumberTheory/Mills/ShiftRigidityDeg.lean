/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftRigidity

/-!
# Phase 65: the `ξ`-free half of the `5/9` wall

`SaitoTypeBTheta.shiftPisotDegreeLeThree_holds` asks that Pisot degree `≥ 4` never occur for an
algebraic least E+ constant when `θ ∈ [5/9, 2/3)`.  Decay cannot give that
(`DecayDegreeFour.decay_admits_degree_four`).  The input that does more than decay in degree `3`
is arithmetic: `ShiftRigidity.not_primeTraces`, no cubic Pisot number has `tr β^(3^n + s)` prime
for all large `n`.  This file states its degree-`ℓ` form as the open node.

Difficulty check.
* Proved: `ℓ = 3` (`shiftTraceRigidityDeg_three`, from `ShiftRigidity.not_primeTraces`).
* Unproved: `ℓ ≥ 4`.  Of the cubic proof, the cube class (`not_primeTraces_of_cube`) and the
  spectral transfer (`exists_spectral_solution_shift`, already degree-general) should carry over;
  `rigidity_generic` (one 3-cycle in the Galois group, circulant Fourier modes) and the E1
  certificate (`f mod 3` irreducible with a root in `ℚ(μ_26)`) are cubic.  For degree `ℓ` the
  Teichmüller orders are `3^f − 1` for the factor degrees `f` of `f mod 3`, and the circulant
  becomes a permutation action of a Galois element on `ℓ` roots.
* Sibling sanity: the heuristic count of primes among `tr β^(3^n + s)` is `Σ 1/(3^n log β) < ∞`,
  so "all large traces prime" is expected false for every Pisot `β` of every degree; the node does
  not prove a believed-false sibling.  It does not use decay, so the control does not bite.
* Still missing for the wiring: in degree `≥ 4` the E+ route does not yet give
  `tr = ⌊ξ^(C k)⌋` at **all** large `k` (that used "all large indices are records",
  `eventually_record_shift_theta`, which needs `card otherConj ≤ 2`).  That is the second half of
  the node, not stated here yet.
-/

namespace LeanFormalizations.Mills.ShiftRigidityDeg

open Filter Polynomial LeanFormalizations.Mills.ShiftRigidity

/-- `PisotData` without the degree: a monic irreducible integer polynomial with a real root
`α > 1` whose other complex roots have modulus `< 1`. -/
structure PisotDataAny (f : ℤ[X]) (α : ℝ) : Prop where
  monic : f.Monic
  irr : Irreducible f
  root : aeval α f = 0
  gt_one : 1 < α
  small : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1

/-- **Open node (degree `ℓ` shift trace rigidity).**  No Pisot number of degree `ℓ` has
`tr β^(3^n + s)` prime for all large `n`, `s ≠ 0`. -/
def ShiftTraceRigidityDeg (ℓ : ℕ) : Prop :=
  ∀ (f : ℤ[X]) (α : ℝ), PisotDataAny f α → f.natDegree = ℓ → ∀ s : ℤ, s ≠ 0 → ¬ PrimeTraces f s

/-- The cubic case is `ShiftRigidity.not_primeTraces`. -/
theorem shiftTraceRigidityDeg_three : ShiftTraceRigidityDeg 3 := fun f α hD hdeg _ hs =>
  not_primeTraces ⟨hD.monic, hD.irr, hdeg, hD.root, hD.gt_one, hD.small⟩ hs

/-- **Believed (~75%)**: shift trace rigidity in every degree `ℓ ≥ 4`.  English route: the
cubic proof's cube class and spectral transfer, with `rigidity_generic` replaced by a Galois
element acting fixed-point-freely on the roots outside `ℚ(μ_Q)`; exceptional cases are the
finitely many factorization types of `f mod 3` with a root in a cyclotomic field `ℚ(μ_(3^f−1))`.
Evidence: the heuristic above, and `ℓ = 3`. -/
theorem shiftTraceRigidityDeg_holds {ℓ : ℕ} (hℓ : 4 ≤ ℓ) : ShiftTraceRigidityDeg ℓ := by
  sorry

end LeanFormalizations.Mills.ShiftRigidityDeg
