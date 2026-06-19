/-
# The Prime Number Theorem — standard textbook form

A headline corollary of the discharged PNT (`Consequences.pi_alt'`, π(x) ∼ x/log x), stated in the
most recognizable form: the ratio `π(x) / (x / log x) → 1` as `x → ∞`. Axiom-clean
(`#print axioms`), the natural capstone of the in-repo Wiener–Ikehara discharge of `weakPNT`.
-/
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Consequences

open Nat Filter Real Asymptotics
open scoped Topology

/-- **The Prime Number Theorem.** `π(x) / (x / log x) → 1` as `x → ∞`, where `π(x)` counts the
primes `≤ x`. Equivalent to `π(x) ∼ x / log x` (`pi_alt'`); machine-checked, axiom-clean. -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ ↦ (primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  have hz : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    positivity
  exact (isEquivalent_iff_tendsto_one hz).mp pi_alt'
