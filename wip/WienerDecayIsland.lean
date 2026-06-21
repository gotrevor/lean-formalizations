/-
# WIP / quarantined — BV-Fourier decay island (NOT built; not in `src/`)

Excised from `src/LeanFormalizations/NumberTheory/PrimeNumberTheorem/Wiener.lean` on 2026-06-19
(FINISH-AND-STOP wind-down). This was a **dead-code island** (referenced nowhere; gated no headline)
carrying two `sorry`s that are **still open upstream** in `PrimeNumberTheoremAnd` (v4.30.0) — closing
them needs a Lebesgue–Stieltjes integration-by-parts for BV functions that mathlib lacks (see
`archive/findings/ON-LINE-FINDINGS-2026-06-19-prelim-decay-infra.md`).

This file is a verbatim snapshot for preservation; it is **not** part of the build (it lives outside
`src/`, so `lake build` ignores it and the treadmill self-stop gate does not scan it) and will not
compile standalone (its imports/context live in `Wiener.lean`). To restore: paste these declarations
back into `Wiener.lean` after the proven `prelim_decay`. The retained `prelim_decay`
(`‖𝓕 ψ u‖ ≤ ∫‖ψ‖`) and `one_add_sq_pos` stay in `src/`.
-/

theorem prelim_decay_2 (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hvar : BoundedVariationOn ψ Set.univ)
    (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn ψ Set.univ).toReal / (2 * π * ‖u‖) := by sorry

noncomputable def AbsolutelyContinuous (f : ℝ → ℂ) : Prop := (∀ᵐ x, DifferentiableAt ℝ f x) ∧
  ∀ a b : ℝ, f b - f a = ∫ t in a..b, deriv f t

theorem prelim_decay_3 (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (habscont : AbsolutelyContinuous ψ)
    (hvar : BoundedVariationOn (deriv ψ) Set.univ) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 := by sorry

theorem decay_alt (ψ : ℝ → ℂ) (hψ : Integrable ψ) (habscont : AbsolutelyContinuous ψ)
    (hvar : BoundedVariationOn (deriv ψ) Set.univ) (u : ℝ) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤
      ((∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2) /
        (1 + ‖u‖ ^ 2) := by
  rw [le_div_iff₀' <| one_add_sq_pos ‖u‖]
  by_cases hu : u = 0
  · subst hu
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      one_mul]
    calc ‖𝓕 ψ 0‖ ≤ ∫ t, ‖ψ t‖ := prelim_decay ψ 0
      _ ≤ (∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by
          have : 0 ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by positivity
          linarith
  · have bound1 : ‖𝓕 ψ u‖ ≤ ∫ t, ‖ψ t‖ := prelim_decay ψ u
    have bound2 : ‖𝓕 ψ u‖ ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 :=
      prelim_decay_3 ψ hψ habscont hvar u hu
    have : (2 * π * ‖u‖) ^ 2 = (2 * π) ^ 2 * ‖u‖ ^ 2 := by ring
    calc (1 + ‖u‖ ^ 2) * ‖𝓕 ψ u‖
        = ‖𝓕 ψ u‖ * 1 + ‖𝓕 ψ u‖ * ‖u‖ ^ 2 := by ring
      _ ≤ (∫ t, ‖ψ t‖) * 1 +
            (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 * ‖u‖ ^ 2 := by
          gcongr
      _ = (∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by
          rw [mul_one, this, div_mul_eq_div_div]
          congr 1
          rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 <| norm_ne_zero_iff.mpr hu)]
