/-
# Dubickas (2022), monic quadratics, without Lemma 8

`c_eq_zero_or_two` (`DubickasPisot.lean`) is the only place Dubickas's Theorem 2 for `d = 2`
consumes `Dubickas2022PisotGap` (his Lemma 8: Smyth / Mignotte / Baker).  It uses it once, in
`hL1`, to turn the decay `‖S_N‖ ≤ K β^(−N)` (`N = 2^j`, `j ≥ j₀`) into `deg β ≤ 2` via
`pisot_degree_bound`.  This file reaches the same conclusion `c ∈ {0, 2}` from `Dubickas2022`
alone, for *every* degree, by the elementary route written up in `PROBE-DUBICKAS-NOGAP.md`.

## The route (all steps sorry-free)

With `β = α^(2^m)` Pisot, `S_N = Σ_{l ≥ 2} β_lᴺ`, `N = 2^j`, the recursion `y_{n+1} = y_n² − c`
gives the exact identity `c = 2 βᴺ S_N + S_N² − S_(2N)` (`exists_pisot_trace_ident`).  Writing
`Eₖ(N) = eₖ(β₁ᴺ, …, β_dᴺ)` and `eₖ(N) = eₖ(β₂ᴺ, …, β_dᴺ)`, that identity says exactly

    E₂(2^j) = c/2      for all `j ≥ j₀`

(`eFull_succ` at `k = 1`, plus `eSmall_one` and `two_mul_eSmall_two`).  So `E₂` is *eventually
constant* along the Graeffe tower, and `eFull_two_const_eq_zero_or_one` (`DubickasLimit.lean`)
turns that into `c/2 ∈ {0, 1}`.  No lower bound on `|S_N|` of Lemma-8 strength is used anywhere:
the arithmetic input is only that `k!·Eₖ(N) ∈ ℤ` (`isRatInt_factorial_mul_eFull`), that the small
conjugates are `< 1` in modulus, and that `eₙ ≡ 0` past `deg β − 1`.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasLimit

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- **`c_eq_zero_or_two` without Lemma 8**: Dubickas's conditions (17)/(18) from `Dubickas2022`
alone, in the `d = 2`, `a₀ = 1` case, with no restriction on `deg β`. -/
theorem c_eq_zero_or_two_noGap (hD : Dubickas2022)
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    c = 0 ∨ c = 2 := by
  classical
  obtain ⟨β, j₀, hβ, hident⟩ := exists_pisot_trace_ident hD hrec halg hα hC hyint hbnd
  have halgβ : IsIntegral ℚ β := hβ.2.1.tower_top
  -- the recursion says exactly that `E₂(2^j)` is the constant `c/2`
  have hE2 : ∀ j ≥ j₀, eFull β 2 (2 ^ j) = (c : ℂ) / 2 := by
    intro j hj
    have h := hident j hj
    rw [show (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j from by rw [pow_succ]; ring] at h
    have hsplit := eFull_succ halgβ 1 (2 ^ j)
    rw [eSmall_one] at hsplit
    have h2 := two_mul_eSmall_two β (2 ^ j)
    rw [hsplit]
    linear_combination h2 / 2 - h / 2
  rcases eFull_two_const_eq_zero_or_one hβ hE2 with h | h
  · left
    have hc : (c : ℂ) = 0 := by linear_combination 2 * h
    exact_mod_cast hc
  · right
    have hc : (c : ℂ) = 2 := by linear_combination 2 * h
    exact_mod_cast hc

end LeanFormalizations.Transcendence.Dubickas
