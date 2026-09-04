/-
# N5 — the arithmetic place: `d_n = lcm(1,…,n) ≤ exp(1.01 n)` eventually

Mathlib already supplies `Chebyshev.psi_eq_log_lcmUpto : ψ n = log (lcmUpto n)`, and the in-repo
`PrimeNumberTheoremAnd` dependency supplies `WeakPNT'' : ψ ~[atTop] id`.  Together:
`log d_n / n → 1`, hence `d_n ≤ e^{1.01 n}` eventually.  No prime-by-prime accounting, no `Φ_n`
saving — the elementary route pays full price for the denominators and still closes, because the
real place gives `-21.657` against `21`.

`1.01` is arbitrary in `(1, 21.3/21) = (1, 1.0142…)`; see `Bound.lean` for the ledger arithmetic.
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences
import LeanFormalizations.NumberTheory.DirichletBeta.LinearForm

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology Asymptotics

/-- `log (lcmUpto n) / n → 1`: the prime number theorem in the form `ψ ~ id`, read through
`Chebyshev.psi_eq_log_lcmUpto`. -/
theorem tendsto_log_dn_div :
    Tendsto (fun n : ℕ => Real.log (dn n : ℝ) / n) atTop (𝓝 1) := by
  have h := WeakPNT''
  rw [isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx using hx)] at h
  have h2 := h.comp tendsto_natCast_atTop_atTop
  refine h2.congr' ?_
  filter_upwards with n
  simp only [Function.comp, Pi.div_apply, dn]
  rw [Chebyshev.psi_eq_log_lcmUpto]

/-- **N5 (denominator growth).**  `lcm(1,…,n) ≤ e^{1.01 n}` for all large `n`. -/
theorem dn_le_exp : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (dn n : ℝ) ≤ Real.exp (1.01 * n) := by
  have h := tendsto_log_dn_div
  have hev := h.eventually (eventually_le_nhds (show (1 : ℝ) < 1.01 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℕ) ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hd : (0 : ℝ) < (dn n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  have := hN n (le_trans (le_max_left _ _) hn)
  rw [div_le_iff₀ hnpos] at this
  calc (dn n : ℝ) = Real.exp (Real.log (dn n : ℝ)) := (Real.exp_log hd).symm
    _ ≤ Real.exp (1.01 * n) := Real.exp_le_exp.2 this

end LeanFormalizations.DirichletBeta
