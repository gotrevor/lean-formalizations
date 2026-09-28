/-
# Dubickas (2022), monic quadratics, without Lemma 8 (phase 8 probe)

`c_eq_zero_or_two` (`DubickasPisot.lean`) is the only place Dubickas's Theorem 2 for `d = 2`
consumes `Dubickas2022PisotGap` (his Lemma 8: Smyth / Mignotte / Baker).  It uses it once, in
`hL1`, to turn the decay `‖S_N‖ ≤ K β^(−N)` (`N = 2^j`, `j ≥ j₀`) into `deg β ≤ 2` via
`pisot_degree_bound`.  The goal here is the same conclusion `c ∈ {0, 2}` from `Dubickas2022`
alone, using the exact algebra that the quadratic recursion hands us.  Removing `hG` is one of the
two hypotheses standing between `oeis_constants` and an unconditional statement.

## Leads (Ren, 2026-09-27; unverified, may be wrong)

Notation as in `c_eq_zero_or_two`: `β = α^(2^m)` Pisot, conjugates `β = β₁, β₂, …, β_d`,
`S_N = Σ_{l≥2} β_lᴺ`, and for `N = 2^j`, `j ≥ j₀`, the exact identity
`c = 2 βᴺ S_N + S_N² − S_{2N}` (`hident` there).  Equivalently, with
`E_k(N) := e_k(β₁ᴺ, …, β_dᴺ) ∈ ℤ` (coefficients of the char. poly of `βᴺ`, integers since `β` is
an algebraic integer): `E_1(N) = T_N = y_{m+j}` and **`E_2(N) = c/2`** for all large `j`.

* `E_2(N) ∈ ℤ` gives `c ∈ 2ℤ` for free.
* `E_k(N) = e_k(others) + βᴺ e_{k−1}(others)`, where `e_k(others)` is `O(ρ^(kN))`, `ρ < 1`.
* Graeffe: the char. poly of `β^(2N)` is determined by that of `βᴺ`
  (`e_k(x²) = Σ_{i+i'=2k} (−1)^(i+k) e_i e_{i'}`), so `E_2(2N) = E_2(N)` together with
  `T_N → ∞` constrains `E_3, E_4, …`: e.g. `c/2 = c²/4 − 2 T_N E_3(N) + 2 E_4(N)`.
* Squaring `βᴺ S_N → c/2` gives `β^(2N) e_2(others) → c(c − 2)/8`, so `c ∉ {0, 2}` means the
  pair products `(β β_k β β_l)ᴺ` do NOT die out.  Look for the contradiction there, against
  `|N(β)| ≥ 1` (`pisot_one_le_prod_norm`) and the integrality of the `E_k`.
* Only `c ∈ {0, 2}` is needed, not `deg β ≤ 2`.

If the elementary route is blocked, a written obstruction (why every such argument needs a
Lemma-8-strength lower bound on `|S_N|`) is a valid outcome: record it in
`PROBE-DUBICKAS-NOGAP.md` and leave the `sorry`.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- **`c_eq_zero_or_two` without Lemma 8**: Dubickas's conditions (17)/(18) from `Dubickas2022`
alone, in the `d = 2`, `a₀ = 1` case. -/
theorem c_eq_zero_or_two_noGap (hD : Dubickas2022)
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    c = 0 ∨ c = 2 := by
  sorry

end LeanFormalizations.Transcendence.Dubickas
