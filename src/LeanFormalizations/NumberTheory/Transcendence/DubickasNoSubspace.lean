/-
# Dubickas (2022), monic quadratics, without Lemma 6 (phase 9 probe)

After phase 8, Theorem 1 (`Dubickas.lean`) rests on `Dubickas2022` alone: Dubickas's Lemma 6,
from Corvaja–Zannier's `p`-adic subspace theorem.  It is consumed exactly once, in
`exists_pisot_pow` (`DubickasPisot.lean`), with `q = 2` and `s_k = 2^k`, to get some `α^(2^m)`
Pisot.  Here we need only a narrow special case, and we have more structure than Lemma 6 assumes:

* the approximation is **reciprocal-rate**: `|2α^(2ⁿ) − k_n| ≤ 2C α^(−2ⁿ)` with `k_n = 2y_n ∈ ℤ`;
* the integers come from an **exact recursion** `y_{n+1} = y_n² − c`, so
  `δ_{n+1} = δ_n (4α^(2ⁿ) − δ_n)/2 + 2c` for `δ_n := 2α^(2ⁿ) − k_n`.  That is an identity in
  `ℚ(α)`, so it holds for every embedding `σ` too.

Target: `exists_pisot_pow_noD`, the same conclusion as `exists_pisot_pow` without `hD`.  Any
route that gets `c ∈ {0, 2}` directly without `hD` is equally good: prove `c_eq_zero_or_two_uncond`
instead and leave the Pisot lemma as a `sorry`d side leaf.

## Status (2026-09-28)

* **Closed, unconditionally (from `Ridout1957`):** every `α` with a rational `2^a`-th power —
  `exists_pisot_pow_of_rat`, `exists_pisot_pow_of_pow_rat`, on top of the new multiplier form of
  Mahler's inequality `Diophantine.mahler_mul_of_ridout1957`.
* **Open:** `exists_pisot_pow_pseudoPisot_core`, which is exactly Corvaja–Zannier's pseudo-Pisot
  dichotomy (their main theorem, p. 177 = Dubickas's Lemma 3).  Both leads that were recorded
  here have been *refuted*: the archimedean Liouville/norm bound is vacuous (it only re-derives
  `M(α) ≥ α`), and the Böttcher coordinate is not of Mahler-method shape.  Full write-up, with
  the proposed literature `Prop`, in `PROBE-DUBICKAS-NOSUBSPACE.md`.
* `hD` therefore still sits on the `Dubickas.lean` headlines; it must not be routed through the
  `sorry`.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot
import LeanFormalizations.NumberTheory.Diophantine.Edges

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- A rational integer `> 1` is a Pisot number: its minimal polynomial is linear, so there are
no other conjugates to bound. -/
theorem isPisot_of_rat_den_one {r : ℚ} (h1 : 1 < r) (hden : r.den = 1) : IsPisot (r : ℝ) := by
  refine ⟨by exact_mod_cast h1, ?_, ?_⟩
  · have hr : ((r : ℝ)) = algebraMap ℤ ℝ r.num := by
      rw [Rat.cast_def, hden]
      simp
    rw [hr]
    exact isIntegral_algebraMap
  · intro z hz
    have hmin : minpoly ℚ ((r : ℝ)) = Polynomial.X - Polynomial.C r := by
      have := minpoly.eq_X_sub_C ℝ r
      rwa [show algebraMap ℚ ℝ r = ((r : ℝ)) from rfl] at this
    rw [hmin, Polynomial.aroots_X_sub_C] at hz
    have hcast : (algebraMap ℚ ℂ r) = ((r : ℝ) : ℂ) := by
      simp [Complex.coe_algebraMap]
    rw [hcast, Multiset.erase_singleton] at hz
    simp at hz

/-- The elementary half of Dubickas's Lemma 9 step 1: the hypotheses say exactly that
`2 α^(2ⁿ)` approaches integers faster than `e^(−ε 2ⁿ)` for `ε = (log α)/2`. -/
theorem round_dist_le_of_bnd {α : ℝ} (hα : 1 < α) {C : ℝ} (hC : 0 < C) {y : ℕ → ℝ} {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, |2 * α ^ 2 ^ k - (round (2 * α ^ 2 ^ k) : ℝ)| ≤
      Real.exp (-(Real.log α / 2 * 2 ^ k)) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hlogα : 0 < Real.log α := Real.log_pos hα
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_two_pow_atTop (show (1:ℝ) < Real.exp (Real.log α / 2) from by
      rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.2 (by positivity))).eventually_ge_atTop (2 * C))
  refine ⟨max n₀ k₁, fun k hk ↦ ?_⟩
  have hkn₀ : n₀ ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_max_right _ _) hk
  have hlarge : 2 * C ≤ Real.exp (Real.log α / 2) ^ 2 ^ k := hk₁ k hkk₁
  have hp0 : (0 : ℝ) < α ^ 2 ^ k := by positivity
  obtain ⟨j, hj⟩ := hyint k
  have hnear : |2 * α ^ 2 ^ k - (j : ℝ)| ≤ 2 * C / α ^ 2 ^ k := by
    have h := hbnd k hkn₀
    rw [show 2 * α ^ 2 ^ k - (j : ℝ) = -(2 * (y k - α ^ 2 ^ k)) from by rw [← hj]; ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show 2 * C / α ^ 2 ^ k = 2 * (C / α ^ 2 ^ k) from by ring]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hround : |2 * α ^ 2 ^ k - (round (2 * α ^ 2 ^ k) : ℝ)| ≤ 2 * C / α ^ 2 ^ k :=
    le_trans (round_le _ j) hnear
  refine le_trans hround ?_
  have he : Real.exp (-(Real.log α / 2 * 2 ^ k)) = (Real.exp (Real.log α / 2) ^ 2 ^ k)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hE0 : (0 : ℝ) < Real.exp (Real.log α / 2) ^ 2 ^ k := by positivity
  rw [he, div_le_iff₀ hp0, inv_mul_eq_div, le_div_iff₀ hE0]
  have h1 : Real.exp (Real.log α / 2) ^ 2 = α := by
    rw [← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (Real.log α / 2) = Real.log α from by push_cast; ring,
      Real.exp_log hα0]
  have hαE : α ^ 2 ^ k = (Real.exp (Real.log α / 2) ^ 2 ^ k) ^ 2 := by
    calc α ^ 2 ^ k = (Real.exp (Real.log α / 2) ^ 2) ^ 2 ^ k := by rw [h1]
      _ = (Real.exp (Real.log α / 2) ^ 2 ^ k) ^ 2 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hαE]
  nlinarith [hlarge, hE0, hC]

/-- **The rational case of `exists_pisot_pow`, without Lemma 6** — from `Ridout1957` alone.

This is the degree-1 case of Dubickas's Lemma 6 at `q = 2`, `s_n = 2ⁿ`, and it is exactly the
route Dubickas sketches in his §2 for Wagner–Ziegler's Theorem 1: Mahler's inequality
`‖q(u/v)ⁿ‖ > e^(−εn)` rules out a rational non-integral growth constant, and a rational integer
`> 1` is itself a Pisot number.  The multiplier form of Mahler's theorem is
`Diophantine.mahler_mul_of_ridout1957` (Mahler 1957 II, §3 from Ridout 1957). -/
theorem exists_pisot_pow_of_rat (hR : Ridout1957) {α : ℝ} (hα : 1 < α) {C : ℝ} (hC : 0 < C)
    {y : ℕ → ℝ} {n₀ : ℕ} (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) {r : ℚ} (hr : α = (r : ℝ)) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  have hr1 : 1 < r := by rw [hr] at hα; exact_mod_cast hα
  rcases eq_or_ne r.den 1 with hden | hden
  · exact ⟨0, by simpa [hr] using isPisot_of_rat_den_one hr1 hden⟩
  -- the non-integral case is impossible
  exfalso
  have hlogα : 0 < Real.log α := Real.log_pos hα
  obtain ⟨k₀, hk₀⟩ := round_dist_le_of_bnd hα hC hyint hbnd
  obtain ⟨n₁, hn₁⟩ := Diophantine.mahler_mul_of_ridout1957 hR 2 (by norm_num) r hr1 hden
    (Real.log α / 2) (by positivity)
  -- pick `k` with `2^k ≥ n₁` and `k ≥ k₀`
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k₀ ≤ k ∧ n₁ ≤ 2 ^ k :=
    ⟨max k₀ n₁, le_max_left _ _,
      le_trans (le_max_right k₀ n₁) (Nat.lt_two_pow_self).le⟩
  have h1 := hk₀ k hk1
  have h2 := hn₁ (2 ^ k) hk2
  rw [← hr] at h2
  push_cast at h2
  linarith

/-- **All `α` with a rational `2^a`-th power**, without Lemma 6.  If some `α^(2^a)` is rational
then the hypotheses force it to be a rational *integer*, and then `α^(2^a)` is already Pisot.
Shifting the sequence `y` by `a` reduces this to `exists_pisot_pow_of_rat`. -/
theorem exists_pisot_pow_of_pow_rat (hR : Ridout1957) {α : ℝ} (hα : 1 < α) {C : ℝ} (hC : 0 < C)
    {y : ℕ → ℝ} {n₀ : ℕ} (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) {a : ℕ} {r : ℚ}
    (hr : α ^ 2 ^ a = (r : ℝ)) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hpow : ∀ j : ℕ, α ^ 2 ^ (a + j) = (r : ℝ) ^ 2 ^ j := by
    intro j
    rw [pow_add, pow_mul, hr]
  have hr1 : (1:ℝ) < (r : ℝ) := by
    rw [← hr]; exact one_lt_pow₀ hα (by positivity)
  obtain ⟨m, hm⟩ := exists_pisot_pow_of_rat hR hr1 hC
    (y := fun j ↦ y (a + j)) (n₀ := n₀) (fun j ↦ hyint (a + j))
    (fun j hj ↦ by
      have := hbnd (a + j) (by omega)
      rwa [hpow j] at this) (r := r) rfl
  exact ⟨a + m, by rwa [hpow m]⟩

/-- **The residual core of Dubickas's Lemma 6 for `q = 2`, `s_n = 2ⁿ`** — the only step of
Theorem 1 that this repo has not reduced to an elementary argument or to `Ridout1957`.

`exists_pisot_pow_of_pow_rat` settles every `α` with a rational `2^a`-th power (Mahler's
inequality, hence Ridout).  What is left is exactly Corvaja–Zannier's dichotomy: either `2 α^(2ⁿ)`
is a *pseudo-Pisot* number for infinitely many `n` — Dubickas's Lemma 5 then makes `α^(2^m)` Pisot,
and that argument is elementary once Corvaja–Zannier's Lemma 4 (trace ⇒ `α` is an algebraic
integer or a root of a rational) is available — or it is pseudo-Pisot only finitely often, and
then the `p`-adic Subspace Theorem gives `‖2 α^(2ⁿ)‖ > (1 − ε)^(2ⁿ)`, contradicting `hbnd`.

The archimedean Liouville/Roth bound cannot replace it: `N(2α^N − k_N) ∈ ℤ ∖ {0}` gives a *lower*
bound `∏_{σ ≠ 1} |k_N − 2σ(α)^N| ≥ c α^N`, which is exactly the direction implied by
`M(α) ≥ α` and is therefore vacuous.  Making it bite needs all places at once.
See `PROBE-DUBICKAS-NOSUBSPACE.md` for the obstruction and the literature `Prop` that closes it. -/
theorem exists_pisot_pow_pseudoPisot_core {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α)
    {C : ℝ} (hC : 0 < C) {y : ℕ → ℝ} {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n)
    (hnr : ∀ (a : ℕ) (r : ℚ), α ^ 2 ^ a ≠ (r : ℝ)) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  sorry

/-- **`exists_pisot_pow` without Lemma 6**, for the growth constant of an exact quadratic
recursion: some `α^(2^m)` is a Pisot number. -/
theorem exists_pisot_pow_noD (hR : Ridout1957)
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  by_cases hrat : ∃ (a : ℕ) (r : ℚ), α ^ 2 ^ a = (r : ℝ)
  · obtain ⟨a, r, hr⟩ := hrat
    exact exists_pisot_pow_of_pow_rat hR hα hC hyint hbnd hr
  · push_neg at hrat
    exact exists_pisot_pow_pseudoPisot_core halg hα hC hyint hbnd hrat

end LeanFormalizations.Transcendence.Dubickas
