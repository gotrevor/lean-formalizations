/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoDegreeTwo
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsAll
import LeanFormalizations.Literature.Primes

/-!
# Phase 62: the pieces of Saito's Type B argument (Saito 2025, §5–§6, §8)

Paper: Saito, arXiv:2508.16068 (`papers/saito-2025-transcendency-variants-mills.txt` in the main
checkout).  We work with `θ = 21/40` (Baker–Harman–Pintz) and an exponent sequence `C` whose
ratios `c_k = C(k+1)/C k` are eventually `≥ 29/10` (this covers Theorem E+, where `c_k → 3`).

## Why a ratio hypothesis and `Dubickas2022PisotGap` appear (2026-10-05)
* Saito's Lemma 5.2 builds a competitor `ζ < ξ` by a prime chain continued with Lemma 4.2, which
  is Matomäki's theorem; it is needed only for steps whose ratio `c` is below `40/19`, where the
  BHP window `[q^c, q^c + q^(21c/40)]` no longer fits under `(q+1)^c − 1`.  With `c_k ≥ 29/10`
  eventually, every chain step is one BHP prime (`bhp_step`), so Matomäki drops out.
* Saito's Lemma 6.1 bounds the Pisot degree by Lemma 5.14 = Dubickas 2022 Lemma 8
  (`Dubickas2022PisotGap`), whose complex-pair case is Baker's theorem (Saito Lemma 5.13).  The
  decay `‖β^n‖ ≤ K β^(−tn)` along a lacunary `n` gives no degree bound by itself when the
  dominant conjugates are a complex pair: exponential cancellation of `2|β₂|^n cos(nφ)` is not
  excluded without a lower bound for `‖nφ − 1/4‖`.  So the degree bound takes `hG`.

## Route (each item a declaration below)
1. `not_intCast_pow` — Saito (3.1): no `ξ^(C m)` is an integer (from `(B5′)`).
2. `exists_of_nested` — nested intervals: a chain of roots gives a `ζ` with prescribed floors.
3. `bhp_step` — one BHP prime in `[q^c, q^c + q^(21c/40)]`, and it stays below `(q+1)^c − 1`.
4. `window_of_least` — Saito Lemma 5.2 (case (I) false ⇒ (II)), via minimality of `ξ`.
5. `fract_lt_of_floor_lt` — Saito (5.1) (the half of Lemma 5.1 we need).
6. `fract_le_of_window` — Saito (5.17) (Lemma 5.3).
7. `isPisot_pow_gcd` — Saito Lemma 5.9 (Bugeaud–Dubickas).
8. `exists_pisot_of_decay_subseq` — Saito Lemma 6.1 (with `hG`).
9. `powTrace_eq_floor` — Saito Lemma 5.8.
10. `not_natDegree_two` — Saito Prop 3.1(iii) + §8, by a divisibility argument in place of the
    golden-ratio computation: for degree 2 the traces `v_n = β^n + w^n` satisfy `v_m ∣ v_(me)`
    for odd `e`, and both are primes.
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature LeanFormalizations.Mills Filter

/-- The Mills set for an exponent sequence `C`. -/
def millsSet (C : ℕ → ℕ) : Set ℝ := {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime}

/-- The `C k`-th root, `x ^ (1 / C k)`. -/
noncomputable def root (x : ℝ) (n : ℕ) : ℝ := x ^ ((n : ℝ)⁻¹)

/-- **Saito (3.1)**: under `(B5′)`, no power `ξ^(C m)`, `m ≥ 1`, of a Mills number is an
integer: `ξ^(C k) = (ξ^(C m))^(C k / C m)` with `C k / C m ≥ 2` would be a perfect power, not a
prime. -/
theorem not_intCast_pow {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    (h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ) := by
  sorry

/-- **Nested intervals.**  If the roots `q_k^(1/C k)` increase weakly and the roots
`(q_k + 1)^(1/C k)` decrease strictly from `k₀` on, some `ζ > 0` has `⌊ζ^(C k)⌋₊ = q k` for all
`k ≥ k₀`. -/
theorem exists_of_nested {C : ℕ → ℕ} {q : ℕ → ℕ} {k₀ : ℕ} (hC : ∀ k ≥ k₀, 0 < C k)
    (hq : 1 ≤ q k₀)
    (hlo : ∀ k ≥ k₀, root (q k) (C k) ≤ root (q (k + 1)) (C (k + 1)))
    (hhi : ∀ k ≥ k₀, root (q (k + 1) + 1) (C (k + 1)) < root (q k + 1) (C k)) :
    ∃ ζ : ℝ, 0 < ζ ∧ (∀ k ≥ k₀, ⌊ζ ^ C k⌋₊ = q k) ∧
      ∀ k ≥ k₀, ζ < root (q k + 1) (C k) := by
  sorry

/-- **One BHP step.**  For all large `q` and every real `c ≥ 29/10` there is a prime `q'` with
`q^c ≤ q' ≤ q^c + q^(21c/40)` and `q' + 1 < (q + 1)^c`. -/
theorem bhp_step (hB : BakerHarmanPintz2001) :
    ∃ X : ℕ, ∀ q ≥ X, ∀ c : ℝ, 29 / 10 ≤ c → ∃ q' : ℕ, q'.Prime ∧
      (q : ℝ) ^ c ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ c + (q : ℝ) ^ (21 / 40 * c) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ c := by
  sorry

/-- The ratio `c_k = C(k+1)/C k`. -/
noncomputable def ratio (C : ℕ → ℕ) (k : ℕ) : ℝ := (C (k + 1) : ℝ) / C k

/-- **Saito Lemma 5.2** (ratios eventually `≥ 29/10`, so BHP alone continues the chain).  If the
floors `p_k = ⌊ξ^(C k)⌋₊` of the least Mills number satisfy the lower chain condition
`p_k^(1/C k) ≤ p_(k+1)^(1/C(k+1))` from some `k₁` on, then eventually
`p_(k+1) ≤ p_k^(c_k) + p_k^(21 c_k/40)`. -/
theorem window_of_least (hB : BakerHarmanPintz2001) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    {k₁ : ℕ} (hlow : ∀ k ≥ k₁, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1))) :
    ∃ k₀, ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (21 / 40 * ratio C k) := by
  sorry

/-- **Saito (5.1)**: if `⌊x^c⌋ < ⌊x⌋^c` (`x ≥ 1`, `c ≥ 1`) then `c·{x}·⌊x⌋^(c−1) < 1`. -/
theorem fract_lt_of_floor_lt {x c : ℝ} (hx : 1 ≤ x) (hc : 1 ≤ c)
    (h : (⌊x ^ c⌋₊ : ℝ) < (⌊x⌋₊ : ℝ) ^ c) :
    c * Int.fract x * (⌊x⌋₊ : ℝ) ^ (c - 1) < 1 := by
  sorry

/-- **Saito (5.17)**: if `x^c < P + 1` with `P ≤ p^c + p^(θc)`, `p = ⌊x⌋ ≥ 1`, `c ≥ 1`,
`0 ≤ θ < 1`, then `{x} ≤ 2 / (c p^((1−θ)c − 1))`. -/
theorem fract_le_of_window {x c θ : ℝ} {P : ℕ} (hx : 1 ≤ x) (hc : 1 ≤ c) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hxc : x ^ c < (P : ℝ) + 1)
    (hP : (P : ℝ) ≤ (⌊x⌋₊ : ℝ) ^ c + (⌊x⌋₊ : ℝ) ^ (θ * c)) :
    Int.fract x ≤ 2 / (c * (⌊x⌋₊ : ℝ) ^ ((1 - θ) * c - 1)) := by
  sorry

/-- **Saito Lemma 5.9** (Bugeaud–Dubickas 2008, Lemma 8): if `α^a` and `α^b` are Pisot then so is
`α^(gcd a b)`. -/
theorem isPisot_pow_gcd {α : ℝ} (hα : 1 < α) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpa : IsPisot (α ^ a)) (hpb : IsPisot (α ^ b)) : IsPisot (α ^ Nat.gcd a b) := by
  sorry

/-- **Saito Lemma 6.1** (with `Dubickas2022PisotGap` for the degree bound).  If an algebraic
`α > 1` satisfies `|α^(s k) − round| ≤ K α^(−μ s k)` for all large `k`, along a strictly
increasing `s` with `s 0 > 0`, and no power `α^(s k)` is an integer, then some `α^g` is Pisot,
`g ∣ s k` eventually, `α^g` has degree `≥ 2`, and `(deg − 1) μ ≤ 1`. -/
theorem exists_pisot_of_decay_subseq (hD : Dubickas2022) (hG : Dubickas2022PisotGap)
    {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {s : ℕ → ℕ} (hs : StrictMono s)
    (hs0 : 0 < s 0) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ k in atTop, |α ^ s k - (round (α ^ s k) : ℝ)| ≤ K * α ^ (-(μ * s k)))
    (hnot : ∀ k, ∀ t : ℤ, α ^ s k ≠ (t : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ IsPisot (α ^ g) ∧ (∀ᶠ k in atTop, g ∣ s k) ∧
      2 ≤ (minpoly ℚ (α ^ g)).natDegree ∧
      ((Multiset.card (otherConj (α ^ g)) : ℝ)) * μ ≤ 1 := by
  sorry

/-- **Saito Lemma 5.8**: for a Pisot `β` and all large `N`, `Int.fract (β^N) < 1/2` forces
`Tr(β^N) = ⌊β^N⌋`. -/
theorem powTrace_eq_floor {β : ℝ} (hβ : IsPisot β) :
    ∀ᶠ N in atTop, Int.fract (β ^ N) < 1 / 2 → powTrace β N = ((⌊β ^ N⌋₊ : ℕ) : ℂ) := by
  sorry

/-- **No degree 2** (Saito Prop 3.1(iii) + §8, by divisibility).  A degree-2 Pisot `β` cannot have
`⌊β^(n k)⌋₊` prime with `Int.fract (β^(n k)) < 1/2` for all large `k`, along exponents `n` with
`n a ∣ n b`, `n a < n b` for infinitely many pairs `a < b`.  Here we state the form used: for
every `M` there are `M ≤ a < b` with `n a ∣ n b` and `n a < n b`. -/
theorem not_natDegree_two {β : ℝ} (hβ : IsPisot β) (hdeg : (minpoly ℚ β).natDegree = 2)
    {n : ℕ → ℕ} {K : ℕ}
    (hprime : ∀ k ≥ K, (⌊β ^ n k⌋₊).Prime)
    (hfrac : ∀ k ≥ K, Int.fract (β ^ n k) < 1 / 2)
    (hdiv : ∀ M, ∃ a ≥ M, ∃ b > a, n a ∣ n b ∧ n a < n b)
    (hlarge : Tendsto n atTop atTop) : False := by
  sorry

/-! ### Assembly lemmas -/

theorem C_ge_one {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, 1 ≤ C k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · have := h2 n hn; have := ih hn; omega

theorem C_lt_succ {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, C k < C (k + 1) := by
  intro k hk
  have := h2 k hk; have := C_ge_one h1 h2 k hk; omega

theorem C_strictMonoOn {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : C a < C b := by
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact lt_trans (ih h) (C_lt_succ h1 h2 n (by omega))
    · subst h; exact C_lt_succ h1 h2 a ha

theorem le_C {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) :
    ∀ k ≥ 1, k ≤ C k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · have := C_lt_succ h1 h2 n hn; have := ih hn; omega

/-- `(ξ^(C k))^(c_k) = ξ^(C(k+1))`. -/
theorem pow_ratio {C : ℕ → ℕ} {ξ : ℝ} (hξ : 0 < ξ) {k : ℕ} (hk : 0 < C k) :
    (ξ ^ C k) ^ ratio C k = ξ ^ C (k + 1) := by
  rw [← Real.rpow_natCast ξ (C k), ← Real.rpow_mul hξ.le, ratio,
    mul_div_cancel₀ _ (by exact_mod_cast hk.ne'), Real.rpow_natCast]

/-- **Case (I) of Saito Lemma 5.2 is impossible for algebraic `ξ`** (Saito Lemma 6.2, ratios
`≥ 29/10`): the lower chain condition holds eventually. -/
theorem eventually_low (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {C : ℕ → ℕ}
    (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    (halg : IsAlgebraic ℚ ξ) :
    ∃ k₁, ∀ k ≥ k₁, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1)) := by
  sorry

/-- **Saito Lemma 5.3 at `θ = 21/40`, ratios `≥ 29/10`**: in case (II),
`{ξ^(C k)} ≤ 2 ⌊ξ^(C k)⌋^(−151/400)` eventually. -/
theorem eventually_fract_le {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {K₀ : ℕ} (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) {k₀ : ℕ}
    (hII : ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (21 / 40 * ratio C k)) :
    ∃ k₂, ∀ k ≥ k₂, Int.fract (ξ ^ C k) ≤ 2 * (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) := by
  sorry

/-- The floors of a Mills number tend to infinity. -/
theorem floor_tendsto {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : 1 < ξ) : Tendsto (fun k => (⌊ξ ^ C k⌋₊ : ℝ)) atTop atTop := by
  sorry

end LeanFormalizations.Mills.SaitoTypeB
