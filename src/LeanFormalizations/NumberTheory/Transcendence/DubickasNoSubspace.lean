/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

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
* **Open (exactly TWO named literature leaves, everything between them proved):**
  `corvajaZannier_dichotomy` — CZ's main theorem, p. 177 = Dubickas's Lemma 3, the *only*
  subspace-strength step — and `corvajaZannier_lemma4` — CZ's Lemma 4.
  `exists_pisot_pow_pseudoPisot_core` is now *proved* from those two.
* **Lemma 4 is now proved for every multiplicatively-closed exponent set, with no escape branch**
  (2026-09-28, eighth lap): `exists_tie_of_bounded_den` forces the tie, and
  `valuation_sum_unit_pow_mulClosed` / `false_of_bounded_den_mulClosed` /
  `isIntegral_of_bounded_den_mulClosed` close it at *every* tie size via Newton's identities —
  `v(j! e_j(x)) ≤ max_{l ≤ k} v(p_l(x))`, and `e_k(x)` is a unit, so the fixed nonzero `v(k!)`
  cannot be beaten.  The degenerate (`α^l ∈ ℚ`) branch therefore exists **only** because the
  exponent set may be sparse.  The former disclosed leaf
  `valuation_sum_unit_pow_nondegenerate` is deleted (superseded).
  Both leads that were recorded here have been *refuted*: the archimedean Liouville/norm bound is vacuous (it only re-derives
  `M(α) ≥ α`), and the Böttcher coordinate is not of Mahler-method shape.  Full write-up, with
  the proposed literature `Prop`, in `PROBE-DUBICKAS-NOSUBSPACE.md`.
* `hD` therefore still sits on the `Dubickas.lean` headlines; it must not be routed through the
  `sorry`.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot
import LeanFormalizations.NumberTheory.Diophantine.Edges
import LeanFormalizations.NumberTheory.Transcendence.MultisetNewton

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology IntermediateField LeanFormalizations.Literature LeanFormalizations.Mills
open NumberField IsDedekindDomain

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

/-! ### Pseudo-Pisot numbers and the Corvaja–Zannier split of Lemma 6

Corvaja–Zannier (2004) call an algebraic `z` **pseudo-Pisot** when `|z| > 1`, every other
conjugate of `z` lies in the open unit disc, and the trace of `z` is a rational integer (an
algebraic *integer* that is pseudo-Pisot is a Pisot number).  Dubickas's Lemma 6 is the
disjunction of

* **Lemma 3** = CZ's main theorem (p. 177) at `δ = 1`, `u = α^(s n)`, `Γ = {α^t}`: if `q α^(s n)`
  is pseudo-Pisot for only finitely many `n`, then `‖q α^(s n)‖ > (1 − ε)^(s n)` eventually.
  *This* is where the `p`-adic Subspace Theorem enters, and it is the only place.
* **Lemma 5**: pseudo-Pisot infinitely often ⇒ some `α^(s m)` is Pisot.  Elementary once CZ's
  **Lemma 4** (trace of `q α^(s n)` a nonzero integer ⇒ `α` is an algebraic integer or a root of a
  rational) is available; both of its branches are discharged below.

We express "`q β` is pseudo-Pisot" through `β`'s own conjugates: the conjugates of `q β` are `q`
times those of `β` and `trace (q β) = q · trace β`, so this is the same condition, and it avoids a
minimal-polynomial rescaling lemma. -/

/-- `q β` is a **pseudo-Pisot** number, phrased in terms of the conjugates of `β`. -/
def IsPseudoPisotMul (q : ℕ) (β : ℝ) : Prop :=
  1 < (q : ℝ) * β ∧ (∀ w ∈ otherConj β, ‖(q : ℂ) * w‖ < 1) ∧
    ∃ t : ℤ, (q : ℂ) * (((minpoly ℚ β).aroots ℂ).sum) = (t : ℂ)

/-- **Lemma 5, algebraic-integer branch.**  If `β > 1` is an algebraic integer and `q β` is
pseudo-Pisot with `q ≥ 1`, then `β` itself is a Pisot number: `‖q w‖ < 1` and `q ≥ 1` force
`‖w‖ < 1` for every other conjugate `w`. -/
theorem isPisot_of_pseudoPisotMul {β : ℝ} {q : ℕ} (hq : 1 ≤ q) (hβ : 1 < β)
    (hint : IsIntegral ℤ β) (h : IsPseudoPisotMul q β) : IsPisot β := by
  refine ⟨hβ, hint, fun z hz ↦ ?_⟩
  have hz' : z ∈ otherConj β := hz
  have h1 := h.2.1 z hz'
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  rw [norm_mul, Complex.norm_natCast] at h1
  nlinarith [norm_nonneg z]

/-- **Lemma 5, root-of-a-rational branch.**  If some power `β^l` is rational then *all* conjugates
of `β` have modulus `β`, so the pseudo-Pisot condition (other conjugates inside the unit disc)
forces `β` to have no other conjugates at all, i.e. `β ∈ ℚ`. -/
theorem otherConj_eq_zero_of_pow_rat {β : ℝ} (hβ : 1 < β) {l : ℕ} (hl : 0 < l) {c : ℚ}
    (hc : β ^ l = (c : ℝ)) {q : ℕ} (hq : 1 ≤ q)
    (h : ∀ w ∈ otherConj β, ‖(q : ℂ) * w‖ < 1) : otherConj β = 0 := by
  have halg : IsAlgebraic ℚ β := ⟨Polynomial.X ^ l - Polynomial.C c, by
    intro he
    have := congrArg (fun p : Polynomial ℚ ↦ p.coeff l) he
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, hl.ne'] at this, by
    simp [hc]⟩
  have hint : IsIntegral ℚ β := halg.isIntegral
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro w hw
  have hdvd : minpoly ℚ β ∣ (Polynomial.X ^ l - Polynomial.C c) := by
    refine minpoly.dvd ℚ β ?_
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, hc, sub_self]
  have hwroot : w ∈ (minpoly ℚ β).aroots ℂ := Multiset.mem_of_mem_erase hw
  have hw0 : Polynomial.aeval w (minpoly ℚ β) = 0 := (Polynomial.mem_aroots.1 hwroot).2
  have hwl : w ^ l = ((c : ℚ) : ℂ) := by
    obtain ⟨g, hg⟩ := hdvd
    have h2 : Polynomial.aeval w (Polynomial.X ^ l - Polynomial.C c) = 0 := by
      rw [hg, map_mul, hw0, zero_mul]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast] at h2
    linear_combination h2
  have hβ0 : (0:ℝ) < β := by linarith
  have hnorm : ‖w‖ = β := by
    have h1 : ‖w‖ ^ l = β ^ l := by
      rw [← norm_pow, hwl]
      have hcc : ((c : ℚ) : ℂ) = (((c : ℝ)) : ℂ) := by push_cast; ring
      rw [hcc, Complex.norm_real, Real.norm_eq_abs, ← hc, abs_of_pos (by positivity)]
    exact (pow_left_inj₀ (norm_nonneg w) hβ0.le hl.ne').1 h1
  have := h w hw
  rw [norm_mul, Complex.norm_natCast, hnorm] at this
  nlinarith

/-- A real algebraic number with no conjugates other than itself is rational. -/
theorem eq_rat_of_otherConj_eq_zero {β : ℝ} (hint : IsIntegral ℚ β) (h : otherConj β = 0) :
    ∃ r : ℚ, β = (r : ℝ) := by
  have hcard := card_otherConj_add_one hint
  rw [h] at hcard
  simp at hcard
  have hmonic := minpoly.monic hint
  have heq : minpoly ℚ β = Polynomial.X + Polynomial.C ((minpoly ℚ β).coeff 0) :=
    hmonic.eq_X_add_C hcard.symm
  have h0 : Polynomial.aeval β (minpoly ℚ β) = 0 := minpoly.aeval ℚ β
  rw [heq] at h0
  simp at h0
  exact ⟨-((minpoly ℚ β).coeff 0), by push_cast; linarith⟩

/-- The degree of `α^N` is at most the degree of `α`, so `α^N` has at most `deg α − 1` other
conjugates — uniformly in `N`.  (`α^N ∈ ℚ⟮α⟯`, and `minpoly.natDegree_le` bounds a degree by the
`ℚ`-rank of the ambient field, which is `deg α`.) -/
theorem card_otherConj_pow_le {α : ℝ} (halg : IsIntegral ℚ α) (N : ℕ) :
    (otherConj (α ^ N)).card + 1 ≤ (minpoly ℚ α).natDegree := by
  haveI : FiniteDimensional ℚ ℚ⟮α⟯ := IntermediateField.adjoin.finiteDimensional halg
  set g : ℚ⟮α⟯ := IntermediateField.AdjoinSimple.gen ℚ α with hg
  have hinj : Function.Injective (algebraMap ℚ⟮α⟯ ℝ) := (algebraMap ℚ⟮α⟯ ℝ).injective
  have hgmap : algebraMap ℚ⟮α⟯ ℝ g = α := IntermediateField.AdjoinSimple.algebraMap_gen ℚ α
  have hmin : minpoly ℚ (g ^ N) = minpoly ℚ (α ^ N) := by
    have h := minpoly.algebraMap_eq (A := ℚ) hinj (g ^ N)
    rw [map_pow, hgmap] at h
    exact h.symm
  have hle : (minpoly ℚ (g ^ N)).natDegree ≤ Module.finrank ℚ ℚ⟮α⟯ := minpoly.natDegree_le _
  rw [hmin, IntermediateField.adjoin.finrank halg] at hle
  have hintN : IsIntegral ℚ (α ^ N) := halg.pow N
  rw [card_otherConj_add_one hintN]
  exact hle

/-- **Conjugates of a power are powers of conjugates.**  If `w` is a root of `minpoly ℚ α` then
`w^N` is a root of `minpoly ℚ (α^N)`: the polynomial `(minpoly ℚ (α^N)).comp (X^N)` kills `α`, so
`minpoly ℚ α` divides it. -/
theorem aroots_pow_mem {α : ℝ} (halg : IsIntegral ℚ α) (N : ℕ) {w : ℂ}
    (hw : w ∈ (minpoly ℚ α).aroots ℂ) : w ^ N ∈ (minpoly ℚ (α ^ N)).aroots ℂ := by
  have hdvd : minpoly ℚ α ∣ (minpoly ℚ (α ^ N)).comp (Polynomial.X ^ N) := by
    refine minpoly.dvd ℚ α ?_
    rw [Polynomial.aeval_comp]
    simp [minpoly.aeval]
  have hw0 : Polynomial.aeval w (minpoly ℚ α) = 0 := (Polynomial.mem_aroots.1 hw).2
  obtain ⟨g, hg⟩ := hdvd
  have h2 : Polynomial.aeval w ((minpoly ℚ (α ^ N)).comp (Polynomial.X ^ N)) = 0 := by
    rw [hg, map_mul, hw0, zero_mul]
  rw [Polynomial.aeval_comp] at h2
  simp only [map_pow, Polynomial.aeval_X] at h2
  rw [Polynomial.mem_aroots]
  exact ⟨minpoly.ne_zero (halg.pow N), h2⟩

/-- **The conjugates of `α` are either inside the unit disc or "collapse".**  If `q α^N` is
pseudo-Pisot (`q ≥ 1`, `N > 0`) then every root `w` of `minpoly ℚ α` with `w^N ≠ α^N` satisfies
`‖w‖ < 1`.  A `w` with `w^N = α^N` is `ζ α` for a root of unity `ζ` of order dividing `N`. -/
theorem norm_lt_one_of_pseudoPisotMul {α : ℝ} (halg : IsIntegral ℚ α) (hα : 1 < α) {q N : ℕ}
    (hq : 1 ≤ q) (hN : 0 < N) (h : IsPseudoPisotMul q (α ^ N)) {w : ℂ}
    (hw : w ∈ (minpoly ℚ α).aroots ℂ) (hne : w ^ N ≠ (((α ^ N : ℝ)) : ℂ)) : ‖w‖ < 1 := by
  have hmem : w ^ N ∈ otherConj (α ^ N) := by
    rw [otherConj, Multiset.mem_erase_of_ne hne]
    exact aroots_pow_mem halg N hw
  have h1 := h.2.1 _ hmem
  rw [norm_mul, Complex.norm_natCast, norm_pow] at h1
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  by_contra hc
  have hge : (1:ℝ) ≤ ‖w‖ := not_lt.1 hc
  have : (1:ℝ) ≤ ‖w‖ ^ N := one_le_pow₀ hge
  nlinarith

/-- If a conjugate `w` of `α` collapses at exponent `N > 0` (`w^N = α^N`) then `‖w‖ = α`. -/
theorem norm_eq_of_pow_eq {α : ℝ} (hα : 1 < α) {N : ℕ} (hN : 0 < N) {w : ℂ}
    (he : w ^ N = (((α ^ N : ℝ)) : ℂ)) : ‖w‖ = α := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1 : ‖w‖ ^ N = α ^ N := by
    rw [← norm_pow, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact (pow_left_inj₀ (norm_nonneg w) hα0.le hN.ne').1 h1

/-! ### Prerequisites for Lemma 4: the trace power sums and their integer recurrence

Any route to `corvajaZannier_lemma4` works with `U_N = Σ_w w^N`, the power sum over *all*
conjugates of `α` (`= Tr_{ℚ(α)/ℚ}(α^N)`): it is rational, and it satisfies the linear recurrence
given by the minimal polynomial.  Both facts are proved here, unconditionally. -/

/-- `U_N = Σ_w w^N`, the power sum over all conjugates of `α`, i.e. `Tr_{ℚ(α)/ℚ}(α^N)`. -/
noncomputable def tracePowSum (α : ℝ) (N : ℕ) : ℂ := (((minpoly ℚ α).aroots ℂ).map (· ^ N)).sum

/-- The trace power sums are **rational**.  (Same route as `Mills.rootPowSum_mem_int` but
stopping at `ℚ`: no integral closure step, so no integrality hypothesis.) -/
theorem tracePowSum_rat {α : ℝ} (halg : IsIntegral ℚ α) (N : ℕ) :
    ∃ u : ℚ, tracePowSum α N = (u : ℂ) := by
  haveI : FiniteDimensional ℚ ℚ⟮α⟯ := IntermediateField.adjoin.finiteDimensional halg
  set g : ℚ⟮α⟯ := IntermediateField.AdjoinSimple.gen ℚ α with hg
  have hinj : Function.Injective (algebraMap ℚ⟮α⟯ ℝ) := (algebraMap ℚ⟮α⟯ ℝ).injective
  have hgmap : algebraMap ℚ⟮α⟯ ℝ g = α := IntermediateField.AdjoinSimple.algebraMap_gen ℚ α
  refine ⟨Algebra.trace ℚ ℚ⟮α⟯ (g ^ N), ?_⟩
  have hsum : algebraMap ℚ ℂ (Algebra.trace ℚ ℚ⟮α⟯ (g ^ N)) = ∑ σ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, σ (g ^ N) :=
    _root_.trace_eq_sum_embeddings ℂ
  have hmin : minpoly ℚ g = minpoly ℚ α := by
    have h := minpoly.algebraMap_eq (A := ℚ) hinj g
    rw [hgmap] at h
    exact h.symm
  classical
  set pb : PowerBasis ℚ ℚ⟮α⟯ := IntermediateField.adjoin.powerBasis halg with hpb
  have hpbgen : pb.gen = g := IntermediateField.adjoin.powerBasis_gen halg
  have hsep : IsSeparable ℚ pb.gen := Algebra.IsSeparable.isSeparable ℚ _
  have hnodup : ((minpoly ℚ pb.gen).aroots ℂ).Nodup :=
    Polynomial.nodup_roots ((Polynomial.separable_map _).mpr hsep)
  have hfin : (∑ σ : ℚ⟮α⟯ →ₐ[ℚ] ℂ, σ (g ^ N))
      = (((minpoly ℚ pb.gen).aroots ℂ).map (· ^ N)).sum := by
    rw [Fintype.sum_equiv pb.liftEquiv' (fun σ : ℚ⟮α⟯ →ₐ[ℚ] ℂ => σ (g ^ N))
        (fun x : {x : ℂ // x ∈ (minpoly ℚ pb.gen).aroots ℂ} => ((x : ℂ)) ^ N)
        (by intro σ; rw [PowerBasis.liftEquiv'_apply_coe, hpbgen, ← map_pow]),
      Finset.sum_mem_multiset _ _ (fun x : ℂ => x ^ N) (fun x => rfl),
      Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [hpbgen, hmin] at hfin
  rw [tracePowSum, ← hfin, ← hsum]
  simp

/-- Pulling a `Finset` sum through a `Multiset` sum. -/
private theorem sum_range_mul_multiset_sum (c : ℕ → ℂ) (m : ℕ) (N : ℕ) (s : Multiset ℂ) :
    (∑ k ∈ Finset.range m, c k * (s.map (· ^ (N + k))).sum)
      = (s.map (fun w ↦ ∑ k ∈ Finset.range m, c k * w ^ (N + k))).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]

/-- **The trace power sums satisfy the recurrence given by the minimal polynomial**:
`Σ_{k ≤ d} p_k U_(N+k) = 0`, where `p = minpoly ℚ α` has degree `d`.  (Each conjugate `w`
contributes `w^N · p(w) = 0`.)  Multiplied by the content of `p` this is a recurrence with
*integer* coefficients whose leading one is the leading coefficient of the primitive minimal
polynomial — the object Lemma 4's valuation argument runs on. -/
theorem tracePowSum_recurrence {α : ℝ} (halg : IsIntegral ℚ α) (N : ℕ) :
    ∑ k ∈ Finset.range ((minpoly ℚ α).natDegree + 1),
      (((minpoly ℚ α).coeff k : ℚ) : ℂ) * tracePowSum α (N + k) = 0 := by
  classical
  set p := minpoly ℚ α with hp
  set d := p.natDegree with hd
  rw [show (fun k ↦ (((p.coeff k : ℚ)) : ℂ) * tracePowSum α (N + k)) = fun k ↦
      (((p.coeff k : ℚ)) : ℂ) * (((p.aroots ℂ).map (· ^ (N + k))).sum) from rfl]
  rw [sum_range_mul_multiset_sum (fun k ↦ (((p.coeff k : ℚ)) : ℂ)) (d + 1) N]
  refine Multiset.sum_eq_zero ?_
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Multiset.mem_map.1 hx
  rw [← hxw]
  have hroot : Polynomial.aeval w p = 0 := (Polynomial.mem_aroots.1 hw).2
  have heval : (Polynomial.aeval w) p = ∑ k ∈ Finset.range (d + 1),
      (((p.coeff k : ℚ)) : ℂ) * w ^ k := by
    rw [Polynomial.aeval_eq_sum_range (p := p) (x := w)]
    rw [← hd]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [Algebra.smul_def, eq_ratCast]
  have hfac : ∑ k ∈ Finset.range (d + 1), (((p.coeff k : ℚ)) : ℂ) * w ^ (N + k)
      = w ^ N * ∑ k ∈ Finset.range (d + 1), (((p.coeff k : ℚ)) : ℂ) * w ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_add]
    ring
  rw [hfac, ← heval, hroot, mul_zero]

/-- **The integrality bridge**: `α` is an algebraic *integer* exactly when the coefficients of its
rational minimal polynomial are integers.  This is the shape in which Lemma 4's valuation argument
delivers its conclusion (a prime dividing a coefficient denominator is the prime at which some
conjugate has negative valuation), so it is stated here once and for all. -/
theorem isIntegral_int_iff_minpoly_den {α : ℝ} (halg : IsIntegral ℚ α) :
    IsIntegral ℤ α ↔ ∀ k, ((minpoly ℚ α).coeff k).den = 1 := by
  constructor
  · intro hint k
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) hint, Polynomial.coeff_map]
    simp
  · intro hden
    have hlift : minpoly ℚ α ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro k
      refine ⟨((minpoly ℚ α).coeff k).num, ?_⟩
      have := (Rat.den_eq_one_iff _).1 (hden k)
      simpa using this
    obtain ⟨q, hmap, -, hmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic halg)
    refine ⟨q, hmonic, ?_⟩
    have hmap' : q.map (algebraMap ℤ ℚ) = minpoly ℚ α := hmap
    have hae := Polynomial.aeval_map_algebraMap (R := ℤ) (A := ℚ) (B := ℝ) α q
    rw [hmap'] at hae
    show Polynomial.aeval α q = 0
    rw [← hae, minpoly.aeval]

/-! ### The non-archimedean core of Lemma 4 (no-tie case)

The `p`-adic half of CZ's Lemma 4 runs like this.  Suppose `α` is *not* an algebraic integer.
Inside a number field `L` containing all conjugates of `α` there is then a prime `v` with
`v α > 1` (`HeightOneSpectrum.mem_integers_of_valuation_le_one`, contrapositive).  The trace power
sum `U_N = Σ_w w^N` is a sum of `N`-th powers of the conjugates; if **one** conjugate `z` strictly
dominates the others at `v`, the ultrametric inequality gives `v U_N = (v z)^N → ∞`, while
`q U_N ∈ ℤ` forces `v U_N ≤ (v q)⁻¹`.  Contradiction.

`no_bounded_den_of_unique_max_valuation` below is exactly that argument, for an arbitrary number
field, and it is unconditional.  What is *not* yet formalized is the tie case (several conjugates
sharing the maximal valuation), which is where CZ's `α^l ∈ ℚ` branch comes from; see
`PROBE-DUBICKAS-NOSUBSPACE.md`. -/

/-- In `ℤₘ₀ = WithZero (Multiplicative ℤ)`: if `1 < a` and `b ≠ 0` then `b · aⁿ` eventually
exceeds `1`. -/
theorem exists_one_lt_mul_pow {a b : WithZero (Multiplicative ℤ)} (ha : 1 < a) (hb : b ≠ 0) :
    ∃ n : ℕ, 1 < b * a ^ n := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha
    exact absurd ha (by simp)
  obtain ⟨x, hx⟩ := WithZero.ne_zero_iff_exists.1 ha0
  obtain ⟨y, hy⟩ := WithZero.ne_zero_iff_exists.1 hb
  have hx1 : (1 : Multiplicative ℤ) < x := by
    rw [← hx] at ha
    exact_mod_cast ha
  have hxA : 0 < Multiplicative.toAdd x := hx1
  refine ⟨(-Multiplicative.toAdd y).toNat + 1, ?_⟩
  rw [← hx, ← hy, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one,
    WithZero.coe_lt_coe]
  show (1 : Multiplicative ℤ) < y * x ^ ((-Multiplicative.toAdd y).toNat + 1)
  rw [show ((1 : Multiplicative ℤ) < y * x ^ ((-Multiplicative.toAdd y).toNat + 1))
      = (0 < Multiplicative.toAdd y +
          ((-Multiplicative.toAdd y).toNat + 1 : ℕ) * Multiplicative.toAdd x) from by
    rw [show Multiplicative.toAdd y
        + ((-Multiplicative.toAdd y).toNat + 1 : ℕ) * Multiplicative.toAdd x
        = Multiplicative.toAdd (y * x ^ ((-Multiplicative.toAdd y).toNat + 1)) from by
      rw [toAdd_mul, toAdd_pow, nsmul_eq_mul]]
    rfl]
  have h1 : -Multiplicative.toAdd y ≤ (-Multiplicative.toAdd y).toNat := Int.self_le_toNat _
  have h2 : (0:ℤ) ≤ ((-Multiplicative.toAdd y).toNat : ℤ) := Int.natCast_nonneg _
  have h3 : (1:ℤ) ≤ Multiplicative.toAdd x := hxA
  push_cast
  nlinarith [h1, h2, h3]

/-- The valuation of a multiset sum is bounded by any bound on its members' valuations. -/
theorem valuation_multiset_sum_lt {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (R : Multiset L) {B : WithZero (Multiplicative ℤ)} (hB : 0 < B)
    (h : ∀ w ∈ R, v.valuation L w < B) : v.valuation L R.sum < B := by
  induction R using Multiset.induction with
  | empty => simpa using hB
  | cons a s ih =>
      rw [Multiset.sum_cons]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) ?_
      exact max_lt (h a (Multiset.mem_cons_self _ _))
        (ih fun w hw ↦ h w (Multiset.mem_cons_of_mem hw))

/-- **The no-tie case of Corvaja–Zannier's Lemma 4, unconditionally.**  If one conjugate `z`
strictly dominates all the others at some prime `v` of a number field `L`, and `v z > 1`, then
`q · (z^N + Σ_w w^N)` cannot be a rational integer for infinitely many `N`: the ultrametric
equality case forces `v` of it to be `v q · (v z)^N`, which is unbounded, while integers have
valuation `≤ 1`. -/
theorem no_bounded_den_of_unique_max_valuation {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {z : L} {R : Multiset L} (hz : 1 < v.valuation L z)
    (hR : ∀ w ∈ R, v.valuation L w < v.valuation L z)
    {q : ℕ} (hq : 0 < q) {S : Set ℕ} (hS : S.Infinite)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : L) * (z ^ N + (R.map (· ^ N)).sum) = (m : L)) : False := by
  classical
  set V : WithZero (Multiplicative ℤ) := v.valuation L z with hV
  have hV0 : (0 : WithZero (Multiplicative ℤ)) < V := lt_trans zero_lt_one hz
  have hqne : (q : L) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hqv0 : v.valuation L (q : L) ≠ 0 := by
    simpa using hqne
  -- the bound coming from `q U_N ∈ ℤ`
  obtain ⟨n₀, hn₀⟩ := exists_one_lt_mul_pow (a := V) (b := v.valuation L (q : L)) hz hqv0
  obtain ⟨N, hNS, hN⟩ := hS.exists_gt (max n₀ 1)
  have hN1 : 1 ≤ N := le_trans (le_max_right n₀ 1) hN.le
  have hNn₀ : n₀ ≤ N := le_trans (le_max_left n₀ 1) hN.le
  obtain ⟨m, hm⟩ := hu N hNS
  -- `v (z^N) = V^N` dominates the rest strictly
  have hzN : v.valuation L (z ^ N) = V ^ N := by rw [map_pow, hV]
  have hrest : v.valuation L ((R.map (· ^ N)).sum) < V ^ N := by
    refine valuation_multiset_sum_lt v _ (pow_pos hV0 N) ?_
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Multiset.mem_map.1 hx
    rw [← hxw, map_pow]
    exact pow_lt_pow_left₀ (hR w hw) (by simp) (by omega)
  have hsum : v.valuation L (z ^ N + (R.map (· ^ N)).sum) = V ^ N := by
    rw [add_comm, Valuation.map_add_eq_of_lt_right _ (by rw [hzN] at *; exact hrest), hzN]
  -- but the left side is `v (m / q)`, at most `(v q)⁻¹`
  have hmv : v.valuation L (m : L) ≤ 1 := by
    rw [show ((m : L)) = algebraMap (NumberField.RingOfIntegers L) L
        (m : NumberField.RingOfIntegers L) from
      (map_intCast (algebraMap (NumberField.RingOfIntegers L) L) m).symm]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _
  have hle : v.valuation L (q : L) * V ^ N ≤ 1 := by
    have h1 : v.valuation L ((q : L) * (z ^ N + (R.map (· ^ N)).sum))
        = v.valuation L (q : L) * V ^ N := by rw [Valuation.map_mul, hsum]
    rw [hm] at h1
    rw [← h1]
    exact hmv
  have hmono : V ^ n₀ ≤ V ^ N := pow_le_pow_right₀ (le_of_lt hz) hNn₀
  have hgt : 1 < v.valuation L (q : L) * V ^ N :=
    lt_of_lt_of_le hn₀ (mul_le_mul_left' hmono _)
  exact absurd hle (not_le.2 hgt)


/-! ### The bridge: the conjugates of `α` inside a number field, and the forced tie

`no_bounded_den_of_unique_max_valuation` above is stated for an arbitrary number field.  To use it
on `α` we need the conjugates of `α` to *live* in a number field: that is `conjField α`, the
subfield of `ℂ` generated by the root set of `minpoly ℚ α` (finite-dimensional over `ℚ`
unconditionally — for transcendental `α` the minimal polynomial is `0` and the root set is empty).
`conjMultiset α` is the conjugate multiset there, and `conjMultiset_pow_sum_coe` identifies its
power sums with `tracePowSum`.

The pay-off is `exists_tie_of_bounded_den`: **Lemma 4's hypothesis forces a tie.**  If `α` is not
an algebraic integer, then at some prime `v` of `conjField α` the maximal conjugate valuation
exceeds `1` and is attained at least twice.  That isolates the residual content of CZ's Lemma 4
into its tie case (the `p`-adic Skolem–Mahler–Lech step that produces the `α^l ∈ ℚ` branch). -/


/-- The field generated over `ℚ` by all complex conjugates of `α`: a number field containing
every root of `minpoly ℚ α`, and the arena for Lemma 4's valuation argument. -/
noncomputable def conjField (α : ℝ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet ℂ)

instance conjField.finiteDimensional (α : ℝ) : FiniteDimensional ℚ (conjField α) :=
  IntermediateField.finiteDimensional_adjoin
    (fun x hx ↦ (_root_.isAlgebraic_of_mem_rootSet hx).isIntegral)

instance conjField.numberField (α : ℝ) : NumberField (conjField α) where

theorem mem_conjField_of_mem_aroots {α : ℝ} {w : ℂ} (hw : w ∈ (minpoly ℚ α).aroots ℂ) :
    w ∈ conjField α := by
  classical
  exact IntermediateField.subset_adjoin ℚ _ (by
    rw [Polynomial.rootSet_def]
    exact Multiset.mem_toFinset.2 hw)

/-- The multiset of conjugates of `α`, inside the number field `conjField α`. -/
noncomputable def conjMultiset (α : ℝ) : Multiset (conjField α) :=
  ((minpoly ℚ α).aroots ℂ).pmap (fun w hw ↦ (⟨w, hw⟩ : conjField α))
    (fun _ hw ↦ mem_conjField_of_mem_aroots hw)

theorem conjMultiset_map_coe (α : ℝ) :
    (conjMultiset α).map (fun w : conjField α ↦ (w : ℂ)) = (minpoly ℚ α).aroots ℂ := by
  classical
  rw [conjMultiset, Multiset.map_pmap]
  simpa using (Multiset.pmap_eq_map _ _ _ _).trans (Multiset.map_id _)


/-- Pushing the conjugate power sum from `conjField α` down to `ℂ`: it *is* `tracePowSum`. -/
theorem conjMultiset_pow_sum_coe (α : ℝ) (N : ℕ) :
    (algebraMap (conjField α) ℂ) (((conjMultiset α).map (· ^ N)).sum) = tracePowSum α N := by
  classical
  rw [map_multiset_sum, Multiset.map_map, tracePowSum, ← conjMultiset_map_coe α, Multiset.map_map]
  rfl

/-- A nonempty multiset in a linear order has a member bounding all the others under any `f`. -/
theorem exists_max_image_multiset {β : Type*} {γ : Type*} [LinearOrder γ] (R : Multiset β)
    (f : β → γ) (h : R ≠ 0) : ∃ z ∈ R, ∀ w ∈ R, f w ≤ f z := by
  classical
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image R.toFinset f
    (Multiset.toFinset_nonempty.2 h)
  exact ⟨z, Multiset.mem_toFinset.1 hz, fun w hw ↦ hmax w (Multiset.mem_toFinset.2 hw)⟩

/-- An element of a number field that is **not** an algebraic integer has valuation `> 1` at some
prime.  (Contrapositive of `mem_integers_of_valuation_le_one`.) -/
theorem exists_valuation_one_lt {L : Type*} [Field L] [NumberField L] {x : L}
    (hx : ¬ IsIntegral ℤ x) : ∃ v : HeightOneSpectrum (𝓞 L), 1 < v.valuation L x := by
  by_contra h
  push_neg at h
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L x
    (fun v ↦ h v)
  exact hx (hy ▸ RingOfIntegers.isIntegral_coe y)


/-- `≤` form of `valuation_multiset_sum_lt`. -/
theorem valuation_multiset_sum_le {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (R : Multiset L) {B : WithZero (Multiplicative ℤ)}
    (h : ∀ w ∈ R, v.valuation L w ≤ B) : v.valuation L R.sum ≤ B := by
  induction R using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.sum_cons]
      refine le_trans (Valuation.map_add _ _ _) ?_
      exact max_le (h a (Multiset.mem_cons_self _ _))
        (ih fun w hw ↦ h w (Multiset.mem_cons_of_mem hw))

theorem coe_mem_aroots_of_mem_conjMultiset {α : ℝ} {w : conjField α} (hw : w ∈ conjMultiset α) :
    (w : ℂ) ∈ (minpoly ℚ α).aroots ℂ := by
  classical
  rw [conjMultiset, Multiset.mem_pmap] at hw
  obtain ⟨a, ha, rfl⟩ := hw
  exact ha

/-- Lemma 4's hypothesis, transported into `conjField α`. -/
theorem conj_bounded_den {α : ℝ} {q : ℕ} {S : Set ℕ}
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : ℂ) * tracePowSum α N = (m : ℂ)) :
    ∀ N ∈ S, ∃ m : ℤ, (q : conjField α) * (((conjMultiset α).map (· ^ N)).sum)
      = (m : conjField α) := by
  intro N hN
  obtain ⟨m, hm⟩ := hu N hN
  refine ⟨m, ?_⟩
  apply (algebraMap (conjField α) ℂ).injective
  rw [map_mul, map_intCast, map_natCast, ← hm, ← conjMultiset_pow_sum_coe α N]

/-- If `α` is not an algebraic integer, some prime of `conjField α` has a conjugate of valuation
`> 1`, and among the conjugates one of maximal valuation can be chosen. -/
theorem exists_dominant_max {α : ℝ} (halg : IsIntegral ℚ α) (hnint : ¬ IsIntegral ℤ α) :
    ∃ (v : HeightOneSpectrum (𝓞 (conjField α))) (z : conjField α), z ∈ conjMultiset α ∧
      1 < v.valuation (conjField α) z ∧
      ∀ y ∈ conjMultiset α, v.valuation (conjField α) y ≤ v.valuation (conjField α) z := by
  classical
  have hmemα : ((α : ℂ)) ∈ conjField α := mem_conjField_of_mem_aroots (beta_mem_aroots halg)
  set a : conjField α := ⟨(α : ℂ), hmemα⟩ with ha
  have haR : a ∈ conjMultiset α := by
    rw [conjMultiset, Multiset.mem_pmap]
    exact ⟨(α : ℂ), beta_mem_aroots halg, rfl⟩
  have hnint' : ¬ IsIntegral ℤ a := by
    intro hint
    have h1 : IsIntegral ℤ ((α : ℝ) : ℂ) := by
      have := hint.map ((algebraMap (conjField α) ℂ).toIntAlgHom)
      simpa [ha] using this
    exact hnint ((isIntegral_algHom_iff (Complex.ofRealHom.toIntAlgHom)
      Complex.ofReal_injective).1 h1)
  obtain ⟨v, hv⟩ := exists_valuation_one_lt hnint'
  obtain ⟨z, hzR, hmax⟩ := exists_max_image_multiset (conjMultiset α)
    (v.valuation (conjField α)) (fun h ↦ by simp [h] at haR)
  exact ⟨v, z, hzR, lt_of_lt_of_le hv (hmax a haR), hmax⟩


/-- **At a prime where one conjugate of `α` strictly dominates, Lemma 4's hypothesis is
contradictory.**  Hence: if the power sums `U_N = Σ_w w^N` have denominators dividing a fixed `q`
for infinitely many `N`, then at *every* prime of `conjField α` the maximal conjugate valuation,
when it exceeds `1`, is attained **at least twice**.  This is the no-tie half of CZ's Lemma 4,
transported from `no_bounded_den_of_unique_max_valuation` to the conjugates of `α`. -/
theorem tie_of_bounded_den {α : ℝ} {q : ℕ} (hq : 0 < q)
    {S : Set ℕ} (hS : S.Infinite)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : ℂ) * tracePowSum α N = (m : ℂ))
    (v : HeightOneSpectrum (𝓞 (conjField α))) {z : conjField α}
    (hzR : z ∈ conjMultiset α) (hz1 : 1 < v.valuation (conjField α) z)
    (hmax : ∀ w ∈ conjMultiset α,
      v.valuation (conjField α) w ≤ v.valuation (conjField α) z) :
    ∃ w ∈ (conjMultiset α).erase z,
      v.valuation (conjField α) w = v.valuation (conjField α) z := by
  classical
  by_contra hcon
  push_neg at hcon
  set E : Multiset (conjField α) := (conjMultiset α).erase z with hE
  have hlt : ∀ w ∈ E, v.valuation (conjField α) w < v.valuation (conjField α) z := by
    intro w hw
    exact lt_of_le_of_ne (hmax w (Multiset.mem_of_mem_erase hw)) (hcon w hw)
  refine no_bounded_den_of_unique_max_valuation v hz1 hlt hq hS ?_
  intro N hN
  obtain ⟨m, hm⟩ := hu N hN
  refine ⟨m, ?_⟩
  have h1 : ((conjMultiset α).map (· ^ N)).sum = z ^ N + (E.map (· ^ N)).sum := by
    conv_lhs => rw [← Multiset.cons_erase hzR]
    simp [Multiset.map_cons, Multiset.sum_cons, hE]
  apply (algebraMap (conjField α) ℂ).injective
  rw [map_mul, map_intCast, map_natCast, ← hm, ← conjMultiset_pow_sum_coe α N, h1]

/-- **Lemma 4's hypothesis forces a tie.**  If `α` is *not* an algebraic integer and the trace
power sums `U_N` have denominators dividing a fixed `q` for infinitely many `N`, then there is a
prime `v` of `conjField α` and two **distinct** conjugates `z ≠ w` of `α` with
`v z = v w = max_y v y > 1`.

This is everything in Corvaja–Zannier's Lemma 4 except its tie case: the residual is exactly the
`p`-adic statement that a sum of `N`-th powers of `v`-units cannot be divisible by arbitrarily high
powers of `v` along an infinite set of `N` unless two of them have a root-of-unity ratio, which is
where CZ's `α^l ∈ ℚ` branch comes from.  See `PROBE-DUBICKAS-NOSUBSPACE.md`. -/
theorem exists_tie_of_bounded_den {α : ℝ} (halg : IsIntegral ℚ α) {q : ℕ} (hq : 0 < q)
    {S : Set ℕ} (hS : S.Infinite)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : ℂ) * tracePowSum α N = (m : ℂ))
    (hnint : ¬ IsIntegral ℤ α) :
    ∃ (v : HeightOneSpectrum (𝓞 (conjField α))) (z w : conjField α),
      z ∈ conjMultiset α ∧ w ∈ (conjMultiset α).erase z ∧
      1 < v.valuation (conjField α) z ∧
      v.valuation (conjField α) w = v.valuation (conjField α) z ∧
      ∀ y ∈ conjMultiset α, v.valuation (conjField α) y ≤ v.valuation (conjField α) z := by
  obtain ⟨v, z, hzR, hz1, hmax⟩ := exists_dominant_max halg hnint
  obtain ⟨w, hw, hwe⟩ := tie_of_bounded_den hq hS hu v hzR hz1 hmax
  exact ⟨v, z, w, hzR, hw, hz1, hwe, hmax⟩
/-- In `ℤₘ₀`: if `r < 1` and `c ≠ 0` then `B rⁿ < c` for some `n`. -/
theorem exists_mul_pow_lt {B r c : WithZero (Multiplicative ℤ)} (hr : r < 1) (hc : c ≠ 0)
    (hB : B ≠ 0) : ∃ n : ℕ, B * r ^ n < c := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨1, by simpa using (zero_lt_iff.2 hc)⟩
  have hrinv : 1 < r⁻¹ := by
    rw [one_lt_inv_iff₀]
    exact ⟨zero_lt_iff.2 hr0, hr⟩
  obtain ⟨n, hn⟩ := exists_one_lt_mul_pow (a := r⁻¹) (b := c * B⁻¹) hrinv
    (by simp [hc, hB])
  refine ⟨n, ?_⟩
  have hx0 : (0 : WithZero (Multiplicative ℤ)) < B * r ^ n := by
    refine zero_lt_iff.2 ?_
    simp [hB, hr0]
  have heq : c * B⁻¹ * r⁻¹ ^ n = c * (B * r ^ n)⁻¹ := by
    rw [inv_pow]
    field_simp
  rw [heq, ← div_eq_mul_inv, lt_div_iff₀ hx0, one_mul] at hn
  exact hn


/-! ### The tie case, CLOSED for multiplicatively-closed exponent sets

Newton's identities collapse the tie case at **every** tie size `k`, with *no* nondegeneracy
hypothesis, as soon as the exponent set is closed under multiplication by `1, …, k`.  Write
`x = {u^N : u ∈ U}` for the `N`-th powers of the dominant (normalized) conjugates, `k = |U|`.  Each
`e_j(x)` is a sum of products of `v`-units, so `v(e_j(x)) ≤ 1`, and `v(m!) ≤ 1` for every natural
number; so Newton's `j e_j = (−1)^(j+1) Σ_{i<j} (−1)^i e_i p_(j−i)` gives, with no induction at all,

    v(j! · e_j(x))  ≤  max_{1 ≤ l ≤ k} v(p_l(x))  =  max_{1 ≤ l ≤ k} v(Σ_{u ∈ U} u^(l N)).

At `j = k` the left-hand side is `v(k!) · v(∏_u u^N) = v(k!)`, a **fixed nonzero** quantity, while
the right-hand side is `≤ B r^N → 0`.  Contradiction.

This **supersedes and replaces** the earlier disclosed leaf `valuation_sum_unit_pow_nondegenerate`
(deleted with this section): the degenerate (`α^l ∈ ℚ`) branch of Corvaja–Zannier's Lemma 4 is
entirely an artifact of exponent-set *sparsity*, not of `p`-adic analysis.  Consistency check:
`α = √(3/2)` has `U_N = 0` for every odd `N` — but `U_(2M) = 2(3/2)^M`, so its index set is *not*
closed under doubling, exactly as the theorem requires.

What the call site cannot yet supply is the closure hypothesis; that is the residual recorded in
`PROBE-DUBICKAS-NOSUBSPACE.md`, and it is a question about the *density* of the index set produced
by CZ's Lemma 3 (his Lemma 6's other branch), not about the local analysis. -/

/-- `v` of a natural number is at most `1`. -/
theorem valuation_natCast_le_one {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (n : ℕ) :
    v.valuation L (n : L) ≤ 1 := by
  rw [show ((n : L)) = (((n : ℤ)) : L) from (Int.cast_natCast n).symm,
    show ((((n : ℤ))) : L) = algebraMap (NumberField.RingOfIntegers L) L (((n : ℤ)) : _) from
      (map_intCast (algebraMap (NumberField.RingOfIntegers L) L) ((n : ℤ))).symm]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _

/-- A product of `v`-units is a `v`-unit. -/
theorem valuation_multiset_prod_eq_one {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {t : Multiset L} (h : ∀ x ∈ t, v.valuation L x = 1) : v.valuation L t.prod = 1 := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Valuation.map_mul, h a (Multiset.mem_cons_self _ _),
        ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx), one_mul]

/-- Ultrametric bound for a `Finset` sum. -/
theorem valuation_finset_sum_le {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {ι : Type*} (t : Finset ι) (g : ι → L) {B : WithZero (Multiplicative ℤ)}
    (h : ∀ i ∈ t, v.valuation L (g i) ≤ B) : v.valuation L (∑ i ∈ t, g i) ≤ B := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact le_trans (Valuation.map_add _ _ _)
        (max_le (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi])))

/-- Every elementary symmetric function of a multiset of `v`-units has valuation `≤ 1`. -/
theorem valuation_esymm_le_one {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {x : Multiset L} (hx : ∀ u ∈ x, v.valuation L u = 1) (j : ℕ) :
    v.valuation L (x.esymm j) ≤ 1 := by
  classical
  rw [Multiset.esymm]
  refine valuation_multiset_sum_le v _ ?_
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
  have hsub : t ≤ x := (Multiset.mem_powersetCard.1 ht).1
  exact le_of_eq
    (valuation_multiset_prod_eq_one v fun w hw ↦ hx w (Multiset.mem_of_le hsub hw))

/-- `esymm` at the cardinality is the whole product. -/
theorem multiset_esymm_card {R : Type*} [CommSemiring R] (x : Multiset R) :
    x.esymm x.card = x.prod := by
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]

/-- **The Newton step.**  For a multiset `x` of `v`-units whose power sums `p_1, …, p_k` all have
valuation `≤ ε` (`k = |x|`), every `j! · e_j` with `1 ≤ j ≤ k` has valuation `≤ ε`.  No induction is
needed: in Newton's identity `j e_j = (−1)^(j+1) Σ_{i<j} (−1)^i e_i p_(j−i)` each summand, after
multiplying through by `(j−1)!`, is `(an element of valuation ≤ 1) · p_(j−i)`. -/
theorem valuation_factorial_mul_esymm_le {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {x : Multiset L} (hx : ∀ u ∈ x, v.valuation L u = 1)
    {ε : WithZero (Multiplicative ℤ)}
    (hps : ∀ j, 0 < j → j ≤ x.card → v.valuation L (x.psum j) ≤ ε)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ x.card) :
    v.valuation L ((j.factorial : L) * x.esymm j) ≤ ε := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  set F : Finset (ℕ × ℕ) := {a ∈ Finset.antidiagonal (m + 1) | a.1 < m + 1} with hF
  have hN := multiset_mul_esymm_eq_sum x (m + 1)
  have hfac : (((m + 1).factorial : ℕ) : L) = (m.factorial : L) * (((m + 1 : ℕ)) : L) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hkey : (((m + 1).factorial : ℕ) : L) * x.esymm (m + 1)
      = (-1 : L) ^ (m + 1 + 1) *
        ∑ a ∈ F, (m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2) := by
    rw [← Finset.mul_sum, hfac]
    calc (m.factorial : L) * (((m + 1 : ℕ)) : L) * x.esymm (m + 1)
        = (m.factorial : L) * ((((m + 1 : ℕ)) : L) * x.esymm (m + 1)) := by ring
      _ = (m.factorial : L) * ((-1 : L) ^ (m + 1 + 1) *
            ∑ a ∈ F, (-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2) := by rw [hN]
      _ = _ := by ring
  rw [hkey, Valuation.map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
  refine valuation_finset_sum_le v _ _ ?_
  intro a ha
  rw [hF, Finset.mem_filter, Finset.mem_antidiagonal] at ha
  obtain ⟨ha1, ha2⟩ := ha
  have ha2pos : 0 < a.2 := by omega
  have ha2le : a.2 ≤ x.card := by omega
  have hleft : v.valuation L ((m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1)) ≤ 1 := by
    rw [Valuation.map_mul, Valuation.map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v.valuation L ((m.factorial : L)) * v.valuation L (x.esymm a.1)
        ≤ 1 * v.valuation L (x.esymm a.1) :=
          mul_le_mul_right' (valuation_natCast_le_one v _) _
      _ = v.valuation L (x.esymm a.1) := one_mul _
      _ ≤ 1 := valuation_esymm_le_one v hx a.1
  calc v.valuation L ((m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2))
      = v.valuation L ((m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1))
          * v.valuation L (x.psum a.2) := by
        rw [← Valuation.map_mul]; congr 1; ring
    _ ≤ 1 * v.valuation L (x.psum a.2) := mul_le_mul_right' hleft _
    _ = v.valuation L (x.psum a.2) := one_mul _
    _ ≤ ε := hps a.2 ha2pos ha2le

/-- **The tie case of Corvaja–Zannier's Lemma 4, closed at every tie size** — for `v`-units
`u_1, …, u_k` (`k ≥ 1`) and an exponent set closed under multiplication by `1, …, k`, the power
sums `Σ_i u_i^N` cannot decay geometrically.  **No nondegeneracy hypothesis.**

Generalizes `valuation_sum_unit_pow_card_two` (the `k = 2` Graeffe collapse) and replaces the
former disclosed leaf `valuation_sum_unit_pow_nondegenerate`. -/
theorem valuation_sum_unit_pow_mulClosed {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {U : Multiset L} (hU : ∀ u ∈ U, v.valuation L u = 1) (hcard : 1 ≤ U.card)
    {S : Set ℕ} (hS : S.Infinite)
    (hmul : ∀ N ∈ S, ∀ j, 0 < j → j ≤ U.card → j * N ∈ S)
    {B r : WithZero (Multiplicative ℤ)} (hB : B ≠ 0) (hr : r < 1)
    (hsum : ∀ N ∈ S, v.valuation L ((U.map (· ^ N)).sum) ≤ B * r ^ N) : False := by
  classical
  set c : WithZero (Multiplicative ℤ) := v.valuation L ((U.card.factorial : L)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    simp only [ne_eq, Valuation.zero_iff, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero _
  obtain ⟨n, hn⟩ := exists_mul_pow_lt (B := B) (r := r) (c := c) hr hc0 hB
  obtain ⟨N, hNS, hNn⟩ := hS.exists_gt n
  have hNge : n ≤ N := hNn.le
  set x : Multiset L := U.map (· ^ N) with hx
  have hxcard : x.card = U.card := by rw [hx, Multiset.card_map]
  have hxu : ∀ u ∈ x, v.valuation L u = 1 := by
    intro u hu'
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu'
    rw [map_pow, hU w hw, one_pow]
  have hxps : ∀ j, 0 < j → j ≤ x.card → v.valuation L (x.psum j) ≤ B * r ^ n := by
    intro j hj hjk
    have hjN : j * N ∈ S := hmul N hNS j hj (by rwa [hxcard] at hjk)
    have hrw : x.psum j = (U.map (· ^ (j * N))).sum := by
      rw [Multiset.psum_def, hx, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl ?_
      intro w _
      simp only [Function.comp_apply, ← pow_mul]
      rw [Nat.mul_comm]
    rw [hrw]
    refine le_trans (hsum _ hjN) (mul_le_mul_left' ?_ B)
    refine pow_le_pow_of_le_one (by simp) hr.le ?_
    calc n ≤ N := hNge
      _ = 1 * N := (one_mul N).symm
      _ ≤ j * N := Nat.mul_le_mul_right N hj
  have hmain := valuation_factorial_mul_esymm_le v hxu hxps
    (j := x.card) (by omega) le_rfl
  rw [multiset_esymm_card, Valuation.map_mul,
    valuation_multiset_prod_eq_one v hxu, mul_one, hxcard, ← hc] at hmain
  exact absurd hmain (not_le.2 hn)

/-- **Corvaja–Zannier's Lemma 4 at the level of an arbitrary number field, for an exponent set
closed under multiplication by `1, …, K`, where `K` bounds the TIE SIZE at `v`** — and now
*unconditionally*: if the maximum of the valuations is `> 1` and attained at most `K` times, the
power sums `Σ_w w^N` cannot have denominators dividing a fixed `q` along such an exponent set.
Both the no-tie case (`K = 1`) and every tie size are handled by
`valuation_sum_unit_pow_mulClosed`.

Taking `K = |R|` gives `false_of_bounded_den_mulClosed` below.  Taking `K = 2` needs only closure
under **doubling**, which the cofiniteness dichotomy
`tracePowSum_int_of_near_int_of_den_lt` actually supplies. -/
theorem false_of_bounded_den_tie_le {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {R : Multiset L} {z : L} (hzR : z ∈ R) (hz1 : 1 < v.valuation L z)
    (hmax : ∀ w ∈ R, v.valuation L w ≤ v.valuation L z)
    {K : ℕ} (hK : (R.filter (fun w ↦ v.valuation L w = v.valuation L z)).card ≤ K)
    {q : ℕ} (hq : 0 < q) {S : Set ℕ} (hS : S.Infinite)
    (hmulS : ∀ N ∈ S, ∀ j, 0 < j → j ≤ K → j * N ∈ S)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : L) * (R.map (· ^ N)).sum = (m : L)) : False := by
  classical
  set V : WithZero (Multiplicative ℤ) := v.valuation L z with hV
  have hV0 : (0 : WithZero (Multiplicative ℤ)) < V := lt_trans zero_lt_one hz1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hV
    simp at hV
    exact absurd hV hV0.ne'
  set W : Multiset L := R.filter (fun w ↦ v.valuation L w = V) with hW
  set Rest : Multiset L := R.filter (fun w ↦ ¬ (v.valuation L w = V)) with hRest
  have hWmem : ∀ w ∈ W, w ∈ R ∧ v.valuation L w = V := by
    intro w hw
    exact Multiset.mem_filter.1 (show w ∈ R.filter (fun w ↦ v.valuation L w = V) from hw)
  have hRestlt : ∀ w ∈ Rest, v.valuation L w < V := by
    intro w hw
    obtain ⟨h1, h2⟩ := Multiset.mem_filter.1
      (show w ∈ R.filter (fun w ↦ ¬ (v.valuation L w = V)) from hw)
    exact lt_of_le_of_ne (hmax w h1) h2
  have hzW : z ∈ W := Multiset.mem_filter.2 ⟨hzR, rfl⟩
  have hsplit : W + Rest = R := Multiset.filter_add_not _ _
  -- the bound coming from `q U_N ∈ ℤ`
  have hqv0 : v.valuation L (q : L) ≠ 0 := by
    simp only [ne_eq, Valuation.zero_iff, Nat.cast_eq_zero]
    omega
  have hUbound : ∀ N ∈ S, v.valuation L ((R.map (· ^ N)).sum) ≤ (v.valuation L (q : L))⁻¹ := by
    intro N hN
    obtain ⟨m, hm⟩ := hu N hN
    have hmv : v.valuation L (m : L) ≤ 1 := by
      rw [show ((m : L)) = algebraMap (NumberField.RingOfIntegers L) L
          (m : NumberField.RingOfIntegers L) from
        (map_intCast (algebraMap (NumberField.RingOfIntegers L) L) m).symm]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _
    have h1 : v.valuation L (q : L) * v.valuation L ((R.map (· ^ N)).sum) ≤ 1 := by
      rw [← Valuation.map_mul, hm]; exact hmv
    calc v.valuation L ((R.map (· ^ N)).sum)
        = (v.valuation L (q : L))⁻¹ * (v.valuation L (q : L)
            * v.valuation L ((R.map (· ^ N)).sum)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hqv0, one_mul]
      _ ≤ (v.valuation L (q : L))⁻¹ * 1 := by exact mul_le_mul_left' h1 _
      _ = (v.valuation L (q : L))⁻¹ := mul_one _
  have hc1 : 1 ≤ W.card := Multiset.card_pos.2 (fun h ↦ by simp [h] at hzW)
  have hWR : W.card ≤ K := by rw [hW]; exact hK
  -- normalize the dominant conjugates by `z`
  set U : Multiset L := W.map (fun w ↦ w / z) with hU
  have hUunit : ∀ u ∈ U, v.valuation L u = 1 := by
    intro u hu'
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu'
    rw [Valuation.map_div, (hWmem w hw).2, ← hV]
    exact div_self (hV0.ne')
  have hUcard : U.card = W.card := by rw [hU, Multiset.card_map]
  -- a uniform bound `r₀ < V` for the non-dominant conjugates
  obtain ⟨r₀, hr₀V, hr₀⟩ : ∃ r₀ : WithZero (Multiplicative ℤ), r₀ < V ∧
      ∀ w ∈ Rest, v.valuation L w ≤ r₀ := by
    by_cases hRe : Rest = 0
    · exact ⟨0, hV0, fun w hw ↦ by simp [hRe] at hw⟩
    · obtain ⟨y, hy, hymax⟩ := exists_max_image_multiset Rest (v.valuation L) hRe
      exact ⟨v.valuation L y, hRestlt y hy, hymax⟩
  set r : WithZero (Multiplicative ℤ) := max V⁻¹ (r₀ / V) with hr
  have hVinv1 : V⁻¹ < 1 := by
    rw [inv_lt_one₀ hV0]
    exact hz1
  have hr1 : r < 1 := max_lt hVinv1 (by rw [div_lt_one₀ hV0]; exact hr₀V)
  set B : WithZero (Multiplicative ℤ) := max ((v.valuation L (q : L))⁻¹) 1 with hB
  have hB0 : B ≠ 0 := by
    intro h
    have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ B := le_max_right _ _
    rw [h] at h1
    exact (not_le.2 zero_lt_one) h1
  refine valuation_sum_unit_pow_mulClosed v hUunit (by omega) hS ?_ hB0 hr1 ?_
  · intro N hN j hj hjU
    exact hmulS N hN j hj (by omega)
  intro N hN
  -- `Σ_u u^N = (Σ_{w ∈ W} w^N) / z^N`
  have hUsum : (U.map (· ^ N)).sum = ((W.map (· ^ N)).sum) / z ^ N := by
    rw [hU, Multiset.map_map]
    rw [show ((· ^ N) ∘ fun w ↦ w / z) = (fun w ↦ w ^ N / z ^ N) from by
      funext w; simp [div_pow]]
    exact Multiset.sum_map_div _ _ _
  have hWsum : (W.map (· ^ N)).sum
      = (R.map (· ^ N)).sum - (Rest.map (· ^ N)).sum := by
    rw [← hsplit, Multiset.map_add, Multiset.sum_add]; ring
  have h1 : v.valuation L ((W.map (· ^ N)).sum) ≤ max ((v.valuation L (q : L))⁻¹) (r₀ ^ N) := by
    rw [hWsum]
    refine le_trans (Valuation.map_sub _ _ _) (max_le_max (hUbound N hN) ?_)
    refine valuation_multiset_sum_le v _ ?_
    intro y hy
    obtain ⟨w, hw, hyw⟩ := Multiset.mem_map.1 hy
    rw [← hyw, map_pow]
    exact pow_le_pow_left₀ (by simp) (hr₀ w hw) N
  have h2 : v.valuation L ((U.map (· ^ N)).sum)
      ≤ max ((v.valuation L (q : L))⁻¹) (r₀ ^ N) / V ^ N := by
    rw [hUsum, Valuation.map_div, map_pow, ← hV, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_right' h1 _
  refine le_trans h2 ?_
  have hrV : (1 : WithZero (Multiplicative ℤ)) ≤ r * V := by
    calc (1 : WithZero (Multiplicative ℤ)) = V⁻¹ * V := (inv_mul_cancel₀ hV0.ne').symm
      _ ≤ r * V := mul_le_mul_right' (le_max_left _ _) _
  have hr0V : r₀ ≤ r * V := by
    calc r₀ = (r₀ / V) * V := (div_mul_cancel₀ r₀ hV0.ne').symm
      _ ≤ r * V := mul_le_mul_right' (le_max_right _ _) _
  rw [div_le_iff₀ (pow_pos hV0 N), mul_assoc, ← mul_pow]
  refine max_le ?_ ?_
  · calc (v.valuation L (q : L))⁻¹ ≤ B := le_max_left _ _
      _ = B * 1 := (mul_one _).symm
      _ ≤ B * (r * V) ^ N := mul_le_mul_left' (one_le_pow₀ hrV) _
  · calc r₀ ^ N ≤ (r * V) ^ N := pow_le_pow_left₀ (by simp) hr0V N
      _ = 1 * (r * V) ^ N := (one_mul _).symm
      _ ≤ B * (r * V) ^ N := mul_le_mul_right' (le_max_right _ _) _

/-- `false_of_bounded_den_tie_le` at `K = |R|`: no tie-size hypothesis, but the exponent set must be
closed under multiplication by every `j ≤ |R|`. -/
theorem false_of_bounded_den_mulClosed {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {R : Multiset L} {z : L} (hzR : z ∈ R) (hz1 : 1 < v.valuation L z)
    (hmax : ∀ w ∈ R, v.valuation L w ≤ v.valuation L z)
    {q : ℕ} (hq : 0 < q) {S : Set ℕ} (hS : S.Infinite)
    (hmulS : ∀ N ∈ S, ∀ j, 0 < j → j ≤ R.card → j * N ∈ S)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : L) * (R.map (· ^ N)).sum = (m : L)) : False := by
  classical
  exact false_of_bounded_den_tie_le v hzR hz1 hmax
    (K := R.card) (Multiset.card_le_card (Multiset.filter_le _ _)) hq hS hmulS hu

/-- **Corvaja–Zannier's Lemma 4's first branch, unconditionally**, for a multiplicatively-closed
exponent set: bounded denominators of the trace power sums `U_N = Tr(α^N)` along an infinite set of
exponents closed under multiplication by `1, …, deg α` force `α` to be an **algebraic integer** —
with no nondegeneracy hypothesis and hence no `α^l ∈ ℚ` escape branch.  (Replaces
`isIntegral_of_bounded_den_of_nondegenerate`, which rested on the deleted leaf.) -/
theorem isIntegral_of_bounded_den_mulClosed {α : ℝ} (halg : IsIntegral ℚ α) {q : ℕ}
    (hq : 0 < q) {S : Set ℕ} (hS : S.Infinite)
    (hmulS : ∀ N ∈ S, ∀ j, 0 < j → j * N ∈ S)
    (hu : ∀ N ∈ S, ∃ m : ℤ, (q : ℂ) * tracePowSum α N = (m : ℂ)) :
    IsIntegral ℤ α := by
  by_contra hnint
  obtain ⟨v, z, hzR, hz1, hmax⟩ := exists_dominant_max halg hnint
  exact false_of_bounded_den_mulClosed v hzR hz1 hmax hq hS
    (fun N hN j hj _ ↦ hmulS N hN j hj) (conj_bounded_den hu)


/-! ### The archimedean half: near-integrality for ALL large `n`, and denominator growth

A separate, unconditional constraint, and the one place where the *archimedean* hypotheses of
Dubickas's Theorem 1 bite on the arithmetic of the conjugates.  Along the pseudo-Pisot index set the
trace power sums are *exactly* integers; the observation here is that once **one** pseudo-Pisot
exponent `n₁` is available, every conjugate either collapses onto `α^(2^n₁)` (and then onto
`α^(2^n)` for every `n ≥ n₁`) or lies in the open unit disc, so for **all** large `n`

    2 U_(2^n) = k · (2 α^(2^n)) + o(1) = k · (2 y_n) + o(1),   k = #collapsing conjugates,

a near-integer with a *geometrically* small error.  Hence `tracePowSum_den_grows`: for every large
`n`, either `2 U_(2^n) ∈ ℤ` or its denominator exceeds `(C₂ r^(2^n))⁻¹`, which grows like
`α^(2^n)`.  This replaces the sparse index set by a cofinite one at the price of "near-integer"
instead of "integer" — see `PROBE-DUBICKAS-NOSUBSPACE.md` for why that trade matters (the `p`-adic
leaf is *false* for arbitrarily sparse exponent sets). -/


/-- A rational number that is *not* an integer stays away from `ℤ` by `1 / den`. -/
theorem one_div_den_le_dist_int {u : ℚ} (hu : u.den ≠ 1) (m : ℤ) :
    1 / (u.den : ℝ) ≤ |(u : ℝ) - (m : ℝ)| := by
  have hd0 : 0 < u.den := u.pos
  have hne : u - (m : ℚ) ≠ 0 := by
    intro h
    have : u = (m : ℚ) := by linarith [sub_eq_zero.1 h]
    rw [this] at hu
    simp at hu
  have hden : (u - (m : ℚ)).den = u.den := by
    simpa using Rat.sub_intCast_den u m
  have h1 : 1 / ((u - (m : ℚ)).den : ℝ) ≤ |((u - (m : ℚ) : ℚ) : ℝ)| := by
    have h2 : 1 ≤ |(u - (m : ℚ)).num| := by
      exact Int.one_le_abs (Rat.num_ne_zero.2 hne)
    rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((u - (m:ℚ)).den : ℝ))]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    calc (1:ℝ) ≤ (|(u - (m : ℚ)).num| : ℝ) := by exact_mod_cast h2
      _ = |((u - (m : ℚ)).num : ℝ)| := rfl
  rw [hden] at h1
  refine le_trans h1 (le_of_eq ?_)
  push_cast
  ring_nf



private theorem multiset_sum_const {M : Type*} [AddCommMonoid M] {s : Multiset M} {b : M}
    (h : ∀ x ∈ s, x = b) : s.sum = s.card • b := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.sum_cons, Multiset.card_cons, succ_nsmul,
        h a (Multiset.mem_cons_self _ _), ih (fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)),
        add_comm]

/-- **The trace power sums are near-integers for ALL large `n`** — not merely along the sparse
pseudo-Pisot index set.  Hypothesis `hsplit` (available at the call site, in the same way `hsmall`
is: each conjugate either collapses onto `α^(2^n₁)` at one pseudo-Pisot exponent, or lies inside
the open unit disc) makes `2 U_(2^n) = k · (2 α^(2^n)) + o(1)` with `k` the number of collapsing
conjugates, and `2 α^(2^n)` is within `2C α^(−2^n)` of the integer `2 y_n`. -/
theorem tracePowSum_near_int {α : ℝ} (halg : IsIntegral ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C)
    {y : ℕ → ℝ} {n₀ : ℕ} (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n)
    {n₁ : ℕ} (hsplit : ∀ w ∈ (minpoly ℚ α).aroots ℂ,
      w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ) ∨ ‖w‖ < 1) :
    ∃ C₂ r : ℝ, 0 < C₂ ∧ 0 ≤ r ∧ r < 1 ∧ ∀ n ≥ max n₀ n₁, ∃ m : ℤ,
      ‖2 * tracePowSum α (2 ^ n) - (m : ℂ)‖ ≤ C₂ * r ^ 2 ^ n := by
  classical
  have hα0 : (0 : ℝ) < α := by linarith
  set R : Multiset ℂ := (minpoly ℚ α).aroots ℂ with hR
  set Kf : Multiset ℂ := R.filter (fun w ↦ w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ)) with hKf
  set Sm : Multiset ℂ := R.filter (fun w ↦ ¬ (w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ))) with hSm
  have hadd : Kf + Sm = R := Multiset.filter_add_not _ _
  have hSmnorm : ∀ w ∈ Sm, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := Multiset.mem_filter.1
      (show w ∈ R.filter (fun w ↦ ¬ (w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ))) from hw)
    exact (hsplit w h1).resolve_left h2
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ w ∈ Sm, ‖w‖ ≤ ρ := by
    by_cases hSe : Sm = 0
    · exact ⟨0, le_rfl, by norm_num, fun w hw ↦ by simp [hSe] at hw⟩
    · obtain ⟨w₀, hw₀, hmax⟩ := exists_max_image_multiset Sm (fun w ↦ ‖w‖) hSe
      exact ⟨‖w₀‖, norm_nonneg _, hSmnorm w₀ hw₀, hmax⟩
  set k : ℕ := Kf.card with hk
  refine ⟨2 * (k : ℝ) * C + 2 * (Sm.card : ℝ) + 1, max α⁻¹ ρ, by positivity,
    le_trans (by positivity) (le_max_right _ _), max_lt ?_ hρ1, ?_⟩
  · rw [inv_lt_one₀ hα0]; exact hα
  intro n hn
  have hn₀ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨kn, hkn⟩ := hyint n
  refine ⟨k * kn, ?_⟩
  -- the collapsing conjugates all contribute `α^(2^n)`
  have hcol : ∀ w ∈ Kf, w ^ 2 ^ n = ((α ^ 2 ^ n : ℝ) : ℂ) := by
    intro w hw
    obtain ⟨-, h2⟩ := Multiset.mem_filter.1
      (show w ∈ R.filter (fun w ↦ w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ)) from hw)
    have hsp : (2 : ℕ) ^ n = 2 ^ n₁ * 2 ^ (n - n₁) := by
      rw [← pow_add]; congr 1; omega
    rw [hsp, pow_mul, h2]
    push_cast
    ring
  have hKsum : (Kf.map (· ^ 2 ^ n)).sum = (k : ℂ) * ((α ^ 2 ^ n : ℝ) : ℂ) := by
    rw [multiset_sum_const (s := Kf.map (· ^ 2 ^ n)) (b := ((α ^ 2 ^ n : ℝ) : ℂ))
      (fun x hx ↦ by
        obtain ⟨w, hw, hxw⟩ := Multiset.mem_map.1 hx
        rw [← hxw]; exact hcol w hw)]
    rw [Multiset.card_map, hk, nsmul_eq_mul]
  have hTsplit : tracePowSum α (2 ^ n)
      = (k : ℂ) * ((α ^ 2 ^ n : ℝ) : ℂ) + (Sm.map (· ^ 2 ^ n)).sum := by
    rw [tracePowSum, ← hR, ← hadd, Multiset.map_add, Multiset.sum_add, hKsum]
  -- bound the two error terms
  have hSbnd : ‖(Sm.map (· ^ 2 ^ n)).sum‖ ≤ (Sm.card : ℝ) * ρ ^ 2 ^ n := by
    refine le_trans (norm_multiset_sum_le _) ?_
    have := Multiset.sum_le_card_nsmul ((Sm.map (· ^ 2 ^ n)).map (‖·‖)) (ρ ^ 2 ^ n)
      (by
        intro x hx
        obtain ⟨z, hz, hxz⟩ := Multiset.mem_map.1 hx
        obtain ⟨w, hw, hwz⟩ := Multiset.mem_map.1 hz
        rw [← hxz, ← hwz, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ w hw) _)
    simpa [nsmul_eq_mul, mul_comm] using this
  have hApprox : |2 * α ^ 2 ^ n - (kn : ℝ)| ≤ 2 * C / α ^ 2 ^ n := by
    have h := hbnd n hn₀
    rw [show 2 * α ^ 2 ^ n - (kn : ℝ) = -(2 * (y n - α ^ 2 ^ n)) from by rw [← hkn]; ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      show 2 * C / α ^ 2 ^ n = 2 * (C / α ^ 2 ^ n) from by ring]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  -- assemble
  have hdiff : 2 * tracePowSum α (2 ^ n) - ((k * kn : ℤ) : ℂ)
      = (k : ℂ) * ((2 * α ^ 2 ^ n - (kn : ℝ) : ℝ) : ℂ) + 2 * (Sm.map (· ^ 2 ^ n)).sum := by
    rw [hTsplit]
    push_cast
    ring
  rw [hdiff]
  have h1 : ‖(k : ℂ) * ((2 * α ^ 2 ^ n - (kn : ℝ) : ℝ) : ℂ)‖ ≤ (k : ℝ) * (2 * C / α ^ 2 ^ n) := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hApprox (by positivity)
  have h2 : ‖(2 : ℂ) * (Sm.map (· ^ 2 ^ n)).sum‖ ≤ 2 * ((Sm.card : ℝ) * ρ ^ 2 ^ n) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hSbnd (by norm_num)
  refine le_trans (norm_add_le _ _) ?_
  have hrα : (α ^ 2 ^ n)⁻¹ ≤ (max α⁻¹ ρ) ^ 2 ^ n := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have hrρ : ρ ^ 2 ^ n ≤ (max α⁻¹ ρ) ^ 2 ^ n := pow_le_pow_left₀ hρ0 (le_max_right _ _) _
  have hrpos : (0:ℝ) < (max α⁻¹ ρ) ^ 2 ^ n := by
    have : (0:ℝ) < max α⁻¹ ρ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    positivity
  have hCα : (k : ℝ) * (2 * C / α ^ 2 ^ n) ≤ 2 * (k : ℝ) * C * (max α⁻¹ ρ) ^ 2 ^ n := by
    rw [div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_left hrα (by positivity : (0:ℝ) ≤ (k:ℝ) * (2 * C))
    calc (k : ℝ) * (2 * C / α ^ 2 ^ n) = (k:ℝ) * (2*C) * (α ^ 2 ^ n)⁻¹ := by
          rw [div_eq_mul_inv]; ring
      _ ≤ (k:ℝ) * (2*C) * (max α⁻¹ ρ) ^ 2 ^ n := by
          exact mul_le_mul_of_nonneg_left hrα (by positivity)
      _ = 2 * (k : ℝ) * C * (max α⁻¹ ρ) ^ 2 ^ n := by ring
  have hSm2 : 2 * ((Sm.card : ℝ) * ρ ^ 2 ^ n)
      ≤ 2 * (Sm.card : ℝ) * (max α⁻¹ ρ) ^ 2 ^ n := by
    have := mul_le_mul_of_nonneg_left hrρ (by positivity : (0:ℝ) ≤ 2 * (Sm.card : ℝ))
    calc 2 * ((Sm.card : ℝ) * ρ ^ 2 ^ n) = 2 * (Sm.card : ℝ) * ρ ^ 2 ^ n := by ring
      _ ≤ 2 * (Sm.card : ℝ) * (max α⁻¹ ρ) ^ 2 ^ n := this
  nlinarith [h1, h2, hCα, hSm2, hrpos]


/-- **The denominators of the trace power sums grow geometrically unless they are `1`.**  The
quantitative form of `tracePowSum_near_int`: for every large `n`, either `2 U_(2^n)` is a rational
*integer*, or its denominator is at least `(C₂ r^(2^n))⁻¹` — which grows like `α^(2^n)` because
`r ≤ max(α⁻¹, ρ)`.

This is the Liouville half of the `α^l ∈ ℚ` / integrality dichotomy, and it needs **no**
Diophantine input beyond the hypotheses of Dubickas's Theorem 1.  Combined with the valuation
analysis (`no_bounded_den_of_unique_max_valuation`) it says: if `α` is not an algebraic integer and
the dominant conjugate valuation at some prime is unique, then that local valuation is at least `α`
— a genuine constraint on `α`, recorded in `PROBE-DUBICKAS-NOSUBSPACE.md`. -/
theorem tracePowSum_den_grows {α : ℝ} (halg : IsIntegral ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C)
    {y : ℕ → ℝ} {n₀ : ℕ} (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n)
    {n₁ : ℕ} (hsplit : ∀ w ∈ (minpoly ℚ α).aroots ℂ,
      w ^ 2 ^ n₁ = ((α ^ 2 ^ n₁ : ℝ) : ℂ) ∨ ‖w‖ < 1) :
    ∃ C₂ r : ℝ, 0 < C₂ ∧ 0 ≤ r ∧ r < 1 ∧ ∀ n ≥ max n₀ n₁, ∀ u : ℚ,
      tracePowSum α (2 ^ n) = ((u : ℚ) : ℂ) →
        (2 * u).den = 1 ∨ 1 ≤ C₂ * r ^ 2 ^ n * ((2 * u).den : ℝ) := by
  obtain ⟨C₂, r, hC₂, hr0, hr1, hnear⟩ :=
    tracePowSum_near_int halg hα hC hyint hbnd hsplit
  refine ⟨C₂, r, hC₂, hr0, hr1, ?_⟩
  intro n hn u hu
  by_cases hden : (2 * u).den = 1
  · exact Or.inl hden
  refine Or.inr ?_
  obtain ⟨m, hm⟩ := hnear n hn
  have hcast : 2 * tracePowSum α (2 ^ n) - (m : ℂ) = ((((2 * u : ℚ) : ℝ) - (m : ℝ) : ℝ) : ℂ) := by
    rw [hu]; push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hm
  have hlow := one_div_den_le_dist_int hden m
  have hd0 : (0 : ℝ) < ((2 * u).den : ℝ) := by positivity
  have h1 : 1 / ((2 * u).den : ℝ) ≤ C₂ * r ^ 2 ^ n := le_trans hlow hm
  rw [div_le_iff₀ hd0] at h1
  linarith [h1]

/-! ### The denominator ceiling, and the cofiniteness dichotomy

`tracePowSum_den_grows` is a *lower* bound on `den(2 U_(2^n))` whenever that denominator is not `1`.
The missing half — supplied here — is the matching **ceiling**: `D w` is an algebraic integer for
every conjugate `w` of `α`, for one positive integer `D` (`exists_common_integral_multiple`), so
`D^N U_N = Σ_w (D w)^N` is a rational algebraic integer and therefore `den(U_N) ∣ D^N`
(`exists_tracePowSum_den_dvd`).

The two halves together give the **cofiniteness dichotomy**
(`tracePowSum_int_of_near_int_of_den_lt`): if `D r < 1`, where `r = max(α⁻¹, ρ) < 1` is the rate
produced by `tracePowSum_near_int`, then `2 U_(2^n)` is *exactly* a rational integer for **every**
large `n`.  The exponent set is then cofinite in the powers of `2`, hence closed under doubling,
which is exactly the hypothesis of `valuation_sum_unit_pow_card_two` / `false_of_two_unit_pow_sums_small`.

So the seventh lap's "sparsity" obstruction has become the single inequality `D ≥ min(α, ρ⁻¹)`, a
statement about the Mahler measure of a growth constant.  See `PROBE-DUBICKAS-NOSUBSPACE.md`
(eighth lap) — including the `ζ_3` witness showing that *doubling* closure alone cannot replace
closure under multiplication by `1, …, k` once the tie size `k` is `3`. -/

/-- A multiset sum of algebraic integers is an algebraic integer. -/
theorem isIntegral_multiset_sum {s : Multiset ℂ} (h : ∀ x ∈ s, IsIntegral ℤ x) :
    IsIntegral ℤ s.sum := by
  induction s using Multiset.induction with
  | empty => simpa using isIntegral_zero
  | cons a t ih =>
      rw [Multiset.sum_cons]
      exact (h a (Multiset.mem_cons_self _ _)).add
        (ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx))

/-- **One integral multiplier for every conjugate at once**: there is a positive integer `D` with
`D w` an algebraic integer for *every* conjugate `w` of `α`.  (Each conjugate has its own
multiplier; the product of the finitely many of them works for all, and `conjField α` is a
`NumberField`, so mathlib's `exists_integral_multiples` supplies them in one step.) -/
theorem exists_common_integral_multiple {α : ℝ} (halg : IsIntegral ℚ α) :
    ∃ D : ℕ, 0 < D ∧ ∀ w ∈ (minpoly ℚ α).aroots ℂ, IsIntegral ℤ ((D : ℂ) * w) := by
  classical
  obtain ⟨D₀, hD₀, hint⟩ :=
    exists_integral_multiples ℤ ℚ (L := conjField α) (conjMultiset α).toFinset
  refine ⟨D₀.natAbs, Int.natAbs_pos.2 hD₀, ?_⟩
  intro w hw
  rw [← conjMultiset_map_coe α] at hw
  obtain ⟨w', hw', rfl⟩ := Multiset.mem_map.1 hw
  have h1 : IsIntegral ℤ (D₀ • w') := hint w' (Multiset.mem_toFinset.2 hw')
  have h1' : IsIntegral ℤ ((D₀ : conjField α) * w') := by rwa [← zsmul_eq_mul]
  have h2 := h1'.map ((algebraMap (conjField α) ℂ).toIntAlgHom)
  simp only [RingHom.toIntAlgHom_apply, map_mul, map_intCast,
    IntermediateField.algebraMap_apply] at h2
  have hk : ((D₀.natAbs : ℤ)) = D₀ ∨ ((D₀.natAbs : ℤ)) = -D₀ := by
    rcases Int.natAbs_eq D₀ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  rw [show ((D₀.natAbs : ℕ) : ℂ) = ((D₀.natAbs : ℤ) : ℂ) from (Int.cast_natCast _).symm]
  rcases hk with h | h
  · rw [h]; exact h2
  · rw [h]; simpa [neg_mul] using h2.neg

/-- **The denominator ceiling: `den(U_N) ∣ D^N`.**  `D^N U_N = Σ_w (D w)^N` is a sum of algebraic
integers, and it is rational (`tracePowSum_rat`), hence a rational integer. -/
theorem exists_tracePowSum_den_dvd {α : ℝ} (halg : IsIntegral ℚ α) :
    ∃ D : ℕ, 0 < D ∧ ∀ (N : ℕ) (u : ℚ), tracePowSum α N = ((u : ℚ) : ℂ) →
      ∃ m : ℤ, (D : ℚ) ^ N * u = (m : ℚ) := by
  classical
  obtain ⟨D, hD0, hDint⟩ := exists_common_integral_multiple halg
  refine ⟨D, hD0, ?_⟩
  intro N u hu
  have hsum : (D : ℂ) ^ N * tracePowSum α N
      = (((minpoly ℚ α).aroots ℂ).map (fun w ↦ ((D : ℂ) * w) ^ N)).sum := by
    rw [tracePowSum, ← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro w _
    rw [mul_pow]
  have hintC : IsIntegral ℤ ((D : ℂ) ^ N * tracePowSum α N) := by
    rw [hsum]
    refine isIntegral_multiset_sum ?_
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    exact (hDint w hw).pow N
  have hcast : (((((D : ℚ) ^ N * u : ℚ)) : ℚ) : ℂ) = (D : ℂ) ^ N * tracePowSum α N := by
    rw [hu]; push_cast; ring
  have hintQ : IsIntegral ℤ (((D : ℚ) ^ N * u : ℚ)) := by
    refine (isIntegral_algHom_iff ((Rat.castHom ℂ).toIntAlgHom) Rat.cast_injective).1 ?_
    rw [show ((Rat.castHom ℂ).toIntAlgHom) ((D : ℚ) ^ N * u) = ((((D : ℚ) ^ N * u : ℚ)) : ℂ) from rfl,
      hcast]
    exact hintC
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintQ
  exact ⟨m, by exact_mod_cast hm.symm⟩

/-- **The cofiniteness dichotomy** (eighth lap).  Suppose `2 U_(2^n)` is within `C₂ r^(2^n)` of a
rational integer for all large `n` — which `tracePowSum_near_int` supplies once *one* pseudo-Pisot
exponent exists — and the denominator base `D` of `exists_tracePowSum_den_dvd` satisfies `D r < 1`.
Then `2 U_(2^n)` is **exactly** a rational integer for every large `n`, so the exact-integrality
exponent set is cofinite in the powers of `2`.

This is the step that converts the sparse pseudo-Pisot index set into a doubling-closed one; what it
costs is precisely the inequality `D < r⁻¹`. -/
theorem tracePowSum_int_of_near_int_of_den_lt {α : ℝ} {C₂ r : ℝ} (hC₂ : 0 < C₂) (hr0 : 0 ≤ r)
    {n₂ : ℕ}
    (hnear : ∀ n ≥ n₂, ∃ m : ℤ, ‖2 * tracePowSum α (2 ^ n) - (m : ℂ)‖ ≤ C₂ * r ^ 2 ^ n)
    {D : ℕ} (hD0 : 0 < D)
    (hDden : ∀ (N : ℕ) (u : ℚ), tracePowSum α N = ((u : ℚ) : ℂ) →
      ∃ m : ℤ, (D : ℚ) ^ N * u = (m : ℚ))
    (hDr : (D : ℝ) * r < 1) :
    ∃ n₃, ∀ n ≥ n₃, ∀ u : ℚ, tracePowSum α (2 ^ n) = ((u : ℚ) : ℂ) → (2 * u).den = 1 := by
  classical
  have hs0 : (0 : ℝ) ≤ (D : ℝ) * r := by positivity
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / C₂ by positivity) hDr
  refine ⟨max n₂ j, ?_⟩
  intro n hn u hu
  by_contra hden
  obtain ⟨m, hm⟩ := hnear n (le_trans (le_max_left _ _) hn)
  -- the Liouville lower bound
  have hcast : 2 * tracePowSum α (2 ^ n) - (m : ℂ)
      = (((((2 * u : ℚ) : ℝ)) - (m : ℝ) : ℝ) : ℂ) := by
    rw [hu]; push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hm
  have hlow := one_div_den_le_dist_int hden m
  have hlow2 : 1 / (((2 * u).den : ℕ) : ℝ) ≤ C₂ * r ^ 2 ^ n := le_trans hlow hm
  -- the denominator ceiling
  obtain ⟨m', hm'⟩ := hDden (2 ^ n) u hu
  have hDQ0 : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD0
  have hdvd : (((2 * u).den : ℕ) : ℤ) ∣ ((D : ℤ) ^ 2 ^ n) := by
    have hE : (2 * u) = Rat.divInt (2 * m') ((D : ℤ) ^ 2 ^ n) := by
      rw [Rat.divInt_eq_div, eq_div_iff (by push_cast; positivity)]
      push_cast
      linear_combination (2 : ℚ) * hm'
    rw [hE]
    exact Rat.den_dvd _ _
  have hle : (((2 * u).den : ℕ) : ℝ) ≤ ((D : ℝ)) ^ 2 ^ n := by
    have h1 : (((2 * u).den : ℕ) : ℤ) ≤ ((D : ℤ) ^ 2 ^ n) :=
      Int.le_of_dvd (by positivity) hdvd
    exact_mod_cast h1
  have hd0 : (0 : ℝ) < (((2 * u).den : ℕ) : ℝ) := by
    have h := (2 * u).den_pos
    exact_mod_cast h
  -- combine: `1 ≤ C₂ (D r)^(2^n)`, contradicting the choice of `j`
  have hcr : (0 : ℝ) ≤ C₂ * r ^ 2 ^ n := by positivity
  have hstep : (1 : ℝ) ≤ C₂ * r ^ 2 ^ n * (D : ℝ) ^ 2 ^ n := by
    rw [div_le_iff₀ hd0] at hlow2
    calc (1 : ℝ) ≤ C₂ * r ^ 2 ^ n * (((2 * u).den : ℕ) : ℝ) := hlow2
      _ ≤ C₂ * r ^ 2 ^ n * (D : ℝ) ^ 2 ^ n := mul_le_mul_of_nonneg_left hle hcr
  have hjn : j ≤ 2 ^ n :=
    le_trans (le_trans (le_max_right n₂ j) hn) (Nat.le_of_lt Nat.lt_two_pow_self)
  have hpow : ((D : ℝ) * r) ^ 2 ^ n ≤ ((D : ℝ) * r) ^ j :=
    pow_le_pow_of_le_one hs0 hDr.le hjn
  have hfinal : C₂ * ((D : ℝ) * r) ^ 2 ^ n < 1 := by
    calc C₂ * ((D : ℝ) * r) ^ 2 ^ n ≤ C₂ * ((D : ℝ) * r) ^ j :=
          mul_le_mul_of_nonneg_left hpow hC₂.le
      _ < C₂ * (1 / C₂) := by exact mul_lt_mul_of_pos_left hj hC₂
      _ = 1 := by field_simp
  rw [mul_pow] at hfinal
  have hcomm : C₂ * r ^ 2 ^ n * (D : ℝ) ^ 2 ^ n
      = C₂ * ((D : ℝ) ^ 2 ^ n * r ^ 2 ^ n) := by ring
  rw [hcomm] at hstep
  linarith

/-- **The capstone of the eighth lap: an unconditional constraint on a growth constant.**
Assume (as `tracePowSum_near_int` delivers once *one* pseudo-Pisot exponent exists) that
`2 U_(2^n)` is within `C₂ r^(2^n)` of a rational integer for all large `n`, and that the denominator
base `D` of `exists_tracePowSum_den_dvd` satisfies `D r < 1`.  If moreover at every prime of
`conjField α` the dominant conjugate valuation is attained **at most twice**, then `α` is an
algebraic integer.

Route: `tracePowSum_int_of_near_int_of_den_lt` makes the exact-integrality exponent set cofinite in
the powers of `2`, hence **closed under doubling**; `false_of_bounded_den_tie_le` at `K = 2` then
needs nothing more.  Contrapositively: a non-integral growth constant must have `D ≥ r⁻¹`, or a
triple tie at some prime — and a triple tie forces a non-`2`-power root of unity among the ratios of
conjugates, which is Corvaja–Zannier's degenerate branch.  See `PROBE-DUBICKAS-NOSUBSPACE.md`. -/
theorem isIntegral_of_tie_le_two_of_den_lt {α : ℝ} (halg : IsIntegral ℚ α)
    {C₂ r : ℝ} (hC₂ : 0 < C₂) (hr0 : 0 ≤ r) {n₂ : ℕ}
    (hnear : ∀ n ≥ n₂, ∃ m : ℤ, ‖2 * tracePowSum α (2 ^ n) - (m : ℂ)‖ ≤ C₂ * r ^ 2 ^ n)
    {D : ℕ} (hD0 : 0 < D)
    (hDden : ∀ (N : ℕ) (u : ℚ), tracePowSum α N = ((u : ℚ) : ℂ) →
      ∃ m : ℤ, (D : ℚ) ^ N * u = (m : ℚ))
    (hDr : (D : ℝ) * r < 1)
    (htie : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (conjField α))) (z : conjField α),
      ((conjMultiset α).filter (fun w ↦ v.valuation (conjField α) w
        = v.valuation (conjField α) z)).card ≤ 2) :
    IsIntegral ℤ α := by
  classical
  by_contra hnint
  obtain ⟨n₃, hn₃⟩ := tracePowSum_int_of_near_int_of_den_lt hC₂ hr0 hnear hD0 hDden hDr
  -- the exact-integrality exponent set, cofinite in the powers of `2`
  set S : Set ℕ := (fun n : ℕ ↦ 2 ^ n) '' {n : ℕ | n₃ ≤ n} with hSdef
  have hpowinj : Function.Injective (fun n : ℕ ↦ 2 ^ n) := fun a b h ↦ by
    exact Nat.pow_right_injective (le_refl 2) h
  have hSinf : S.Infinite := by
    refine Set.Infinite.image (Set.injOn_of_injective hpowinj) ?_
    exact Set.Ici_infinite n₃
  have hdbl : ∀ N ∈ S, ∀ j, 0 < j → j ≤ 2 → j * N ∈ S := by
    intro N hN j hj hj2
    obtain ⟨n, hn, rfl⟩ := hN
    interval_cases j
    · exact ⟨n, hn, by ring⟩
    · exact ⟨n + 1, by simpa using le_trans hn (Nat.le_succ n), by ring⟩
  -- on `S` the trace power sums are exactly half-integers
  have hu : ∀ N ∈ S, ∃ m : ℤ, ((2 : ℕ) : ℂ) * tracePowSum α N = (m : ℂ) := by
    intro N hN
    obtain ⟨n, hn, rfl⟩ := hN
    obtain ⟨u, hu'⟩ := tracePowSum_rat halg (2 ^ n)
    have hden := hn₃ n hn u hu'
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (2 * u : ℚ) = (m : ℚ) := by
      refine ⟨(2 * u).num, ?_⟩
      rw [← Rat.num_div_den (2 * u), hden]
      simp
    refine ⟨m, ?_⟩
    have hc : (((2 * u : ℚ)) : ℂ) = (((m : ℚ)) : ℂ) := by rw [hm]
    rw [hu']
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨v, z, hzR, hz1, hmax⟩ := exists_dominant_max halg hnint
  exact false_of_bounded_den_tie_le v hzR hz1 hmax (K := 2) (htie v z)
    (q := 2) (by norm_num) hSinf hdbl (conj_bounded_den hu)

/-! ### The double tie closes elementarily — the residual is *sparsity*, not `p`-adic analysis

`valuation_two_le_of_two_unit_pow_sums` is the Graeffe identity
`2 (u₁u₂)^N = (u₁^N + u₂^N)² − (u₁^(2N) + u₂^(2N))` read through `v`: the left side has valuation
exactly `v 2` (the `u_i` are units), so the power sums at `N` and `2N` cannot both be highly
divisible.  Hence `false_of_two_unit_pow_sums_small` / `valuation_sum_unit_pow_card_two`: the local
leaf is **proved** for a double tie whenever the exponent set is closed under doubling, with no
nondegeneracy hypothesis at all.

The same collapse handles a tie of any size `k` as soon as the exponent set is closed under
multiplication by `1, …, k` — that is `valuation_sum_unit_pow_mulClosed` above, which subsumes this
section.  So the residual difficulty of the tie case is entirely the **sparsity** of the exponent
set: for `{2^n : n ∈ S}` with `S` merely infinite, neither this nor Strassmann applies. -/


/-- **Graeffe at `k = 2`.**  For `v`-units `u₁, u₂`,
`2 (u₁u₂)^N = (u₁^N + u₂^N)² − (u₁^(2N) + u₂^(2N))`, and the left side has valuation exactly
`v 2`.  So the two power sums at `N` and `2N` cannot *both* be highly divisible: the fixed nonzero
value `v 2` bounds them. -/
theorem valuation_two_le_of_two_unit_pow_sums {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {u₁ u₂ : L}
    (h₁ : v.valuation L u₁ = 1) (h₂ : v.valuation L u₂ = 1) (N : ℕ) :
    v.valuation L (2 : L) ≤ max ((v.valuation L (u₁ ^ N + u₂ ^ N)) ^ 2)
      (v.valuation L (u₁ ^ (2 * N) + u₂ ^ (2 * N))) := by
  have key : (2 : L) * (u₁ * u₂) ^ N
      = (u₁ ^ N + u₂ ^ N) ^ 2 - (u₁ ^ (2 * N) + u₂ ^ (2 * N)) := by
    rw [mul_comm 2 N, pow_mul, pow_mul, mul_pow]
    ring
  have hv : v.valuation L ((2 : L) * (u₁ * u₂) ^ N) = v.valuation L (2 : L) := by
    rw [Valuation.map_mul, map_pow, Valuation.map_mul, h₁, h₂]
    simp
  rw [← hv, key]
  refine le_trans (Valuation.map_sub _ _ _) (max_le_max ?_ le_rfl)
  rw [map_pow]

/-- **The tie case of Corvaja–Zannier's Lemma 4 for a *double* tie is elementary** — provided the
exponent set is closed under doubling.  Two `v`-units whose power sums decay geometrically along
such a set do not exist: `valuation_two_le_of_two_unit_pow_sums` pins the fixed nonzero `v 2`
below something that tends to `0`.

Historically the first closed instance of the tie case; `valuation_sum_unit_pow_mulClosed` above now
subsumes it at every tie size via Newton's identities, so this is kept as the self-contained Graeffe
argument (it needs no `esymm` machinery).  See `PROBE-DUBICKAS-NOSUBSPACE.md`. -/
theorem false_of_two_unit_pow_sums_small {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {u₁ u₂ : L}
    (h₁ : v.valuation L u₁ = 1) (h₂ : v.valuation L u₂ = 1)
    {S : Set ℕ} (hSne : ∃ N ∈ S, 0 < N) (hdbl : ∀ N ∈ S, 2 * N ∈ S)
    {B r : WithZero (Multiplicative ℤ)} (hB : B ≠ 0) (hr : r < 1)
    (hsum : ∀ N ∈ S, v.valuation L (u₁ ^ N + u₂ ^ N) ≤ B * r ^ N) : False := by
  classical
  set c : WithZero (Multiplicative ℤ) := v.valuation L (2 : L) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    simp only [ne_eq, Valuation.zero_iff]
    exact two_ne_zero
  have hc1 : c ≤ 1 := by
    rw [hc, show ((2 : L)) = ((2 : ℤ) : L) from by norm_num,
      show (((2 : ℤ)) : L) = algebraMap (NumberField.RingOfIntegers L) L ((2 : ℤ) : _) from
        (map_intCast (algebraMap (NumberField.RingOfIntegers L) L) 2).symm]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _
  obtain ⟨n, hn⟩ := exists_mul_pow_lt (B := B) (r := r) (c := c) hr hc0 hB
  -- an element of `S` above `n`, obtained by repeated doubling
  obtain ⟨N₀, hN₀S, hN₀⟩ := hSne
  have hpow : ∀ j : ℕ, N₀ * 2 ^ j ∈ S := by
    intro j
    induction j with
    | zero => simpa using hN₀S
    | succ j ih =>
        have := hdbl _ ih
        rw [show 2 * (N₀ * 2 ^ j) = N₀ * 2 ^ (j + 1) from by ring] at this
        exact this
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n ≤ N₀ * 2 ^ j := by
    refine ⟨n, le_trans ?_ (Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_two_pow_self)))⟩
    calc n = 1 * n := (one_mul n).symm
      _ ≤ N₀ * n := Nat.mul_le_mul_right _ hN₀
  set N : ℕ := N₀ * 2 ^ j with hN
  have hNS : N ∈ S := hpow j
  have hmono : ∀ M : ℕ, n ≤ M → B * r ^ M ≤ B * r ^ n := by
    intro M hM
    refine mul_le_mul_left' ?_ B
    exact pow_le_pow_of_le_one (by simp) hr.le hM
  have hx : B * r ^ N < c := lt_of_le_of_lt (hmono N hj) hn
  have hx2 : B * r ^ (2 * N) < c := lt_of_le_of_lt (hmono (2 * N) (by omega)) hn
  have hxle1 : B * r ^ N ≤ 1 := le_trans hx.le hc1
  have hsq : (v.valuation L (u₁ ^ N + u₂ ^ N)) ^ 2 < c := by
    refine lt_of_le_of_lt ?_ hx
    calc (v.valuation L (u₁ ^ N + u₂ ^ N)) ^ 2
        ≤ (B * r ^ N) ^ 2 := pow_le_pow_left₀ (by simp) (hsum N hNS) 2
      _ = (B * r ^ N) * (B * r ^ N) := by rw [sq]
      _ ≤ (B * r ^ N) * 1 := mul_le_mul_left' hxle1 _
      _ = B * r ^ N := mul_one _
  have h2 : v.valuation L (u₁ ^ (2 * N) + u₂ ^ (2 * N)) < c :=
    lt_of_le_of_lt (hsum (2 * N) (hdbl N hNS)) hx2
  have := valuation_two_le_of_two_unit_pow_sums v h₁ h₂ N
  rw [← hc] at this
  exact absurd this (not_le.2 (max_lt hsq h2))


/-- The tie case for a *double* tie and an exponent set closed under doubling, with no nondegeneracy
hypothesis.  Subsumed by `valuation_sum_unit_pow_mulClosed`; kept as the Graeffe route. -/
theorem valuation_sum_unit_pow_card_two {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {U : Multiset L} (hU : ∀ u ∈ U, v.valuation L u = 1) (hcard : U.card = 2)
    {S : Set ℕ} (hSne : ∃ N ∈ S, 0 < N) (hdbl : ∀ N ∈ S, 2 * N ∈ S)
    {B r : WithZero (Multiplicative ℤ)} (hB : B ≠ 0) (hr : r < 1)
    (hsum : ∀ N ∈ S, v.valuation L ((U.map (· ^ N)).sum) ≤ B * r ^ N) : False := by
  obtain ⟨u₁, u₂, hU12⟩ := Multiset.card_eq_two.1 hcard
  subst hU12
  refine false_of_two_unit_pow_sums_small v (hU u₁ (by simp)) (hU u₂ (by simp))
    hSne hdbl hB hr ?_
  intro N hN
  have := hsum N hN
  simpa using this

/-- Power sums of `v`-units have valuation `≤ 1`. -/
theorem valuation_psum_le_one {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {x : Multiset L} (hx : ∀ u ∈ x, v.valuation L u = 1) (n : ℕ) :
    v.valuation L (x.psum n) ≤ 1 := by
  rw [Multiset.psum_def]
  refine valuation_multiset_sum_le v _ ?_
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hy
  rw [map_pow, hx u hu, one_pow]

/-- **Refined Newton step.**  Only *some* power sums need to be small.  Let `D` be the set of
indices `j` with `v(p_j) ≤ ε`, and let `G` be any set of indices closed under the rule

> `j ∈ G → j ∈ D ∧ ∀ 1 ≤ i < j, (i ∈ G ∨ j − i ∈ D)`.

Then `v(j! · e_j) ≤ ε` for every `j ∈ G`.  (With `D = G = [1, k]` this is
`valuation_factorial_mul_esymm_le`.)  In Newton's identity the `i = 0` term is `p_j`, which is why
`j ∈ D` is needed; for `i ≥ 1` the term is `[(j−1)!/i!] · (i! e_i) · p_(j−i)`, small either because
`i ∈ G` or because `j − i ∈ D`. -/
theorem valuation_factorial_mul_esymm_le_of_closed {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {x : Multiset L} (hx : ∀ u ∈ x, v.valuation L u = 1)
    {ε : WithZero (Multiplicative ℤ)} {D G : Set ℕ}
    (hD : ∀ j ∈ D, 0 < j → j ≤ x.card → v.valuation L (x.psum j) ≤ ε)
    (hG : ∀ j ∈ G, j ∈ D ∧ ∀ i, 1 ≤ i → i < j → (i ∈ G ∨ (j - i) ∈ D)) :
    ∀ j ∈ G, 0 < j → j ≤ x.card → v.valuation L ((j.factorial : L) * x.esymm j) ≤ ε := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjG hj hjk
    obtain ⟨hjD, hisplit⟩ := hG j hjG
    obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    subst hm
    set F : Finset (ℕ × ℕ) := {a ∈ Finset.antidiagonal (m + 1) | a.1 < m + 1} with hF
    have hN := multiset_mul_esymm_eq_sum x (m + 1)
    have hfac : (((m + 1).factorial : ℕ) : L) = (m.factorial : L) * (((m + 1 : ℕ)) : L) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hkey : (((m + 1).factorial : ℕ) : L) * x.esymm (m + 1)
        = (-1 : L) ^ (m + 1 + 1) *
          ∑ a ∈ F, (m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2) := by
      rw [← Finset.mul_sum, hfac]
      calc (m.factorial : L) * (((m + 1 : ℕ)) : L) * x.esymm (m + 1)
          = (m.factorial : L) * ((((m + 1 : ℕ)) : L) * x.esymm (m + 1)) := by ring
        _ = (m.factorial : L) * ((-1 : L) ^ (m + 1 + 1) *
              ∑ a ∈ F, (-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2) := by rw [hN]
        _ = _ := by ring
    rw [hkey, Valuation.map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    refine valuation_finset_sum_le v _ _ ?_
    intro a ha
    rw [hF, Finset.mem_filter, Finset.mem_antidiagonal] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have ha2pos : 0 < a.2 := by omega
    have ha2le : a.2 ≤ x.card := by omega
    rcases Nat.eq_zero_or_pos a.1 with h0 | hpos
    · -- `i = 0`: the term is `m! · p_j`, small because `j ∈ D`
      have hre : (m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2)
          = (m.factorial : L) * x.psum a.2 := by
        rw [h0]; simp [Multiset.esymm]
      have ha2j : a.2 = m + 1 := by omega
      rw [hre, Valuation.map_mul]
      calc v.valuation L ((m.factorial : L)) * v.valuation L (x.psum a.2)
          ≤ 1 * v.valuation L (x.psum a.2) := mul_le_mul_right' (valuation_natCast_le_one v _) _
        _ = v.valuation L (x.psum a.2) := one_mul _
        _ ≤ ε := by rw [ha2j]; exact hD _ hjD (by omega) hjk
    · rcases hisplit a.1 hpos ha2 with hiG | hiD
      · -- `i ∈ G`: peel off `i! · e_i`, which the induction hypothesis bounds
        obtain ⟨C, hC⟩ : (a.1.factorial) ∣ m.factorial :=
          Nat.factorial_dvd_factorial (by omega)
        have hre : (m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2)
            = ((C : L) * (-1 : L) ^ a.1 * x.psum a.2)
              * ((a.1.factorial : L) * x.esymm a.1) := by
          have : ((m.factorial : ℕ) : L) = (a.1.factorial : L) * (C : L) := by
            rw [hC]; push_cast; ring
          rw [this]; ring
        rw [hre, Valuation.map_mul]
        have hleft : v.valuation L ((C : L) * (-1 : L) ^ a.1 * x.psum a.2) ≤ 1 := by
          rw [Valuation.map_mul, Valuation.map_mul, map_pow, Valuation.map_neg, map_one,
            one_pow, mul_one]
          calc v.valuation L ((C : L)) * v.valuation L (x.psum a.2)
              ≤ 1 * v.valuation L (x.psum a.2) :=
                mul_le_mul_right' (valuation_natCast_le_one v _) _
            _ = v.valuation L (x.psum a.2) := one_mul _
            _ ≤ 1 := valuation_psum_le_one v hx _
        calc v.valuation L ((C : L) * (-1 : L) ^ a.1 * x.psum a.2)
              * v.valuation L ((a.1.factorial : L) * x.esymm a.1)
            ≤ 1 * v.valuation L ((a.1.factorial : L) * x.esymm a.1) :=
              mul_le_mul_right' hleft _
          _ = v.valuation L ((a.1.factorial : L) * x.esymm a.1) := one_mul _
          _ ≤ ε := ih a.1 (by omega) hiG hpos (by omega)
      · -- `j − i ∈ D`: the power sum itself is small
        have ha2eq : a.2 = m + 1 - a.1 := by omega
        have hre : (m.factorial : L) * ((-1 : L) ^ a.1 * x.esymm a.1 * x.psum a.2)
            = ((m.factorial : L) * (-1 : L) ^ a.1 * x.esymm a.1) * x.psum a.2 := by ring
        rw [hre, Valuation.map_mul]
        have hleft : v.valuation L ((m.factorial : L) * (-1 : L) ^ a.1 * x.esymm a.1) ≤ 1 := by
          rw [Valuation.map_mul, Valuation.map_mul, map_pow, Valuation.map_neg, map_one,
            one_pow, mul_one]
          calc v.valuation L ((m.factorial : L)) * v.valuation L (x.esymm a.1)
              ≤ 1 * v.valuation L (x.esymm a.1) :=
                mul_le_mul_right' (valuation_natCast_le_one v _) _
            _ = v.valuation L (x.esymm a.1) := one_mul _
            _ ≤ 1 := valuation_esymm_le_one v hx _
        calc v.valuation L ((m.factorial : L) * (-1 : L) ^ a.1 * x.esymm a.1)
              * v.valuation L (x.psum a.2)
            ≤ 1 * v.valuation L (x.psum a.2) := mul_le_mul_right' hleft _
          _ = v.valuation L (x.psum a.2) := one_mul _
          _ ≤ ε := hD _ (by rw [ha2eq]; exact hiD) ha2pos ha2le

/-- **The tie case at tie size 4, from DOUBLING closure alone.**  `k = 4` closes even though
`p_3` is unavailable: in Newton's identity at `j = 4` the unknown `p_3` is multiplied by `e_1`,
which is itself `p_1` and hence small.  (`k = 3` genuinely does *not* close — `u_i = ζ₃^i c` has
`Σ u_i^(2^n) = 0` for every `n` — and neither does `k = 8`: there `p_3` multiplies `e_5` and `p_5`
multiplies `e_3`, and neither `e_3` nor `e_5` is controlled by `p_1, p_2, p_4`.  So "tie size a
power of 2" is *not* enough; see `PENDING_WORK.md`.) -/
theorem valuation_sum_unit_pow_card_four {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {U : Multiset L} (hU : ∀ u ∈ U, v.valuation L u = 1) (hcard : U.card = 4)
    {S : Set ℕ} (hS : S.Infinite) (hdbl : ∀ N ∈ S, 2 * N ∈ S)
    {B r : WithZero (Multiplicative ℤ)} (hB : B ≠ 0) (hr : r < 1)
    (hsum : ∀ N ∈ S, v.valuation L ((U.map (· ^ N)).sum) ≤ B * r ^ N) : False := by
  classical
  set c : WithZero (Multiplicative ℤ) := v.valuation L (((4 : ℕ).factorial : L)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    simp only [ne_eq, Valuation.zero_iff, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero _
  obtain ⟨n, hn⟩ := exists_mul_pow_lt (B := B) (r := r) (c := c) hr hc0 hB
  obtain ⟨N, hNS, hNn⟩ := hS.exists_gt n
  have hNge : n ≤ N := hNn.le
  set x : Multiset L := U.map (· ^ N) with hx
  have hxcard : x.card = 4 := by rw [hx, Multiset.card_map, hcard]
  have hxu : ∀ u ∈ x, v.valuation L u = 1 := by
    intro u hu'
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu'
    rw [map_pow, hU w hw, one_pow]
  have hmem : ∀ j : ℕ, j = 1 ∨ j = 2 ∨ j = 4 → j * N ∈ S := by
    rintro j (rfl | rfl | rfl)
    · simpa using hNS
    · exact hdbl N hNS
    · have := hdbl _ (hdbl N hNS)
      simpa [show 2 * (2 * N) = 4 * N by ring] using this
  have hD : ∀ j ∈ ({1, 2, 4} : Set ℕ), 0 < j → j ≤ x.card →
      v.valuation L (x.psum j) ≤ B * r ^ n := by
    intro j hj hjpos _
    have hjmem : j = 1 ∨ j = 2 ∨ j = 4 := by simpa using hj
    have hrw : x.psum j = (U.map (· ^ (j * N))).sum := by
      rw [Multiset.psum_def, hx, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl ?_
      intro w _
      simp only [Function.comp_apply, ← pow_mul]
      rw [Nat.mul_comm]
    rw [hrw]
    refine le_trans (hsum _ (hmem j hjmem)) (mul_le_mul_left' ?_ B)
    refine pow_le_pow_of_le_one (by simp) hr.le ?_
    calc n ≤ N := hNge
      _ = 1 * N := (one_mul N).symm
      _ ≤ j * N := Nat.mul_le_mul_right N hjpos
  have hG : ∀ j ∈ ({1, 2, 4} : Set ℕ), j ∈ ({1, 2, 4} : Set ℕ) ∧
      ∀ i, 1 ≤ i → i < j → (i ∈ ({1, 2, 4} : Set ℕ) ∨ (j - i) ∈ ({1, 2, 4} : Set ℕ)) := by
    intro j hj
    refine ⟨hj, ?_⟩
    have hjmem : j = 1 ∨ j = 2 ∨ j = 4 := by simpa using hj
    intro i hi1 hij
    rcases hjmem with rfl | rfl | rfl
    · omega
    · have : i = 1 := by omega
      subst this; left; simp
    · interval_cases i
      · left; simp
      · left; simp
      · right; simp
  have hmain := valuation_factorial_mul_esymm_le_of_closed v hxu hD hG 4 (by simp)
    (by omega) (by omega)
  rw [show (4 : ℕ) = x.card from hxcard.symm, multiset_esymm_card, Valuation.map_mul,
    valuation_multiset_prod_eq_one v hxu, mul_one, hxcard, ← hc] at hmain
  exact absurd hmain (not_le.2 hn)

/-- **A tie whose ratios are roots of unity of order dividing the tower step closes at once.**
If every `u ∈ U` has the same `M`-th power and the exponent set consists of multiples of `M`, then
`Σ_i u_i^N = |U| · w^(N/M)` has the *fixed* nonzero valuation `v(|U|)`, so it cannot decay.

This is the second half of the "tie ratios are `2`-power roots of unity" attack: with `M = 2^t`
and `S ⊆ {2^n : n ≥ t}` the hypothesis `hw` says exactly that all the ratios `u_i/u_1` are
`2^t`-th roots of unity. -/
theorem valuation_sum_unit_pow_of_common_pow {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {U : Multiset L} (hU : ∀ u ∈ U, v.valuation L u = 1) (hcard : 1 ≤ U.card)
    {M : ℕ} {w : L} (hw : ∀ u ∈ U, u ^ M = w)
    {S : Set ℕ} (hS : S.Infinite) (hSM : ∀ N ∈ S, M ∣ N)
    {B r : WithZero (Multiplicative ℤ)} (hB : B ≠ 0) (hr : r < 1)
    (hsum : ∀ N ∈ S, v.valuation L ((U.map (· ^ N)).sum) ≤ B * r ^ N) : False := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ ∈ U := Multiset.card_pos_iff_exists_mem.1 (by omega)
  have hwv : v.valuation L w = 1 := by
    rw [← hw u₀ hu₀, map_pow, hU u₀ hu₀, one_pow]
  set c : WithZero (Multiplicative ℤ) := v.valuation L ((U.card : L)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    simp only [ne_eq, Valuation.zero_iff, Nat.cast_eq_zero]
    omega
  obtain ⟨n, hn⟩ := exists_mul_pow_lt (B := B) (r := r) (c := c) hr hc0 hB
  obtain ⟨N, hNS, hNn⟩ := hS.exists_gt n
  obtain ⟨e, he⟩ := hSM N hNS
  have hconst : U.map (· ^ N) = Multiset.replicate U.card (w ^ e) := by
    rw [← Multiset.map_const']
    refine Multiset.map_congr rfl ?_
    intro u hu
    show u ^ N = w ^ e
    rw [he, pow_mul, hw u hu]
  have hval : v.valuation L ((U.map (· ^ N)).sum) = c := by
    rw [hconst, Multiset.sum_replicate, nsmul_eq_mul, Valuation.map_mul, map_pow, hwv, one_pow,
      mul_one, hc]
  have hle := hsum N hNS
  rw [hval] at hle
  have hmono : B * r ^ N ≤ B * r ^ n :=
    mul_le_mul_left' (pow_le_pow_of_le_one (by simp) hr.le hNn.le) B
  exact absurd (le_trans hle hmono) (not_le.2 hn)

/-! ### Sharpness of the doubling-closure frontier -/

/-- A full set of `m`-th roots of unity, scaled, has **vanishing** power sums along every exponent
`N` with `m ∤ N`. -/
theorem sum_root_of_unity_pow_eq_zero {L : Type*} [Field L] {m : ℕ} (hm : 1 < m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) {N : ℕ} (hN : ¬ m ∣ N) :
    (((Multiset.range m).map (fun i => (ζ ^ i) ^ N)).sum) = 0 := by
  have hsum : (((Multiset.range m).map (fun i => (ζ ^ i) ^ N)).sum)
      = ∑ i ∈ Finset.range m, (ζ ^ N) ^ i := by
    have hfun : ∀ i : ℕ, (ζ ^ i) ^ N = (ζ ^ N) ^ i := by
      intro i; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simp only [hfun]
    rfl
  rw [hsum]
  have hne : (ζ : L) ^ N ≠ 1 := fun h => hN ((hζ.pow_eq_one_iff_dvd N).1 h)
  rw [geom_sum_eq hne]
  have hone : ((ζ : L) ^ N) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [hone, sub_self, zero_div]

/-- **The doubling-closure frontier is SHARP.**  A number `m > 1` that is not a power of `2`
never divides `2^n`, so a full set of `m`-th roots of unity — all of them `v`-units — has
`Σ_i u_i^(2^n) = 0` for **every** `n`.  Its valuation is therefore `0`, which is `≤ B r^(2^n)`
vacuously: the hypotheses of `valuation_sum_unit_pow_card_four` (and of every doubling-closure
statement) are *satisfiable* at every tie size `m` that is not a power of `2`.

Combined with the additivity of the counterexample (disjoint blocks add), the realizable tie
sizes are exactly the sums of parts that are not powers of `2`, i.e. **every `k` except
`1, 2, 4`** — which is precisely the list that `valuation_sum_unit_pow_mulClosed` (`k = 1`),
`valuation_sum_unit_pow_card_two` and `valuation_sum_unit_pow_card_four` close.  So the local
leaf can NOT be improved further without enlarging the exponent set or bounding the tie size. -/
theorem sum_root_of_unity_two_pow_eq_zero {L : Type*} [Field L] {m : ℕ} (hm : 1 < m)
    (hm2 : ∀ a : ℕ, m ≠ 2 ^ a) {ζ : L} (hζ : IsPrimitiveRoot ζ m) (n : ℕ) :
    (((Multiset.range m).map (fun i => (ζ ^ i) ^ (2 ^ n))).sum) = 0 := by
  refine sum_root_of_unity_pow_eq_zero hm hζ ?_
  intro hdvd
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact hm2 a ha

/-- The tie size `3` witness in closed form: `1 + ζ₃^(2^n) + ζ₃^(2·2^n) = 0` for every `n`. -/
theorem sum_cube_root_two_pow_eq_zero {L : Type*} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3)
    (n : ℕ) : (1 : L) + ζ ^ 2 ^ n + (ζ ^ 2) ^ 2 ^ n = 0 := by
  have h := sum_root_of_unity_two_pow_eq_zero (m := 3) (by norm_num)
    (fun a ha => by
      rcases a with _ | _ | a
      · omega
      · omega
      · have : 2 ^ 2 ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega) hζ n
  have hrange : Multiset.range 3 = (0 : ℕ) ::ₘ (1 : ℕ) ::ₘ {(2 : ℕ)} := by decide
  rw [hrange] at h
  rw [add_assoc]
  simpa using h

/-- **Corvaja–Zannier (2004), main theorem, p. 177** (`δ = 1`, `u = α^(s n)`, `Γ = {α^t}`) —
Dubickas (2022), Lemma 3.  If `q α^(s n)` is pseudo-Pisot for only finitely many `n`, then
`‖q α^(s n)‖` is eventually larger than `e^(−ε s n)`.

**DISCLOSED OPEN.**  This is the single step of Dubickas's Theorem 1 that needs the `p`-adic
Subspace Theorem (Schlickewei), of which mathlib has nothing.  Everything else in Lemma 6 is
discharged in this file (`isPisot_of_pseudoPisotMul`, `otherConj_eq_zero_of_pow_rat`,
`exists_pisot_pow_of_pow_rat`) or is `corvajaZannier_lemma4` below.  See
`PROBE-DUBICKAS-NOSUBSPACE.md`: the archimedean Liouville/Roth bound provably cannot replace it. -/
theorem corvajaZannier_dichotomy {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ}
    (hq : 0 < q) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 0 < s 0)
    (hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * s n)) < |(q : ℝ) * α ^ s n - round ((q : ℝ) * α ^ s n)| := by
  sorry

/-- **Corvaja–Zannier (2004), Lemma 4.**  If the trace of `q α^(s n)` is a nonzero rational
integer for infinitely many `n`, then `α` is an algebraic integer or an `l`-th root of a rational.

**DISCLOSED OPEN.**  Unlike `corvajaZannier_dichotomy` this is *not* subspace-strength: it is a
valuation argument in `ℚ(α)` (a place where `α` has negative valuation makes the traces have
unbounded denominators unless all conjugates share the valuation pattern, which is the
root-of-a-rational case).  Formalizing it needs the ideal-valuation / trace machinery for number
fields; the concrete `d = 2` analysis (Newton polygon in `ℚ_p`, plus a root-of-unity tie case that
*is* the `α^l ∈ ℚ` branch) is written out in `PROBE-DUBICKAS-NOSUBSPACE.md`.

**Residual (2026-09-28, eighth lap)**: `isIntegral_of_bounded_den_mulClosed` proves this lemma
**outright and with no escape branch** — `IsIntegral ℤ α`, no `α^l ∈ ℚ` disjunct — for every
exponent set closed under multiplication.  The local input is
`valuation_sum_unit_pow_mulClosed`: Newton's identities force `v(j! e_j(x)) ≤ max_{l ≤ k} v(p_l(x))`
for the multiset `x` of `N`-th powers of the dominant conjugates, and at `j = k` the left side is the
fixed nonzero `v(k!)` because `e_k(x)` is a unit.  So the degenerate (`α^l ∈ ℚ`) branch of this lemma
is **entirely an artifact of exponent-set sparsity** — `√(3/2)` has `U_N = 0` for odd `N` but
`U_(2M) = 2(3/2)^M`, so its index set is not closed under doubling.  What is still missing is
therefore *only* the density of the index set `S`, which is produced by CZ's Lemma 3
(`corvajaZannier_dichotomy`) and which nothing in the present derivation makes dense.

Earlier in the chain: `exists_tie_of_bounded_den` proves the argument except the
tie case — if `α` is not an algebraic integer then at some prime `v` of `conjField α` the maximal
conjugate valuation is `> 1` and is attained at least twice.  So what is left is purely local:
writing the dominant conjugates as `z u_i` with `u_i` a `v`-unit, the hypothesis forces
`v(Σ_i u_i^N) → 0` along an infinite set of `N`, and one has to conclude that some `u_i/u_j` is a
root of unity (a `p`-adic Skolem–Mahler–Lech step) — which is exactly the source of the
`α^l ∈ ℚ` branch.

Stated with an index *set* rather than a strictly monotone sequence (interchangeable), and with the
extra hypothesis `hsmall` — every conjugate of `α` is inside the unit disc or has modulus `α` —
which is *free* in our application (`norm_lt_one_of_pseudoPisotMul` + `norm_eq_of_pow_eq`) and
removes the archimedean-large conjugates from any future proof. -/
theorem corvajaZannier_lemma4 {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q)
    (hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α)
    {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α ∨ ∃ (l : ℕ) (r : ℚ), 0 < l ∧ α ^ l = (r : ℝ) := by
  sorry

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
  classical
  have hint : IsIntegral ℚ α := halg.isIntegral
  have hα0 : (0:ℝ) < α := by linarith
  set d : ℕ := (minpoly ℚ α).natDegree with hd
  have hs : StrictMono (fun n : ℕ ↦ 2 ^ n) := fun a b h ↦ Nat.pow_lt_pow_right (by norm_num) h
  -- ### Step 1: the pseudo-Pisot set is infinite (else Lemma 3 contradicts `hbnd`)
  have hSinf : {n : ℕ | IsPseudoPisotMul 2 (α ^ 2 ^ n)}.Infinite := by
    intro hfin
    obtain ⟨k₀, hk₀⟩ := round_dist_le_of_bnd hα hC hyint hbnd
    obtain ⟨n₁, hn₁⟩ := corvajaZannier_dichotomy halg hα (q := 2) (by norm_num)
      (fun n : ℕ ↦ 2 ^ n) hs (by norm_num) hfin (Real.log α / 2) (by
      have := Real.log_pos hα; linarith)
    have h1 := hk₀ (max k₀ n₁) (le_max_left _ _)
    have h2 := hn₁ (max k₀ n₁) (le_max_right _ _)
    push_cast at h1 h2
    linarith
  -- ### Step 2: on the pseudo-Pisot set the trace is eventually nonzero
  have hlarge : ∃ K : ℕ, ∀ n ≥ K, (d : ℝ) < α ^ 2 ^ n := by
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((tendsto_pow_two_pow_atTop hα).eventually_gt_atTop (d : ℝ))
    exact ⟨K, fun n hn ↦ hK n hn⟩
  obtain ⟨K, hK⟩ := hlarge
  set S : Set ℕ := {n : ℕ | IsPseudoPisotMul 2 (α ^ 2 ^ n)} \ Set.Iio K with hSdef
  have hS : S.Infinite := hSinf.sdiff (Set.finite_Iio K)
  have hmemS : ∀ n ∈ S, IsPseudoPisotMul 2 (α ^ 2 ^ n) ∧ K ≤ n := by
    intro n hn
    exact ⟨hn.1, not_lt.1 hn.2⟩
  have htrne : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      ((2 : ℕ) : ℂ) * (((minpoly ℚ (α ^ 2 ^ n)).aroots ℂ).sum) = (t : ℂ) := by
    intro n hn
    obtain ⟨⟨h1, h2, t, ht⟩, hnK⟩ := hmemS n hn
    refine ⟨t, ?_, ht⟩
    intro ht0
    subst ht0
    -- `aroots = β ::ₘ otherConj β`, each other conjugate has modulus `< 1/2`
    have hintβ : IsIntegral ℚ (α ^ 2 ^ n) := hint.pow _
    have hmem : ((α ^ 2 ^ n : ℝ) : ℂ) ∈ (minpoly ℚ (α ^ 2 ^ n)).aroots ℂ := beta_mem_aroots hintβ
    have hcons : (minpoly ℚ (α ^ 2 ^ n)).aroots ℂ
        = ((α ^ 2 ^ n : ℝ) : ℂ) ::ₘ otherConj (α ^ 2 ^ n) := (Multiset.cons_erase hmem).symm
    rw [hcons, Multiset.sum_cons] at ht
    have hhalf : ∀ w ∈ otherConj (α ^ 2 ^ n), ‖w‖ ≤ 1 / 2 := by
      intro w hw
      have := h2 w hw
      rw [norm_mul, Complex.norm_natCast] at this
      push_cast at this
      linarith
    have hsum : ‖(otherConj (α ^ 2 ^ n)).sum‖ ≤ ((otherConj (α ^ 2 ^ n)).card : ℝ) * (1 / 2) := by
      refine le_trans (norm_multiset_sum_le _) ?_
      have := Multiset.sum_le_card_nsmul ((otherConj (α ^ 2 ^ n)).map (‖·‖)) (1/2 : ℝ)
        (by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Multiset.mem_map.1 hx
          rw [← hxw]; exact hhalf w hw)
      simpa [nsmul_eq_mul, mul_comm] using this
    have hcard : ((otherConj (α ^ 2 ^ n)).card : ℝ) ≤ (d : ℝ) := by
      have := card_otherConj_pow_le hint (2 ^ n)
      have : (otherConj (α ^ 2 ^ n)).card ≤ d := by omega
      exact_mod_cast this
    have hz : ((α ^ 2 ^ n : ℝ) : ℂ) = -(otherConj (α ^ 2 ^ n)).sum := by
      push_cast at ht ⊢
      linear_combination ht / 2
    have hnorm : α ^ 2 ^ n ≤ (d : ℝ) := by
      have h3 : ‖((α ^ 2 ^ n : ℝ) : ℂ)‖ = α ^ 2 ^ n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hz, norm_neg] at h3
      have := hK n hnK
      nlinarith [hsum, hcard, h3]
    linarith [hK n hnK]
  -- ### Step 3: Lemma 4, then the two elementary branches of Lemma 5
  have hSimg : ((fun n : ℕ ↦ 2 ^ n) '' S).Infinite :=
    hS.image (Set.injOn_of_injective hs.injective)
  have htr' : ∀ N ∈ (fun n : ℕ ↦ 2 ^ n) '' S, ∃ t : ℤ, t ≠ 0 ∧
      ((2 : ℕ) : ℂ) * (((minpoly ℚ (α ^ N)).aroots ℂ).sum) = (t : ℂ) := by
    intro N hN
    obtain ⟨n, hn, hNn⟩ := hN
    rw [← hNn]
    exact htrne n hn
  obtain ⟨n, hn⟩ := hS.nonempty
  obtain ⟨hps, -⟩ := hmemS n hn
  -- every conjugate of `α` is inside the unit disc or collapses onto `α` in modulus
  have hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α := by
    intro w hw
    by_cases hcol : w ^ 2 ^ n = (((α ^ 2 ^ n : ℝ)) : ℂ)
    · exact Or.inr (norm_eq_of_pow_eq hα (by positivity) hcol)
    · exact Or.inl (norm_lt_one_of_pseudoPisotMul hint hα (q := 2) (by norm_num)
        (by positivity) hps hw hcol)
  rcases corvajaZannier_lemma4 halg hα (q := 2) (by norm_num) hsmall hSimg htr' with
    hintα | ⟨l, r, hl, hlr⟩
  · -- `α` is an algebraic integer: the pseudo-Pisot number `2 α^(2ⁿ)` makes `α^(2ⁿ)` Pisot
    exact ⟨n, isPisot_of_pseudoPisotMul (q := 2) (by norm_num)
      (one_lt_pow₀ hα (by positivity)) (hintα.pow _) hps⟩
  · -- `α^l ∈ ℚ`: then `α^(2ⁿ)` would have to be rational, which `hnr` forbids
    exfalso
    have hβ1 : 1 < α ^ 2 ^ n := one_lt_pow₀ hα (by positivity)
    have hcl : (α ^ 2 ^ n) ^ l = ((r ^ 2 ^ n : ℚ) : ℝ) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hlr]
      push_cast
      ring
    have h0 := otherConj_eq_zero_of_pow_rat hβ1 hl hcl (q := 2) (by norm_num) hps.2.1
    obtain ⟨r', hr'⟩ := eq_rat_of_otherConj_eq_zero (hint.pow _) h0
    exact hnr n r' hr'

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
