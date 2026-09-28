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
* **Open (exactly two named leaves, everything between them proved):**
  `corvajaZannier_dichotomy` — CZ's main theorem, p. 177 = Dubickas's Lemma 3, the *only*
  subspace-strength step — and `corvajaZannier_lemma4` — CZ's Lemma 4, a valuation/trace argument
  in `ℚ(α)` that is **not** subspace-strength and is the next target.
  `exists_pisot_pow_pseudoPisot_core` is now *proved* from those two.  Of Lemma 4, everything
  except its **tie case** is now proved (`exists_tie_of_bounded_den`: its hypothesis forces two
  distinct conjugates to share the dominant valuation at some prime).
  Both leads that were recorded here have been *refuted*: the archimedean Liouville/norm bound is vacuous (it only re-derives
  `M(α) ≥ α`), and the Böttcher coordinate is not of Mahler-method shape.  Full write-up, with
  the proposed literature `Prop`, in `PROBE-DUBICKAS-NOSUBSPACE.md`.
* `hD` therefore still sits on the `Dubickas.lean` headlines; it must not be routed through the
  `sorry`.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot
import LeanFormalizations.NumberTheory.Diophantine.Edges

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
  have hz1 : 1 < v.valuation (conjField α) z := lt_of_lt_of_le hv (hmax a haR)
  obtain ⟨w, hw, hwe⟩ := tie_of_bounded_den hq hS hu v hzR hz1 hmax
  exact ⟨v, z, w, hzR, hw, hz1, hwe, hmax⟩
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

**Residual after this lap**: `exists_tie_of_bounded_den` proves the *whole* argument except the
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
