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
  `exists_pisot_pow_pseudoPisot_core` is now *proved* from those two.
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
