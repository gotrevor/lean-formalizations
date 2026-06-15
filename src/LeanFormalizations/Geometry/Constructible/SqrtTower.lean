/-
# Square-root towers and the degree of a constructible number

The algebraic core of Wantzel's theorem (the "convergence" direction needed for the
classical impossibility proofs).

A real number is *constructible* (by compass and straightedge, starting from the
rationals) iff it lies in some field reached from `ℚ` by repeatedly adjoining a
square root — a *square-root tower*. We capture that lattice-theoretically: an
`IntermediateField ℚ ℝ` is a `IsSqrtTower` if it is `⊥`, or obtained from a tower `K`
by adjoining a real `a` with `a * a ∈ K`.

The key fact (`IsSqrtTower.finrank_eq_pow_two`): every square-root tower has degree a
**power of two** over `ℚ`. Each adjunction step has relative degree `≤ 2` (the
element `a` is a root of `X² - (a*a)`), and the tower law multiplies the degrees.

This is exactly the obstruction that kills the three classical construction problems;
`Statement.lean` applies it to `∛2` (degree 3, not a power of 2) to prove the cube
cannot be doubled.

The geometric faithfulness layer — that compass-and-straightedge constructions yield
*precisely* these quadratic towers — is a separate development (see `PENDING_WORK.md`).
-/
import Mathlib

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- A *square-root tower* over `ℚ` inside `ℝ`: built from `⊥ = ℚ` by repeatedly
adjoining a real square root `a` of an element `a * a` already present. -/
inductive IsSqrtTower : IntermediateField ℚ ℝ → Prop
  | base : IsSqrtTower ⊥
  | step {K : IntermediateField ℚ ℝ} (hK : IsSqrtTower K) {a : ℝ} (ha : a * a ∈ K) :
      IsSqrtTower ((K⟮a⟯).restrictScalars ℚ)

/-- A real number is *constructible* if it lies in some square-root tower over `ℚ`. -/
def IsConstructible (x : ℝ) : Prop :=
  ∃ K : IntermediateField ℚ ℝ, IsSqrtTower K ∧ x ∈ K

variable {K : IntermediateField ℚ ℝ} {a : ℝ}

/-- If `a * a ∈ K`, then `a` is a root of the monic degree-2 polynomial `X² - (a*a)`
over `K`. -/
lemma aeval_X_sq_sub_C (ha : a * a ∈ K) :
    (aeval a) (X ^ 2 - C (⟨a * a, ha⟩ : K)) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply]
  show a ^ 2 - a * a = 0
  ring

/-- An adjoined square root is integral over the base field. -/
lemma isIntegral_of_sq_mem (ha : a * a ∈ K) : IsIntegral K a :=
  ⟨X ^ 2 - C (⟨a * a, ha⟩ : K), monic_X_pow_sub_C _ (by norm_num), aeval_X_sq_sub_C ha⟩

/-- A square-root adjunction has relative degree at most `2`. -/
lemma finrank_adjoin_le_two (ha : a * a ∈ K) : finrank K K⟮a⟯ ≤ 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_of_sq_mem ha)]
  have hdvd : minpoly K a ∣ (X ^ 2 - C (⟨a * a, ha⟩ : K)) :=
    minpoly.dvd K a (aeval_X_sq_sub_C ha)
  have h := natDegree_le_of_dvd hdvd (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  rwa [natDegree_X_pow_sub_C] at h

/-- **The degree of a square-root tower is a power of two.** -/
theorem IsSqrtTower.finrank_eq_pow_two {K : IntermediateField ℚ ℝ} (h : IsSqrtTower K) :
    ∃ n : ℕ, finrank ℚ K = 2 ^ n := by
  induction h with
  | base => exact ⟨0, by simp [IntermediateField.finrank_bot]⟩
  | @step K hK a ha ih =>
    obtain ⟨n, hn⟩ := ih
    haveI : FiniteDimensional ℚ K := .of_finrank_pos (by rw [hn]; positivity)
    haveI hai : IsIntegral K a := isIntegral_of_sq_mem ha
    haveI : FiniteDimensional K K⟮a⟯ := adjoin.finiteDimensional hai
    have hstep : finrank ℚ ((K⟮a⟯).restrictScalars ℚ) = finrank ℚ K * finrank K K⟮a⟯ :=
      (Module.finrank_mul_finrank ℚ K K⟮a⟯).symm
    have hle : finrank K K⟮a⟯ ≤ 2 := finrank_adjoin_le_two ha
    have hpos : 1 ≤ finrank K K⟮a⟯ := finrank_pos
    have hcases : finrank K K⟮a⟯ = 1 ∨ finrank K K⟮a⟯ = 2 := by omega
    rcases hcases with h1 | h2
    · exact ⟨n, by rw [hstep, hn, h1, mul_one]⟩
    · exact ⟨n + 1, by rw [hstep, hn, h2, pow_succ]⟩

/-- **Degree of a constructible number.** If `x` is constructible then `[ℚ(x):ℚ]` is a
power of two: `ℚ(x)` sits inside a square-root tower `K`, so `[ℚ(x):ℚ] ∣ [K:ℚ] = 2ⁿ`,
and every divisor of `2ⁿ` is a power of two. This is the obstruction behind the
classical impossibility results. -/
theorem IsConstructible.finrank_adjoin_eq_pow_two {x : ℝ} (hx : IsConstructible x) :
    ∃ n : ℕ, finrank ℚ ℚ⟮x⟯ = 2 ^ n := by
  obtain ⟨K, hK, hmem⟩ := hx
  obtain ⟨n, hn⟩ := hK.finrank_eq_pow_two
  haveI : FiniteDimensional ℚ K := .of_finrank_pos (by rw [hn]; positivity)
  have hle : ℚ⟮x⟯ ≤ K := by rw [IntermediateField.adjoin_simple_le_iff]; exact hmem
  have hdvd : finrank ℚ ℚ⟮x⟯ ∣ finrank ℚ K :=
    ⟨_, (IntermediateField.finrank_bot_mul_relfinrank hle).symm⟩
  rw [hn] at hdvd
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨m, hm⟩

/-- **Every constructible number is algebraic over `ℚ`.** It lies in the
finite-dimensional field `ℚ(x)`, and every element of a finite extension is
algebraic. (This is the obstruction behind *squaring the circle*: `√π` would be
algebraic, forcing `π` algebraic — contradicting Lindemann.) -/
theorem IsConstructible.isAlgebraic {x : ℝ} (hx : IsConstructible x) :
    IsAlgebraic ℚ x := by
  obtain ⟨n, hn⟩ := hx.finrank_adjoin_eq_pow_two
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := .of_finrank_pos (by rw [hn]; positivity)
  have hgen : IsAlgebraic ℚ (AdjoinSimple.gen ℚ x) := IsAlgebraic.of_finite _ _
  have h := hgen.algebraMap (A := ℝ)
  rwa [AdjoinSimple.algebraMap_gen] at h

/-- `3` does not divide any power of `2`. (The arithmetic obstruction: a degree-3
number cannot live in a degree-`2ⁿ` tower.) -/
lemma three_not_dvd_two_pow (n : ℕ) : ¬ (3 ∣ 2 ^ n) := fun hd => by
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- A real number whose degree over `ℚ` is exactly `3` is not constructible. -/
theorem not_isConstructible_of_finrank_adjoin_eq_three {x : ℝ}
    (hx : finrank ℚ ℚ⟮x⟯ = 3) : ¬ IsConstructible x := fun h => by
  obtain ⟨n, hn⟩ := h.finrank_adjoin_eq_pow_two
  rw [hx] at hn
  exact three_not_dvd_two_pow n (hn ▸ dvd_refl 3)

/-! ### The definition captures genuine ruler-and-compass capability

The two basic constructions: every rational length is available, and a square root
of any constructible nonnegative length is constructible (the compass step). -/

/-- Every rational is constructible (available in the base field `⊥ = ℚ`). -/
theorem isConstructible_ratCast (q : ℚ) : IsConstructible (q : ℝ) :=
  ⟨⊥, IsSqrtTower.base, by rw [IntermediateField.mem_bot]; exact ⟨q, rfl⟩⟩

/-- **Constructible numbers are closed under square roots.** If `x ≥ 0` is
constructible then so is `√x` — adjoining `√x` to a tower `K ∋ x` is a square-root
step, since `(√x)·(√x) = x ∈ K`. This is the compass construction of a mean
proportional. -/
theorem IsConstructible.sqrt {x : ℝ} (hx : IsConstructible x) (hx0 : 0 ≤ x) :
    IsConstructible (Real.sqrt x) := by
  obtain ⟨K, hK, hmem⟩ := hx
  have ha : Real.sqrt x * Real.sqrt x ∈ K := by rw [Real.mul_self_sqrt hx0]; exact hmem
  refine ⟨(K⟮Real.sqrt x⟯).restrictScalars ℚ, hK.step ha, ?_⟩
  rw [IntermediateField.mem_restrictScalars]
  exact IntermediateField.mem_adjoin_simple_self K (Real.sqrt x)

/-! ### Constructible numbers form a subfield

Two constructible numbers live in (generally different) square-root towers `K`, `L`.
Stacking `L`'s square-root steps on top of `K` produces a single tower containing
both (`IsSqrtTower.sup_exists`), inside which the field operations close. -/

/-- **Any two square-root towers embed in a common one.** Replay `L`'s square-root
adjunctions on top of `K`: each `a` with `a*a ∈ L'` still has `a*a` in the larger
field, so the same step applies. -/
theorem IsSqrtTower.sup_exists {K : IntermediateField ℚ ℝ} (hK : IsSqrtTower K)
    {L : IntermediateField ℚ ℝ} (hL : IsSqrtTower L) :
    ∃ M, IsSqrtTower M ∧ K ≤ M ∧ L ≤ M := by
  induction hL with
  | base => exact ⟨K, hK, le_refl K, bot_le⟩
  | @step L' hL' a ha ihL' =>
    obtain ⟨M', hM', hKM', hL'M'⟩ := ihL'
    have haM' : a * a ∈ M' := hL'M' ha
    refine ⟨(M'⟮a⟯).restrictScalars ℚ, hM'.step haM', le_trans hKM' ?_, ?_⟩
    · intro x hx
      rw [IntermediateField.mem_restrictScalars]
      simpa using IntermediateField.algebraMap_mem M'⟮a⟯ (⟨x, hx⟩ : M')
    · have eL : (L'⟮a⟯).restrictScalars ℚ = adjoin ℚ (↑L' ∪ {a}) :=
        IntermediateField.restrictScalars_adjoin ℚ L' {a}
      have eM : (M'⟮a⟯).restrictScalars ℚ = adjoin ℚ (↑M' ∪ {a}) :=
        IntermediateField.restrictScalars_adjoin ℚ M' {a}
      rw [eL, eM]
      exact adjoin.mono _ _ _
        (Set.union_subset_union_left _ (SetLike.coe_subset_coe.mpr hL'M'))

/-- Constructible numbers are closed under addition. -/
theorem IsConstructible.add {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) :
    IsConstructible (x + y) := by
  obtain ⟨K, hK, hxK⟩ := hx; obtain ⟨L, hL, hyL⟩ := hy
  obtain ⟨M, hM, hKM, hLM⟩ := hK.sup_exists hL
  exact ⟨M, hM, M.add_mem (hKM hxK) (hLM hyL)⟩

/-- Constructible numbers are closed under multiplication. -/
theorem IsConstructible.mul {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) :
    IsConstructible (x * y) := by
  obtain ⟨K, hK, hxK⟩ := hx; obtain ⟨L, hL, hyL⟩ := hy
  obtain ⟨M, hM, hKM, hLM⟩ := hK.sup_exists hL
  exact ⟨M, hM, M.mul_mem (hKM hxK) (hLM hyL)⟩

/-- Constructible numbers are closed under negation. -/
theorem IsConstructible.neg {x : ℝ} (hx : IsConstructible x) : IsConstructible (-x) := by
  obtain ⟨K, hK, hxK⟩ := hx; exact ⟨K, hK, K.neg_mem hxK⟩

/-- Constructible numbers are closed under subtraction. -/
theorem IsConstructible.sub {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) :
    IsConstructible (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- Constructible numbers are closed under inversion. -/
theorem IsConstructible.inv {x : ℝ} (hx : IsConstructible x) : IsConstructible x⁻¹ := by
  obtain ⟨K, hK, hxK⟩ := hx; exact ⟨K, hK, K.inv_mem hxK⟩

end LeanFormalizations.Constructible
