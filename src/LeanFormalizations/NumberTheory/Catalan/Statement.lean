/-
# Catalan salvage — the audit surface

The load-bearing statements of the thread, written to be checked against Sun's arXiv:2609.04176v1
(3 Sep 2026).  Everything else in this directory is engine.

* `residual_rank` — **Theorem 2.1** for the actual Catalan tails: `rank (resid tail B S) = S`
  whenever `B > S > 0`.  Delegates to the field-generic `resid_rank` (`Residual.lean`) through the
  one analytic input `tail_add_tail_succ` (`Tails.lean`).
* `exists_row_set_det_ne_zero` — **Corollary 2.1**: an `S`-row set with nonvanishing minor.
* `fakeTail_eq_tail_of_catalan_eq` — the faithfulness edge for the refutation: if `G` really
  were `a/q`, the paper's construction in `TwoAdic.lean` (built from `fakeTail (a/q)`) is
  built from the true tails.
* `sun_ledger_impossible` — **the no-go**: for every hypothetical `G = a/q` and every
  `B > S > 0` there is a row set for which the paper's integer `N_B` is nonzero and
  `|N_B| ≥ 2^{B(2B−1) − 2B(⌊log₂ 2B⌋+1)}`.  Theorem 9.1 needs `log|N_B| ≤ −δ₀B² + o(B²)`.
  This is a statement about the paper's *construction*; it says nothing about `G` itself.

**⚠️ Nothing here claims that Catalan's constant is irrational.  It remains open.**
-/
import LeanFormalizations.NumberTheory.Catalan.Tails
import LeanFormalizations.NumberTheory.Catalan.Residual
import LeanFormalizations.NumberTheory.Catalan.TwoAdic

namespace LeanFormalizations.Catalan

/-- The Catalan tails satisfy Sun's recurrence: the bridge from `Tails.lean` into the
field-generic core. -/
theorem tail_isTailSeq : IsTailSeq tail := fun m => tail_add_tail_succ m

/-- **Theorem 2.1** (Sun, arXiv:2609.04176v1): for `B > S > 0`, the `(S+3) × S` weighted
residual matrix `R_{a,j} = Σ_{i=0}^{a+2B} (-1)^i C(a+2B,i) Π_i u_{i+j}` of the Catalan tails
has rank `S`. -/
theorem residual_rank {B S : ℕ} (hS : 0 < S) (hBS : S < B) : (resid tail B S).rank = S :=
  resid_rank tail tail_isTailSeq hS hBS

/-- **Corollary 2.1**: some `S` of the `S+3` rows form a nonsingular minor.  (Row rank equals
column rank; `S` independent rows give an invertible `S × S` submatrix —
`Matrix.linearIndependent_rows_iff_isUnit`.) -/
theorem exists_row_set_det_ne_zero {F : Type*} [Field F] [CharZero F] {T : ℕ → F}
    (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    ∃ A : Fin S → Fin (S + 3), Function.Injective A ∧
      ((resid T B S).submatrix A id).det ≠ 0 := by
  classical
  have hrank : (resid T B S).rank = S := resid_rank T hT hS hBS
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F (resid T B S).row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = S := by
    rw [← finrank_span_eq_card hli, hspan, hrank]
  let e : κ ≃ Fin S := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_⟩
  have hli' : LinearIndependent F ((resid T B S).submatrix (a ∘ e.symm) id).row := by
    have : ((resid T B S).submatrix (a ∘ e.symm) id).row = ((resid T B S).row ∘ a) ∘ e.symm := by
      ext i j; rfl
    rw [this]
    exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

/-- **Faithfulness edge.**  If Catalan's constant were the rational `a/q`, the paper's fake
tails (`TwoAdic.lean`, built from `a/q` by (1.1)) coincide with the true tails — so the
2-adic obstruction is a fact about the paper's construction *as applied to* `G`.  From
`tail_eq_catalan_sub_partialSum` and `push_cast`. -/
theorem fakeTail_eq_tail_of_catalan_eq (a q : ℤ) (hG : catalanConst = (a : ℝ) / q) (m : ℕ) :
    ((fakeTail ((a : ℚ) / q) m : ℚ) : ℝ) = tail m := by
  rw [tail_eq_catalan_sub_partialSum, hG]
  unfold fakeTail partialSum
  push_cast
  ring

/-- **The no-go.**  For every hypothetical `G = a/q` (`q ≠ 0`) and all `B > S > 0`, some row
selection makes the paper's integer `N_B` (3.8) nonzero with
`|N_B| ≥ 2^{B(2B−1) − 2B(⌊log₂ 2B⌋+1)}` — so `|N_B| → ∞`, where Theorem 9.1 claims
`log|N_B| ≤ −δ₀ B² + o(B²)`.  Assembly: Corollary 2.1 over `ℚ` for `fakeTail (a/q)`
(`fakeTail_isTailSeq`) gives `det ≠ 0`, hence `qhat ≠ 0` (`bigF`, `normaliserProd`, `q` are
nonzero), hence `N_B ≠ 0`; then `two_pow_le_abs_NB` and `padicValNat_two_bigF_ge`. -/
theorem sun_ledger_impossible (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    ∃ A : Fin S → Fin (S + 3), NB a q B S A ≠ 0 ∧
      (2 : ℤ) ^ (B * (2 * B - 1) - 2 * B * (Nat.log 2 (2 * B) + 1)) ≤ |NB a q B S A| := by
  obtain ⟨A, -, hdet⟩ := exists_row_set_det_ne_zero (fakeTail_isTailSeq ((a : ℚ) / q)) hS hBS
  have hq' : (q : ℚ) ≠ 0 := Int.cast_ne_zero.2 hq
  have hF : (bigF B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun r _ => Nat.factorial_ne_zero r)
  have hP : (normaliserProd B S : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (odd_normaliserProd B S).pos.ne'
  have hne : NB a q B S A ≠ 0 := by
    unfold NB qhat
    rw [Rat.num_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ hq') (div_ne_zero (mul_ne_zero hF hdet) hP)
  refine ⟨A, hne, le_trans ?_ (two_pow_le_abs_NB a q hq B S A hne)⟩
  exact pow_le_pow_right₀ (by norm_num) (padicValNat_two_bigF_ge B)

end LeanFormalizations.Catalan
