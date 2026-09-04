/-
# The 2-adic obstruction: Sun's stage-3 integer is divisible by `2^{v₂(F_B)}`

Machine-checkable refutation of the *shape* of §9 of arXiv:2609.04176v1.  Assume, as the paper
does, `G = a/q`.  §3 builds a scalar `q̂_B = ± F_B · det R[A,J] / ∏_{i<N} Π_i` (3.5) with
`F_B = ∏_{r<2B} r!` and `N = 2B+S+3`, and the nonzero integer `N_B = q^S H_B^min q̂_B` (3.8),
`H_B^min` the denominator of `q^S q̂_B`.  Theorem 9.1 claims `log|N_B| ≤ −δ₀B² + o(B²)`.

But every `Π_i` is a product of **odd** squares, and every entry of `q·R` is 2-integral (the
paper's own Lemma 5.4), so `v₂(N_B) ≥ v₂(F_B) = 2B²(1+o(1))` and `|N_B| ≥ 2^{v₂(F_B)}` — the
ledger is off by `≈ 1.4 B²` against a claimed margin of `0.0097 B²`.  The paper's Prop. 9.5
asserts a `B² log B` cancellation between `F_B` and `∏Π_i` "because they come from the same
scalar": true at the real place, false 2-adically.  A real-place cancellation is not a
`p`-adic cancellation.

## What this file states

* `fakeTail g` — the paper's (1.1) read as a **definition** from a hypothetical value `g` of `G`:
  `T_m := (-1)^m (g − S_{m−1})`.  It satisfies the recurrence (`fakeTail_isTailSeq`), so all of
  `Residual.lean` applies to it over `ℚ`; and if `G` really equalled `a/q` these would be the
  true tails (`Statement.lean`, `fakeTail_eq_tail_of_catalan_eq`).  Nothing analytic is needed:
  the obstruction is purely about the paper's *construction*.
* `bigF`, `normaliserProd`, `qhat`, `NB` — the paper's `F_B`, `∏_{i<N} Π_i`, `q̂_B` (up to the
  irrelevant sign), and `N_B = (q^S q̂_B).num` (since `H_B^min = (q^S q̂_B).den`).
* `two_pow_padicValNat_bigF_dvd_NB` — **`2^{v₂(F_B)} ∣ N_B`**, for every `a, q ≠ 0, B, S` and
  every row selection `A` (an arbitrary function `Fin S → Fin (S+3)`; a non-injective one gives
  `det = 0`, `N_B = 0`, and the divisibility is vacuous).
* `padicValNat_two_bigF_ge` — Legendre: `v₂(F_B) ≥ B(2B−1) − 2B(⌊log₂ 2B⌋+1)`.
* `two_pow_le_abs_NB` — hence `|N_B| ≥ 2^{v₂(F_B)}` whenever `N_B ≠ 0`.

The exact-rational check that found this (`papers/sun-2026-catalan-twoadic-check.py`) is the
numeric probe for these statements: at `B = 4,5,6` it reports `v₂(H_B^min) = 0` and
`v₂(N_B) ≥ v₂(F_B)` for every admissible `A`.
-/
import LeanFormalizations.NumberTheory.Catalan.Residual

namespace LeanFormalizations.Catalan

open Finset

/-- The paper's (1.1) read as a **definition** from a hypothetical value `g` of `G`:
`T_m := (-1)^m (g − S_{m−1})`, `S_{m−1} = Σ_{k<m} (-1)^k/(2k+1)^2`. -/
def fakeTail (g : ℚ) (m : ℕ) : ℚ :=
  (-1 : ℚ) ^ m * (g - ∑ k ∈ range m, (-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2)

/-- The fake tails satisfy Sun's recurrence, so `Residual.lean` applies to them over `ℚ`. -/
theorem fakeTail_isTailSeq (g : ℚ) : IsTailSeq (fakeTail g) := by
  intro m
  have h : (-1 : ℚ) ^ m * (-1 : ℚ) ^ m = 1 := by rw [← mul_pow]; simp
  simp only [fakeTail, sum_range_succ, pow_succ]
  linear_combination (1 / (2 * (m : ℚ) + 1) ^ 2) * h

/-- `F_B = ∏_{r<2B} r!` (paper (3.3)): the product of the pivots of the finite-difference
transform on the `2B` monomial reference columns `i^r`. -/
def bigF (B : ℕ) : ℕ := ∏ r ∈ range (2 * B), r.factorial

/-- `∏_{i<N} Π_i`, `N = 2B+S+3` — the denominator of (3.5).  **Odd** (`odd_normaliserProd`). -/
def normaliserProd (B S : ℕ) : ℕ := ∏ i ∈ range (2 * B + S + 3), normaliser B i

/-- The paper's stage-3 scalar `q̂_B` (3.5), up to its irrelevant sign, for the row selection
`A`: `F_B · det R[A,J] / ∏_{i<N} Π_i`, built from the fake tails of `G = g`. -/
noncomputable def qhat (g : ℚ) (B S : ℕ) (A : Fin S → Fin (S + 3)) : ℚ :=
  (bigF B : ℚ) * ((resid (fakeTail g) B S).submatrix A id).det / (normaliserProd B S : ℚ)

/-- The paper's integer `N_B = q^S H_B^min q̂_B` (3.8).  With `x := q^S q̂_B` we have
`H_B^min = x.den` (Definition 3.1), so `N_B = x.num`. -/
noncomputable def NB (a q : ℤ) (B S : ℕ) (A : Fin S → Fin (S + 3)) : ℤ :=
  ((q : ℚ) ^ S * qhat ((a : ℚ) / q) B S A).num

/-- `Π_i` is a product of odd squares. -/
theorem odd_normaliser (B i : ℕ) : Odd (normaliser B i) := by
  unfold normaliser
  refine Finset.prod_induction _ (fun n => Odd n) (fun a b ha hb => ha.mul hb) odd_one ?_
  intro h _
  have ho : Odd (2 * (h + i) + 1) := ⟨h + i, rfl⟩
  exact ho.pow

/-- The stage-3 denominator `∏_{i<N} Π_i` is odd: `v₂` of it is exactly `0`. -/
theorem odd_normaliserProd (B S : ℕ) : Odd (normaliserProd B S) := by
  unfold normaliserProd
  exact Finset.prod_induction _ (fun n => Odd n) (fun a b ha hb => ha.mul hb) odd_one
    (fun i _ => odd_normaliser B i)

/-- **Lemma 5.4, first half**: `q · T_m = ±(a − q S_{m−1})` has odd denominator, since
`S_{m−1}` has denominator dividing `∏_{k<m} (2k+1)^2`. -/
theorem odd_den_mul_fakeTail (a q : ℤ) (hq : q ≠ 0) (m : ℕ) :
    Odd ((q : ℚ) * fakeTail ((a : ℚ) / q) m).den := by
  sorry

/-- **Lemma 5.4, second half**: every entry of `q · R` is 2-integral — division by the odd
`2(i+j)+1` preserves odd denominators, and odd denominators are closed under `+`, `*`
(`Rat.add_den_dvd`, `Rat.mul_den_dvd`). -/
theorem odd_den_smul_resid (a q : ℤ) (hq : q ≠ 0) (B S : ℕ) (i : Fin (S + 3)) (j : Fin S) :
    Odd (((q : ℚ) • resid (fakeTail ((a : ℚ) / q)) B S) i j).den := by
  sorry

/-- A determinant of odd-denominator rationals has odd denominator (`Matrix.det_apply`: a
signed sum of products). -/
theorem odd_den_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ)
    (hM : ∀ i j, Odd (M i j).den) : Odd M.det.den := by
  sorry

/-- **The 2-adic obstruction: `2^{v₂(F_B)} ∣ N_B`.**
With `y := det(q • R[A,J])` (odd denominator by `odd_den_det`, and `q^S det R[A,J] = y` by
`Matrix.det_smul`), `x = q^S q̂_B = F_B · y / ∏Π_i` has odd denominator, so
`v₂(x.num) = v₂(x) = v₂(F_B) + v₂(y) − 0 ≥ v₂(F_B)` (`padicValRat`), i.e.
`2^{v₂(F_B)} ∣ x.num = N_B` (`padicValInt_dvd_iff`).  If `y = 0` the claim is `2^k ∣ 0`. -/
theorem two_pow_padicValNat_bigF_dvd_NB (a q : ℤ) (hq : q ≠ 0) (B S : ℕ)
    (A : Fin S → Fin (S + 3)) :
    (2 : ℤ) ^ padicValNat 2 (bigF B) ∣ NB a q B S A := by
  sorry

/-- **Legendre**: `v₂(r!) = r − s₂(r) ≥ r − (⌊log₂ r⌋ + 1)`
(`sub_one_mul_padicValNat_factorial`), summed over `r < 2B`:
`v₂(F_B) ≥ B(2B−1) − 2B(⌊log₂ 2B⌋ + 1)`, which is `2B² − O(B log B)`. -/
theorem padicValNat_two_bigF_ge (B : ℕ) :
    B * (2 * B - 1) - 2 * B * (Nat.log 2 (2 * B) + 1) ≤ padicValNat 2 (bigF B) := by
  sorry

/-- A nonzero `N_B` is at least `2^{v₂(F_B)}` in absolute value — the opposite of `|N_B| < 1`. -/
theorem two_pow_le_abs_NB (a q : ℤ) (hq : q ≠ 0) (B S : ℕ) (A : Fin S → Fin (S + 3))
    (hne : NB a q B S A ≠ 0) :
    (2 : ℤ) ^ padicValNat 2 (bigF B) ≤ |NB a q B S A| :=
  Int.le_of_dvd (abs_pos.2 hne)
    ((dvd_abs _ _).2 (two_pow_padicValNat_bigF_dvd_NB a q hq B S A))

end LeanFormalizations.Catalan
