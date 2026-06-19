/-
# Anti-vacuity anchors for the no-three-in-line definitions

The headline theorems are stated against `Collinear ℝ` (via `toReal`). A faithful audit must rule
out the two ways such a definition could be silently vacuous:

* `Collinear ℝ` could be **always false** on grid points — then `NoThreeCollinear` would hold
  trivially. Refuted by `collinear_diagonal`: three real grid points genuinely *are* collinear.
* `Collinear ℝ` could be **always true** — then no nonempty set would satisfy `NoThreeCollinear`.
  Refuted by `not_collinear_corner` (a genuine non-collinear triple) together with
  `Parabola.parabola_noThreeCollinear` (a proven nonempty no-three-collinear family).

Together with the exact criterion `collinear_iff_det3_zero`, these pin the predicate to its
intended geometric meaning. They are tiny `norm_num` computations on explicit points — concrete
witnesses in the spirit of the other modules' `Anchors.lean`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Collinearity
import LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola

namespace LeanFormalizations.NoThreeInLine

/-- Three grid points on the main diagonal genuinely *are* collinear: `Collinear ℝ` fires, so
`NoThreeCollinear` is not vacuously true. -/
theorem collinear_diagonal :
    Collinear ℝ ({toReal (0, 0), toReal (1, 1), toReal (2, 2)} : Set (ℝ × ℝ)) := by
  apply det3_zero_imp_collinear
  norm_num [det3, toReal]

/-- A right-angle corner triple is *not* collinear: `Collinear ℝ` is not always true, so
`NoThreeCollinear` is a genuine constraint (not unsatisfiable). -/
theorem not_collinear_corner :
    ¬ Collinear ℝ ({toReal (0, 0), toReal (1, 0), toReal (0, 1)} : Set (ℝ × ℝ)) := by
  intro h
  have hd := collinear_imp_det3_zero h
  norm_num [det3, toReal] at hd

/-! ### A decidable criterion + a `native_decide`-verified concrete witness

`NoThreeCollinear` itself is not decidable (`Collinear ℝ`), but a *sufficient* condition is: every
triple either repeats a point or has nonzero **integer** determinant. This is decidable, and the
bridge `det3_toReal_eq_idet3` shows the real determinant of grid points is exactly the cast of the
integer one — so a vanishing real determinant forces a vanishing integer one, contradicting the
check. This lets `native_decide` certify explicit configurations. -/

/-- Integer `2×2` determinant of grid points — the decidable mirror of `det3 ∘ toReal`. -/
def idet3 (P Q R : ℕ × ℕ) : ℤ :=
  ((Q.1 : ℤ) - P.1) * ((R.2 : ℤ) - P.2) - ((R.1 : ℤ) - P.1) * ((Q.2 : ℤ) - P.2)

/-- The real determinant of grid points is the cast of the integer determinant. -/
theorem det3_toReal_eq_idet3 (P Q R : ℕ × ℕ) :
    det3 (toReal P) (toReal Q) (toReal R) = ((idet3 P Q R : ℤ) : ℝ) := by
  simp only [det3, toReal, idet3]; push_cast; ring

/-- **Decidable sufficient criterion.** If every triple of `s` repeats a point or has nonzero
integer determinant, then `s` has no three collinear. -/
theorem noThreeCollinear_of_idet {s : Finset (ℕ × ℕ)}
    (h : ∀ P ∈ s, ∀ Q ∈ s, ∀ R ∈ s, P = Q ∨ P = R ∨ Q = R ∨ idet3 P Q R ≠ 0) :
    NoThreeCollinear s := by
  intro P hP Q hQ R hR hcol
  rcases h P hP Q hQ R hR with h1 | h1 | h1 | hdet
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)
  · exact absurd (by exact_mod_cast (det3_toReal_eq_idet3 P Q R ▸ collinear_imp_det3_zero hcol))
      hdet

/-- A concrete `5`-point no-three-collinear set (the Erdős parabola for `p = 5`), certified
end-to-end by `native_decide` through the integer-determinant criterion. A computational
anti-vacuity witness: `NoThreeCollinear` is satisfiable by an explicit nonempty set. -/
theorem parabola5_noThreeCollinear :
    NoThreeCollinear ({(0, 0), (1, 1), (2, 4), (3, 4), (4, 1)} : Finset (ℕ × ℕ)) := by
  apply noThreeCollinear_of_idet
  native_decide

/-- Concrete witness that the **doubled hyperbola arc** (now wired into the `2(p−1)` lower bound,
`two_mul_pred_le_maxNoThreeInLine`) computes to a genuine non-vacuous no-three-collinear set:
`hyperbolaWide 3 1` is `4` points, certified via the integer-determinant criterion. Guards the
definition itself — `hyperbolaWide_noThreeCollinear` could be vacuous if the set were empty or
misdefined; this rules that out computationally. -/
theorem hyperbolaWide3_noThreeCollinear : NoThreeCollinear (hyperbolaWide 3 1) := by
  apply noThreeCollinear_of_idet
  native_decide

end LeanFormalizations.NoThreeInLine
