/-
# The general HJSW Lemma: a line meets the hyperbola in ≤ 2 congruence classes

This is the load-bearing lemma of the **Hall–Jackson–Sudbery–Wild `3(p−1)` pinwheel**
(J. Combin. Theory Ser. A 18 (1975) 336–341, Theorem 2). Where `Hyperbola.lean` proves the
*arc-restricted* corollary (one representative per residue ⇒ no three collinear), the pinwheel
covering needs the genuine general form:

> **Lemma (HJSW, p. 337).** If three points of the full modular hyperbola
> `H(k,p) = {(x,y) : x·y ≡ k (mod p)}` lie on a straight line, two of them are *congruent*
> (mod p), i.e. share both coordinate residues.

The proof is the same determinant collapse as the arc case, but stated for *arbitrary* lattice
points `(xᵢ, yᵢ)` satisfying `xᵢ·yᵢ ≡ k` rather than the parametrized points `(x, k·x⁻¹ mod p)`:
collinearity forces the integer determinant to vanish, hence vanish mod `p`; multiplying by
`x_a x_b x_c` (all nonzero) and using `xᵢyᵢ = k` collapses it to `−k·(a−b)(a−c)(b−c) ≡ 0`. As
`ZMod p` is a field and `k ≢ 0`, two `x`-residues agree; the relation then forces the matching
`y`-residues to agree too (`y ≡ k·x⁻¹`). So the two points are congruent.

The block argument (`§2` of the construction) consumes this as: any line through three points of
`N_set` has two congruent ones, which (since congruence preserves the quadrant-family) must lie in
the same family — reducing no-three-in-line to a finite slope/incidence check.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- **The HJSW collapse, residue form.** Three lattice points on the hyperbola `x·y ≡ k (mod p)`
(`xᵢ ≢ 0`, `k ≢ 0`) that are collinear over `ℝ` have two of their `x`-residues equal. This is the
determinant collapse `−k·(a−b)(a−c)(b−c) ≡ 0` over the field `ZMod p`. -/
theorem hyperbola_line_x_residue_eq {p k : ℕ} [Fact p.Prime] (hk : (k : ZMod p) ≠ 0)
    {xa ya xb yb xc yc : ℕ}
    (rA : (xa : ZMod p) * (ya : ZMod p) = k)
    (rB : (xb : ZMod p) * (yb : ZMod p) = k)
    (rC : (xc : ZMod p) * (yc : ZMod p) = k)
    (hcol : Collinear ℝ ({toReal (xa, ya), toReal (xb, yb), toReal (xc, yc)} : Set (ℝ × ℝ))) :
    (xa : ZMod p) = xb ∨ (xa : ZMod p) = xc ∨ (xb : ZMod p) = xc := by
  -- Collinearity ⇒ real determinant vanishes ⇒ integer determinant vanishes ⇒ reduce mod p.
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((xb : ℤ) - xa) * ((yc : ℤ) - ya) - ((xc : ℤ) - xa) * ((yb : ℤ) - ya) = 0 := by
    exact_mod_cast hdet
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast at hcast
  -- The determinant collapses to `k·(a−b)(a−c)(b−c) = 0`.
  have key : (k : ZMod p) * (((xa : ZMod p) - xb) * ((xa : ZMod p) - xc) * ((xb : ZMod p) - xc)) = 0 := by
    linear_combination (-(xa : ZMod p) * xb * xc) * hcast
      + ((xb : ZMod p) * xc * (xc - xb)) * rA
      - ((xa : ZMod p) * xc * (xc - xa)) * rB
      + ((xa : ZMod p) * xb * (xb - xa)) * rC
  have prod := (mul_eq_zero.mp key).resolve_left hk
  rcases mul_eq_zero.mp prod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h3))

/-- On the hyperbola, equal `x`-residue forces equal `y`-residue (`y ≡ k·x⁻¹`): two such points are
**congruent** mod `p`. -/
theorem hyperbola_y_residue_eq_of_x {p k : ℕ} [Fact p.Prime]
    {xa ya xb yb : ℕ} (hxa : (xa : ZMod p) ≠ 0)
    (rA : (xa : ZMod p) * (ya : ZMod p) = k)
    (rB : (xb : ZMod p) * (yb : ZMod p) = k)
    (hx : (xa : ZMod p) = xb) : (ya : ZMod p) = yb := by
  have : (xa : ZMod p) * (ya : ZMod p) = (xa : ZMod p) * (yb : ZMod p) := by
    rw [rA, hx, rB]
  exact mul_left_cancel₀ hxa this

/-- **The HJSW Lemma, congruence form.** Three collinear hyperbola points have two that are
*congruent* mod `p` (both coordinate residues agree). This is the exact statement the pinwheel
covering argument consumes. -/
theorem hyperbola_line_two_congruent {p k : ℕ} [Fact p.Prime] (hk : (k : ZMod p) ≠ 0)
    {xa ya xb yb xc yc : ℕ}
    (hxa : (xa : ZMod p) ≠ 0) (hxb : (xb : ZMod p) ≠ 0) (_hxc : (xc : ZMod p) ≠ 0)
    (rA : (xa : ZMod p) * (ya : ZMod p) = k)
    (rB : (xb : ZMod p) * (yb : ZMod p) = k)
    (rC : (xc : ZMod p) * (yc : ZMod p) = k)
    (hcol : Collinear ℝ ({toReal (xa, ya), toReal (xb, yb), toReal (xc, yc)} : Set (ℝ × ℝ))) :
    ((xa : ZMod p) = xb ∧ (ya : ZMod p) = yb) ∨
    ((xa : ZMod p) = xc ∧ (ya : ZMod p) = yc) ∨
    ((xb : ZMod p) = xc ∧ (yb : ZMod p) = yc) := by
  rcases hyperbola_line_x_residue_eq hk rA rB rC hcol with h | h | h
  · exact Or.inl ⟨h, hyperbola_y_residue_eq_of_x hxa rA rB h⟩
  · exact Or.inr (Or.inl ⟨h, hyperbola_y_residue_eq_of_x hxa rA rC h⟩)
  · exact Or.inr (Or.inr ⟨h, hyperbola_y_residue_eq_of_x hxb rB rC h⟩)

end LeanFormalizations.NoThreeInLine
