/-
# The Erdős parabola lower bound: `Θ(N)` points with no three collinear

Erdős's construction. For a prime `p`, the `p` points `(i, i² mod p)`, `i ∈ [0, p)`, lie in
the `p × p` grid and have **no three collinear**. Hence the grid maximum is at least `p`,
which (with the `2N` upper bound) pins its order at `Θ(N)`.

**Why no three are collinear** — the formalizable arithmetic heart. Three of the points are
collinear over `ℝ` iff the integer determinant
`D = (b−a)(c²%p − a²%p) − (c−a)(b²%p − a²%p)` vanishes. Reducing mod `p`, since
`i²%p ≡ i² (mod p)`,
`D ≡ (b−a)(c²−a²) − (c−a)(b²−a²) = (b−a)(c−a)(c−b)  (mod p)`.
As `ZMod p` is a field (an integral domain), `D ≡ 0` forces one factor to vanish, i.e. two of
`a, b, c` agree mod `p`; being `< p`, they are equal, so two of the points coincide. The
primality does exactly one job: making `ZMod p` a domain.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Collinearity
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- The Erdős parabola point set in the `p × p` grid: `(i, i² mod p)` for `i ∈ [0, p)`. -/
def parabola (p : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range p).image (fun i => (i, i ^ 2 % p))

/-- The parabola set has exactly `p` points (the first coordinates are distinct). -/
theorem parabola_card (p : ℕ) : (parabola p).card = p := by
  have hinj : Function.Injective (fun i => (i, i ^ 2 % p)) := by
    intro i j hij; simpa using congrArg Prod.fst hij
  rw [parabola, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- The parabola set lies in the `p × p` grid. -/
theorem parabola_grid {p : ℕ} (hp : 0 < p) : IsGridSet p (parabola p) := by
  intro x hx
  simp only [parabola, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨hi, Nat.mod_lt _ hp⟩

/-- **No three points of the Erdős parabola set are collinear.** -/
theorem parabola_noThreeCollinear {p : ℕ} (hp : p.Prime) :
    NoThreeCollinear (parabola p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro P hP Q hQ R hR hcol
  simp only [parabola, Finset.mem_image, Finset.mem_range] at hP hQ hR
  obtain ⟨a, ha, rfl⟩ := hP
  obtain ⟨b, hb, rfl⟩ := hQ
  obtain ⟨c, hc, rfl⟩ := hR
  -- Collinearity ⇒ the real determinant vanishes.
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  -- The same determinant as an integer equation.
  have hZ : (b - a : ℤ) * ((c ^ 2 % p : ℕ) - (a ^ 2 % p : ℕ))
      - (c - a) * ((b ^ 2 % p : ℕ) - (a ^ 2 % p : ℕ)) = 0 := by
    exact_mod_cast hdet
  -- Reduce mod p and factor.
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast [ZMod.natCast_mod] at hcast
  have hz : ((b : ZMod p) - a) * ((c : ZMod p) - a) * ((c : ZMod p) - b) = 0 := by
    linear_combination hcast
  -- A field is a domain: one factor is zero, so two of a, b, c agree mod p, hence are equal.
  rcases mul_eq_zero.mp hz with hxy | h3
  · rcases mul_eq_zero.mp hxy with h1 | h2
    · left
      have : b % p = a % p := (ZMod.natCast_eq_natCast_iff' b a p).mp (sub_eq_zero.mp h1)
      rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] at this
      rw [this]
    · right; left
      have : c % p = a % p := (ZMod.natCast_eq_natCast_iff' c a p).mp (sub_eq_zero.mp h2)
      rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt ha] at this
      rw [this]
  · right; right
    have : c % p = b % p := (ZMod.natCast_eq_natCast_iff' c b p).mp (sub_eq_zero.mp h3)
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hb] at this
    rw [this]

end LeanFormalizations.NoThreeInLine
