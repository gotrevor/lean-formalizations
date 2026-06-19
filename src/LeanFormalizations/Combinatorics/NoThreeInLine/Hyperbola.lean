/-
# The hyperbola arc: no three collinear on `xy ≡ k (mod p)`

The algebraic crux of the **Hall–Jackson–Sudbery–Wild `3N/2`** construction (1975), the best
*proven* lower bound for the no-three-in-line problem. Where Erdős uses the parabola
`(i, i² mod p)`, HJSW uses the hyperbola `xy ≡ k (mod p)`. This file formalizes the foundational
fact (PLAN item A, piece 1): **no three points of a single hyperbola arc are collinear.**

For a prime `p` and `k ≢ 0`, the `p − 1` points `(x, (k·x⁻¹) mod p)`, `x ∈ [1, p)`, lie in the
`p × p` grid and have no three collinear. The arithmetic heart mirrors the parabola, but the
factorisation is genuinely different: three points collinear over `ℝ` force the integer
determinant to vanish, hence vanish mod `p`. Multiplying the mod-`p` determinant by `x_a x_b x_c`
(all nonzero) and using `x·y ≡ k` on each point collapses it to
`−k · (a−b)(a−c)(b−c) ≡ 0 (mod p)`. As `ZMod p` is a field and `k ≢ 0`, two of `a, b, c` agree
mod `p`; being `< p`, they are equal, so two of the points coincide.

The single most reusable lemma is `hyperbola_xy_eq` (`x·y ≡ k` on each point): it is what makes
the `ZMod p` determinant factor without ever computing an explicit inverse in the algebra.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Collinearity
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- The `y`-coordinate of the hyperbola point at `x`: `(k · x⁻¹) mod p`, taken as a residue
in `[0, p)`. -/
def hyperbolaY (p k x : ℕ) : ℕ := ((k : ZMod p) * (x : ZMod p)⁻¹).val

/-- The hyperbola arc `xy ≡ k (mod p)` in the `p × p` grid: `(x, (k·x⁻¹) mod p)` for
`x ∈ [1, p)`. -/
def hyperbola (p k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 p).image (fun x => (x, hyperbolaY p k x))

/-- The defining relation, in `ZMod p`: every hyperbola point satisfies `x · y = k`. -/
theorem hyperbola_xy_eq {p k x : ℕ} [Fact p.Prime] (hx : (x : ZMod p) ≠ 0) :
    (x : ZMod p) * (hyperbolaY p k x : ZMod p) = (k : ZMod p) := by
  unfold hyperbolaY
  rw [ZMod.natCast_rightInverse ((k : ZMod p) * (x : ZMod p)⁻¹)]
  field_simp

/-- The hyperbola arc has exactly `p − 1` points (the first coordinates are distinct). -/
theorem hyperbola_card (p k : ℕ) : (hyperbola p k).card = p - 1 := by
  have hinj : Function.Injective (fun x => (x, hyperbolaY p k x)) := by
    intro i j hij; simpa using congrArg Prod.fst hij
  rw [hyperbola, Finset.card_image_of_injective _ hinj, Nat.card_Ico]

/-- The hyperbola arc lies in the `p × p` grid. -/
theorem hyperbola_grid {p k : ℕ} (hp : 0 < p) : IsGridSet p (hyperbola p k) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  intro x hx
  simp only [hyperbola, Finset.mem_image, Finset.mem_Ico] at hx
  obtain ⟨i, ⟨_, hi⟩, rfl⟩ := hx
  exact ⟨hi, ZMod.val_lt _⟩

/-- A residue `< p` that is nonzero in `ℕ` is nonzero in `ZMod p`. -/
private theorem cast_ne_zero_of_pos_lt {p a : ℕ} [NeZero p] (ha0 : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd ha0 hdvd
  omega

/-- **No three points of the hyperbola arc `xy ≡ k (mod p)` are collinear** (`k ≢ 0`, `p`
prime). The genuinely new ingredient over the parabola: the mod-`p` determinant is collapsed
using the defining relation `x·y = k` on each point (`hyperbola_xy_eq`), giving
`−k·(a−b)(a−c)(b−c) ≡ 0`; the field `ZMod p` and `k ≢ 0` then force two coordinates to agree. -/
theorem hyperbola_noThreeCollinear {p k : ℕ} (hp : p.Prime) (hk : (k : ZMod p) ≠ 0) :
    NoThreeCollinear (hyperbola p k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  intro P hP Q hQ R hR hcol
  simp only [hyperbola, Finset.mem_image, Finset.mem_Ico] at hP hQ hR
  obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := hP
  obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := hQ
  obtain ⟨c, ⟨hc1, hc2⟩, rfl⟩ := hR
  have hA : (a : ZMod p) ≠ 0 := cast_ne_zero_of_pos_lt ha1 ha2
  have hB : (b : ZMod p) ≠ 0 := cast_ne_zero_of_pos_lt hb1 hb2
  have hC : (c : ZMod p) ≠ 0 := cast_ne_zero_of_pos_lt hc1 hc2
  -- Collinearity ⇒ real determinant vanishes ⇒ integer determinant vanishes.
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((b : ℤ) - a) * ((hyperbolaY p k c : ℤ) - hyperbolaY p k a)
      - ((c : ℤ) - a) * ((hyperbolaY p k b : ℤ) - hyperbolaY p k a) = 0 := by
    exact_mod_cast hdet
  -- Reduce mod p.
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast at hcast
  -- The defining relations `x·y = k` (mod p) on each point.
  have rA := hyperbola_xy_eq (k := k) hA
  have rB := hyperbola_xy_eq (k := k) hB
  have rC := hyperbola_xy_eq (k := k) hC
  -- Collapse: x_a x_b x_c · det = −k·(a−b)(a−c)(b−c).
  have key : (k : ZMod p) * (((a : ZMod p) - b) * ((a : ZMod p) - c) * ((b : ZMod p) - c)) = 0 := by
    linear_combination (-(a : ZMod p) * b * c) * hcast
      + ((b : ZMod p) * c * (c - b)) * rA
      - ((a : ZMod p) * c * (c - a)) * rB
      + ((a : ZMod p) * b * (b - a)) * rC
  -- A field with k ≠ 0 forces two of a, b, c to agree mod p, hence be equal.
  have prod := (mul_eq_zero.mp key).resolve_left hk
  rcases mul_eq_zero.mp prod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · left
      have : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp (sub_eq_zero.mp h1)
      rw [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at this
      rw [this]
    · right; left
      have : a % p = c % p := (ZMod.natCast_eq_natCast_iff' a c p).mp (sub_eq_zero.mp h2)
      rw [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hc2] at this
      rw [this]
  · right; right
    have : b % p = c % p := (ZMod.natCast_eq_natCast_iff' b c p).mp (sub_eq_zero.mp h3)
    rw [Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hc2] at this
    rw [this]

end LeanFormalizations.NoThreeInLine
