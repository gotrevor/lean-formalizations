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


/-! ### The doubled (wide) arc: `x ∈ [1, 2p) \ {p}`, `2(p−1)` points, no three collinear

Extending the `x`-range to `[1, 2p)` (dropping `x = p`, the only multiple of `p`) keeps the arc
free of three collinear points. Each residue `r ∈ [1, p)` now occurs at **two** abscissae `r` and
`r + p` (sharing a `y`), so a collinear triple cannot sneak in: if two points share a residue they
share a `y` (horizontal line), forcing the third onto the same height, hence the same residue — but
only two abscissae have a given residue, contradicting three distinct points. This is the precise
mechanism the HJSW covering relies on, isolated as a clean lemma. -/

/-- A point `< 2p` is its residue, or its residue shifted by `p`. -/
private theorem lt_two_mul_split {p x : ℕ} (hp : 0 < p) (h : x < 2 * p) :
    x = x % p ∨ x = x % p + p := by
  have hdm := Nat.div_add_mod x p
  have hd : x / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  interval_cases (x / p) <;> omega

/-- Horizontal-line collapse: if a real collinear triple has its first two `y`s equal (and distinct
`x`s), the third `y` equals them too. -/
private theorem y_eq_of_collinear_pair {a b c ya yb yc : ℝ}
    (hd : (b - a) * (yc - ya) - (c - a) * (yb - ya) = 0)
    (hyab : yb = ya) (hab : a ≠ b) : yc = ya := by
  rw [hyab, sub_self, mul_zero, sub_zero] at hd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (fun h => hab h.symm)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hba)

/-- Three pairwise-distinct abscissae in `[0, 2p)` cannot all share a residue mod `p`. -/
private theorem residue_pigeonhole {p a b c : ℕ} (hp0 : 0 < p)
    (ha : a < 2 * p) (hb : b < 2 * p) (hc : c < 2 * p)
    (eab : a % p = b % p) (eac : a % p = c % p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have sa := lt_two_mul_split hp0 ha
  have sb := lt_two_mul_split hp0 hb
  have sc := lt_two_mul_split hp0 hc
  omega

/-- `hyperbolaY` depends only on the residue of `x` mod `p`. -/
theorem hyperbolaY_residue {p k a b : ℕ} (h : (a : ZMod p) = (b : ZMod p)) :
    hyperbolaY p k a = hyperbolaY p k b := by
  unfold hyperbolaY; rw [h]

/-- With `k ≢ 0`, equal `y`-coordinates force equal residues (the `y`-map is injective on
nonzero residues). -/
theorem hyperbolaY_inj_residue {p k a c : ℕ} [Fact p.Prime] (hk : (k : ZMod p) ≠ 0)
    (_ha : (a : ZMod p) ≠ 0) (_hc : (c : ZMod p) ≠ 0)
    (h : hyperbolaY p k a = hyperbolaY p k c) : (a : ZMod p) = (c : ZMod p) := by
  unfold hyperbolaY at h
  have h2 : (k : ZMod p) * (a : ZMod p)⁻¹ = (k : ZMod p) * (c : ZMod p)⁻¹ :=
    ZMod.val_injective p h
  exact inv_inj.mp (mul_left_cancel₀ hk h2)

/-- The doubled hyperbola arc `xy ≡ k (mod p)` over `x ∈ [1, 2p) \ {p}`, in the `2p × 2p` grid. -/
def hyperbolaWide (p k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 p) ∪ (Finset.Ico (p + 1) (2 * p))).image (fun x => (x, hyperbolaY p k x))

/-- The doubled arc has `2(p − 1)` points (two abscissae `r`, `r + p` per nonzero residue). -/
theorem hyperbolaWide_card {p k : ℕ} : (hyperbolaWide p k).card = 2 * (p - 1) := by
  have hinj : Function.Injective (fun x => (x, hyperbolaY p k x)) := by
    intro i j hij; simpa using congrArg Prod.fst hij
  have hdisj : Disjoint (Finset.Ico 1 p) (Finset.Ico (p + 1) (2 * p)) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hyperbolaWide, Finset.card_image_of_injective _ hinj,
    Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.card_Ico]
  omega

/-- The doubled arc lies in the `2p × 2p` grid. -/
theorem hyperbolaWide_grid {p k : ℕ} (hp : 0 < p) : IsGridSet (2 * p) (hyperbolaWide p k) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  intro x hx
  simp only [hyperbolaWide, Finset.mem_image, Finset.mem_union, Finset.mem_Ico] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨by rcases hi with ⟨_, r⟩ | ⟨_, r⟩ <;> omega, ?_⟩
  exact (ZMod.val_lt _).trans_le (by omega)

/-- `(a : ZMod p) ≠ 0` for any `a ∈ [1, 2p) \ {p}` (the only multiple of `p` there is `p`). -/
private theorem cast_ne_zero_wide {p a : ℕ} (_hp0 : 0 < p) (ha1 : 1 ≤ a) (ha2 : a < 2 * p)
    (hap : a ≠ p) : (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  rintro ⟨t, rfl⟩
  have ht2 : t < 2 := by
    by_contra h; rw [Nat.not_lt] at h
    have hle := Nat.mul_le_mul_right p h
    rw [mul_comm t p] at hle
    omega
  interval_cases t <;> omega

/-- **No three points of the doubled hyperbola arc are collinear** (`p` prime, `k ≢ 0`). The new
content over the single arc: two points may share a residue (hence a `y`); the horizontal-line
collapse (`y_eq_of_collinear_pair`) then forces the third to the same residue, and
`residue_pigeonhole` rules that out for three distinct abscissae. -/
theorem hyperbolaWide_noThreeCollinear {p k : ℕ} (hp : p.Prime) (hk : (k : ZMod p) ≠ 0) :
    NoThreeCollinear (hyperbolaWide p k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hp0 := hp.pos
  intro P hP Q hQ R hR hcol
  simp only [hyperbolaWide, Finset.mem_image, Finset.mem_union, Finset.mem_Ico] at hP hQ hR
  obtain ⟨a, haD, rfl⟩ := hP
  obtain ⟨b, hbD, rfl⟩ := hQ
  obtain ⟨c, hcD, rfl⟩ := hR
  obtain ⟨ha1, ha2, hap⟩ : 1 ≤ a ∧ a < 2 * p ∧ a ≠ p := by rcases haD with ⟨l, r⟩ | ⟨l, r⟩ <;> omega
  obtain ⟨hb1, hb2, hbp⟩ : 1 ≤ b ∧ b < 2 * p ∧ b ≠ p := by rcases hbD with ⟨l, r⟩ | ⟨l, r⟩ <;> omega
  obtain ⟨hc1, hc2, hcp⟩ : 1 ≤ c ∧ c < 2 * p ∧ c ≠ p := by rcases hcD with ⟨l, r⟩ | ⟨l, r⟩ <;> omega
  have hA : (a : ZMod p) ≠ 0 := cast_ne_zero_wide hp0 ha1 ha2 hap
  have hB : (b : ZMod p) ≠ 0 := cast_ne_zero_wide hp0 hb1 hb2 hbp
  have hC : (c : ZMod p) ≠ 0 := cast_ne_zero_wide hp0 hc1 hc2 hcp
  -- real determinant vanishes
  have d0 := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at d0
  -- integer determinant, reduced mod p, factored
  have hZ : ((b : ℤ) - a) * ((hyperbolaY p k c : ℤ) - hyperbolaY p k a)
      - ((c : ℤ) - a) * ((hyperbolaY p k b : ℤ) - hyperbolaY p k a) = 0 := by exact_mod_cast d0
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast at hcast
  have rA := hyperbola_xy_eq (k := k) hA
  have rB := hyperbola_xy_eq (k := k) hB
  have rC := hyperbola_xy_eq (k := k) hC
  have key : (k : ZMod p) * (((a : ZMod p) - b) * ((a : ZMod p) - c) * ((b : ZMod p) - c)) = 0 := by
    linear_combination (-(a : ZMod p) * b * c) * hcast
      + ((b : ZMod p) * c * (c - b)) * rA
      - ((a : ZMod p) * c * (c - a)) * rB
      + ((a : ZMod p) * b * (b - a)) * rC
  have prod := (mul_eq_zero.mp key).resolve_left hk
  -- if any two abscissae coincide we are done; otherwise derive a contradiction
  by_cases hab : a = b
  · exact Or.inl (by rw [hab])
  by_cases hac : a = c
  · exact Or.inr (Or.inl (by rw [hac]))
  by_cases hbc : b = c
  · exact Or.inr (Or.inr (by rw [hbc]))
  exfalso
  rcases mul_eq_zero.mp prod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · -- a ≡ b : third forced to share residue with a
      have hres : (a : ZMod p) = (b : ZMod p) := sub_eq_zero.mp h1
      have hyab : (hyperbolaY p k b : ℝ) = (hyperbolaY p k a : ℝ) := by
        exact_mod_cast (hyperbolaY_residue hres).symm
      have hyc : (hyperbolaY p k c : ℝ) = (hyperbolaY p k a : ℝ) :=
        y_eq_of_collinear_pair d0 hyab (by exact_mod_cast hab)
      have hresc : (c : ZMod p) = (a : ZMod p) :=
        hyperbolaY_inj_residue hk hC hA (by exact_mod_cast hyc)
      exact residue_pigeonhole hp0 ha2 hb2 hc2
        ((ZMod.natCast_eq_natCast_iff' a b p).mp hres)
        ((ZMod.natCast_eq_natCast_iff' a c p).mp hresc.symm) hab hac hbc
    · -- a ≡ c : third (b) forced to share residue with a
      have hres : (a : ZMod p) = (c : ZMod p) := sub_eq_zero.mp h2
      have hyac : (hyperbolaY p k c : ℝ) = (hyperbolaY p k a : ℝ) := by
        exact_mod_cast (hyperbolaY_residue hres).symm
      have hd' : ((c : ℝ) - a) * ((hyperbolaY p k b : ℝ) - (hyperbolaY p k a : ℝ))
          - ((b : ℝ) - a) * ((hyperbolaY p k c : ℝ) - (hyperbolaY p k a : ℝ)) = 0 := by
        linear_combination -d0
      have hyb : (hyperbolaY p k b : ℝ) = (hyperbolaY p k a : ℝ) :=
        y_eq_of_collinear_pair hd' hyac (by exact_mod_cast hac)
      have hresb : (b : ZMod p) = (a : ZMod p) :=
        hyperbolaY_inj_residue hk hB hA (by exact_mod_cast hyb)
      exact residue_pigeonhole hp0 ha2 hb2 hc2
        ((ZMod.natCast_eq_natCast_iff' a b p).mp hresb.symm)
        ((ZMod.natCast_eq_natCast_iff' a c p).mp hres) hab hac hbc
  · -- b ≡ c : third (a) forced to share residue with b
    have hres : (b : ZMod p) = (c : ZMod p) := sub_eq_zero.mp h3
    have hybc : (hyperbolaY p k c : ℝ) = (hyperbolaY p k b : ℝ) := by
      exact_mod_cast (hyperbolaY_residue hres).symm
    have hd' : ((c : ℝ) - b) * ((hyperbolaY p k a : ℝ) - (hyperbolaY p k b : ℝ))
        - ((a : ℝ) - b) * ((hyperbolaY p k c : ℝ) - (hyperbolaY p k b : ℝ)) = 0 := by
      linear_combination d0
    have hya : (hyperbolaY p k a : ℝ) = (hyperbolaY p k b : ℝ) :=
      y_eq_of_collinear_pair hd' hybc (by exact_mod_cast hbc)
    have hresa : (a : ZMod p) = (b : ZMod p) :=
      hyperbolaY_inj_residue hk hA hB (by exact_mod_cast hya)
    exact residue_pigeonhole hp0 ha2 hb2 hc2
      ((ZMod.natCast_eq_natCast_iff' a b p).mp hresa)
      ((ZMod.natCast_eq_natCast_iff' a c p).mp (hresa.trans hres)) hab hac hbc

end LeanFormalizations.NoThreeInLine
