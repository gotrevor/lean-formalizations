/-
# Hall–Jackson–Sudbery–Wild `3N/2` lower bound — FRONTIER (in progress)

The best *proven* lower bound for the no-three-in-line problem (1975), unimproved since.
Improves Erdős's `~N` parabola to `3(N−2)/2` via the hyperbola `x·y ≡ k (mod p)`.

**This file is the active treadmill target.** The headline `hjsw_lower` below is still a `sorry`
placeholder (the `3/2` covering count is the hard mile). What IS proven and axiom-clean here is the
reusable building block: **the modular-hyperbola arc has no three collinear points** — the analogue
of `parabola_noThreeCollinear`, with the Vandermonde determinant identity worked out for the
hyperbola `x·y ≡ k (mod p)`. See `PLAN.md` and `HANDOFF.md`.

## The arc non-collinearity argument (proven below)
Three grid points `(aᵢ, yᵢ)` on the arc satisfy `aᵢ · yᵢ ≡ k (mod p)`. Collinearity over `ℝ`
forces the integer determinant to vanish, and mod `p` that determinant `D` obeys the identity
`k · (a₁−a₂)(a₂−a₃)(a₃−a₁) = a₁a₂a₃ · D`  (a Vandermonde reduction, using `aᵢyᵢ = k`).
With `k ≢ 0` and `ZMod p` a domain, `D ≡ 0` forces two of the `aᵢ` to agree mod `p`, hence (being
`< p`) to be equal — so two of the points coincide. Primality does exactly one job: `ZMod p` a field.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound
import LeanFormalizations.Combinatorics.NoThreeInLine.Parabola
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

namespace LeanFormalizations.NoThreeInLine

open Finset

/-- The modular-hyperbola arc in the `p × p` grid: the points `(a, val(k · a⁻¹ mod p))` for nonzero
`a ∈ [0, p)`. For `p` prime and `k ≢ 0 (mod p)` these are the `p − 1` solutions of `x·y ≡ k (mod p)`
with `x ≠ 0`. -/
def hyperbola (p k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range p).erase 0).image (fun a => (a, (↑k * (↑a : ZMod p)⁻¹).val))

/-- The arc has exactly `p − 1` points (the first coordinates are the nonzero residues). -/
theorem hyperbola_card {p : ℕ} (hp : 0 < p) (k : ℕ) : (hyperbola p k).card = p - 1 := by
  have hinj : Function.Injective (fun a : ℕ => (a, (↑k * (↑a : ZMod p)⁻¹).val)) := by
    intro i j hij; simpa using congrArg Prod.fst hij
  rw [hyperbola, Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_range.mpr hp), Finset.card_range]

/-- The arc lies in the `p × p` grid. -/
theorem hyperbola_grid {p : ℕ} (hp : 0 < p) (k : ℕ) : IsGridSet p (hyperbola p k) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  intro x hx
  simp only [hyperbola, Finset.mem_image, Finset.mem_erase, Finset.mem_range] at hx
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hx
  exact ⟨ha, ZMod.val_lt _⟩

/-- **No three points of the modular-hyperbola arc are collinear.** -/
theorem hyperbola_noThreeCollinear {p k : ℕ} (hp : p.Prime) (hk : ¬ (p ∣ k)) :
    NoThreeCollinear (hyperbola p k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  intro P hP Q hQ R hR hcol
  simp only [hyperbola, Finset.mem_image, Finset.mem_erase, Finset.mem_range] at hP hQ hR
  obtain ⟨a, ⟨ha0, ha⟩, rfl⟩ := hP
  obtain ⟨b, ⟨hb0, hb⟩, rfl⟩ := hQ
  obtain ⟨c, ⟨hc0, hc⟩, rfl⟩ := hR
  -- Collinearity ⇒ the real determinant vanishes.
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  -- Cast the determinant equation into `ZMod p` (it is a ℤ-equation between nat-casts).
  have hcast : (((b : ZMod p) - a) * (((↑k * (↑c : ZMod p)⁻¹).val : ZMod p) - (↑k * (↑a : ZMod p)⁻¹).val)
      - ((c : ZMod p) - a) * (((↑k * (↑b : ZMod p)⁻¹).val : ZMod p) - (↑k * (↑a : ZMod p)⁻¹).val)) = 0 := by
    have : ((b : ℝ) - a) * (((↑k * (↑c : ZMod p)⁻¹).val : ℝ) - (↑k * (↑a : ZMod p)⁻¹).val)
        - ((c : ℝ) - a) * (((↑k * (↑b : ZMod p)⁻¹).val : ℝ) - (↑k * (↑a : ZMod p)⁻¹).val) = 0 := hdet
    have hZ : ((b : ℤ) - a) * (((↑k * (↑c : ZMod p)⁻¹).val : ℤ) - (↑k * (↑a : ZMod p)⁻¹).val)
        - ((c : ℤ) - a) * (((↑k * (↑b : ZMod p)⁻¹).val : ℤ) - (↑k * (↑a : ZMod p)⁻¹).val) = 0 := by
      exact_mod_cast this
    have := congrArg (Int.cast : ℤ → ZMod p) hZ
    push_cast at this
    convert this using 2
  -- Abbreviate.  We deliberately do NOT fold `↑a, ↑b, ↑c` (they live inside the grid coordinates,
  -- which the final `rw` of a nat-equality must still reach).
  set kZ : ZMod p := (k : ZMod p) with hkZ
  set yaZ : ZMod p := ((↑k * (↑a : ZMod p)⁻¹).val : ZMod p) with hyaZ
  set ybZ : ZMod p := ((↑k * (↑b : ZMod p)⁻¹).val : ZMod p) with hybZ
  set ycZ : ZMod p := ((↑k * (↑c : ZMod p)⁻¹).val : ZMod p) with hycZ
  -- Each first coordinate is a nonzero residue.
  have hane : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => ha0 (Nat.eq_zero_of_dvd_of_lt h ha ▸ rfl)
  have hbne : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hb0 (Nat.eq_zero_of_dvd_of_lt h hb ▸ rfl)
  have hcne : (c : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h hc ▸ rfl)
  have hkne : kZ ≠ 0 := by rw [hkZ, Ne, ZMod.natCast_eq_zero_iff]; exact hk
  -- The hyperbola relations `aᵢ · yᵢ = k`.
  have ea : (a : ZMod p) * yaZ = kZ := by
    rw [hyaZ, ZMod.natCast_rightInverse, hkZ, mul_comm, mul_assoc, inv_mul_cancel₀ hane, mul_one]
  have eb : (b : ZMod p) * ybZ = kZ := by
    rw [hybZ, ZMod.natCast_rightInverse, hkZ, mul_comm, mul_assoc, inv_mul_cancel₀ hbne, mul_one]
  have ec : (c : ZMod p) * ycZ = kZ := by
    rw [hycZ, ZMod.natCast_rightInverse, hkZ, mul_comm, mul_assoc, inv_mul_cancel₀ hcne, mul_one]
  -- The Vandermonde reduction: `k·(a−b)(b−c)(c−a) = a·b·c · D`, with `D` the vanishing determinant.
  have hprod : kZ * (((a : ZMod p) - b) * ((b : ZMod p) - c) * ((c : ZMod p) - a)) = 0 := by
    have identity : kZ * (((a : ZMod p) - b) * ((b : ZMod p) - c) * ((c : ZMod p) - a))
        = (a : ZMod p) * b * c * ((((b : ZMod p) - a) * (ycZ - yaZ)) - (((c : ZMod p) - a) * (ybZ - yaZ))) := by
      linear_combination (-((b : ZMod p) * c * (c - b))) * ea + (-((a : ZMod p) * c * (a - c))) * eb
        + (-((a : ZMod p) * b * (b - a))) * ec
    rw [identity, hcast, mul_zero]
  -- A domain: one factor of the product is zero, so two of `a, b, c` agree mod p, hence are equal.
  have hprod' : ((a : ZMod p) - b) * ((b : ZMod p) - c) * ((c : ZMod p) - a) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hkne
    · exact h
  rcases mul_eq_zero.mp hprod' with hxy | h3
  · rcases mul_eq_zero.mp hxy with h1 | h2
    · left
      have hab : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp (sub_eq_zero.mp h1)
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
      rw [hab]
    · right; right
      have hbc : b % p = c % p := (ZMod.natCast_eq_natCast_iff' b c p).mp (sub_eq_zero.mp h2)
      rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc] at hbc
      rw [hbc]
  · right; left
    have hca : c % p = a % p := (ZMod.natCast_eq_natCast_iff' c a p).mp (sub_eq_zero.mp h3)
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt ha] at hca
    rw [hca]

/-! ## Reduction toolkit for the lifted construction (the covering count)

The HJSW construction places its `3(p−1)` points in the `2p × 2p` grid as **lifts** of the
`p × p` modular hyperbola: each base point `(a, ā)` (with `a·ā ≡ k`) has four lifts
`(a + εp, ā + δp)`, `ε, δ ∈ {0,1}`. The lemmas below isolate the *geometric* content of
"no three of the chosen lifts are collinear" so that the only remaining obligation is the
*combinatorial* choice of which lifts to keep.

The key reduction (`hyperbola_lift_collinear_share_residue`): **any** three real-collinear grid
points whose residues lie on one modular hyperbola must have two points sharing the same residue
mod `p` — i.e. being two lifts of the *same* base point. (Proof: reduce the integer collinearity
determinant mod `p`; the mod-`p` Vandermonde core `hyperbola_collinear_zmod` then forces two
residues to coincide.) Combined with `coord_diff_of_residue_eq` (two same-residue grid points in
`[0,2p)` differ by `0` or `±p` in each coordinate), this shows the only possible collinear triples
are "two lifts of one base point + one lift of another, on a line of slope `0, ∞, +1` or `−1`" —
exactly the slope-`±1` obstruction recorded in `PLAN.md`. The covering count is then the purely
combinatorial task of choosing lifts so no such slope-`±1` line carries three chosen points. -/

/-- **Mod-`p` Vandermonde core.** Three points of the modular hyperbola `x·y = k` over the field
`ZMod p` (`k ≠ 0`) whose `2×2` collinearity determinant vanishes must have two coordinates fully
coincide. This is the field-theoretic heart shared by the arc lemma and the lift reduction:
`k·(x₁−x₂)(x₂−x₃)(x₃−x₁) = x₁x₂x₃·D` with `D` the determinant, so `D = 0` and `k, xᵢ ≠ 0` force
two of the `xᵢ` equal; the hyperbola relation then equates the matching `yᵢ`. -/
theorem hyperbola_collinear_zmod {p : ℕ} [Fact p.Prime] {k : ZMod p} (hk : k ≠ 0)
    {x₁ y₁ x₂ y₂ x₃ y₃ : ZMod p}
    (h1 : x₁ * y₁ = k) (h2 : x₂ * y₂ = k) (h3 : x₃ * y₃ = k)
    (hdet : (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) = 0) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₃ ∧ y₁ = y₃) ∨ (x₂ = x₃ ∧ y₂ = y₃) := by
  have hx1 : x₁ ≠ 0 := fun h => hk (by rw [← h1, h, zero_mul])
  have hx2 : x₂ ≠ 0 := fun h => hk (by rw [← h2, h, zero_mul])
  have hprod : k * ((x₁ - x₂) * (x₂ - x₃) * (x₃ - x₁)) = 0 := by
    have identity : k * ((x₁ - x₂) * (x₂ - x₃) * (x₃ - x₁))
        = x₁ * x₂ * x₃ * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) := by
      linear_combination (-(x₂ * x₃ * (x₃ - x₂))) * h1 + (-(x₁ * x₃ * (x₁ - x₃))) * h2
        + (-(x₁ * x₂ * (x₂ - x₁))) * h3
    rw [identity, hdet, mul_zero]
  have hprod' : (x₁ - x₂) * (x₂ - x₃) * (x₃ - x₁) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hk
    · exact h
  rcases mul_eq_zero.mp hprod' with hxy | h31
  · rcases mul_eq_zero.mp hxy with h12 | h23
    · refine Or.inl ⟨sub_eq_zero.mp h12, mul_left_cancel₀ hx1 ?_⟩
      rw [h1, sub_eq_zero.mp h12, h2]
    · refine Or.inr (Or.inr ⟨sub_eq_zero.mp h23, mul_left_cancel₀ hx2 ?_⟩)
      rw [h2, sub_eq_zero.mp h23, h3]
  · refine Or.inr (Or.inl ⟨(sub_eq_zero.mp h31).symm, mul_left_cancel₀ hx1 ?_⟩)
    rw [h1, ← (sub_eq_zero.mp h31), h3]

/-- **Mod-`p` projection of real collinearity (construction-agnostic).** If three grid points are
collinear over `ℝ`, then the `2×2` collinearity determinant of their *residues* vanishes in
`ZMod p` — for every `p` and every base curve. This is the universal bridge that lets any base
set's mod-`p` non-collinearity rule out cross-residue collinear triples among its lifts: the
integer determinant is `0`, hence `0` mod `p`, and `ℤ → ZMod p` is a ring hom. -/
theorem collinear_imp_modp_det_zero (p : ℕ) {P Q R : ℕ × ℕ}
    (hcol : Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ))) :
    ((Q.1 : ZMod p) - P.1) * ((R.2 : ZMod p) - P.2)
      - ((R.1 : ZMod p) - P.1) * ((Q.2 : ZMod p) - P.2) = 0 := by
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((Q.1 : ℤ) - P.1) * ((R.2 : ℤ) - P.2) - ((R.1 : ℤ) - P.1) * ((Q.2 : ℤ) - P.2) = 0 := by
    exact_mod_cast hdet
  have h := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast at h
  linear_combination h

/-- **Lift reduction (the covering-count lever).** If three grid points `P, Q, R` whose residues
mod `p` all lie on the modular hyperbola `x·y ≡ k (mod p)` (`k ≢ 0`) are collinear over `ℝ`, then
two of them share the *same residue* mod `p` — i.e. are two lifts of one base hyperbola point.

This is the hyperbola twin of `hyperbola_noThreeCollinear` extended to the full `2p × 2p` lift
problem: collinearity between points on *different* lifted arcs (distinct residues) is impossible,
so the only collinear triples that survive are pairs of lifts of a single base point together with
a third point — reducing no-three-in-line to a finite slope-`±1` combinatorial condition. -/
theorem hyperbola_lift_collinear_share_residue {p k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k)
    {P Q R : ℕ × ℕ}
    (hP : (P.1 : ZMod p) * (P.2 : ZMod p) = (k : ZMod p))
    (hQ : (Q.1 : ZMod p) * (Q.2 : ZMod p) = (k : ZMod p))
    (hR : (R.1 : ZMod p) * (R.2 : ZMod p) = (k : ZMod p))
    (hcol : Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ))) :
    ((P.1 : ZMod p) = (Q.1 : ZMod p) ∧ (P.2 : ZMod p) = (Q.2 : ZMod p)) ∨
    ((P.1 : ZMod p) = (R.1 : ZMod p) ∧ (P.2 : ZMod p) = (R.2 : ZMod p)) ∨
    ((Q.1 : ZMod p) = (R.1 : ZMod p) ∧ (Q.2 : ZMod p) = (R.2 : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hkk : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hk
  exact hyperbola_collinear_zmod hkk hP hQ hR (collinear_imp_modp_det_zero p hcol)

/-- Two grid coordinates in `[0, 2p)` that are congruent mod `p` differ by `0` or exactly `p`.
(The lift structure: a residue `r ∈ [0, p)` has the two lifts `r` and `r + p` inside `[0, 2p)`.)
Together with `hyperbola_lift_collinear_share_residue` this pins every collinear triple of lifts to
two lifts of one base point — whose connecting line has slope `0, ∞, +1`, or `−1`. -/
theorem coord_diff_of_residue_eq {p a b : ℕ} (ha : a < 2 * p) (hb : b < 2 * p)
    (h : a % p = b % p) : a = b ∨ a = b + p ∨ b = a + p := by
  rcases Nat.lt_or_ge a p with ha1 | ha1 <;> rcases Nat.lt_or_ge b p with hb1 | hb1
  · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h; exact Or.inl h
  · rw [Nat.mod_eq_of_lt ha1] at h
    have hb2 : b % p = b - p := by rw [Nat.mod_eq_sub_mod hb1, Nat.mod_eq_of_lt (by omega)]
    rw [hb2] at h; exact Or.inr (Or.inr (by omega))
  · rw [Nat.mod_eq_of_lt hb1] at h
    have ha2 : a % p = a - p := by rw [Nat.mod_eq_sub_mod ha1, Nat.mod_eq_of_lt (by omega)]
    rw [ha2] at h; exact Or.inr (Or.inl (by omega))
  · have ha2 : a % p = a - p := by rw [Nat.mod_eq_sub_mod ha1, Nat.mod_eq_of_lt (by omega)]
    have hb2 : b % p = b - p := by rw [Nat.mod_eq_sub_mod hb1, Nat.mod_eq_of_lt (by omega)]
    rw [ha2, hb2] at h; exact Or.inl (by omega)

/-- A coordinate difference between two same-residue nats factors through `p`: writing each as
`residue + p·(·/p)`, the integer difference is `p` times the difference of the (nat) high parts. -/
theorem intCoord_diff_factor {p u v : ℕ} (h : u % p = v % p) :
    (u : ℤ) - (v : ℤ) = (p : ℤ) * (((u / p : ℕ) : ℤ) - ((v / p : ℕ) : ℤ)) := by
  have hu : (p : ℤ) * ((u / p : ℕ) : ℤ) + ((u % p : ℕ) : ℤ) = u := by exact_mod_cast Nat.div_add_mod u p
  have hv : (p : ℤ) * ((v / p : ℕ) : ℤ) + ((v % p : ℕ) : ℤ) = v := by exact_mod_cast Nat.div_add_mod v p
  have hmod : ((u % p : ℕ) : ℤ) = ((v % p : ℕ) : ℤ) := by exact_mod_cast h
  linear_combination -hu + hv + hmod

/-- **The same-base-point case.** Three *distinct* grid points in `[0,2p)²` that are pairwise
congruent mod `p` in both coordinates (i.e. three lifts of one base point) are never collinear:
they are three distinct corners of a `p × p` axis-aligned rectangle, so the integer orientation
determinant is `±p² ≠ 0`. Together with `*_lift_share_residue` this closes the geometry — every
collinear triple of lifts must be two lifts of one base point plus a lift of a *different* one. -/
theorem lift_triple_noncollinear {p : ℕ} (hp : 0 < p) {P Q R : ℕ × ℕ}
    (hP1 : P.1 < 2 * p) (hP2 : P.2 < 2 * p) (hQ1 : Q.1 < 2 * p) (hQ2 : Q.2 < 2 * p)
    (hR1 : R.1 < 2 * p) (hR2 : R.2 < 2 * p)
    (e1Q : P.1 % p = Q.1 % p) (e1R : P.1 % p = R.1 % p)
    (e2Q : P.2 % p = Q.2 % p) (e2R : P.2 % p = R.2 % p)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ¬ Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ)) := by
  intro hcol
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((Q.1 : ℤ) - P.1) * ((R.2 : ℤ) - P.2) - ((R.1 : ℤ) - P.1) * ((Q.2 : ℤ) - P.2) = 0 := by
    exact_mod_cast hdet
  -- factor each difference through `p`
  rw [intCoord_diff_factor e1Q.symm, intCoord_diff_factor e2R.symm,
      intCoord_diff_factor e1R.symm, intCoord_diff_factor e2Q.symm] at hZ
  -- hZ now reads `p² · B = 0`; since `p ≠ 0`, the high-bit determinant `B` vanishes
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hB : (((Q.1 / p : ℕ) : ℤ) - ((P.1 / p : ℕ) : ℤ)) * (((R.2 / p : ℕ) : ℤ) - ((P.2 / p : ℕ) : ℤ))
      - (((R.1 / p : ℕ) : ℤ) - ((P.1 / p : ℕ) : ℤ)) * (((Q.2 / p : ℕ) : ℤ) - ((P.2 / p : ℕ) : ℤ))
      = 0 := by
    have h2 : (p : ℤ) * p * ((((Q.1 / p : ℕ) : ℤ) - ((P.1 / p : ℕ) : ℤ))
          * (((R.2 / p : ℕ) : ℤ) - ((P.2 / p : ℕ) : ℤ))
        - (((R.1 / p : ℕ) : ℤ) - ((P.1 / p : ℕ) : ℤ))
          * (((Q.2 / p : ℕ) : ℤ) - ((P.2 / p : ℕ) : ℤ))) = 0 := by linear_combination hZ
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (mul_eq_zero.mp h |>.elim id id) hpZ
    · exact h
  -- the high parts are `0` or `1`; distinctness of the three corners contradicts `B = 0`
  have hb : ∀ {u : ℕ}, u < 2 * p → u / p = 0 ∨ u / p = 1 := by
    intro u hu
    have h2 : u / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    interval_cases (u / p) <;> tauto
  -- recompose: same residue + same high part ⇒ equal coordinate
  have recompose : ∀ {u v : ℕ}, u % p = v % p → u / p = v / p → u = v := by
    intro u v hm hd
    calc u = p * (u / p) + u % p := (Nat.div_add_mod u p).symm
      _ = p * (v / p) + v % p := by rw [hd, hm]
      _ = v := Nat.div_add_mod v p
  have dPQ : ¬ (P.1 / p = Q.1 / p ∧ P.2 / p = Q.2 / p) :=
    fun ⟨h1, h2⟩ => hPQ (Prod.ext (recompose e1Q h1) (recompose e2Q h2))
  have dPR : ¬ (P.1 / p = R.1 / p ∧ P.2 / p = R.2 / p) :=
    fun ⟨h1, h2⟩ => hPR (Prod.ext (recompose e1R h1) (recompose e2R h2))
  have dQR : ¬ (Q.1 / p = R.1 / p ∧ Q.2 / p = R.2 / p) :=
    fun ⟨h1, h2⟩ => hQR (Prod.ext (recompose (e1Q.symm.trans e1R) h1)
      (recompose (e2Q.symm.trans e2R) h2))
  rcases hb hP1 with a1 | a1 <;> rcases hb hP2 with a2 | a2 <;>
    rcases hb hQ1 with b1 | b1 <;> rcases hb hQ2 with b2 | b2 <;>
    rcases hb hR1 with c1 | c1 <;> rcases hb hR2 with c2 | c2 <;>
    (simp only [a1, a2, b1, b2, c1, c2] at hB dPQ dPR dQR; revert hB dPQ dPR dQR; decide)

/-! ### The sheared-hyperbola base (the current construction lead)

Computational search (lap 2026-06-19) found that the plain hyperbola `xy ≡ 1` (`|B| = p−1`) cannot
reach `3(p−1)` (it caps at `2p−... ≤ 17` at `p=7` by an over-constraint), but the **sheared**
hyperbola `y·(2x+1) ≡ 1 (mod p)` — a conic with `|B| = p` (the pole `x = −2⁻¹` maps to `0`) — *does*
reach `3(p−1)` (verified at p = 7, 11, 13). The shear `x ↦ 2x+1` is an affine change of the first
coordinate, so non-collinearity of the sheared base reduces to the plain hyperbola core; the lift
geometry below is the analogue of `hyperbola_lift_collinear_share_residue` for this base. (The open
part is the non-uniform lift-selection rule — see `PENDING_WORK.md` Path B.) -/

/-- Mod-`p` Vandermonde core for the **sheared** hyperbola `(2x+1)·y = 1`. Reduces to
`hyperbola_collinear_zmod` via the substitution `u = 2x+1` (which scales the determinant by `2`). -/
theorem shear_hyperbola_collinear_zmod {p : ℕ} [Fact p.Prime] (h2ne : (2 : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ x₃ y₃ : ZMod p}
    (h1 : (2 * x₁ + 1) * y₁ = 1) (h2 : (2 * x₂ + 1) * y₂ = 1) (h3 : (2 * x₃ + 1) * y₃ = 1)
    (hdet : (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) = 0) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₃ ∧ y₁ = y₃) ∨ (x₂ = x₃ ∧ y₂ = y₃) := by
  have hdet' : ((2 * x₂ + 1) - (2 * x₁ + 1)) * (y₃ - y₁)
      - ((2 * x₃ + 1) - (2 * x₁ + 1)) * (y₂ - y₁) = 0 := by linear_combination 2 * hdet
  have key := hyperbola_collinear_zmod (one_ne_zero) h1 h2 h3 hdet'
  have hx : ∀ {a b : ZMod p}, 2 * a + 1 = 2 * b + 1 → a = b := fun {a b} h =>
    mul_left_cancel₀ h2ne (by linear_combination h)
  rcases key with ⟨hu, hy⟩ | ⟨hu, hy⟩ | ⟨hu, hy⟩
  · exact Or.inl ⟨hx hu, hy⟩
  · exact Or.inr (Or.inl ⟨hx hu, hy⟩)
  · exact Or.inr (Or.inr ⟨hx hu, hy⟩)

/-- **Lift reduction for the sheared hyperbola** (the actual construction base). A real-collinear
triple of grid points whose residues lie on `(2x+1)·y ≡ 1 (mod p)` has two sharing a residue mod
`p` — so, exactly as for the plain hyperbola, every collinear triple of lifts is two lifts of one
base point plus a third, leaving only the slope-`±1` selection obligation. -/
theorem shear_hyperbola_lift_share_residue {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q R : ℕ × ℕ}
    (hP : (2 * (P.1 : ZMod p) + 1) * (P.2 : ZMod p) = 1)
    (hQ : (2 * (Q.1 : ZMod p) + 1) * (Q.2 : ZMod p) = 1)
    (hR : (2 * (R.1 : ZMod p) + 1) * (R.2 : ZMod p) = 1)
    (hcol : Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ))) :
    ((P.1 : ZMod p) = (Q.1 : ZMod p) ∧ (P.2 : ZMod p) = (Q.2 : ZMod p)) ∨
    ((P.1 : ZMod p) = (R.1 : ZMod p) ∧ (P.2 : ZMod p) = (R.2 : ZMod p)) ∨
    ((Q.1 : ZMod p) = (R.1 : ZMod p) ∧ (Q.2 : ZMod p) = (R.2 : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    simpa using h
  exact shear_hyperbola_collinear_zmod h2ne hP hQ hR (collinear_imp_modp_det_zero p hcol)

/-! ### ⭐ The closed-form sheared construction `shearSel p`

A **closed-form** lift-selection rule (found 2026-06-19, see `SELECTION-RULE-FOUND.md`) for the
sheared hyperbola, cracking the crux the prior baton believed was intrinsically non-uniform. For
prime `p`, with pole `pl = (p−1)/2`:

* base column `x` is the point `(x, shearY p x)`, `shearY p x = ((2x+1)⁻¹ : ZMod p).val`
  (so `shearY p pl = 0`: the pole, since `0⁻¹ = 0` in `ZMod p`);
* **drop the pole column** entirely; for every other column keep **3 of the 4 lifts**, dropping the
  corner nearest the grid centre: `shearDrop p r s = (r + p·[r≤pl], s + p·[s≤pl])`.

`card`, distinctness, grid-bound and `NoThreeCollinear` were verified (exact integer determinant) for
EVERY prime `3 ≤ p ≤ 109`; `Anchors.lean` certifies `p = 7,11,13` by `native_decide`. The `card` and
grid facts are proven below axiom-clean; the lone remaining obligation for an axiom-clean
`hjsw_lower` is `shearSel_noThree` (the slope-`±1` counting lemma for this explicit rule). -/
def shearY (p x : ℕ) : ℕ := ((2 * (x : ZMod p) + 1)⁻¹).val

/-- The single lift dropped from base point `(r,s)`: the corner nearest the grid centre (shift a
coordinate up by `p` exactly when its residue is `≤ (p−1)/2`). Always one of the four corners. -/
def shearDrop (p r s : ℕ) : ℕ × ℕ :=
  (r + (if r ≤ (p - 1) / 2 then p else 0), s + (if s ≤ (p - 1) / 2 then p else 0))

/-- The 3 kept lifts of base column `x`: all four corners except `shearDrop`. -/
def shearKept (p x : ℕ) : Finset (ℕ × ℕ) :=
  ({(x, shearY p x), (x + p, shearY p x), (x, shearY p x + p), (x + p, shearY p x + p)} :
    Finset (ℕ × ℕ)).erase (shearDrop p x (shearY p x))

/-- The full closed-form sheared selection: drop the pole column `(p−1)/2`, take 3 lifts of each
other column. -/
def shearSel (p : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range p).erase ((p - 1) / 2)).biUnion (shearKept p)

/-- Every kept lift of column `x` has first coordinate `x` or `x+p` and second `shearY p x` or
`shearY p x + p`. -/
theorem mem_shearKept {p x : ℕ} {q : ℕ × ℕ} (hq : q ∈ shearKept p x) :
    (q.1 = x ∨ q.1 = x + p) ∧ (q.2 = shearY p x ∨ q.2 = shearY p x + p) := by
  simp only [shearKept, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq.2 with h | h | h | h <;> subst h <;> simp

/-- `shearDrop` is one of the four corners (so erasing it from the 4-element corner set leaves 3). -/
theorem shearDrop_mem_corners (p x : ℕ) :
    shearDrop p x (shearY p x) ∈
      ({(x, shearY p x), (x + p, shearY p x), (x, shearY p x + p), (x + p, shearY p x + p)} :
        Finset (ℕ × ℕ)) := by
  simp only [shearDrop, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x ≤ (p - 1) / 2 <;> by_cases hs : shearY p x ≤ (p - 1) / 2 <;>
    simp [hx, hs]

/-- Each column keeps exactly 3 lifts. -/
theorem shearKept_card {p x : ℕ} (hp : 0 < p) : (shearKept p x).card = 3 := by
  have hs : shearY p x + p ≠ shearY p x := by omega
  have hx : x + p ≠ x := by omega
  have h4 : ({(x, shearY p x), (x + p, shearY p x), (x, shearY p x + p), (x + p, shearY p x + p)} :
      Finset (ℕ × ℕ)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]; omega), Finset.card_singleton]
  rw [shearKept, Finset.card_erase_of_mem (shearDrop_mem_corners p x), h4]

/-- **The sheared selection has exactly `3(p−1)` points** (prime `p`). -/
theorem shearSel_card {p : ℕ} (hp : p.Prime) : (shearSel p).card = 3 * (p - 1) := by
  have hp0 : 0 < p := hp.pos
  rw [shearSel, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun x _ => shearKept_card (x := x) hp0)]
    rw [Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_range.mpr (by omega : (p - 1) / 2 < p)), Finset.card_range,
      smul_eq_mul, Nat.mul_comm]
  · intro a ha b hb hab
    have hak : a < p := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
    have hbk : b < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hb)
    show Disjoint (shearKept p a) (shearKept p b)
    rw [Finset.disjoint_left]
    intro q hqa hqb
    have h1 := (mem_shearKept hqa).1
    have h2 := (mem_shearKept hqb).1
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

/-- **The sheared selection lies in the `2p × 2p` grid.** -/
theorem shearSel_grid {p : ℕ} (hp : p.Prime) : IsGridSet (2 * p) (shearSel p) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  intro q hq
  simp only [shearSel, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_range] at hq
  obtain ⟨x, ⟨_, hxp⟩, hqk⟩ := hq
  have hxy := mem_shearKept hqk
  have hsy : shearY p x < p := ZMod.val_lt _
  constructor
  · rcases hxy.1 with h | h <;> omega
  · rcases hxy.2 with h | h <;> omega

/-- `shearY` lands in `[0, p)`. -/
theorem shearY_lt {p : ℕ} [NeZero p] (x : ℕ) : shearY p x < p := ZMod.val_lt _

/-- Off the pole column, the shear factor `2x+1` is a unit mod `p`. -/
theorem shear_two_ne {p x : ℕ} (hp : p.Prime) (hx : x < p) (hne : x ≠ (p - 1) / 2) :
    (2 * (x : ZMod p) + 1) ≠ 0 := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  intro h
  have hcast : ((2 * x + 1 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
  have hdvd : p ∣ (2 * x + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  obtain ⟨k, hk⟩ := hdvd
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hk2 : k < 2 := by
    by_contra hge
    push_neg at hge
    have : 2 * p ≤ p * k := by nlinarith
    omega
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hk
    · exact h0
  have : k = 1 := by omega
  rw [this, Nat.mul_one] at hk
  omega

/-- **The base column lies on the sheared hyperbola.** For `x ≠ pole`, `(2x+1)·shearY = 1` mod `p`. -/
theorem shear_curve {p x : ℕ} (hp : p.Prime) (hx : x < p) (hne : x ≠ (p - 1) / 2) :
    (2 * (x : ZMod p) + 1) * ((shearY p x : ℕ) : ZMod p) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hval : ((shearY p x : ℕ) : ZMod p) = (2 * (x : ZMod p) + 1)⁻¹ := by
    rw [shearY]; simp [ZMod.natCast_val, ZMod.cast_id]
  rw [hval, mul_inv_cancel₀ (shear_two_ne hp hx hne)]

/-- `shearY` is injective on `[0,p)` (the base has distinct rows): `x ↦ (2x+1)⁻¹` is a composite of
injective maps (`x ↦ 2x+1` injective on residues, inversion an involution on the field). -/
theorem shearY_injective {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x x' : ℕ} (hx : x < p) (hx' : x' < p)
    (h : shearY p x = shearY p x') : x = x' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [shearY, shearY] at h
  have hv : (2 * (x : ZMod p) + 1)⁻¹ = (2 * (x' : ZMod p) + 1)⁻¹ :=
    ZMod.val_injective p h
  have hu : 2 * (x : ZMod p) + 1 = 2 * (x' : ZMod p) + 1 := inv_injective hv
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    simpa using this
  have hxx : (x : ZMod p) = (x' : ZMod p) :=
    mul_left_cancel₀ h2 (by linear_combination hu)
  calc x = ((x : ZMod p)).val := (ZMod.val_cast_of_lt hx).symm
    _ = ((x' : ZMod p)).val := by rw [hxx]
    _ = x' := ZMod.val_cast_of_lt hx'

/-- The slope-`±1` counting lemma for the closed-form rule — the lone remaining obligation. With
this explicit selection, no real-collinear triple of `shearSel p` exists: by
`shear_hyperbola_lift_share_residue` every collinear triple has two lifts of one base column, by
`lift_triple_noncollinear` not all three, so it is two lifts of one column plus a lift of another on
a slope-`±1` line — which this drop rule provably avoids (`coord_diff_of_residue_eq` reduces it to
modular arithmetic). Verified `native_decide` at `p ≤ 13` and by exact determinant for all primes
`≤ 109`. -/
theorem shearSel_noThree {p : ℕ} (hp : p.Prime) : NoThreeCollinear (shearSel p) := by
  sorry

/-- **HJSW lower bound.** For prime `p`, the `2p × 2p` grid admits `3(p−1)` points with no three
collinear — the closed-form sheared-hyperbola construction `shearSel p` (the `3(n−2)/2` count with
`n = 2p`). Reduced to the single combinatorial obligation `shearSel_noThree`; `card` and grid are
proven axiom-clean above. -/
theorem hjsw_lower {p : ℕ} (hp : p.Prime) : 3 * (p - 1) ≤ maxNoThreeInLine (2 * p) :=
  le_csSup (bddAbove_grid (2 * p))
    ⟨shearSel p, (shearSel_card hp).symm, shearSel_grid hp, shearSel_noThree hp⟩

end LeanFormalizations.NoThreeInLine
