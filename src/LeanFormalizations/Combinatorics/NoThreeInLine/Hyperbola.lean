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
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((Q.1 : ℤ) - P.1) * ((R.2 : ℤ) - P.2) - ((R.1 : ℤ) - P.1) * ((Q.2 : ℤ) - P.2) = 0 := by
    exact_mod_cast hdet
  have hcast : ((Q.1 : ZMod p) - P.1) * ((R.2 : ZMod p) - P.2)
      - ((R.1 : ZMod p) - P.1) * ((Q.2 : ZMod p) - P.2) = 0 := by
    have h := congrArg (Int.cast : ℤ → ZMod p) hZ
    push_cast at h
    linear_combination h
  have hkk : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hk
  exact hyperbola_collinear_zmod hkk hP hQ hR hcast

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

/-- **HJSW lower bound (TARGET — not yet proven).** For prime `p`, the `2p × 2p` grid admits
`3(p−1)` points with no three collinear — the hyperbola `x·y ≡ k (mod p)` construction, i.e. the
`3(n−2)/2` count with `n = 2p` (since `3(2p−2)/2 = 3(p−1)`).

⚠️ The arc non-collinearity (`hyperbola_noThreeCollinear`) is proven above; the open part is the
`3/2` covering count — assembling `3(p−1)` actual grid points from ~3 lifted copies of the arc in
the `2p × 2p` grid, and ruling out cross-arc collinearities. See the online request / `PLAN.md`. -/
theorem hjsw_lower {p : ℕ} (hp : p.Prime) : 3 * (p - 1) ≤ maxNoThreeInLine (2 * p) := by
  sorry

end LeanFormalizations.NoThreeInLine
