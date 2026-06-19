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

/-- **HJSW lower bound (TARGET — not yet proven).** For prime `p`, the `2p × 2p` grid admits
`3(p−1)` points with no three collinear — the hyperbola `x·y ≡ k (mod p)` construction, i.e. the
`3(n−2)/2` count with `n = 2p` (since `3(2p−2)/2 = 3(p−1)`).

⚠️ The arc non-collinearity (`hyperbola_noThreeCollinear`) is proven above; the open part is the
`3/2` covering count — assembling `3(p−1)` actual grid points from ~3 lifted copies of the arc in
the `2p × 2p` grid, and ruling out cross-arc collinearities. See the online request / `PLAN.md`. -/
theorem hjsw_lower {p : ℕ} (hp : p.Prime) : 3 * (p - 1) ≤ maxNoThreeInLine (2 * p) := by
  sorry

end LeanFormalizations.NoThreeInLine
