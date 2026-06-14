/-
# Curtis (1990) — Lemma 2 (Brauer–Shockley Apéry-set value)

For `S = ⟨s₁,s₂,s₃⟩` with `2 < s₁ < s₂ < s₃`, `2 ≤ k ≤ (s₁−1)/2 + 1`, the ratio
constraint `s₁ − k < s₃/s₂ < s₁ − k + 1` (cleared of denominators), and the
congruences `s₂ ≡ 1`, `s₃ ≡ s₁ − k + 1 (mod s₁)`, the Frobenius number is exactly
`(k−2)·s₂ + s₃ − s₁`.

This is Curtis 1990, Lemma 2 (Math. Scand. 67, p. 191), feeding Step A
(`substCurve_eq_zero`) of the main theorem.

## Provenance
Proof produced by Harmonic's Aristotle auto-formalizer (job
`03706c46-1ccd-44b2-8b2a-ea4b2dfd9e83`, prompt archived at
`tools/aristotle/curtis-lemma2-prompt.txt`) and **independently re-verified in this
repo's kernel** (Lean v4.29.1): `#print axioms lemma2` = `[propext,
Classical.choice, Quot.sound]` (no `sorry`, no added `axiom`). The Apéry-set
argument is decomposed into the helper lemmas below.
-/
import Mathlib

open scoped Classical

set_option maxHeartbeats 8000000

namespace LeanFormalizations.NumericalSemigroups.Curtis.Lemma2

open AddSubmonoid

/-- Membership in the closure of a triple `{s₁,s₂,s₃}` is representability
`a*s₁ + b*s₂ + c*s₃`. -/
lemma mem_closure_triple (s₁ s₂ s₃ m : ℕ) :
    m ∈ AddSubmonoid.closure ({s₁, s₂, s₃} : Set ℕ) ↔
    ∃ a b c : ℕ, m = a * s₁ + b * s₂ + c * s₃ := by
  refine' ⟨ _, _ ⟩;
  · refine' AddSubmonoid.closure_induction _ _ _;
    · exact fun x hx => by rcases hx with ( rfl | rfl | rfl ) <;> [ exact ⟨ 1, 0, 0, by ring ⟩ ; exact ⟨ 0, 1, 0, by ring ⟩ ; exact ⟨ 0, 0, 1, by ring ⟩ ] ;
    · exact ⟨ 0, 0, 0, by norm_num ⟩;
    · rintro x y hx hy ⟨ a, b, c, rfl ⟩ ⟨ a', b', c', rfl ⟩ ; exact ⟨ a + a', b + b', c + c', by ring ⟩;
  · norm_num +zetaDelta at *;
    intro a b c h; rw [ h ] ; exact AddSubmonoid.add_mem _ ( AddSubmonoid.add_mem _ ( AddSubmonoid.nsmul_mem _ ( AddSubmonoid.subset_closure ( by simp +decide ) ) _ ) ( AddSubmonoid.nsmul_mem _ ( AddSubmonoid.subset_closure ( by simp +decide ) ) _ ) ) ( AddSubmonoid.nsmul_mem _ ( AddSubmonoid.subset_closure ( by simp +decide ) ) _ ) ;

/-- Part A core: `M = (k-2)*s₂ + s₃` is the smallest element of the semigroup in its
residue class `s₁ - 1` mod `s₁`. -/
lemma curtis_class_min (s₁ s₂ s₃ k : ℕ)
    (h1 : 2 < s₁) (h2 : s₁ < s₂) (h3 : s₂ < s₃)
    (hk_lo : 2 ≤ k) (hk_hi : 2 * k ≤ s₁ + 1)
    (hr_lo : (s₁ - k) * s₂ < s₃) (hr_hi : s₃ < (s₁ - k + 1) * s₂)
    (hc₂ : s₂ % s₁ = 1) (hc₃ : s₃ % s₁ = s₁ - k + 1)
    (b c : ℕ) (hres : (b * s₂ + c * s₃) % s₁ = s₁ - 1) :
    (k - 2) * s₂ + s₃ ≤ b * s₂ + c * s₃ := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide;
  rcases c with ( _ | _ | c ) <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
  · rcases s₁ with ( _ | _ | s₁ ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
    -- Since $b \equiv s₁ + 1 \pmod{s₁ + 2}$, we have $b \geq s₁ + 1$.
    have hb_ge : b ≥ s₁ + 1 := by
      exact hres ▸ Nat.mod_le _ _;
    nlinarith only [ hb_ge, h2, h3, hr_lo, hr_hi, Nat.sub_add_cancel ( by linarith : k ≤ s₁ ) ];
  · contrapose! hres; simp_all +decide [ ← Nat.mul_mod ] ;
    rw [ Nat.mod_eq_of_lt ];
    · lia;
    · nlinarith only [ hres, hk_hi, Nat.sub_add_cancel ( by linarith : k + 1 + 1 ≤ s₁ ) ];
  · nlinarith [ Nat.sub_add_cancel ( by linarith : k + 1 + 1 ≤ s₁ ) ]

/-- Part B core: every residue class `r < s₁` has an element of the semigroup
that is `≤ M = (k-2)*s₂+s₃` and congruent to `r` mod `s₁`. -/
lemma curtis_cover (s₁ s₂ s₃ k : ℕ)
    (h1 : 2 < s₁) (h2 : s₁ < s₂) (h3 : s₂ < s₃)
    (hk_lo : 2 ≤ k) (hk_hi : 2 * k ≤ s₁ + 1)
    (hr_lo : (s₁ - k) * s₂ < s₃) (hr_hi : s₃ < (s₁ - k + 1) * s₂)
    (hc₂ : s₂ % s₁ = 1) (hc₃ : s₃ % s₁ = s₁ - k + 1)
    (r : ℕ) (hr : r < s₁) :
    ∃ w : ℕ, (∃ a b c : ℕ, w = a * s₁ + b * s₂ + c * s₃) ∧
      w % s₁ = r ∧ w ≤ (k - 2) * s₂ + s₃ := by
  by_cases hr_le : r ≤ s₁ - k;
  · refine' ⟨ r * s₂, ⟨ 0, r, 0, _ ⟩, _, _ ⟩ <;> norm_num [ Nat.mul_mod, hc₂ ];
    · exact Nat.mod_eq_of_lt hr;
    · nlinarith only [ hr_le, hr_lo, Nat.sub_add_cancel ( by linarith : 2 ≤ k ), Nat.sub_add_cancel ( by omega : k ≤ s₁ ) ];
  · -- Let $j = r - (s₁ - k + 1)$. Note that $j \leq k - 2$ since $r \geq s₁ - k + 1$.
    set j : ℕ := r - (s₁ - k + 1)
    have hj_le : j ≤ k - 2 := by
      omega;
    refine' ⟨ j * s₂ + s₃, ⟨ 0, j, 1, by ring ⟩, _, _ ⟩ <;> norm_num [ Nat.add_mod, Nat.mul_mod, hc₂, hc₃ ];
    · simp +zetaDelta at *;
      rw [ Nat.sub_add_cancel ( by linarith ), Nat.mod_eq_of_lt hr ];
    · exact Nat.mul_le_mul_right _ hj_le

/-- If `m` and `w` have the same residue mod `s` and `w < m + s`, then `w ≤ m`. -/
lemma ge_of_modeq_lt (s m w : ℕ) (hs : 0 < s) (hmod : m % s = w % s)
    (hlt : w < m + s) : w ≤ m := by
  by_contra h_contra; exact (by
  exact h_contra ( by have := Nat.modEq_iff_dvd.mp hmod.symm; obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith ] ));

/-- Residue of `M = (k-2)*s₂+s₃` mod `s₁` is `s₁ - 1`. -/
lemma curtis_M_mod (s₁ s₂ s₃ k : ℕ) (h1 : 2 < s₁) (hk_lo : 2 ≤ k)
    (hk_hi : 2 * k ≤ s₁ + 1) (hc₂ : s₂ % s₁ = 1) (hc₃ : s₃ % s₁ = s₁ - k + 1) :
    ((k - 2) * s₂ + s₃) % s₁ = s₁ - 1 := by
  simp +decide [ *, Nat.add_mod, Nat.mul_mod ];
  simp +zetaDelta at *;
  rw [ Nat.mod_eq_of_lt ] <;> omega;

/-- **Curtis 1990, Lemma 2.** The Frobenius number of `⟨s₁,s₂,s₃⟩` is
`(k−2)·s₂ + s₃ − s₁` under the stated congruence/ratio constraints. -/
theorem lemma2 (s₁ s₂ s₃ k : ℕ)
    (h1 : 2 < s₁) (h2 : s₁ < s₂) (h3 : s₂ < s₃)
    (hk_lo : 2 ≤ k) (hk_hi : 2 * k ≤ s₁ + 1)
    (hr_lo : (s₁ - k) * s₂ < s₃) (hr_hi : s₃ < (s₁ - k + 1) * s₂)
    (hc₂ : s₂ % s₁ = 1) (hc₃ : s₃ % s₁ = s₁ - k + 1) :
    FrobeniusNumber ((k - 2) * s₂ + s₃ - s₁) {s₁, s₂, s₃} := by
  rw [frobeniusNumber_iff]
  have hMge : s₁ ≤ (k - 2) * s₂ + s₃ := by
    have : s₁ < s₃ := lt_trans h2 h3
    omega
  have hMmod : ((k - 2) * s₂ + s₃) % s₁ = s₁ - 1 :=
    curtis_M_mod s₁ s₂ s₃ k h1 hk_lo hk_hi hc₂ hc₃
  constructor
  · -- N ∉ closure
    rw [mem_closure_triple]
    rintro ⟨a, b, c, habc⟩
    have hsplit : (a * s₁ + b * s₂ + c * s₃) % s₁ = (b * s₂ + c * s₃) % s₁ := by
      have : a * s₁ + b * s₂ + c * s₃ = (b * s₂ + c * s₃) + s₁ * a := by ring
      rw [this, Nat.add_mul_mod_self_left]
    have hNmod : ((k - 2) * s₂ + s₃ - s₁) % s₁ = s₁ - 1 := by
      have : (k - 2) * s₂ + s₃ - s₁ + s₁ = (k - 2) * s₂ + s₃ := by omega
      have h2' : ((k - 2) * s₂ + s₃ - s₁ + s₁) % s₁
          = ((k - 2) * s₂ + s₃ - s₁) % s₁ := by
        rw [Nat.add_mod_right]
      rw [← h2', this, hMmod]
    have hres : (b * s₂ + c * s₃) % s₁ = s₁ - 1 := by
      rw [← hsplit, ← habc, hNmod]
    have hmin := curtis_class_min s₁ s₂ s₃ k h1 h2 h3 hk_lo hk_hi hr_lo hr_hi hc₂ hc₃ b c hres
    omega
  · -- every m > N is in closure
    intro m hm
    rw [mem_closure_triple]
    have hs1pos : 0 < s₁ := by omega
    obtain ⟨w, ⟨a, b, c, hw⟩, hwmod, hwle⟩ :=
      curtis_cover s₁ s₂ s₃ k h1 h2 h3 hk_lo hk_hi hr_lo hr_hi hc₂ hc₃
        (m % s₁) (Nat.mod_lt _ hs1pos)
    have hmod : m % s₁ = w % s₁ := by rw [hwmod]
    have hlt : w < m + s₁ := by omega
    have hwm : w ≤ m := ge_of_modeq_lt s₁ m w hs1pos hmod hlt
    obtain ⟨t, ht⟩ : s₁ ∣ (m - w) :=
      (Nat.modEq_iff_dvd' hwm).mp hmod.symm
    refine ⟨a + t, b, c, ?_⟩
    have e1 : m = w + s₁ * t := by omega
    rw [e1, hw]; ring

end LeanFormalizations.NumericalSemigroups.Curtis.Lemma2
