/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremA

/-!
# Phase 54: Theorem A for every `d` when `h ≠ 0`; Tetranacci `T₄(2^n) + h` composite for every `h`

Phase 52's survivor count only used `d` odd to exclude `h = 0`: from `Σ_(k<d) ε_k = d·h` with
`ε_k ∈ {±1}`, `h ≠ 0` already forces `h = ±1` and every `ε_k = h`, for any `d ≥ 1`.  So:

**Theorem A′.**  Same hypotheses as `TheoremA.entry_prime_pow_add_not_prime`, with `Odd d` replaced by
`Odd d ∨ h ≠ 0`.

**Corollary (Tetranacci, `c = 2`).**  `T₄ 0 = T₄ 1 = T₄ 2 = 0`, `T₄ 3 = 1`, `T₄(n+4) = T₄(n+3) + … + T₄ n`.
`X⁴ − X³ − X² − X − 1 ≡ Φ₅ (mod 2)` is irreducible (`ord₅ 2 = 4`); `μ(ℤ₂) = {±1}`; `T₄(2^2) = T₄ 4 = 1`
is odd.  So `T₄(2^n) + h` is composite i.o. for every `h ≠ 0`.  For `h = 0`: by the period
(`OrbitSum.pow_prime_pow_add_card_congr` at `n = 0`, `d = 4`), `T₄(2^(4k)) ≡ T₄(1) = 0 (mod 2)`, and
`T₄(2^(4k)) > 2` for `k ≥ 1`, so it is even and composite.  Hence **every `h`**.
Hypotheses checked by `scripts/theorem-a-tetranacci-probe.py`.  (At `c = 5` the charpoly is also
irreducible, but `μ₄ ⊂ ℤ₅` breaks the window, so `c = 5` is not claimed.)
`T₄ N = (A^N) 3 0` for `A = !![1,1,1,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]`.

## Route
Copy phase 52's proof of `entry_prime_pow_add_not_prime`, replacing the parity step by the case split.
Ideally refactor phase 52's proof into a public lemma that takes the counting step as input.  Do NOT
change phase 52's frozen statements.

Frozen: the two statements below and the def `tetra`; all earlier statements; `Literature/`.
No `private`.
-/

namespace LeanFormalizations.Mills.TheoremAEven

open Matrix Filter

/-- **Theorem A′** (any `d`, `h ≠ 0`). -/
theorem entry_prime_pow_add_not_prime' {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c))))
    (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) {i j : Fin d} (hij : i ≠ j)
    (hnz : ∃ r < d, ¬ (c : ℤ) ∣ (A ^ (c ^ r)) i j)
    (hgrow : Tendsto (fun n => |(A ^ (c ^ n)) i j|) atTop atTop) (h : ℤ) (hdh : Odd d ∨ h ≠ 0) :
    ∃ᶠ n in atTop, ¬ Prime ((A ^ (c ^ n)) i j + h) :=
  TheoremA.entry_prime_pow_add_not_prime_gen A hc hirr hmu hij hnz hgrow h hdh

/-- Tetranacci: `T₄ 0 = T₄ 1 = T₄ 2 = 0`, `T₄ 3 = 1`. -/
def tetra : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => tetra (n + 3) + tetra (n + 2) + tetra (n + 1) + tetra n

/-! ### The Tetranacci companion matrix -/

/-- The Tetranacci companion matrix. -/
def tetraMat : Matrix (Fin 4) (Fin 4) ℤ := !![1, 1, 1, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

theorem tetraMat_pow_col (N : ℕ) :
    (tetraMat ^ N) 0 0 = tetra (N + 3) ∧ (tetraMat ^ N) 1 0 = tetra (N + 2) ∧
      (tetraMat ^ N) 2 0 = tetra (N + 1) ∧ (tetraMat ^ N) 3 0 = tetra N := by
  induction N with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [tetra]
  | succ N ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have hmul : ∀ a : Fin 4, (tetraMat ^ (N + 1)) a 0 =
        ∑ k : Fin 4, tetraMat a k * (tetraMat ^ N) k 0 := by
      intro a
      rw [pow_succ']
      exact Matrix.mul_apply
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmul 0, Fin.sum_univ_four, h0, h1, h2, h3, show N + 1 + 3 = N + 4 from rfl, tetra]
      simp [tetraMat]
    · rw [hmul 1, Fin.sum_univ_four, h0, h1, h2, h3]
      simp [tetraMat]
    · rw [hmul 2, Fin.sum_univ_four, h0, h1, h2, h3]
      simp [tetraMat]
    · rw [hmul 3, Fin.sum_univ_four, h0, h1, h2, h3]
      simp [tetraMat]

theorem tetraMat_pow_apply (N : ℕ) : (tetraMat ^ N) 3 0 = tetra N := (tetraMat_pow_col N).2.2.2

theorem tetraMat_charpoly :
    tetraMat.charpoly
      = Polynomial.X ^ 4 - Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X - 1 := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Matrix.charmatrix, tetraMat, Matrix.det_fin_three, Fin.sum_univ_succ,
    Matrix.diagonal, Fin.succAbove]
  ring

/-- Mod `2` the Tetranacci charpoly is `Φ₅ = X⁴ + X³ + X² + X + 1`. -/
theorem tetraMat_charpolyBar_two :
    tetraMat.charpoly.map (Int.castRingHom (ZMod 2)) = Polynomial.cyclotomic 5 (ZMod 2) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [tetraMat_charpoly, Polynomial.cyclotomic_prime]
  simp [Finset.sum_range_succ, Polynomial.map_sub, Polynomial.map_pow]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring

/-- `ord₅ 2 = 4`, so `Φ₅` is irreducible over `𝔽₂`. -/
theorem tetraMat_charpolyBar_two_irreducible :
    Irreducible (tetraMat.charpoly.map (Int.castRingHom (ZMod 2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [tetraMat_charpolyBar_two]
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5)
    (by decide) dvd_rfl ?_
  rw [Polynomial.natDegree_cyclotomic]
  have h4 : orderOf (ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr (by decide)) :
      (ZMod 5)ˣ) = 4 := by
    have := orderOf_eq_prime_pow (x := (ZMod.unitOfCoprime 2
      (Nat.prime_two.coprime_iff_not_dvd.mpr (by decide)) : (ZMod 5)ˣ)) (p := 2) (n := 1)
      (by decide) (by decide)
    simpa using this
  rw [h4]
  decide

/-! ### Growth of the Tetranacci sequence -/

theorem tetra_bounds (n : ℕ) :
    0 ≤ tetra n ∧ 0 ≤ tetra (n + 1) ∧ 0 ≤ tetra (n + 2) ∧ 1 ≤ tetra (n + 3) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [tetra]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have heq : tetra (n + 4) = tetra (n + 3) + tetra (n + 2) + tetra (n + 1) + tetra n := rfl
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [show n + 1 + 1 = n + 2 from rfl]; omega
    · rw [show n + 1 + 2 = n + 3 from rfl]; omega
    · rw [show n + 1 + 3 = n + 4 from rfl, heq]; omega

theorem tetra_ge (n : ℕ) : (n : ℤ) + 1 ≤ tetra (n + 4) := by
  induction n with
  | zero => norm_num [tetra]
  | succ n ih =>
    have heq : tetra (n + 5) = tetra (n + 4) + tetra (n + 3) + tetra (n + 2) + tetra (n + 1) := rfl
    obtain ⟨h0, h1, h2, h3⟩ := tetra_bounds (n + 1)
    obtain ⟨-, -, -, g3⟩ := tetra_bounds n
    rw [show n + 1 + 4 = n + 5 from rfl, heq]
    push_cast
    rw [show n + 1 + 3 = n + 4 from rfl] at h3
    rw [show n + 1 + 2 = n + 3 from rfl] at h2
    rw [show n + 1 + 1 = n + 2 from rfl] at h1
    linarith [ih, h1, h2, h3, g3]

theorem tetra_tendsto : Tendsto (fun n => |(tetraMat ^ (2 ^ n)) 3 0|) atTop atTop := by
  refine tendsto_atTop.2 fun B => eventually_atTop.2 ⟨B.toNat + 4, fun n hn => ?_⟩
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 4 := ⟨2 ^ n - 4, by omega⟩
  have h1 : (m : ℤ) + 1 ≤ tetra (2 ^ n) := by rw [hm]; exact tetra_ge m
  have hBm : B ≤ (m : ℤ) + 1 := by
    have hBt : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
    have hm1 : B.toNat < m := by omega
    have : (B.toNat : ℤ) < (m : ℤ) := by exact_mod_cast hm1
    omega
  rw [tetraMat_pow_apply]
  exact le_trans (le_trans hBm h1) (le_abs_self _)

/-! ### The corollary -/

/-- The case `h ≠ 0`, straight from Theorem A′. -/
theorem tetra_two_pow_add_not_prime_of_ne_zero {h : ℤ} (h0 : h ≠ 0) :
    ∃ᶠ n in atTop, ¬ Prime (tetra (2 ^ n) + h) := by
  have hkey := entry_prime_pow_add_not_prime' tetraMat Nat.prime_two
    tetraMat_charpolyBar_two_irreducible (Or.inl rfl) (show (3 : Fin 4) ≠ 0 by decide)
    ⟨2, by omega, by rw [tetraMat_pow_apply]; decide⟩ tetra_tendsto h (Or.inr h0)
  simpa [tetraMat_pow_apply] using hkey

/-- The case `h = 0`: along `n ≡ 0 (mod 4)` the period mod `2` gives
`T₄(2^n) ≡ T₄(2^0) = T₄ 1 = 0`, and the value exceeds `2`. -/
theorem tetra_two_pow_not_prime :
    ∃ᶠ n in atTop, ¬ Prime (tetra (2 ^ n)) := by
  refine Filter.frequently_atTop.2 fun a => ⟨4 * (a + 1), by omega, ?_⟩
  set n : ℕ := 4 * (a + 1) with hn
  have hper := TheoremA.entry_period tetraMat Nat.prime_two
    tetraMat_charpolyBar_two_irreducible 0 (a + 1) 3 0
  rw [zero_add, tetraMat_pow_apply, tetraMat_pow_apply] at hper
  have hn' : (a + 1) * 4 = n := by omega
  rw [hn'] at hper
  have h1 : tetra (2 ^ 0) = 0 := by decide
  rw [h1, sub_zero] at hper
  -- the value is large
  have hbig : 3 ≤ tetra (2 ^ n) := by
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h16' : 16 ≤ 2 ^ n := by norm_num at h16; omega
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 4 := ⟨2 ^ n - 4, by omega⟩
    have h2 : (m : ℤ) + 1 ≤ tetra (2 ^ n) := by rw [hm]; exact tetra_ge m
    have hm2 : 2 ≤ m := by omega
    have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
    omega
  intro hp
  have hnat := Int.prime_iff_natAbs_prime.1 hp
  have hdvd : 2 ∣ (tetra (2 ^ n)).natAbs := Int.ofNat_dvd.1 (by
    rw [Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ tetra (2 ^ n))]; exact_mod_cast hper)
  have hge : 3 ≤ (tetra (2 ^ n)).natAbs := by
    have := Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ tetra (2 ^ n))
    omega
  rcases hnat.eq_one_or_self_of_dvd 2 hdvd with hh | hh <;> omega

/-- **`T₄(2^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem tetra_two_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (tetra (2 ^ n) + h) := by
  rcases eq_or_ne h 0 with rfl | h0
  · simpa using tetra_two_pow_not_prime
  · exact tetra_two_pow_add_not_prime_of_ne_zero h0

end LeanFormalizations.Mills.TheoremAEven
