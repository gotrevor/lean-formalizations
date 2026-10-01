/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.MertensBound

/-!
# ε–N₀ normal forms `LowerAt`, `UpperAt`, and Selberg's bound at every level (phase E5)

`upperAt_of_theta`: `UpperAt s (1/θ' + δ/4)` for `0 < θ' < θ < 1/2`, `θ s < 1`.
`upperAt_two`: `UpperAt s (2 + δ)` for `s ≤ 2`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter

/-- `S⁻(N, z) ≥ c N / log N` for every `z ≤ N^{1/s}`, `N ≥ N₀`: the normalised lower bound at
sifting level `s`.  Jurkat–Richert's `a(s)` is the sup of such `c`. -/
def LowerAt (s c : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z : ℕ, (z : ℝ) ≤ (N : ℝ) ^ (1 / s) → c * N / Real.log N ≤ siftMin N z

/-- `S⁺(N, z) ≤ c N / log N` for every `z ≥ N^{1/s}`, `N ≥ N₀`.  Jurkat–Richert's `b(s)` is the inf. -/
def UpperAt (s c : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z : ℕ, (N : ℝ) ^ (1 / s) ≤ z → (siftMax N z : ℝ) ≤ c * N / Real.log N

/-- **Selberg upper bound at any level**: for `0 < θ' < θ < 1/2` with `θ s < 1`, Selberg at
`ξ = ⌊N^θ⌋` gives `S⁺(N, z) ≤ (1/θ' + δ/4) N / log N` for `z ≥ N^{1/s}`; the error
`(Cξ log ξ)² ≤ N^{2θ} log² N` is `o(N / log N)` since `2θ < 1`. -/
theorem upperAt_of_theta {s θ θ' δ : ℝ} (hs : 0 < s) (hθ'pos : 0 < θ') (hθθ' : θ' < θ)
    (hθhalf : θ < 1 / 2) (hθs : θ * s < 1) (hδ : 0 < δ) : UpperAt s (1 / θ' + δ / 4) := by
  obtain ⟨C, hC, ξ₀, hξ₀2, hsel⟩ := siftMax_le_explicit
  have hθpos : 0 < θ := hθ'pos.trans hθθ'
  set k : ℝ := 1 - 2 * θ with hk
  have hkpos : 0 < k := by linarith
  -- eventual conditions on x = N
  have e1 : ∀ᶠ x : ℝ in atTop, (ξ₀ + 1 : ℝ) ≤ x ^ θ :=
    (tendsto_rpow_atTop hθpos).eventually_ge_atTop _
  have e2 : ∀ᶠ x : ℝ in atTop, Real.log 2 ≤ (θ - θ') * Real.log x :=
    (Real.tendsto_log_atTop.const_mul_atTop (by linarith)).eventually_ge_atTop _
  have e3 : ∀ᶠ x : ℝ in atTop, C ^ 2 * θ ^ 2 * Real.log x ^ (3 : ℝ) ≤ δ / 4 * x ^ k := by
    have h := (isLittleO_log_rpow_rpow_atTop 3 hkpos).bound
      (c := δ / 4 / (C ^ 2 * θ ^ 2 + 1)) (by positivity)
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    have hA : 0 ≤ Real.log x ^ (3 : ℝ) := Real.rpow_nonneg hl _
    have hB : C ^ 2 * θ ^ 2 ≤ C ^ 2 * θ ^ 2 + 1 := by linarith
    calc C ^ 2 * θ ^ 2 * Real.log x ^ (3 : ℝ) ≤ (C ^ 2 * θ ^ 2 + 1) * Real.log x ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hB hA
      _ ≤ (C ^ 2 * θ ^ 2 + 1) * (δ / 4 / (C ^ 2 * θ ^ 2 + 1) * x ^ k) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = δ / 4 * x ^ k := by field_simp
  obtain ⟨X, hX⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_ge_atTop (4 : ℝ)))))
  refine ⟨⌈X⌉₊, fun N hN z hz => ?_⟩
  have hNX : X ≤ (N : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hN)
  obtain ⟨h1, h2, h3, h4⟩ := hX (N : ℝ) hNX
  set x : ℝ := ((N : ℕ) : ℝ) with hx
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  set ξ : ℕ := ⌊x ^ θ⌋₊ with hξ
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have hξle : (ξ : ℝ) ≤ x ^ θ := Nat.floor_le hxθ.le
  have hξgt : x ^ θ - 1 < ξ := Nat.sub_one_lt_floor _
  have hξ₀ : ξ₀ ≤ ξ := by
    have : (ξ₀ : ℝ) < ξ + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hξ2 : (2 : ℝ) ≤ ξ := by exact_mod_cast (hξ₀2.trans hξ₀)
  have hξz : ξ < z := by
    have : x ^ θ < x ^ (1 / s) :=
      Real.rpow_lt_rpow_of_exponent_lt hx1 (by rw [lt_div_iff₀ hs]; linarith)
    exact_mod_cast (hξle.trans_lt this).trans_le hz
  have hsel' := hsel N z ξ hξ₀ hξz
  -- main term
  have hlogξ : θ' * Real.log x ≤ Real.log ξ := by
    have : (2 : ℝ) ≤ ξ₀ := by exact_mod_cast hξ₀2
    have hhalf : x ^ θ / 2 ≤ ξ := by linarith
    have := Real.log_le_log (by positivity) hhalf
    rw [Real.log_div hxθ.ne' (by norm_num), Real.log_rpow (by linarith)] at this
    linarith
  have hmain : (N : ℝ) / Real.log ξ ≤ 1 / θ' * (N / Real.log x) := by
    rw [div_le_iff₀ (by nlinarith), ← hx]
    field_simp
    nlinarith
  -- error term
  have hlogξ' : Real.log ξ ≤ θ * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) hξle
  have hlogξ0 : 0 ≤ Real.log ξ := Real.log_nonneg (by linarith)
  have hxk : x ^ (2 * θ) * x ^ k = x := by
    rw [← Real.rpow_add (by linarith), hk]; simp
  have hl3 : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hl3] at h3
  have herr : (C * ξ * Real.log ξ) ^ 2 ≤ δ / 4 * (N / Real.log x) := by
    have hsq : (C * ξ * Real.log ξ) ^ 2 ≤ C ^ 2 * x ^ (2 * θ) * (θ ^ 2 * Real.log x ^ 2) := by
      have hx2θ : x ^ (2 * θ) = (x ^ θ) ^ 2 := by
        rw [mul_comm, Real.rpow_mul (by linarith), Real.rpow_two]
      rw [hx2θ, mul_pow, mul_pow]
      have : (ξ : ℝ) ^ 2 ≤ (x ^ θ) ^ 2 := pow_le_pow_left₀ (by positivity) hξle 2
      have h' : Real.log ξ ^ 2 ≤ θ ^ 2 * Real.log x ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hlogξ0 hlogξ' 2
      have := mul_le_mul this h' (by positivity) (by positivity)
      nlinarith [sq_nonneg C]
    rw [← mul_div_assoc, le_div_iff₀ hlogx]
    have hx2 : 0 < x ^ (2 * θ) := Real.rpow_pos_of_pos (by linarith) _
    calc (C * ξ * Real.log ξ) ^ 2 * Real.log x
        ≤ C ^ 2 * x ^ (2 * θ) * (θ ^ 2 * Real.log x ^ 2) * Real.log x :=
          mul_le_mul_of_nonneg_right hsq hlogx.le
      _ = x ^ (2 * θ) * (C ^ 2 * θ ^ 2 * Real.log x ^ 3) := by ring
      _ ≤ x ^ (2 * θ) * (δ / 4 * x ^ k) := mul_le_mul_of_nonneg_left h3 hx2.le
      _ = δ / 4 * (x ^ (2 * θ) * x ^ k) := by ring
      _ = δ / 4 * x := by rw [hxk]
  calc (siftMax N z : ℝ) ≤ N / Real.log ξ + (C * ξ * Real.log ξ) ^ 2 := hsel'
    _ ≤ 1 / θ' * (N / Real.log x) + δ / 4 * (N / Real.log x) := add_le_add hmain herr
    _ = (1 / θ' + δ / 4) * N / Real.log N := by ring

/-- **Step 1 limit (b ≤ 2 on (0, 2])**: `upperAt_of_theta` at `θ = 2/(4+δ)`, `θ' = 4/(8+3δ)`. -/
theorem upperAt_two : ∀ s : ℝ, 0 < s → s ≤ 2 → ∀ δ : ℝ, 0 < δ → UpperAt s (2 + δ) := by
  intro s hs hs2 δ hδ
  have hθhalf : 2 / (4 + δ) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
  have h := upperAt_of_theta (θ := 2 / (4 + δ)) (θ' := 4 / (8 + 3 * δ)) hs (by positivity)
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith) hθhalf
    (by nlinarith [show (0 : ℝ) < 2 / (4 + δ) by positivity]) hδ
  have hfin : 1 / (4 / (8 + 3 * δ)) + δ / 4 = 2 + δ := by field_simp; ring
  rwa [hfin] at h

end LeanFormalizations.Erdos385.LinearSieve
