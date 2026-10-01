/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 power saving: tiling short intervals of primes (phase E9b)

`primeCount_tile`: if every `(t, t + t^e]`, `t ≥ y₀`, holds `≥ t^e/(2 log t)` primes, then
`(y, y + H]` holds `≥ (H − L)/(2 log 2y)` primes, where `t^e ∈ [m, L]` on `[y, 2y]`.  Tile
`(y, y + H]` greedily by the intervals `(t, t + t^e]`.
-/

namespace LeanFormalizations.Erdos385

open Real

theorem primeCounting_floor_mono {a b : ℝ} (h : a ≤ b) :
    (Nat.primeCounting ⌊a⌋₊ : ℝ) ≤ Nat.primeCounting ⌊b⌋₊ := by
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor h)

theorem primeCount_tile {e y₀ y H L m : ℝ}
    (hS : ∀ t : ℝ, y₀ ≤ t →
      t ^ e / (2 * Real.log t) ≤ (Nat.primeCounting ⌊t + t ^ e⌋₊ : ℝ) - Nat.primeCounting ⌊t⌋₊)
    (hy₀ : y₀ ≤ y) (hy2 : 2 ≤ y) (hH : 0 ≤ H) (hHy : H ≤ y) (hm : 0 < m)
    (hmL : ∀ t, y ≤ t → t ≤ 2 * y → m ≤ t ^ e ∧ t ^ e ≤ L) :
    (H - L) / (2 * Real.log (2 * y)) ≤
      (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ := by
  have hD : 0 < 2 * Real.log (2 * y) := by
    have := Real.log_pos (show (1 : ℝ) < 2 * y by linarith); linarith
  have hL : m ≤ L := by
    obtain ⟨h1, h2⟩ := hmL y le_rfl (by linarith); linarith
  have key : ∀ n : ℕ, ∀ t, y ≤ t → t ≤ y + H → y + H - t ≤ n * m →
      (y + H - t - L) / (2 * Real.log (2 * y)) ≤
        (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊t⌋₊ := by
    intro n
    induction n with
    | zero =>
      intro t _ ht _
      have := primeCounting_floor_mono ht
      have : (y + H - t - L) / (2 * Real.log (2 * y)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by push_cast at *; linarith) hD.le
      linarith
    | succ n ih =>
      intro t ht1 ht2 htn
      by_cases hc : y + H - t ≤ L
      · have := primeCounting_floor_mono ht2
        have : (y + H - t - L) / (2 * Real.log (2 * y)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
        linarith
      · push Not at hc
        obtain ⟨hmt, htL⟩ := hmL t ht1 (by linarith)
        set t' := t + t ^ e
        have ih' := ih t' (by linarith) (by linarith) (by push_cast at htn ⊢; nlinarith)
        have hst := hS t (hy₀.trans ht1)
        have hlt : 0 < Real.log t := Real.log_pos (by linarith)
        have hlt2 : Real.log t ≤ Real.log (2 * y) := Real.log_le_log (by linarith) (by linarith)
        have h1 : t ^ e / (2 * Real.log (2 * y)) ≤ t ^ e / (2 * Real.log t) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
        have e1 : (y + H - t - L) / (2 * Real.log (2 * y)) =
            (y + H - t' - L) / (2 * Real.log (2 * y)) + t ^ e / (2 * Real.log (2 * y)) := by
          rw [← add_div]; congr 1; simp only [t']; ring
        rw [e1]
        linarith
  have := key ⌈H / m⌉₊ y le_rfl (by linarith) (by
    have := Nat.le_ceil (H / m)
    rw [div_le_iff₀ hm] at this
    linarith)
  rwa [show y + H - y - L = H - L by ring] at this

end LeanFormalizations.Erdos385
