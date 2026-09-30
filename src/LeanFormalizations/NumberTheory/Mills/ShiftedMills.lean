/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Saito2025
import LeanFormalizations.NumberTheory.Mills.TheoremDGround

/-!
# Phase 45: `ξ(3^k − 2)` is transcendental, modulo Saito 2025 and our rigidity node

Theorem E of `PROOF-THEOREM-E.md` as a conjecture-graph edge:
* **Literature input:** `Literature.Saito2025TypeBTrace` (Saito's Type B + Prop 3.1(iv)).
* **Our open node:** `ShiftedTraceRigidity`, i.e. Steps 3–6 of `PROOF-THEOREM-E.md`: the prime-as-modulus
  filter, Teichmüller limit points, Galois rigidity, the mod-3 congruence and the E1 certificate.
  It is **stated here, not proved**; it is our own mathematics (not literature), so it stays a
  named `Prop` node until a later phase proves it.
* **This phase proves the glue:** the hypotheses of Saito's theorem for `C_k = 3^k − 2`, the
  asymptotic gcd, and `Saito2025TypeBTrace → ShiftedTraceRigidity → Transcendental ℚ ξ`.

## Route
1. `shiftedC k = 3^k − 2` (as `ℕ`, meaningful for `k ≥ 1`).
2. `shiftedC_hyps`: `C 1 = 1`; `2·C k ≤ C (k+1)` (`3^(k+1) − 2 ≥ 2·3^k − 4`); the ratio is
   `≥ 29/10` for every `k ≥ 1` (`10(3^(k+1) − 2) ≥ 29(3^k − 2)` iff `3^k ≥ −38`); and
   `C m ∣ C (m + φ(C m))` (`gcd(3, C m) = 1`, Euler: `3^(φ(C m)) ≡ 1`, so
   `3^(m+φ) − 2 ≡ 3^m − 2 ≡ 0`).  Take `k = m + totient (C m)` (`> m` as `totient ≥ 1`).
3. `eq_one_of_eventually_dvd`: if `g ∣ 3^k − 2` for all large `k`, then `g = 1`.
   `g ∣ 3(3^k − 2) − (3^(k+1) − 2) = 4`, and every `3^k − 2` is odd, so `g` is odd, `g ∣ 4`, and `g = 1`.
4. `xi_shifted_transcendental`: take `ξ` from Saito (the `IsLeast` element is unique, so it matches the
   given one); in the Pisot branch `g = 1` by step 3, and for large `k`
   `powTrace ξ (C k) = ⌊ξ^(C k)⌋₊`, which is prime.  That contradicts `ShiftedTraceRigidity ξ`.

Frozen: every statement and def below (and `Literature/Saito2025.lean`), all earlier Mills phase
statements, the rest of `Literature/`.  Do not mark new declarations `private`.  **Do not attempt to
prove `ShiftedTraceRigidity`**: it is a `def … : Prop` (an open node), not a theorem.
-/

namespace LeanFormalizations.Mills.ShiftedMills

open LeanFormalizations.Literature Filter

/-- The exponent sequence `C_k = 3^k − 2`. -/
def shiftedC (k : ℕ) : ℕ := 3 ^ k - 2

/-- **Open node (our Theorem E, Steps 3–6).**  No cubic Pisot number `β` has
`Tr(β^(3^k − 2))` prime for all large `k`. -/
def ShiftedTraceRigidity : Prop :=
  ∀ β : ℝ, IsPisot β → (minpoly ℚ β).natDegree = 3 →
    ¬ ∀ᶠ k in atTop, ∃ p : ℕ, p.Prime ∧ powTrace β (shiftedC k) = (p : ℂ)

/-- For `k ≥ 1`, `2 ≤ 3 ^ k`. -/
theorem two_le_three_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 3 ^ k :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)

/-- The defining identity, with `ℕ`-subtraction discharged. -/
theorem shiftedC_add_two {k : ℕ} (hk : 1 ≤ k) : shiftedC k + 2 = 3 ^ k :=
  Nat.sub_add_cancel (two_le_three_pow hk)

theorem shiftedC_pos {k : ℕ} (hk : 1 ≤ k) : 0 < shiftedC k := by
  have h := shiftedC_add_two hk
  have h3 : 3 ≤ 3 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  omega

theorem shiftedC_odd {k : ℕ} (hk : 1 ≤ k) : Odd (shiftedC k) := by
  have h := shiftedC_add_two hk
  have ho : Odd (3 ^ k) := Odd.pow (by decide)
  rw [Nat.odd_iff] at ho ⊢
  omega

theorem three_not_dvd_shiftedC {k : ℕ} (hk : 1 ≤ k) : ¬ (3 ∣ shiftedC k) := by
  intro hd
  have h := shiftedC_add_two hk
  have h3 : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  obtain ⟨a, ha⟩ := hd
  obtain ⟨b, hb⟩ := h3
  omega

theorem shiftedC_succ {k : ℕ} (hk : 1 ≤ k) : shiftedC (k + 1) = 3 * shiftedC k + 4 := by
  have h1 := shiftedC_add_two hk
  have h2 := shiftedC_add_two (show 1 ≤ k + 1 by omega)
  have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
  have h4 : 3 ≤ 3 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  omega

/-- `C m ∣ C (m + φ (C m))`, by Euler's theorem in base `3`. -/
theorem shiftedC_dvd_totient_shift {m : ℕ} (hm : 1 ≤ m) :
    shiftedC m ∣ shiftedC (m + Nat.totient (shiftedC m)) := by
  set n := shiftedC m with hn
  have hnpos : 0 < n := shiftedC_pos hm
  have hcop : Nat.Coprime 3 n := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    exact three_not_dvd_shiftedC hm
  have heuler : 3 ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
  have hbase : 3 ^ m ≡ 2 [MOD n] := by
    have h := shiftedC_add_two hm
    have : n ∣ 3 ^ m - 2 := dvd_refl _
    exact ((Nat.modEq_iff_dvd' (two_le_three_pow hm)).mpr this).symm
  have hkey : 3 ^ (m + n.totient) ≡ 2 [MOD n] := by
    calc 3 ^ (m + n.totient) = 3 ^ m * 3 ^ n.totient := by ring
      _ ≡ 2 * 1 [MOD n] := Nat.ModEq.mul hbase heuler
      _ = 2 := by ring
  exact (Nat.modEq_iff_dvd' (two_le_three_pow (by omega))).mp hkey.symm

theorem shiftedC_hyps :
    1 ≤ shiftedC 1 ∧ (∀ k ≥ 1, 2 * shiftedC k ≤ shiftedC (k + 1)) ∧
      (∀ k ≥ 1, (29 : ℝ) / 10 * shiftedC k ≤ shiftedC (k + 1)) ∧
      (∀ m ≥ 1, ∃ k > m, shiftedC m ∣ shiftedC k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [shiftedC]
  · intro k hk
    rw [shiftedC_succ hk]; omega
  · intro k hk
    have h1 : ((shiftedC k : ℝ)) + 2 = 3 ^ k := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (shiftedC_add_two hk)
    have h2 : ((shiftedC (k + 1) : ℝ)) = 3 * shiftedC k + 4 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (shiftedC_succ hk)
    have h3 : (3 : ℝ) ≤ 3 ^ k := by
      have : (3 : ℕ) ≤ 3 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      exact_mod_cast this
    linarith
  · intro m hm
    refine ⟨m + Nat.totient (shiftedC m), ?_, shiftedC_dvd_totient_shift hm⟩
    have := Nat.totient_pos.mpr (shiftedC_pos hm)
    omega

theorem eq_one_of_eventually_dvd {g : ℕ} (hg : ∀ᶠ k in atTop, g ∣ shiftedC k) : g = 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  set k := max N 1 with hk
  have hk1 : 1 ≤ k := le_max_right _ _
  have h1 : g ∣ shiftedC k := hN k (le_max_left _ _)
  have h2 : g ∣ shiftedC (k + 1) := hN (k + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  have hsucc := shiftedC_succ hk1
  have hg4 : g ∣ 4 := by
    have : g ∣ shiftedC (k + 1) - 3 * shiftedC k := Nat.dvd_sub h2 (Dvd.dvd.mul_left h1 3)
    simpa [hsucc] using this
  have hgodd : Odd g := (shiftedC_odd hk1).of_dvd_nat h1
  have hle : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  rw [Nat.odd_iff] at hgodd
  interval_cases g <;> simp_all

/-- **Theorem E, conditional form**: the least `A > 1` with `⌊A^(3^k − 2)⌋` prime for all `k ≥ 1`
is transcendental, given Saito's Type B/Prop 3.1 and our rigidity node. -/
theorem xi_shifted_transcendental (hS : Saito2025TypeBTrace) (hR : ShiftedTraceRigidity)
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  obtain ⟨h1, h2, h3, h5⟩ := shiftedC_hyps
  obtain ⟨ξ', hleast, hdisj⟩ :=
    hS shiftedC h1 h2 (fun K => ⟨max K 1, le_max_left _ _, h3 _ (le_max_right _ _)⟩)
      (fun m hm => by
        obtain ⟨k, hk, hdvd⟩ := h5 m hm
        exact ⟨k, hk, hdvd, h3 k (by omega)⟩)
  have hxi : ξ' = ξ := hleast.unique hξ
  rw [hxi] at hdisj hleast
  rcases hdisj with htr | ⟨g, hg1, hpisot, hdeg, K, hK⟩
  · exact htr
  -- Pisot branch: the asymptotic gcd forces `g = 1`, and then every large trace is prime.
  have hgone : g = 1 := by
    refine eq_one_of_eventually_dvd (g := g) ?_
    filter_upwards [eventually_ge_atTop (max K 1)] with k hk
    exact (hK k (le_trans (le_max_left _ _) hk) (h3 k (le_trans (le_max_right _ _) hk))).1
  subst hgone
  rw [pow_one] at hpisot hdeg
  refine absurd ?_ (hR ξ hpisot hdeg)
  filter_upwards [eventually_ge_atTop (max K 1)] with k hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have htrace := (hK k (le_trans (le_max_left _ _) hk) (h3 k hk1)).2
  refine ⟨⌊ξ ^ shiftedC k⌋₊, hleast.1.2 k hk1, ?_⟩
  simpa using htrace

end LeanFormalizations.Mills.ShiftedMills
