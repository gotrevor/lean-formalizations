/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Stress tests for the Leopoldt statement (phase 26)

`Literature.LeopoldtConjecture` is Ren's design; its faithfulness argument is in the file header,
at about 75%.  These tests are meant to catch a mistake.
* **Positive**: when the unit rank is 0 (`ℚ`, imaginary quadratic fields) the conjecture must
  hold, because every multiplicatively independent family of units is empty.
  `leopoldt_of_rank_zero` checks that the statement is not accidentally false.
* **Negative (the hypotheses bite)**: drop the multiplicative-independence hypothesis and the
  statement must become FALSE.  For `ℚ`, take `ε = −1`, `mₙ = 2`, `a = 2`.  Then `(−1)² = 1`, but
  `a ≠ 0`.  `not_leopoldtNoIndep_rat` checks that the independence clause is doing work.
* **Stretch (not frozen)**: Leopoldt for a real quadratic field (unit rank 1), e.g. `ℚ(√2)` at
  `p = 7`.  It reduces to "`ε^a = 1` with `a ∈ ℤ_p` forces `a = 0`" for the fundamental unit, which
  holds because `ε` is not a root of unity.  This would be a genuinely nontrivial positive test.
  Add it if the rank-0 cases go quickly.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Leopoldt

namespace LeanFormalizations.Leopoldt

open NumberField IsDedekindDomain Filter Topology LeanFormalizations.Literature

/-- The broken variant: `LeopoldtConjecture` with the independence hypothesis removed. -/
def LeopoldtNoIndep (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (r : ℕ) (ε : Fin r → (𝓞 K)ˣ) (a : Fin r → ℤ_[p]) (m : ℕ → Fin r → ℤ),
    (∀ i, Tendsto (fun n ↦ ((m n i : ℤ) : ℤ_[p])) atTop (𝓝 (a i))) →
    (∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Tendsto (fun n ↦ algebraMap K (v.adicCompletion K)
        (∏ i, (((ε i : 𝓞 K) : K)) ^ (m n i))) atTop (𝓝 1)) →
    a = 0

/-- In unit rank `0` every unit is torsion: Dirichlet's decomposition has an empty product. -/
theorem isOfFinOrder_of_rank_zero {K : Type*} [Field K] [NumberField K]
    (h : Units.rank K = 0) (x : (𝓞 K)ˣ) : IsOfFinOrder x := by
  haveI : IsEmpty (Fin (Units.rank K)) := by rw [h]; infer_instance
  obtain ⟨⟨ζ, e⟩, hx, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K x
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hx
  subst hx
  exact ζ.2

theorem leopoldt_of_rank_zero (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (h : Units.rank K = 0) : LeopoldtConjecture K p := by
  intro r ε hind a m _ _
  -- In rank `0` there is no nonempty multiplicatively independent family, so `r = 0`.
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨i₀⟩ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
    obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).mp (isOfFinOrder_of_rank_zero h (ε i₀))
    have hprod : ∏ i, ε i ^ ((Pi.single i₀ (N : ℤ) : Fin r → ℤ) i) = 1 := by
      rw [Finset.prod_eq_single i₀]
      · simpa using hpow
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hb; exact absurd (Finset.mem_univ i₀) hb
    have := congrFun (hind (Pi.single i₀ (N : ℤ)) hprod) i₀
    simp at this
    omega
  subst hr
  funext i
  exact i.elim0

theorem not_leopoldtNoIndep_rat (p : ℕ) [Fact p.Prime] : ¬ LeopoldtNoIndep ℚ p := by
  intro H
  have := H 1 (fun _ => -1) (fun _ => (2 : ℤ_[p])) (fun _ _ => (2 : ℤ))
    (fun _ => by simp only [Int.cast_ofNat]; exact tendsto_const_nhds)
    (fun v _ => by
      have hone : (∏ _i : Fin 1, ((((-1 : (𝓞 ℚ)ˣ) : 𝓞 ℚ) : ℚ)) ^ (2 : ℤ)) = 1 := by
        norm_num
      simp only [hone, map_one]
      exact tendsto_const_nhds)
  have h2 := congrFun this 0
  rw [Pi.zero_apply] at h2
  exact two_ne_zero h2

end LeanFormalizations.Leopoldt
