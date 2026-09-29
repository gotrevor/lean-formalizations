/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Dubickas's Lemma 6 from Stephan's machine-checked Corvaja–Zannier

R. Stephan formalized all of Corvaja–Zannier 2004 (`rwst/Subspace-Theorems`,
`CorvajaZannier2004/`).  Its Main Theorem and Lemma 4 enter verbatim as
`Literature.Stephan2026CZMain` and `Literature.Stephan2026CZLemma4`.  This file derives the two
phase-9 disclosed statements and `Dubickas2022` from them — wiring, not a CZ proof.  (Phase 13's
`CorvajaZannier.lean` started re-deriving CZ from the Subspace Theorem before this was found; it
is superseded, its disclosed `sorry`s stay.)

## `corvajaZannier_dichotomy_of_czMain`
`Γ = ⟨α⟩ ≤ ℝˣ` (`α > 1` algebraic), `δ = 1`, points `(q, α^(s n))`.  `H(α^(s n)) = H(α)^(s n)`
(`absMulHeight₁` of a power), `H(α) > 1` (`α > 1` is not a root of unity), and
`[ℚ(α^(s n)) : ℚ] ≤ deg α`, so `‖q α^(s n)‖ ≤ e^(−ε s n)` gives the CZ inequality with
`ε' = ε / (2 log H(α))` for large `n` (absorb `q^(−d−ε')` into half the exponent).  Finiteness of
CZ's set, `StrictMono s`, and the hypothesis `hfin` (relate `IsPseudoPisotMul q β` to
`IsPseudoPisot (q β)`; check both definitions) give the claim.  Zero distance: `q α^(s n) ∈ ℤ`
with `> 1` is pseudo-Pisot, so it is covered by `hfin`.

## `corvajaZannier_lemma4_of_czLemma4`
Stephan's form concludes `IsIntegral ℤ α` outright (left disjunct).  Take `α` in `ℂ`, `q_n := q · e_n`
with `e_n = [ℚ(α) : ℚ(αⁿ)] ≤ deg α`, so `log q_n / n → 0`; `Tr_{ℚ(α)/ℚ}(q_n αⁿ) = q · e_n ·
(sum of conjugates of αⁿ) ⋯` — relate `Algebra.trace ℚ ℚ⟮α⟯` to the `aroots` sum of
`minpoly ℚ (αⁿ)` (trace in a tower = degree × trace below; mathlib `Algebra.trace_eq_sum_roots`,
`trace_trace`).  The nonzero integer is `e_n · t`.

## `dubickas2022_of_czMain`
Dubickas's Lemma 6 = Lemma 3 (CZ Main) ∨ Lemma 5 (formalized in `DubickasNoSubspace.lean`), per
`PROBE-DUBICKAS-NOSUBSPACE.md`.  Reassemble phase 9's route with the two derived statements in
place of its two `sorry`s.  `hR` is there in case a rational-power case needs Ridout/Mahler
(`StephanEdges.lean`); drop nothing, it is harmless if unused.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Pisot
import LeanFormalizations.NumberTheory.Transcendence.DubickasNoSubspace

namespace LeanFormalizations.Transcendence.Dubickas

open LeanFormalizations.Literature
open Filter Topology IntermediateField Module LeanFormalizations.Mills

/-! ### The trace bridge

Stephan's Lemma 4 wants `Tr_{ℚ(α)/ℚ}(q_n αⁿ) ∈ ℤ ∖ {0}`; phase 9 states the hypothesis as
`q · Σ (roots of minpoly (αⁿ)) ∈ ℤ ∖ {0}`.  The two differ by the factor
`e_n = [ℚ(α) : ℚ(αⁿ)]`, which mathlib's `trace_eq_sum_roots` supplies:
`Tr_{ℚ(α)/ℚ}(x) = [ℚ(x) : ℚ(α)]⁻¹`-fold … precisely,
`algebraMap ℚ ℂ (Tr x) = finrank ℚ⟮x⟯ ℚ⟮α⟯ • (minpoly ℚ x).aroots ℂ |>.sum`.
Since `e_n ≥ 1`, nonvanishing is preserved, and `q_n := q` is constant so `log q_n / n → 0`
is trivial.  Note Stephan's conclusion has **no** `αˡ ∈ ℚ` escape branch. -/

/-- **Corvaja–Zannier's Lemma 4 in the phase-9 formulation**, from Stephan's stronger form:
if `q · Σ(roots of minpoly (αⁿ))` is a nonzero rational integer along an infinite set of `n`,
then `α` is an algebraic integer. -/
theorem isIntegral_of_aroots_trace (hL : Stephan2026CZLemma4) {α : ℝ}
    (halg : IsAlgebraic ℚ α) {q : ℕ} (hq : 0 < q) {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α := by
  have hinjRC : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  set a : ℂ := (α : ℂ) with ha
  have halgC : IsAlgebraic ℚ a := by
    have := halg.algebraMap (A := ℂ)
    simpa [ha] using this
  have hintC : IsIntegral ℚ a := halgC.isIntegral
  haveI : FiniteDimensional ℚ ℚ⟮a⟯ := adjoin.finiteDimensional hintC
  have key := hL halgC hS (q := fun _ ↦ q) (fun n _ ↦ hq) ?_ ?_
  · rw [ha] at key
    exact (isIntegral_algebraMap_iff (R := ℤ) hinjRC).mp key
  · exact (tendsto_const_div_atTop_nhds_zero_nat (Real.log q)).mono_left inf_le_left
  · intro n hn
    obtain ⟨t, ht0, ht⟩ := htr n hn
    set g : ℚ⟮a⟯ := AdjoinSimple.gen ℚ a with hg
    have hgm : algebraMap ℚ⟮a⟯ ℂ g = a := AdjoinSimple.algebraMap_gen ℚ a
    have hinj : Function.Injective (algebraMap ℚ⟮a⟯ ℂ) := (algebraMap ℚ⟮a⟯ ℂ).injective
    have hmp : minpoly ℚ (g ^ n) = minpoly ℚ (α ^ n) := by
      rw [← minpoly.algebraMap_eq hinj (g ^ n), map_pow, hgm, ha,
        show ((α : ℂ)) ^ n = algebraMap ℝ ℂ (α ^ n) by push_cast; norm_num,
        minpoly.algebraMap_eq hinjRC]
    have hsplits : ((minpoly ℚ (g ^ n)).map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
    have htr2 := _root_.trace_eq_sum_roots (K := ℚ) (L := ℚ⟮a⟯) (F := ℂ) hsplits
    rw [hmp] at htr2
    set e : ℕ := finrank ℚ⟮g ^ n⟯ ℚ⟮a⟯ with he
    haveI : FiniteDimensional ℚ⟮g ^ n⟯ ℚ⟮a⟯ := FiniteDimensional.right ℚ _ _
    have he0 : 0 < e := finrank_pos
    have hgoalne : (e : ℤ) * t ≠ 0 := mul_ne_zero (by exact_mod_cast he0.ne') ht0
    refine ⟨(e : ℤ) * t, hgoalne, ?_⟩
    have hsmul : ((q : ℚ⟮a⟯)) * g ^ n = (q : ℚ) • g ^ n := by
      rw [Algebra.smul_def]; push_cast; ring
    have hlin : Algebra.trace ℚ ℚ⟮a⟯ ((q : ℚ⟮a⟯) * g ^ n)
        = (q : ℚ) * Algebra.trace ℚ ℚ⟮a⟯ (g ^ n) := by
      rw [hsmul, map_smul, smul_eq_mul]
    have hinjQ : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
    apply hinjQ
    rw [hlin, map_mul, htr2]
    rw [nsmul_eq_mul]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    push_cast
    linear_combination (e : ℂ) * ht

/-! ### Dubickas's Lemma 5 -/

/-- **Dubickas (2022), Lemma 5**, with Stephan's Lemma 4 in place of Corvaja–Zannier's: if
`q α^(s n)` is pseudo-Pisot for infinitely many `n`, then some `α^(s m)` is a Pisot number.

Dubickas has to run a second argument for the `α = (u/v)^(1/ℓ)` branch of Lemma 4; Stephan's
form has no such branch, so `α` is an algebraic integer outright and the pseudo-Pisot
`q α^(s m)` makes `α^(s m)` Pisot (`isPisot_of_pseudoPisotMul`). -/
theorem exists_isPisot_pow_of_pseudoPisotMul_infinite (hL : Stephan2026CZLemma4) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q) (s : ℕ → ℕ)
    (hs : StrictMono s) (hs0 : 0 < s 0)
    (hinf : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Infinite) :
    ∃ m, IsPisot (α ^ s m) := by
  classical
  have hint : IsIntegral ℚ α := halg.isIntegral
  have hα0 : (0:ℝ) < α := by linarith
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  set d : ℕ := (minpoly ℚ α).natDegree with hd
  -- for `n` large, `α^(s n)` exceeds the degree bound, which forces a nonzero trace
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n ≥ K, (d : ℝ) < α ^ s n := by
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((tendsto_pow_atTop_atTop_of_one_lt hα).eventually_gt_atTop (d : ℝ))
    refine ⟨K, fun n hn ↦ lt_of_lt_of_le (hK n hn) ?_⟩
    exact pow_le_pow_right₀ hα.le (hs.le_apply.trans (le_refl _))
  set S : Set ℕ := {n : ℕ | IsPseudoPisotMul q (α ^ s n)} \ Set.Iio K with hSdef
  have hS : S.Infinite := hinf.diff (Set.finite_Iio K)
  have hmemS : ∀ n ∈ S, IsPseudoPisotMul q (α ^ s n) ∧ K ≤ n := fun n hn ↦ ⟨hn.1, not_lt.1 hn.2⟩
  have htrne : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ s n)).aroots ℂ).sum) = (t : ℂ) := by
    intro n hn
    obtain ⟨⟨h1, h2, t, ht⟩, hnK⟩ := hmemS n hn
    refine ⟨t, ?_, ht⟩
    intro ht0
    subst ht0
    have hintβ : IsIntegral ℚ (α ^ s n) := hint.pow _
    have hmem : ((α ^ s n : ℝ) : ℂ) ∈ (minpoly ℚ (α ^ s n)).aroots ℂ := beta_mem_aroots hintβ
    have hcons : (minpoly ℚ (α ^ s n)).aroots ℂ
        = ((α ^ s n : ℝ) : ℂ) ::ₘ otherConj (α ^ s n) := (Multiset.cons_erase hmem).symm
    rw [hcons, Multiset.sum_cons] at ht
    have hone : ∀ w ∈ otherConj (α ^ s n), ‖w‖ ≤ 1 := by
      intro w hw
      have := h2 w hw
      rw [norm_mul, Complex.norm_natCast] at this
      nlinarith [norm_nonneg w]
    have hsum : ‖(otherConj (α ^ s n)).sum‖ ≤ ((otherConj (α ^ s n)).card : ℝ) * 1 := by
      refine le_trans (norm_multiset_sum_le _) ?_
      have := Multiset.sum_le_card_nsmul ((otherConj (α ^ s n)).map (‖·‖)) (1 : ℝ)
        (by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Multiset.mem_map.1 hx
          rw [← hxw]; exact hone w hw)
      simpa [nsmul_eq_mul, mul_comm] using this
    have hcard : ((otherConj (α ^ s n)).card : ℝ) ≤ (d : ℝ) := by
      have h4 := card_otherConj_pow_le hint (s n)
      have h5 : (otherConj (α ^ s n)).card ≤ d := by omega
      exact_mod_cast h5
    have hq0 : ((q : ℂ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hz : ((α ^ s n : ℝ) : ℂ) = -(otherConj (α ^ s n)).sum := by
      push_cast at ht ⊢
      have := mul_eq_zero.1 ht
      rcases this with h | h
      · exact absurd h hq0
      · linear_combination h
    have hnorm : α ^ s n ≤ (d : ℝ) := by
      have h3 : ‖((α ^ s n : ℝ) : ℂ)‖ = α ^ s n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hz, norm_neg] at h3
      nlinarith [hsum, hcard, h3]
    linarith [hK n hnK]
  -- transport to the exponent set and apply Lemma 4
  have hSimg : (s '' S).Infinite := hS.image (Set.injOn_of_injective hs.injective)
  have htr' : ∀ N ∈ s '' S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ N)).aroots ℂ).sum) = (t : ℂ) := by
    intro N hN
    obtain ⟨n, hn, hNn⟩ := hN
    rw [← hNn]
    exact htrne n hn
  have hintα : IsIntegral ℤ α := isIntegral_of_aroots_trace hL halg hq hSimg htr'
  obtain ⟨n, hn⟩ := hS.nonempty
  obtain ⟨hps, -⟩ := hmemS n hn
  have hsn : 0 < s n := lt_of_lt_of_le hs0 (hs.monotone (Nat.zero_le n))
  exact ⟨n, isPisot_of_pseudoPisotMul hq (one_lt_pow₀ hα hsn.ne') (hintα.pow _) hps⟩


open LeanFormalizations.Literature

/-- Phase 9's `corvajaZannier_dichotomy`, from Stephan's CZ Main Theorem. -/
theorem corvajaZannier_dichotomy_of_czMain (hM : Stephan2026CZMain) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ}
    (hq : 0 < q) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 0 < s 0)
    (hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * s n)) < |(q : ℝ) * α ^ s n - round ((q : ℝ) * α ^ s n)| := by
  sorry

/-- Phase 9's `corvajaZannier_lemma4`, from Stephan's CZ Lemma 4. -/
theorem corvajaZannier_lemma4_of_czLemma4 (hL : Stephan2026CZLemma4) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q)
    (hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α)
    {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α ∨ ∃ (l : ℕ) (r : ℚ), 0 < l ∧ α ^ l = (r : ℝ) :=
  Or.inl (isIntegral_of_aroots_trace hL halg hq hS htr)

/-- **Dubickas (2022), Lemma 6, from Stephan's machine-checked Corvaja–Zannier.**  With this,
Dubickas's Theorem 1 (`Dubickas.lean`) rests only on Stephan's theorems. -/
theorem dubickas2022_of_czMain (hM : Stephan2026CZMain) (hL : Stephan2026CZLemma4)
    (hR : Stephan2026Ridout) : Dubickas2022 := by
  intro α halg hα q hq s hs hs0
  by_cases hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite
  · exact Or.inr (corvajaZannier_dichotomy_of_czMain hM halg hα hq s hs hs0 hfin)
  · exact Or.inl
      (exists_isPisot_pow_of_pseudoPisotMul_infinite hL halg hα hq s hs hs0 hfin)

end LeanFormalizations.Transcendence.Dubickas
