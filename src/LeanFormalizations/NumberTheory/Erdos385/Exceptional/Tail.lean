/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Basic
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.McD
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Mertens

/-!
# Erdős #385, phase E4, step 3: few residues `s mod y#` leave few unblocked positions

`tail_bound`: for `ε ∈ (0, 1/2)` there is `c > 0` with
`#{s < y# : |uSet y s| < c y / log y} ≤ y# · exp(−y^{1/2−ε})` for large `y`.

Split the primes `≤ y` at `z = y^θ`, `θ = 1/2 − ε/2` (CRT, `card_filter_range_primorial`).  For
fixed low residues `u`, `LinearSieveIntervalLower` gives `T(u) ⊆ (y/2, y]` unblocked by the low
primes with `|T(u)| ≥ c₁ y / log y`; the count `f(v)` of `a ∈ T(u)` unblocked by the high residues
`v` has mean `|T(u)| ∏_{z<p≤y}(1 − 1/p) ≥ δ c₁ y / log y` (`exists_prod_high_ge`) and bounded
differences `2(y/p + 1) ≤ 4y/p`, whose squares sum to `≤ 16 y²/⌊z⌋` (`sum_high_inv_sq_le`);
`mcd_count` finishes, since `|uSet y s| ≥ f`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Literature Finset Filter

theorem exponent_bound {c y lg S tt F z ε : ℝ} (hc : 0 < c) (hy : 1 ≤ y) (hlg : 0 < lg)
    (hS : 0 < S) (_hF : 0 < F) (hzF : z ≤ 2 * F) (hSF : S * F ≤ 16 * y ^ 2)
    (ht : c * y / lg ≤ tt) (hlog : lg ^ 2 ≤ c ^ 2 / 16 * y ^ (ε / 2))
    (hz : z = y ^ ((1 : ℝ) / 2 - ε) * y ^ (ε / 2)) :
    y ^ ((1 : ℝ) / 2 - ε) ≤ 2 * tt ^ 2 / S := by
  have hA : c ^ 2 * z / (16 * lg ^ 2) ≤ 2 * tt ^ 2 / S := by
    rw [div_le_div_iff₀ (by positivity) hS]
    have h0 : (c * y / lg) ^ 2 * lg ^ 2 = c ^ 2 * y ^ 2 := by field_simp
    have h1 : c ^ 2 * y ^ 2 ≤ tt ^ 2 * lg ^ 2 := by
      rw [← h0]; gcongr
    have h2 : c ^ 2 * z * S ≤ c ^ 2 * (2 * F) * S := by gcongr
    have h3 : c ^ 2 * (2 * F) * S ≤ 32 * (c ^ 2 * y ^ 2) := by nlinarith [sq_nonneg c]
    nlinarith
  have hB : y ^ ((1 : ℝ) / 2 - ε) ≤ c ^ 2 * z / (16 * lg ^ 2) := by
    rw [le_div_iff₀ (by positivity), hz]
    have : 0 ≤ y ^ ((1 : ℝ) / 2 - ε) := by positivity
    nlinarith
  linarith

/-- **Step 3: the tail of `|uSet y s|`.** -/
theorem tail_bound (h2 : LinearSieveIntervalLower) (h3 : McDiarmidFinite) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      (((range (primorial y)).filter fun s =>
          ((uSet y s).card : ℝ) < c * y / Real.log y).card : ℝ) ≤
        primorial y * Real.exp (-(y : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
  obtain ⟨c₁, hc₁, Y₀, hY₀⟩ := h2 (ε / 2) (by linarith)
  obtain ⟨δ, hδ, y₁, hy₁⟩ := exists_prod_high_ge (θ := 1 / 2 - ε / 2) (by linarith) (by linarith)
  set c : ℝ := δ * c₁ / 2 with hcdef
  have hc : 0 < c := by positivity
  refine ⟨c, hc, ?_⟩
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by linarith : 0 < ε / 2)).bound
    (by positivity : (0 : ℝ) < c ^ 2 / 16)
  have hev : ∀ᶠ y : ℕ in atTop,
      Real.log y ^ 2 ≤ (c ^ 2 / 16) * (y : ℝ) ^ (ε / 2) ∧ (2 : ℝ) ≤ y ∧
        (2 : ℝ) ≤ (y : ℝ) ^ (1 / 2 + ε / 2) := by
    refine ((tendsto_natCast_atTop_atTop.eventually hlo).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 2).and
        (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 + ε / 2)).comp
          tendsto_natCast_atTop_atTop).eventually_ge_atTop 2))).mono
      fun y hy => ⟨?_, hy.2.1, hy.2.2⟩
    have h := hy.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (ε / 2))] at h
    exact (le_abs_self _).trans h
  obtain ⟨y₂, hy₂⟩ := eventually_atTop.1 hev
  refine ⟨max (max Y₀ y₁) y₂, fun y hy => ?_⟩
  obtain ⟨hlog2, hy2, hyrp⟩ := hy₂ y (le_of_max_le_right hy)
  have hyY : Y₀ ≤ y := le_of_max_le_left (le_of_max_le_left hy)
  have hyy₁ : y₁ ≤ y := le_of_max_le_right (le_of_max_le_left hy)
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set θ : ℝ := 1 / 2 - ε / 2 with hθ
  set z : ℝ := (y : ℝ) ^ θ with hzdef
  have hz1 : 1 ≤ z := Real.one_le_rpow hy1 (by linarith)
  have hzy : z ≤ y := by
    calc (y : ℝ) ^ θ ≤ (y : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ = y := Real.rpow_one _
  set L : Finset ℕ := (ps y).filter fun p => (p : ℝ) ≤ z with hLdef
  have hL : L ⊆ ps y := filter_subset _ _
  have hH : hiPs y z = ps y \ L := by rw [hiPs, filter_not]
  -- the low residues as a function on primes
  let r : (∀ p : L, Fin p) → ℕ → ℕ := fun u q => if h : q ∈ L then (u ⟨q, h⟩ : ℕ) else 0
  let T : (∀ p : L, Fin p) → Finset ℕ := fun u =>
    (Icc 1 y).filter fun a => y / 2 < a ∧ ∀ q ∈ L, a % q ≠ r u q % q
  have hTsub : ∀ u, T u ⊆ Icc 1 y := fun u => filter_subset _ _
  have hTcard : ∀ u, c₁ * y / Real.log y ≤ (T u).card := by
    intro u
    have h := hY₀ y hyY (r u)
    have hset : {a : ℕ | y / 2 < a ∧ a ≤ y ∧ ∀ q : ℕ, q.Prime →
        (q : ℝ) ≤ (y : ℝ) ^ ((1 : ℝ) / 2 - ε / 2) → a % q ≠ r u q % q} = ↑(T u) := by
      ext a
      simp only [Set.mem_setOf_eq, coe_filter, mem_Icc, T]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨by omega, h2⟩, h1, fun q hq => ?_⟩
        have hq' := mem_filter.1 hq
        exact h3 q (mem_filter.1 hq'.1).2 hq'.2
      · rintro ⟨⟨_, h2⟩, h1, h3⟩
        refine ⟨h1, h2, fun q hq hqz => h3 q (mem_filter.2 ⟨mem_filter.2 ⟨?_, hq⟩, hqz⟩)⟩
        have : (q : ℝ) ≤ y := hqz.trans hzy
        have : q ≤ y := by exact_mod_cast this
        exact mem_range.2 (by omega)
    rw [hset, Set.ncard_coe_finset] at h
    exact h
  set H : Finset ℕ := ps y \ L with hHdef
  have hm2 : ∀ i : H, 2 ≤ (i : ℕ) := fun i => (mem_filter.1 (Finset.mem_sdiff.1 i.2).1).2.two_le
  set Pr : ℝ := ∏ i : H, (1 - 1 / ((i : ℕ) : ℝ)) with hPrdef
  have hPr : δ ≤ Pr := by
    have := hy₁ y hyy₁
    rw [hH, ← prod_coe_sort] at this
    exact this
  set t : (∀ p : L, Fin p) → ℝ := fun u => (T u).card * Pr / 2 with htdef
  have htpos : ∀ u, 0 < t u := by
    intro u
    have := hTcard u
    have : 0 < c₁ * y / Real.log y := by positivity
    have : 0 < Pr := lt_of_lt_of_le hδ hPr
    have : (0 : ℝ) < (T u).card := by linarith
    simp only [htdef]; positivity
  let Φ : (∀ p : L, Fin p) → (∀ p : H, Fin p) → Prop := fun u v =>
    (((T u).filter fun a => ∀ i, (v i : ℕ) ≠ a % (i : ℕ)).card : ℝ) ≤ (T u).card * Pr - t u
  -- small `uSet` forces the McDiarmid event
  have hsub : ((range (primorial y)).filter fun s => ((uSet y s).card : ℝ) < c * y / Real.log y)
      ⊆ (range (primorial y)).filter fun s => Φ (resVec L hL s) (resVec H sdiff_subset s) := by
    intro s hs
    rw [mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    set u := resVec L hL s
    have hle : (((T u).filter fun a => ∀ i : H, ((resVec H sdiff_subset s i : Fin _) : ℕ) ≠
        a % (i : ℕ)).card : ℝ) ≤ (uSet y s).card := by
      have : ((T u).filter fun a => ∀ i : H, ((resVec H sdiff_subset s i : Fin _) : ℕ) ≠
          a % (i : ℕ)) ⊆ uSet y s := by
        intro a ha
        simp only [mem_filter, T] at ha
        obtain ⟨⟨haI, _, haL⟩, haH⟩ := ha
        simp only [uSet, mem_filter]
        refine ⟨haI, fun p hp => ?_⟩
        have hpps : p ∈ ps y := by
          simp only [ps, mem_filter, mem_range, mem_Iic] at hp ⊢; exact ⟨by omega, hp.2⟩
        by_cases hpL : p ∈ L
        · have := haL p hpL
          simp only [r, dif_pos hpL, u, resVec] at this
          rw [Nat.mod_mod] at this
          exact fun h => this h.symm
        · have := haH ⟨p, mem_sdiff.2 ⟨hpps, hpL⟩⟩
          simp only [resVec] at this
          exact this
      exact_mod_cast card_le_card this
    have hK : c * y / Real.log y ≤ (T u).card * Pr - t u := by
      have h1 := hTcard u
      have h0 : 0 ≤ c₁ * y / Real.log y := by positivity
      have : (T u).card * Pr - t u = (T u).card * Pr / 2 := by simp only [htdef]; ring
      rw [this, hcdef]
      have : δ * (c₁ * y / Real.log y) ≤ Pr * (T u).card := mul_le_mul hPr h1 h0 (by linarith)
      have : δ * c₁ / 2 * y / Real.log y = δ * (c₁ * y / Real.log y) / 2 := by ring
      linarith
    show _ ≤ _
    linarith [hs.2]
  -- `H` is nonempty (Bertrand), so the McDiarmid denominator is positive
  have hz2 : 2 * z ≤ y := by
    have : (y : ℝ) = z * (y : ℝ) ^ (1 / 2 + ε / 2) := by
      rw [hzdef, ← Real.rpow_add (by linarith)]
      have : θ + (1 / 2 + ε / 2) = 1 := by rw [hθ]; ring
      rw [this, Real.rpow_one]
    nlinarith
  have hHne : H.Nonempty := by
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (y / 2)
      (by have : 2 ≤ y := by exact_mod_cast hy2
          omega)
    refine ⟨p, mem_sdiff.2 ⟨mem_filter.2 ⟨mem_range.2 (by omega), hp⟩, fun hpL => ?_⟩⟩
    have hpz := (mem_filter.1 hpL).2
    have : ((y / 2 : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hp1
    have : (y : ℝ) / 2 < ((y / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := y) (by norm_num : 0 < 2)
      have : (y : ℝ) < ((y / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
      linarith
    linarith
  set S : ℝ := ∑ i : H, (2 * ((y : ℝ) / ((i : ℕ) : ℝ) + 1)) ^ 2 with hSdef
  have hSle : S ≤ 16 * (y : ℝ) ^ 2 / ⌊z⌋₊ := by
    have hterm : ∀ i : H, (2 * ((y : ℝ) / ((i : ℕ) : ℝ) + 1)) ^ 2 ≤
        16 * (y : ℝ) ^ 2 * (1 / ((i : ℕ) : ℝ) ^ 2) := by
      intro i
      have hi2 : (2 : ℝ) ≤ (i : ℕ) := by exact_mod_cast hm2 i
      have hiy : ((i : ℕ) : ℝ) ≤ y := by
        have := mem_range.1 (mem_filter.1 (mem_sdiff.1 i.2).1).1
        exact_mod_cast (show (i : ℕ) ≤ y by omega)
      have h1 : (1 : ℝ) ≤ y / (i : ℕ) := by rw [le_div_iff₀ (by linarith)]; linarith
      have : 2 * ((y : ℝ) / ((i : ℕ) : ℝ) + 1) ≤ 4 * ((y : ℝ) / (i : ℕ)) := by linarith
      calc (2 * ((y : ℝ) / ((i : ℕ) : ℝ) + 1)) ^ 2 ≤ (4 * ((y : ℝ) / (i : ℕ))) ^ 2 := by
            gcongr
        _ = _ := by field_simp; ring
    have hsq := sum_high_inv_sq_le y z hz1
    rw [hH, ← sum_coe_sort] at hsq
    calc S ≤ ∑ i : H, 16 * (y : ℝ) ^ 2 * (1 / ((i : ℕ) : ℝ) ^ 2) := sum_le_sum fun i _ => hterm i
      _ = 16 * (y : ℝ) ^ 2 * ∑ i : H, (1 / ((i : ℕ) : ℝ) ^ 2) := by rw [mul_sum]
      _ ≤ 16 * (y : ℝ) ^ 2 * (1 / ⌊z⌋₊) := by gcongr
      _ = _ := by ring
  have hSpos : 0 < S := by
    obtain ⟨p, hp⟩ := hHne
    exact lt_of_lt_of_le (by positivity) (single_le_sum (f := fun i : H =>
      (2 * ((y : ℝ) / ((i : ℕ) : ℝ) + 1)) ^ 2) (fun _ _ => by positivity) (mem_univ ⟨p, hp⟩))
  have hfloor : z / 2 ≤ (⌊z⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one z
    have : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hz1)
    linarith
  have hexp : ∀ u, Real.exp (-2 * t u ^ 2 / S) ≤ Real.exp (-(y : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
    intro u
    apply Real.exp_le_exp.2
    have htu : c * y / Real.log y ≤ t u := by
      have h1 := hTcard u
      have h0 : 0 ≤ c₁ * y / Real.log y := by positivity
      have : δ * (c₁ * y / Real.log y) ≤ Pr * (T u).card := mul_le_mul hPr h1 h0 (by linarith)
      simp only [htdef, hcdef]
      have : δ * c₁ / 2 * y / Real.log y = δ * (c₁ * y / Real.log y) / 2 := by ring
      linarith
    have hfl0 : 0 < (⌊z⌋₊ : ℝ) := by linarith
    have hS' : S * ⌊z⌋₊ ≤ 16 * (y : ℝ) ^ 2 := by
      rwa [le_div_iff₀ hfl0] at hSle
    have hsplit : z = (y : ℝ) ^ ((1 : ℝ) / 2 - ε) * (y : ℝ) ^ (ε / 2) := by
      rw [hzdef, ← Real.rpow_add (by linarith), hθ]; ring_nf
    have := exponent_bound hc hy1 hlogy hSpos hfl0 (by linarith) hS' htu hlog2 hsplit
    rw [neg_mul, neg_div, neg_le_neg_iff]
    exact this
  have hcrt := card_filter_range_primorial y L hL Φ
  calc (((range (primorial y)).filter fun s =>
          ((uSet y s).card : ℝ) < c * y / Real.log y).card : ℝ)
      ≤ (((range (primorial y)).filter fun s =>
          Φ (resVec L hL s) (resVec H sdiff_subset s)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ = ∑ u, ((univ.filter fun v => Φ u v).card : ℝ) := by
        rw [hcrt]; push_cast; rfl
    _ ≤ ∑ u : (∀ p : L, Fin p), (∏ i : H, (((i : ℕ)) : ℝ)) *
          Real.exp (-(y : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
        refine sum_le_sum fun u _ => ?_
        have := mcd_count h3 (fun i : H => (i : ℕ)) hm2 y (T u) (hTsub u) (t u) (htpos u)
        refine this.trans ?_
        gcongr
        exact Real.exp_le_exp.1 (hexp u)
    _ = primorial y * Real.exp (-(y : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
        rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [Fintype.card_pi]
        simp only [Fintype.card_fin]
        push_cast
        rw [prod_coe_sort L (fun p => (p : ℝ)), prod_coe_sort H (fun p => (p : ℝ)), mul_comm,
          prod_sdiff hL, primorial_eq_prod_ps]
        push_cast; rfl

end LeanFormalizations.Erdos385.Exceptional
