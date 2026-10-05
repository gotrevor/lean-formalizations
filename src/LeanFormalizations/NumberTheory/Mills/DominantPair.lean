/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.PisotGalois

/-!
# Phase 62, lap 4: the dominant pair does not cancel along a `3n − d` orbit

Let `β` be Pisot of degree `≥ 2`, `R = conjMax β`.  By Mignotte-lite
(`PisotGalois.eq_or_eq_conj_of_norm_eq`) the other conjugates of modulus `R` are `{γ}` (`γ` real)
or `{γ, γ̄}`.  In the real case `|S(n)| ≈ Rⁿ`.  In the pair case, with `u = γ/R`,
`|γⁿ + γ̄ⁿ| = Rⁿ |u^(2n) + 1|`.  If `u^(2n_k) → −1` along a set of indices with bounded gaps on which
`g n_r = 3^(r−k) g n_k − s (3^(r−k) − 1)`, then comparing consecutive indices gives
`u^(2s(3^t−1)) = 1` for some `t ≥ 1`, so `γ^N = γ̄^N`, contradicting
`PisotGalois.pow_ne_pow_of_roots`.  Main result: `lower_along_records`.
-/

namespace LeanFormalizations.Mills.DominantPair

open Polynomial Filter LeanFormalizations.Literature LeanFormalizations.Mills
open LeanFormalizations.Mills.ShiftedMillsLarge LeanFormalizations.Mills.PisotGalois

/-- `‖xᵐ − yᵐ‖ ≤ m ‖x − y‖` on the closed unit disc. -/
theorem norm_pow_sub_pow_le_mul {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (m : ℕ) :
    ‖x ^ m - y ^ m‖ ≤ m * ‖x - y‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hid : x ^ (m + 1) - y ^ (m + 1) = x * (x ^ m - y ^ m) + (x - y) * y ^ m := by ring
    have hym : ‖y ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    rw [hid]
    calc ‖x * (x ^ m - y ^ m) + (x - y) * y ^ m‖
        ≤ ‖x‖ * ‖x ^ m - y ^ m‖ + ‖x - y‖ * ‖y ^ m‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ 1 * (m * ‖x - y‖) + ‖x - y‖ * 1 := by
          gcongr
      _ = ((m + 1 : ℕ) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- On the unit circle, `‖v + v̄‖ = ‖v² + 1‖`. -/
theorem norm_add_conj_eq {v : ℂ} (hv : ‖v‖ = 1) : ‖v + starRingEnd ℂ v‖ = ‖v ^ 2 + 1‖ := by
  have : v ^ 2 + 1 = v * (v + starRingEnd ℂ v) := by
    rw [mul_add, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; push_cast; ring
  rw [this, norm_mul, hv, one_mul]

/-- Small conjugates are negligible: `Σ |z|ⁿ / Rⁿ → 0` when every `|z| < R`. -/
theorem tendsto_sum_pow_div {s : Multiset ℂ} {R : ℝ} (hR : 0 < R) (hs : ∀ z ∈ s, ‖z‖ < R) :
    Tendsto (fun n : ℕ => (s.map (fun z => ‖z‖ ^ n)).sum / R ^ n) atTop (nhds 0) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have h1 : Tendsto (fun n : ℕ => (‖a‖ / R) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hR).2 ha)
    have h2 := ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    have := h1.add h2
    simp only [add_zero] at this
    refine this.congr (fun n => ?_)
    simp [Multiset.map_cons, Multiset.sum_cons, add_div, div_pow]

/-- **The root-of-unity step.**  If `u` is on the unit circle, `u^(2 n_k) → −1` along `Rec`, `Rec`
has gaps `≤ T`, and `g n_r = 3^(r−k) g n_k − s(3^(r−k) − 1)` between members, then
`u^(2s(3^t − 1)) = 1` for some `1 ≤ t ≤ T`. -/
theorem zpow_eq_one_of_records {u : ℂ} (hu : ‖u‖ = 1) {n : ℕ → ℕ} {Rec : ℕ → Prop} {T K' : ℕ}
    (hT : ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ Rec r) {g : ℕ} {s : ℤ}
    (hrel : ∀ k r, K' ≤ k → Rec k → Rec r → k < r →
      (g : ℤ) * n r = 3 ^ (r - k) * (g * n k) - s * (3 ^ (r - k) - 1))
    (hlim : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, Rec k → ‖u ^ (2 * n k) + 1‖ < ε) :
    ∃ t, 1 ≤ t ∧ t ≤ T ∧ u ^ (2 * s * ((3 : ℤ) ^ t - 1)) = 1 := by
  by_contra hcon
  push Not at hcon
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  obtain ⟨r1, hr1, hr1T, -⟩ := hT K' le_rfl
  set E : ℕ → ℤ := fun t => 2 * s * ((3 : ℤ) ^ t - 1) with hE
  obtain ⟨t0, ht0, hmin⟩ := (Finset.Icc 1 T).exists_min_image (fun t => ‖u ^ E t - 1‖)
    ⟨1, by simp; omega⟩
  rw [Finset.mem_Icc] at ht0
  set ε0 := ‖u ^ E t0 - 1‖ with hε0
  have hε0pos : 0 < ε0 := norm_pos_iff.2 (sub_ne_zero.2 (hcon t0 ht0.1 ht0.2))
  set D : ℝ := g * 3 ^ T + g + 1 with hD
  have hDpos : 0 < D := by positivity
  set δ := ε0 / D with hδ
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hlim δ (by positivity))
  obtain ⟨k, hk1, -, hkrec⟩ := hT (max N0 K') (le_max_right _ _)
  obtain ⟨r, hkr, hrT, hrrec⟩ := hT k (by omega)
  have ha := hN0 k (by omega) hkrec
  have hb := hN0 r (by omega) hrrec
  set a := u ^ (2 * n k) with hadef
  set b := u ^ (2 * n r) with hbdef
  have hrel' := hrel k r (by omega) hkrec hrrec hkr
  set t := r - k with htdef
  have ht1 : 1 ≤ t := by omega
  have htT : t ≤ T := by omega
  have hkey : b ^ g * u ^ E t = (a ^ g) ^ (3 ^ t) := by
    rw [hbdef, hadef, ← pow_mul, ← pow_mul, ← pow_mul, ← zpow_natCast u (2 * n r * g),
      ← zpow_add₀ hu0, ← zpow_natCast]
    congr 1
    rw [hE]; push_cast
    linear_combination 2 * hrel'
  have hnu : ∀ m : ℕ, ‖u ^ m‖ = 1 := fun m => by rw [norm_pow, hu, one_pow]
  have hna : ‖a‖ = 1 := hnu _
  have hnb : ‖b‖ = 1 := hnu _
  have hnbg : ‖b ^ g‖ = 1 := by rw [norm_pow, hnb, one_pow]
  have hodd : ((-1 : ℂ)) ^ (g * 3 ^ t) = (-1) ^ g := by
    rw [pow_mul', Odd.neg_one_pow (Odd.pow (by decide : Odd 3)), ]
  have hn1 : ‖(-1 : ℂ)‖ ≤ 1 := by simp
  have h1 := norm_pow_sub_pow_le_mul hna.le hn1 (g * 3 ^ t)
  have h2 := norm_pow_sub_pow_le_mul hn1 hnb.le g
  have hfac : u ^ E t - 1 = b ^ g * (u ^ E t - 1) * (b ^ g)⁻¹ := by
    have : b ^ g ≠ 0 := by intro h; rw [h, norm_zero] at hnbg; exact zero_ne_one hnbg
    field_simp
  have hsplit : b ^ g * (u ^ E t - 1) =
      (a ^ (g * 3 ^ t) - (-1) ^ (g * 3 ^ t)) + ((-1) ^ g - b ^ g) := by
    rw [hodd, pow_mul, ← hkey]; ring
  have hle : ε0 ≤ ‖u ^ E t - 1‖ := hmin t (Finset.mem_Icc.2 ⟨ht1, htT⟩)
  have hnorm : ‖u ^ E t - 1‖ = ‖b ^ g * (u ^ E t - 1)‖ := by
    rw [norm_mul, hnbg, one_mul]
  have hamb : ‖a - (-1)‖ < δ := by simpa using ha
  have hbm : ‖(-1) - b‖ < δ := by rw [norm_sub_rev]; simpa using hb
  have h3t : (3 : ℝ) ^ t ≤ 3 ^ T := pow_le_pow_right₀ (by norm_num) htT
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hbound : ‖b ^ g * (u ^ E t - 1)‖ ≤ (g * 3 ^ T + g) * δ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have e1 : ((g * 3 ^ t : ℕ) : ℝ) * ‖a - -1‖ ≤ g * 3 ^ T * δ := by
      push_cast
      have := mul_le_mul_of_nonneg_left h3t hg0
      rw [mul_comm ((g : ℝ) * 3 ^ T) δ]
      calc (g : ℝ) * 3 ^ t * ‖a - -1‖ ≤ (g * 3 ^ T) * δ :=
            mul_le_mul this hamb.le (norm_nonneg _) (by positivity)
        _ = δ * (g * 3 ^ T) := by ring
    have e2 : (g : ℝ) * ‖-1 - b‖ ≤ g * δ := mul_le_mul_of_nonneg_left hbm.le hg0
    nlinarith
  have hfin : (g * 3 ^ T + g) * δ < ε0 := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ hDpos, hD]
    nlinarith
  linarith

/-- A nonempty multiset of nonnegative reals contains its `fold max 0`. -/
theorem fold_max_mem {s : Multiset ℝ} (hs : s ≠ 0) (h0 : ∀ x ∈ s, 0 ≤ x) : s.fold max 0 ∈ s := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a t ih =>
    rw [Multiset.fold_cons_left]
    by_cases ht : t = 0
    · subst ht; simp [max_eq_left (h0 a (by simp))]
    · have hm := ih ht (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
      rcases le_total a (t.fold max 0) with h | h
      · rw [max_eq_right h]; exact Multiset.mem_cons_of_mem hm
      · rw [max_eq_left h]; exact Multiset.mem_cons_self _ _

/-- **The dominant conjugates do not cancel along a `3n − d` orbit.**  For `β` Pisot of degree
`≥ 2`, exponents `n_k → ∞`, and a set `Rec` with gaps `≤ T` on which
`g n_r = 3^(r−k) g n_k − s(3^(r−k) − 1)` (`s ≠ 0`), the conjugate power sum is at least
`c Rⁿ` infinitely often on `Rec`. -/
theorem lower_along_records {β : ℝ} (hβ : IsPisot β) (hdeg : 2 ≤ (minpoly ℚ β).natDegree)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {Rec : ℕ → Prop} {T K' : ℕ}
    (hT : ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ Rec r) {g : ℕ} {s : ℤ} (hs : s ≠ 0)
    (hrel : ∀ k r, K' ≤ k → Rec k → Rec r → k < r →
      (g : ℤ) * n r = 3 ^ (r - k) * (g * n k) - s * (3 ^ (r - k) - 1)) :
    ∃ c > (0 : ℝ), ∃ᶠ k in atTop, Rec k ∧ c * conjMax β ^ n k ≤ ‖conjPowSum β (n k)‖ := by
  classical
  have hRec : ∃ᶠ k in atTop, Rec k := frequently_atTop.2 fun m => by
    obtain ⟨r, h1, -, h2⟩ := hT (max m K') (le_max_right _ _)
    exact ⟨r, by omega, h2⟩
  have hint := hβ.2.1
  set R := conjMax β with hRdef
  have hR0 : 0 ≤ R := conjMax_nonneg β
  rcases hR0.eq_or_lt with hR | hRpos
  · refine ⟨1, one_pos, (hRec.and_eventually (hn.eventually_ge_atTop 1)).mono ?_⟩
    rintro k ⟨hk, hk1⟩
    refine ⟨hk, ?_⟩
    rw [← hR, zero_pow (by omega)]; simp
  -- the dominant conjugate `γ`
  set oc := otherConj β with hoc
  have hcard := card_otherConj_add_one hint.tower_top
  have hne : oc ≠ 0 := by
    intro h; rw [← hoc, h, Multiset.card_zero] at hcard; omega
  have hmem := fold_max_mem (s := oc.map (‖·‖)) (by simpa using hne)
    (fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg _)
  obtain ⟨γ, hγoc, hγR⟩ := Multiset.mem_map.1 hmem
  change ‖γ‖ = R at hγR
  set fC := (minpoly ℤ β).map (Int.castRingHom ℂ) with hfC
  have hmon : fC.Monic := (minpoly_int_monic hint).map _
  have hroot : ∀ z ∈ oc, fC.eval z = 0 := by
    intro z hz
    have := Multiset.mem_of_mem_erase hz
    rw [aroots_eq_roots hint] at this
    exact (mem_roots hmon.ne_zero).1 this
  have hR1 : R < 1 := conjMax_lt_one hβ
  have hβ1 : 1 < β := hβ.1
  set γb := starRingEnd ℂ γ with hγb
  have hγbR : ‖γb‖ = R := by rw [hγb, Complex.norm_conj, hγR]
  have hγboc : γb ∈ oc := by
    refine (Multiset.mem_erase_of_ne ?_).2 ?_
    · intro h
      have : ‖γb‖ = β := by rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · rw [aroots_eq_roots hint]
      exact (mem_roots hmon.ne_zero).2 (eval_conj_complex (hroot γ hγoc))
  have hsep : (minpoly ℚ β).Separable := (minpoly.irreducible hint.tower_top).separable
  have hnodup : oc.Nodup :=
    (nodup_roots ((separable_map _).mpr hsep)).erase _
  set F := oc.filter (fun z => ‖z‖ = R) with hF
  set G := oc.filter (fun z => ¬ ‖z‖ = R) with hG
  have hsum : ∀ m, conjPowSum β m = (F.map (· ^ m)).sum + (G.map (· ^ m)).sum := by
    intro m
    rw [conjPowSum, ← hoc, ← Multiset.sum_add, ← Multiset.map_add, hF, hG,
      Multiset.filter_add_not]
  have hFmem : ∀ z, z ∈ F ↔ z = γ ∨ z = γb := by
    intro z
    rw [hF, Multiset.mem_filter]
    constructor
    · rintro ⟨hz, hzR⟩
      exact eq_or_eq_conj_of_norm_eq hβ (hroot γ hγoc) (hroot z hz) (by rw [hzR, hγR])
    · rintro (rfl | rfl)
      · exact ⟨hγoc, hγR⟩
      · exact ⟨hγboc, hγbR⟩
  -- the small part is negligible
  have hGsmall : ∀ z ∈ G, ‖z‖ < R := by
    intro z hz
    rw [hG, Multiset.mem_filter] at hz
    exact lt_of_le_of_ne (norm_le_conjMax hz.1) hz.2
  have hGlim := tendsto_sum_pow_div hRpos hGsmall
  have hGbound : ∀ m, ‖(G.map (· ^ m)).sum‖ ≤ (G.map (fun z => ‖z‖ ^ m)).sum := by
    intro m
    refine (norm_multiset_sum_le _).trans (le_of_eq ?_)
    rw [Multiset.map_map]; congr 1; apply Multiset.map_congr rfl; intro z _; simp [norm_pow]
  have hGev : ∀ ε > (0 : ℝ), ∀ᶠ m : ℕ in atTop, ‖(G.map (· ^ m)).sum‖ ≤ ε * R ^ m := by
    intro ε hε
    filter_upwards [hGlim.eventually (gt_mem_nhds hε)] with m hm
    have hRm : 0 < R ^ m := pow_pos hRpos m
    rw [div_lt_iff₀ hRm] at hm
    exact (hGbound m).trans hm.le
  have hFnd : F.Nodup := hnodup.filter _
  by_cases hreal : γb = γ
  · -- one real dominant conjugate
    have hFeq : F = {γ} := by
      rw [Multiset.Nodup.ext hFnd (Multiset.nodup_singleton γ)]
      intro z; rw [hFmem, Multiset.mem_singleton, hreal, or_self]
    refine ⟨1 / 2, by norm_num, ?_⟩
    refine (hRec.and_eventually (hn.eventually (hGev (1 / 2) (by norm_num)))).mono ?_
    rintro k ⟨hk, hkG⟩
    refine ⟨hk, ?_⟩
    rw [hsum, hFeq]
    simp only [Multiset.map_singleton, Multiset.sum_singleton]
    have h1 : ‖γ ^ n k‖ = R ^ n k := by rw [norm_pow, hγR]
    have := norm_sub_norm_le (γ ^ n k) (-(G.map (· ^ n k)).sum)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  · -- the pair `γ, γ̄`
    have hFeq : F = γ ::ₘ {γb} := by
      have hnd : (γ ::ₘ ({γb} : Multiset ℂ)).Nodup := by
        rw [Multiset.nodup_cons]
        exact ⟨by rw [Multiset.mem_singleton]; exact fun h => hreal h.symm,
          Multiset.nodup_singleton _⟩
      rw [Multiset.Nodup.ext hFnd hnd]
      intro z; rw [hFmem, Multiset.mem_cons, Multiset.mem_singleton]
    set u : ℂ := γ / (R : ℂ) with hudef
    have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_div, hγR, Complex.norm_real, Real.norm_of_nonneg hR0, div_self hRpos.ne']
    have hγu : γ = R * u := by rw [hudef]; field_simp
    have hmain : ∀ m : ℕ, ‖(F.map (· ^ m)).sum‖ = R ^ m * ‖u ^ (2 * m) + 1‖ := by
      intro m
      rw [hFeq]
      simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
        Multiset.sum_singleton]
      have hu' : γb = R * starRingEnd ℂ u := by
        rw [hγb, hγu, map_mul, Complex.conj_ofReal]
      rw [hu', hγu, mul_pow, mul_pow, ← mul_add, norm_mul, ← map_pow, norm_pow,
        Complex.norm_real, Real.norm_of_nonneg hR0, norm_add_conj_eq (by rw [norm_pow, hu,
          one_pow]), ← pow_mul, mul_comm m 2]
    -- the non-cancellation input
    have hc0 : ∃ c0 > (0 : ℝ), ∃ᶠ k in atTop, Rec k ∧ c0 ≤ ‖u ^ (2 * n k) + 1‖ := by
      by_contra hcon
      push Not at hcon
      have hlim : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, Rec k → ‖u ^ (2 * n k) + 1‖ < ε := by
        intro ε hε
        exact hcon ε hε
      obtain ⟨t, ht1, -, ht⟩ := zpow_eq_one_of_records hu hT hrel hlim
      set E : ℤ := 2 * s * ((3 : ℤ) ^ t - 1) with hE
      have hE0 : E ≠ 0 := by
        have : (3 : ℤ) ^ 1 ≤ 3 ^ t := pow_le_pow_right₀ (by norm_num) ht1
        rw [hE]; intro h
        rcases mul_eq_zero.1 h with h | h
        · omega
        · norm_num at this; omega
      have hN : u ^ E.natAbs = 1 := by
        rcases Int.natAbs_eq E with h | h
        · rw [← zpow_natCast, ← h, ht]
        · rw [← zpow_natCast, show ((E.natAbs : ℕ) : ℤ) = -E by omega, zpow_neg, ht, inv_one]
      have hγN : γ ^ E.natAbs = γb ^ E.natAbs := by
        rw [hγb, ← map_pow, hγu, mul_pow, hN, mul_one, ← Complex.ofReal_pow,
          Complex.conj_ofReal]
      exact pow_ne_pow_of_roots hβ (hroot γ hγoc) (hroot γb hγboc) (Ne.symm hreal)
        (Int.natAbs_pos.2 hE0) hγN
    obtain ⟨c0, hc0pos, hfreq⟩ := hc0
    refine ⟨c0 / 2, by positivity, ?_⟩
    refine (hfreq.and_eventually (hn.eventually (hGev (c0 / 2) (by positivity)))).mono ?_
    rintro k ⟨⟨hk, hkc⟩, hkG⟩
    refine ⟨hk, ?_⟩
    rw [hsum]
    have h1 := hmain (n k)
    have := norm_sub_norm_le ((F.map (· ^ n k)).sum) (-(G.map (· ^ n k)).sum)
    rw [sub_neg_eq_add, norm_neg] at this
    have hRk : 0 ≤ R ^ n k := pow_nonneg hR0 _
    nlinarith [mul_le_mul_of_nonneg_left hkc hRk]

end LeanFormalizations.Mills.DominantPair
