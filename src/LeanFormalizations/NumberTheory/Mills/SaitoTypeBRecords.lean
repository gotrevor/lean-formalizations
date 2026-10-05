/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBNoGap

/-!
# Phase 62, lap 2: a record-index competitor that avoids Saito's case (I)

Saito's Lemma 5.2 needs the lower chain condition `p_k^(1/C k) ≤ p_(k+1)^(1/C(k+1))` eventually
(`eventually_low`), and its proof (case (I)) is where Baker enters.  Here we never assume it.

**Records.**  Call `m` a *record* when `p_m^(1/C m) ≥ p_k^(1/C k)` for every `1 ≤ k ≤ m`
(`IsRecord`).  For the least `ξ`:
* records are infinite (`frequently_record`): `ξ = sup_k p_k^(1/C k)`, and the sup is not attained
  since no `ξ^(C m)` is an integer;
* the BHP window holds at every large record (`window_at_record`): the competitor chain started
  at a record `m` lies above every earlier lower root, so no lower-chain hypothesis is needed.

**Non-records are rigid.**  If `r < m` and `p_m^(1/C m) < p_r^(1/C r)` then
`e {ξ^(C r)} p_r^(e − 1) < 1` with `e = C m / C r` (Saito (5.1), `fract_lt_of_floor_lt`).  Once
`β = ξ^g` is Pisot of degree `ℓ` with `g ∣ C r`, the norm of `β^(C r / g) − p_r` is a nonzero
integer, so `{ξ^(C r)} ≥ (p_r + 1)^(−(ℓ−1))`.  Hence:
* record gaps are bounded (`record_gap_bounded`);
* the case-(II) degree bound runs along records with bounded gaps (no Baker:
  `natDegree_le_three_of_records`, Mignotte/Smyth plus the `3n − d` orbit);
* for `ℓ = 3` a non-record at `r + 1` forces `|N β| = 1` and `e₂(β^n) = 0` exactly at
  `n = C r / g` (`e2_zero_of_nonrecord`), i.e. `Tr β^(−n) = 0`;
* exact zeros of the ternary recurrence `Tr β^(−n)` along the orbit `n ↦ 3n − d` (which converges
  3-adically) are finite by Skolem's 3-adic argument (`finite_e2_zero_orbit`; no Baker: an exact
  zero is an algebraic condition).
So all large `k` are records (`eventually_record_shift`), which is `eventually_low`, and the rest
of `saitoTypeBLeastEv_holds` goes through with the degree bound from records in place of `hG`
(`saitoTypeB_shift`).
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature LeanFormalizations.Mills Filter
open LeanFormalizations.Mills.ShiftedMillsAll

/-- `m` is a record index: `p_m^(1/C m)` is the largest of the `p_k^(1/C k)`, `1 ≤ k ≤ m`. -/
def IsRecord (C : ℕ → ℕ) (ξ : ℝ) (m : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ m → root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C m⌋₊ (C m)

/-- Records of the least Mills number are infinite. -/
theorem frequently_record {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ)) :
    ∃ᶠ m in atTop, IsRecord C ξ m := by
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  rw [frequently_atTop]
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM⟩ := hcon
  obtain ⟨r, hrmem, hrmax⟩ := Finset.exists_max_image (Finset.Icc 1 (M + 1))
    (fun k => root (p k) (C k)) ⟨1, by simp⟩
  simp only [Finset.mem_Icc] at hrmem
  have hall : ∀ k, 1 ≤ k → root (p k) (C k) ≤ root (p r) (C r) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases le_or_gt k (M + 1) with hkM | hkM
      · exact hrmax k (by simp; omega)
      · have hnr := hM k (by omega)
        unfold IsRecord at hnr
        push_neg at hnr
        obtain ⟨k', hk'1, hk'k, hlt⟩ := hnr
        rcases Nat.lt_or_ge k' k with h | h
        · exact le_trans hlt.le (ih k' h hk'1)
        · have : k' = k := by omega
          subst this; exact absurd hlt (lt_irrefl _)
  have hroot : ∀ k, 1 ≤ k → root (ξ ^ C k) (C k) = ξ := fun k hk =>
    Real.pow_rpow_inv_natCast hξ0.le (by have := hCge k hk; omega)
  set ζ := root (p r) (C r) with hζ
  have hCr : 0 < C r := hCge r hrmem.1
  have hpr : (2 : ℝ) ≤ p r := by exact_mod_cast (hξS.2 r hrmem.1).two_le
  have hζ0 : 0 ≤ ζ := by rw [hζ, root]; positivity
  have hζξ : ζ ≤ ξ := by
    rw [hζ, ← hroot r hrmem.1, root, root]
    exact Real.rpow_le_rpow (by positivity) (Nat.floor_le (by positivity)) (by positivity)
  have hζpow : ∀ k, 1 ≤ k → (p k : ℝ) ≤ ζ ^ C k := by
    intro k hk
    have hCk := hCge k hk
    have := pow_le_pow_left₀ (by rw [root]; positivity) (hall k hk) (C k)
    rwa [root_pow (Nat.cast_nonneg _) hCk] at this
  have hζ1 : 1 < ζ := by
    by_contra h
    push_neg at h
    have := hζpow r hrmem.1
    have : ζ ^ C r ≤ 1 := pow_le_one₀ hζ0 h
    linarith
  have hζS : ζ ∈ millsSet C := by
    refine ⟨hζ1, fun k hk => ?_⟩
    have hfl : ⌊ζ ^ C k⌋₊ = p k := by
      rw [Nat.floor_eq_iff (by positivity)]
      exact ⟨hζpow k hk, lt_of_le_of_lt (pow_le_pow_left₀ hζ0 hζξ _) (Nat.lt_floor_add_one _)⟩
    rw [hfl]; exact hξS.2 k hk
  have hξζ : ξ ≤ ζ := hξ.2 hζS
  have heq : ξ = ζ := le_antisymm hξζ hζξ
  apply hnot r hrmem.1 (p r : ℤ)
  rw [heq, hζ, root_pow (Nat.cast_nonneg _) hCr]
  simp

/-- **Saito Lemma 5.2 at records** (no lower-chain hypothesis): at every large record the BHP
window holds. -/
theorem window_at_record (hB : BakerHarmanPintz2001) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) :
    ∃ k₀, ∀ m ≥ k₀, IsRecord C ξ m → (⌊ξ ^ C (m + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C m⌋₊ : ℝ) ^ ratio C m + (⌊ξ ^ C m⌋₊ : ℝ) ^ (21 / 40 * ratio C m) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hX⟩ := bhp_step hB
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  set k₁' := max K₀ 1 with hk₁'
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop (X : ℝ))
  obtain ⟨m, hm, hrec, hviol⟩ := hcon (max M1 (k₁' + 1))
  have hmM1 : M1 ≤ m := by omega
  have hmk : k₁' + 1 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := by omega
  -- the chain
  have hratio : ∀ k ≥ K₀, 1 ≤ k → (29 : ℝ) / 10 ≤ ratio C k := by
    intro k hk hk1
    have hCk : (0 : ℝ) < C k := by exact_mod_cast hCge k hk1
    rw [ratio, le_div_iff₀ hCk]; exact hEv k hk
  have hX' : ∀ q k : ℕ, ∃ q' : ℕ, X ≤ q → K₀ ≤ k → 1 ≤ k → (q'.Prime ∧
      (q : ℝ) ^ ratio C k ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ ratio C k + (q : ℝ) ^ (21 / 40 * ratio C k) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ ratio C k) := by
    intro q k
    by_cases h : X ≤ q ∧ K₀ ≤ k ∧ 1 ≤ k
    · obtain ⟨q', hq'⟩ := hX q h.1 (ratio C k) (hratio k h.2.1 h.2.2)
      exact ⟨q', fun _ _ _ => hq'⟩
    · exact ⟨0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose nxt hnxt using hX'
  let r : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (p m) (fun n r => nxt r (m + n)) n
  have hr0 : r 0 = p m := rfl
  have hrs : ∀ n, r (n + 1) = nxt (r n) (m + n) := fun n => rfl
  have hpmX : X ≤ p m := by exact_mod_cast hM1 m hmM1
  have hrX : ∀ n, X ≤ r n ∧ (r n).Prime := by
    intro n
    induction n with
    | zero => exact ⟨hpmX, hξS.2 m hm1⟩
    | succ n ih =>
      obtain ⟨hpr, hlo, -, -⟩ := hnxt (r n) (m + n) ih.1 (by omega) (by omega)
      refine ⟨?_, by rw [hrs]; exact hpr⟩
      rw [hrs]
      have hq1 : (1 : ℝ) ≤ (Nat.cast (r n) : ℝ) := by exact_mod_cast ih.2.one_lt.le
      have : ((r n : ℕ) : ℝ) ≤ ((r n : ℕ) : ℝ) ^ ratio C (m + n) := by
        calc ((r n : ℕ) : ℝ) = ((r n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1
              (by linarith [hratio (m + n) (by omega) (by omega)])
      have : ((r n : ℕ) : ℝ) ≤ nxt (r n) (m + n) := le_trans this hlo
      exact le_trans ih.1 (by exact_mod_cast this)
  set q : ℕ → ℕ := fun j => r (j - m) with hq
  have hqs : ∀ j ≥ m, q (j + 1) = nxt (q j) j := by
    intro j hj
    simp only [hq, show j + 1 - m = (j - m) + 1 by omega, hrs, show m + (j - m) = j by omega]
  have hstep : ∀ j ≥ m, ((q j : ℕ) : ℝ) ^ ratio C j ≤ ((q (j + 1) : ℕ) : ℝ) ∧
      ((q (j + 1) : ℕ) : ℝ) ≤ ((q j : ℕ) : ℝ) ^ ratio C j + ((q j : ℕ) : ℝ) ^ (21 / 40 * ratio C j) ∧
      ((q (j + 1) : ℕ) : ℝ) + 1 < (((q j : ℕ) : ℝ) + 1) ^ ratio C j := by
    intro j hj
    rw [hqs j hj]
    obtain ⟨-, a, b, c⟩ := hnxt (q j) j (hrX (j - m)).1 (by omega) (by omega)
    exact ⟨a, b, c⟩
  have hCpos : ∀ k ≥ m, 0 < C k := fun k hk => hCge k (by omega)
  have hrat_eq : ∀ k ≥ m, ratio C k = ((C (k + 1) : ℕ) : ℝ) / (C k : ℕ) := fun k _ => rfl
  obtain ⟨ζ, hζ0, hζfl, hζU⟩ := exists_of_nested (q := q) (k₀ := m) hCpos
    (by simp only [hq, Nat.sub_self, hr0]; exact (hξS.2 m hm1).one_lt.le)
    (fun j hj => root_le_root (Nat.cast_nonneg _) (hCpos j hj) (hCpos (j + 1) (by omega))
      (hstep j hj).1)
    (fun j hj => root_lt_root' (by positivity) (by positivity) (hCpos (j + 1) (by omega))
      (hCpos j hj) (hstep j hj).2.2)
  have hqm : q m = p m := by simp [hq, hr0]
  -- `ζ < ξ`
  have hq1lt : q (m + 1) + 1 ≤ p (m + 1) := by
    have h := (hstep m le_rfl).2.1
    rw [hqm] at h
    have : ((q (m + 1) : ℕ) : ℝ) < p (m + 1) := lt_of_le_of_lt h (hviol)
    exact_mod_cast this
  have hζξ : ζ < ξ := by
    have hU := hζU (m + 1) (by omega)
    have h2' : root (((q (m + 1) : ℕ) : ℝ) + 1) (C (m + 1)) ≤ root (ξ ^ C (m + 1)) (C (m + 1)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have : ((q (m + 1) + 1 : ℕ) : ℝ) ≤ p (m + 1) := by exact_mod_cast hq1lt
      push_cast at this
      exact le_trans this (Nat.floor_le (by positivity))
    have h3' : root (ξ ^ C (m + 1)) (C (m + 1)) = ξ :=
      Real.pow_rpow_inv_natCast hξ0.le (hCpos (m + 1) (by omega)).ne'
    linarith
  -- `ζ^(C m) ≥ p m`
  have hζm : (p m : ℝ) ≤ ζ ^ C m := by
    have := hζfl m le_rfl
    rw [hqm] at this
    rw [← this]; exact Nat.floor_le (by positivity)
  have hpm2 : (2 : ℝ) ≤ p m := by exact_mod_cast (hξS.2 m hm1).two_le
  have hζ1 : 1 < ζ := by
    by_contra h
    push_neg at h
    have : ζ ^ C m ≤ 1 := pow_le_one₀ hζ0.le h
    linarith
  -- closeness: `C m (ξ − ζ) < 1`
  have hclose : (C m : ℝ) * (ξ - ζ) < 1 := by
    have hge := pow_sub_pow_ge hζ0 hζξ.le (C m)
    have hlt : ξ ^ C m < (p m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpow1 : (1 : ℝ) ≤ ζ ^ (C m - 1) := one_le_pow₀ hζ1.le
    have hd : 0 ≤ ξ - ζ := by linarith
    have hCm0 : (0 : ℝ) ≤ C m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hCm0 hd)]
  -- the floors of `ζ`
  have hfloor : ∀ k ≥ 1, ⌊ζ ^ C k⌋₊ = p k ∨ ⌊ζ ^ C k⌋₊ = q k ∧ m ≤ k := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · left
      rw [Nat.floor_eq_iff (by positivity)]
      refine ⟨?_, lt_of_lt_of_le (pow_lt_pow_left₀ hζξ hζ0.le (by have := hCge k hk; omega))
        (Nat.lt_floor_add_one _).le⟩
      have h1' : root (p k) (C k) ≤ root (p m) (C m) := hrec k hk hkm.le
      have h2' : root (p m) (C m) ≤ ζ := by
        have := Real.rpow_le_rpow (by positivity) hζm
          (inv_nonneg.2 (Nat.cast_nonneg (C m)))
        rwa [Real.pow_rpow_inv_natCast hζ0.le (hCpos m le_rfl).ne'] at this
      have h3' := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_trans h1' h2')
        (C k)
      rwa [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by have := hCge k hk; omega)]
        at h3'
    · right
      exact ⟨hζfl k hkm, hkm⟩
  have hζS : ζ ∈ millsSet C := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rcases hfloor k hk with h | ⟨h, hkm⟩
    · rw [h]; exact hξS.2 k hk
    · rw [h]; exact (hrX (k - m)).2
  exact absurd (hξ.2 hζS) (not_le.2 hζξ)

/-- Degree bound from a lower bound `c R^n ≤ |S(n)|` holding together with decay
`|S(n)| ≤ K β^(−μn)` infinitely often (the Baker-free replacement of `pisot_degree_bound`). -/
theorem card_mul_le_of_lower {β : ℝ} (hβ : IsPisot β) {μ K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (h : ∃ᶠ n : ℕ in atTop, c * conjMax β ^ n ≤ ‖conjPowSum β n‖ ∧
      ‖conjPowSum β n‖ ≤ K * (β ^ (-(μ * n)) : ℝ)) :
    ((Multiset.card (otherConj β) : ℝ)) * μ ≤ 1 := by
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  set ρ : ℝ := β ^ (-μ) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hβ0 _
  have hmax : conjMax β ≤ ρ := by
    refine le_of_pow_le_const_mul_pow 0 (conjMax_nonneg β) hρ0 (div_pos hK hc) ?_
    refine h.mono ?_
    rintro n ⟨hlo, hhi⟩
    have hrho : (β ^ (-(μ * n)) : ℝ) = ρ ^ n := by
      rw [hρdef, ← Real.rpow_natCast (β ^ (-μ)) n, ← Real.rpow_mul hβ0.le]
      ring_nf
    rw [hrho] at hhi
    rw [pow_zero, mul_one, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  set L : ℕ := Multiset.card (otherConj β) with hL
  have hprod : ((otherConj β).map (‖·‖)).prod ≤ ρ ^ L :=
    le_trans (conjMax_pow_card_le β) (pow_le_pow_left₀ (conjMax_nonneg β) hmax L)
  have hone := pisot_one_le_prod_norm hβ
  have hchain : (1 : ℝ) ≤ β * ρ ^ L :=
    le_trans hone (mul_le_mul_of_nonneg_left hprod hβ0.le)
  have hrewrite : β * ρ ^ L = β ^ (1 - μ * L) := by
    have h1 : (ρ : ℝ) ^ L = β ^ (-(μ * L)) := by
      rw [hρdef, ← Real.rpow_natCast (β ^ (-μ)) L, ← Real.rpow_mul hβ0.le]
      ring_nf
    rw [h1, Real.rpow_sub hβ0, Real.rpow_one, Real.rpow_neg hβ0.le]
    field_simp
  rw [hrewrite] at hchain
  by_contra hcon
  push_neg at hcon
  have : β ^ (1 - μ * L) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg hβ1
    linarith
  linarith

/-- **Case-(II) degree bound along the orbit `n ↦ 3n − d`** (no Baker). -/
theorem card_mul_le_of_orbit {β : ℝ} (hβ : IsPisot β) (hdeg : 2 ≤ (minpoly ℚ β).natDegree)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {d : ℤ} (hd : d ≠ 0)
    (hrec : ∀ k, (n (k + 1) : ℤ) = 3 * n k - d) {μ K : ℝ} (hK : 0 < K)
    (hdec : ∀ᶠ k in atTop, ‖conjPowSum β (n k)‖ ≤ K * (β ^ (-(μ * n k)) : ℝ)) :
    ((Multiset.card (otherConj β) : ℝ)) * μ ≤ 1 := by
  obtain ⟨c, hc, hfr⟩ := conjPowSum_lower_of_recurrence hβ hdeg hn hd hrec
  exact card_mul_le_of_lower hβ hK hc (hn.frequently (hfr.and_eventually hdec))

/-- Saito Lemma 6.1 without the degree bound (no `Dubickas2022PisotGap`). -/
theorem exists_pisot_of_decay_subseq' (hD : Dubickas2022)
    {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {s : ℕ → ℕ} (hs : StrictMono s)
    (hs0 : 0 < s 0) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ k in atTop, |α ^ s k - (round (α ^ s k) : ℝ)| ≤ K * α ^ (-(μ * s k)))
    (hnot : ∀ k, ∀ t : ℤ, α ^ s k ≠ (t : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ IsPisot (α ^ g) ∧ (∀ᶠ k in atTop, g ∣ s k) ∧
      2 ≤ (minpoly ℚ (α ^ g)).natDegree := by
  classical
  have hα0 : (0 : ℝ) < α := by linarith
  have hspos : ∀ k, 0 < s k := fun k => lt_of_lt_of_le hs0 (hs.monotone (Nat.zero_le k))
  have hex : ∃ g, 1 ≤ g ∧ IsPisot (α ^ g) := by
    obtain ⟨m, hm⟩ := exists_pisot_of_decay_dub hD halg hα hs hs0 hμ hK hdecay
    exact ⟨s m, hspos m, hm⟩
  set g := Nat.find hex with hg
  obtain ⟨hg1, hpis⟩ := Nat.find_spec hex
  have hgmin : ∀ g' < g, ¬ (1 ≤ g' ∧ IsPisot (α ^ g')) := fun g' h => Nat.find_min hex h
  -- `g ∣ s k` eventually
  have hdiv : ∀ᶠ k in atTop, g ∣ s k := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop (hcon.and_eventually hdecay)
    have hs' : StrictMono (s ∘ φ) := hs.comp hφ
    obtain ⟨r, hr⟩ := exists_pisot_of_decay_dub hD halg hα hs' (hspos _) hμ hK
      (Eventually.of_forall fun n => (hφP n).2)
    have hgcd := isPisot_pow_gcd hα (by omega) (hspos _) hpis hr
    have hle : Nat.gcd g (s (φ r)) ≤ g := Nat.gcd_le_left _ (by omega)
    have hne : Nat.gcd g (s (φ r)) ≠ g := by
      intro h
      exact (hφP r).1 (h ▸ Nat.gcd_dvd_right g (s (φ r)))
    exact hgmin _ (lt_of_le_of_ne hle hne) ⟨Nat.gcd_pos_of_pos_left _ (by omega), hgcd⟩
  set β := α ^ g with hβ
  have hpow : ∀ k, g ∣ s k → β ^ (s k / g) = α ^ s k := by
    intro k hk; rw [hβ, ← pow_mul, Nat.mul_div_cancel' hk]
  obtain ⟨k₂, hk₂⟩ := eventually_atTop.1 hdiv
  have hnd : 2 ≤ (minpoly ℚ β).natDegree := by
    refine pisot_two_le_natDegree hpis fun t ht => ?_
    have h := hpow k₂ (hk₂ k₂ le_rfl)
    rw [ht] at h
    exact hnot k₂ (t ^ (s k₂ / g)) (by rw [← h]; push_cast; ring)
  exact ⟨g, hg1, hpis, hdiv, hnd⟩

/-- **All large indices are records** for the E+ exponents, if `ξ` is algebraic.  The crux of
lap 2; sub-nodes in the module docstring. -/
theorem eventually_record_shift (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m := by
  sorry

/-- For a Pisot `β`, eventually `|S(n)| = |β^n − round(β^n)|`. -/
theorem norm_conjPowSum_eq_round {β : ℝ} (hβ : IsPisot β) :
    ∀ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ = |β ^ n - (round (β ^ n) : ℝ)| := by
  have hmax := conjMax_lt_one hβ
  have hmax0 := conjMax_nonneg β
  have htend : Tendsto
      (fun n : ℕ => (Multiset.card (otherConj β) : ℝ) * conjMax β ^ n) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hmax0 hmax
    simpa using this.const_mul (Multiset.card (otherConj β) : ℝ)
  filter_upwards [htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with n hn
  obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ n
  have hcps : conjPowSum β n = ((((t : ℝ) - β ^ n : ℝ)) : ℂ) := by
    push_cast
    push_cast at ht
    linear_combination ht
  have hnorm : ‖conjPowSum β n‖ = |β ^ n - (t : ℝ)| := by
    rw [hcps, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hhalf : |β ^ n - (t : ℝ)| < 1 / 2 := by
    rw [← hnorm]
    exact lt_of_le_of_lt (norm_conjPowSum_le β n) hn
  have hround : round (β ^ n) = t := by
    have hz : round (β ^ n - (t : ℝ)) = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨(abs_lt.1 hhalf).1.le, (abs_lt.1 hhalf).2⟩
    have := round_add_intCast (β ^ n - (t : ℝ)) t
    rw [hz, sub_add_cancel] at this
    simpa using this
  rw [hnorm, hround]

/-- The degree bound for the E+ exponents: decay of `‖ξ^(C k)‖` at rate `151/400` along all
large `k`, with `ξ^g` Pisot and `g ∣ C k`, gives `(ℓ − 1)·151/400 ≤ 1` (no Baker). -/
theorem card_mul_le_shift {e : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + e) (he : e ≠ 0)
    {ξ : ℝ} (hξ1 : 1 < ξ) {g : ℕ} (hg1 : 1 ≤ g) (hpis : IsPisot (ξ ^ g))
    (hdeg2 : 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree) {sq : ℕ → ℕ} {k₃ : ℕ} (hk₃ : 1 ≤ k₃)
    (hsq : ∀ k, sq k = shiftC j e (k + k₃)) {k₄ : ℕ} (hk₄ : ∀ k ≥ k₄, g ∣ sq k)
    (hdecay : ∀ᶠ k in atTop, |ξ ^ sq k - (round (ξ ^ sq k) : ℝ)| ≤
      4 * ξ ^ (-((151 / 400 : ℝ) * sq k))) :
    ((Multiset.card (otherConj (ξ ^ g)) : ℝ)) * (151 / 400 : ℝ) ≤ 1 := by
  have hξ0 : 0 < ξ := by linarith
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set n : ℕ → ℕ := fun k => sq (k + k₄) / g with hn
  have hgn : ∀ k, g * n k = sq (k + k₄) := fun k => Nat.mul_div_cancel' (hk₄ _ (by omega))
  have hcast : ∀ k, ((g : ℤ) * n k) = 3 ^ (k + k₄ + k₃ + j) + e := by
    intro k
    have := hgn k
    rw [hsq] at this
    have h := shiftC_cast hj1 (k := k + k₄ + k₃) (by omega)
    rw [← h]; exact_mod_cast this
  have hstep : ∀ k, (g : ℤ) * (3 * n k - n (k + 1)) = 2 * e := by
    intro k
    have a := hcast k
    have b := hcast (k + 1)
    rw [show k + 1 + k₄ + k₃ + j = (k + k₄ + k₃ + j) + 1 by ring, pow_succ] at b
    linear_combination 3 * a - b
  set d : ℤ := 3 * n 0 - n 1 with hd
  have hrec : ∀ k, (n (k + 1) : ℤ) = 3 * n k - d := by
    intro k
    have h := hstep k
    rw [← hstep 0] at h
    have := mul_left_cancel₀ hg0 h
    linarith
  have hd0 : d ≠ 0 := by
    intro h0
    have := hstep 0
    rw [← hd, h0, mul_zero] at this
    exact he (by linarith)
  have hnt : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * g, fun a ha => ?_⟩
    have h1 := hcast a
    have h3 : (a : ℤ) + 1 ≤ 3 ^ (a + k₄ + k₃ + j) + e := by
      have hp : (3 : ℤ) ^ (a + k₄ + k₃ + j) = 3 ^ (j + 1) * 3 ^ (a + k₄ + k₃ - 1) := by
        rw [← pow_add]; congr 1; omega
      have hq : (a : ℤ) + 1 ≤ 3 ^ (a + k₄ + k₃ - 1) := by
        have : a + 1 ≤ 3 ^ (a + k₄ + k₃ - 1) := by
          calc a + 1 ≤ 3 ^ a := Nat.lt_pow_self (by norm_num)
            _ ≤ 3 ^ (a + k₄ + k₃ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this
      have h31 : (1 : ℤ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have : (b : ℤ) * g < (g : ℤ) * n a + 1 := by
      have : (b * g : ℕ) ≤ a := ha
      push_cast at this
      linarith
    have hgpos : (0 : ℤ) < g := by exact_mod_cast (show 0 < g by omega)
    have : (b : ℤ) ≤ n a := by
      by_contra hlt
      push_neg at hlt
      have : (n a : ℤ) + 1 ≤ b := hlt
      nlinarith
    exact_mod_cast this
  have hdec : ∀ᶠ k in atTop, ‖conjPowSum (ξ ^ g) (n k)‖ ≤
      4 * ((ξ ^ g) ^ (-((151 / 400 : ℝ) * n k)) : ℝ) := by
    have h1 := hnt.eventually (norm_conjPowSum_eq_round hpis)
    have h2 := (tendsto_add_atTop_nat k₄).eventually hdecay
    filter_upwards [h1, h2] with k hk1 hk2
    have hpow : (ξ ^ g) ^ n k = ξ ^ sq (k + k₄) := by rw [← pow_mul, hgn]
    have hrp : ((ξ ^ g) ^ (-((151 / 400 : ℝ) * n k)) : ℝ) =
        ξ ^ (-((151 / 400 : ℝ) * sq (k + k₄))) := by
      rw [← Real.rpow_natCast ξ g, ← Real.rpow_mul hξ0.le, ← hgn]
      push_cast; ring_nf
    rw [hk1, hpow, hrp]
    exact hk2
  exact card_mul_le_of_orbit hpis hdeg2 hnt hd0 hrec (by norm_num) hdec

/-- **Saito's Type B for the E+ exponents, from BHP and Dubickas 2022 Lemma 6 only.** -/
theorem saitoTypeB_shift (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {e : ℤ} {j : ℕ} (he : e ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + e) (hj2 : e ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j e k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ ∨
      ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ (minpoly ℚ (ξ ^ g)).natDegree = 3 ∧
        ∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * shiftC j e k ≤ shiftC j e (k + 1) →
          g ∣ shiftC j e k ∧ powTrace (ξ ^ g) (shiftC j e k / g) = (⌊ξ ^ shiftC j e k⌋₊ : ℂ) := by
  by_cases htr : Transcendental ℚ ξ
  · exact Or.inl htr
  right
  have halg : IsAlgebraic ℚ ξ := not_not.1 htr
  set C := shiftC j e with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  set K₀ := 19 * e.natAbs + 1 with hK₀def
  have hK₀ : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1) := fun k hk =>
    shiftC_ratio hj1 (by omega) (by omega)
  have hξS : ξ ∈ millsSet C := hξ.1
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  have hnot := not_intCast_pow h1 h2 h5 hξS
  obtain ⟨Kr, hKr⟩ := eventually_record_shift hB hD he hj1 hj2 hξ halg
  have hlow : ∀ k ≥ Kr + 1, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1)) :=
    fun k hk => hKr (k + 1) (by omega) k (by omega) (by omega)
  obtain ⟨k₀, hII⟩ := window_of_least hB h1 h2 hK₀ hξ hnot hlow
  obtain ⟨k₂, hfr⟩ := eventually_fract_le h1 h2 hK₀ hξS hII
  have hCge := C_ge_one h1 h2
  -- the decay along `s k = C (k + k₃)`
  set k₃ := k₂ + 1 with hk₃
  set s : ℕ → ℕ := fun k => C (k + k₃) with hs
  have hsmono : StrictMono s := by
    intro a b hab
    exact C_strictMonoOn h1 h2 (by omega) (by omega)
  have hs0 : 0 < s 0 := hCge _ (by omega)
  have hflo := floor_tendsto h1 h2 hξ1
  have hdecay : ∀ᶠ k in atTop, |ξ ^ s k - (round (ξ ^ s k) : ℝ)| ≤
      4 * ξ ^ (-((151 / 400 : ℝ) * s k)) := by
    filter_upwards [eventually_ge_atTop 0] with k _
    set x := ξ ^ s k with hx
    have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
    have hfl1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      have := Nat.floor_pos.2 hx1; exact_mod_cast this
    have hxfl : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x; linarith
    have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
      have := round_le x ⌊x⌋
      rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
    have hf := hfr (k + k₃) (by omega)
    -- `⌊x⌋^(−t) ≤ 2^t x^(−t) ≤ 2 x^(−t)`
    have hpow : (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ 2 * x ^ (-(151 / 400 : ℝ)) := by
      have hxpos : 0 < x := by linarith
      have h1' : (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ (x / 2) ^ (-(151 / 400 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2' : (x / 2) ^ (-(151 / 400 : ℝ)) = 2 ^ (151 / 400 : ℝ) * x ^ (-(151 / 400 : ℝ)) := by
        rw [Real.div_rpow hxpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
      have h3' : (2 : ℝ) ^ (151 / 400 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (151 / 400 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      rw [h2'] at h1'
      have : 0 ≤ x ^ (-(151 / 400 : ℝ)) := by positivity
      nlinarith
    have hxe : x ^ (-(151 / 400 : ℝ)) = ξ ^ (-((151 / 400 : ℝ) * s k)) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
    calc |x - (round x : ℝ)| ≤ Int.fract x := hround
      _ ≤ 2 * (⌊x⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) := hf
      _ ≤ 2 * (2 * x ^ (-(151 / 400 : ℝ))) := by linarith
      _ = 4 * ξ ^ (-((151 / 400 : ℝ) * s k)) := by rw [hxe]; ring
  have hnot' : ∀ k, ∀ t : ℤ, ξ ^ s k ≠ (t : ℝ) := fun k t => hnot _ (by omega) t
  obtain ⟨g, hg1, hpis, hgdiv, hdeg2⟩ :=
    exists_pisot_of_decay_subseq' hD halg hξ1 hsmono hs0 (by norm_num) (by norm_num)
      hdecay hnot'
  obtain ⟨k₄, hk₄⟩ := eventually_atTop.1 hgdiv
  have hcard : ((Multiset.card (otherConj (ξ ^ g)) : ℝ)) * (151 / 400 : ℝ) ≤ 1 :=
    card_mul_le_shift hj1 he hξ1 hg1 hpis hdeg2 (k₃ := k₃) (by omega) (fun k => rfl) hk₄ hdecay
  -- `g ∣ C k` for `k ≥ k₅`
  set k₅ := k₄ + k₃ with hk₅
  have hgC : ∀ k ≥ k₅, g ∣ C k := by
    intro k hk
    have := hk₄ (k - k₃) (by omega)
    simpa [hs, show k - k₃ + k₃ = k by omega] using this
  have hpowg : ∀ k ≥ k₅, (ξ ^ g) ^ (C k / g) = ξ ^ C k := by
    intro k hk
    rw [← pow_mul, Nat.mul_div_cancel' (hgC k hk)]
  -- eventually the fractional part is `< 1/2`
  obtain ⟨k₆, hk₆⟩ := eventually_atTop.1
    (hflo.eventually_ge_atTop ((16 : ℝ) ^ ((400 : ℝ) / 151)))
  have hhalf : ∀ k ≥ max k₆ k₂, Int.fract (ξ ^ C k) < 1 / 2 := by
    intro k hk
    have hf := hfr k (le_trans (le_max_right _ _) hk)
    have hbig := hk₆ k (le_trans (le_max_left _ _) hk)
    have hpos : (0 : ℝ) < (16 : ℝ) ^ ((400 : ℝ) / 151) := by positivity
    have : (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ)) ≤ 1 / 16 := by
      calc (⌊ξ ^ C k⌋₊ : ℝ) ^ (-(151 / 400 : ℝ))
          ≤ ((16 : ℝ) ^ ((400 : ℝ) / 151)) ^ (-(151 / 400 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hbig (by norm_num)
        _ = 1 / 16 := by
            rw [← Real.rpow_mul (by norm_num)]
            norm_num
    linarith
  -- the degree is `3`
  have hβ := hpis
  have hcardle : Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
    by_contra hc
    push_neg at hc
    have : (3 : ℝ) ≤ (Multiset.card (otherConj (ξ ^ g)) : ℝ) := by exact_mod_cast hc
    nlinarith
  have hcard1 := card_otherConj_add_one (hpis.2.1.tower_top)
  have hdeg3 : (minpoly ℚ (ξ ^ g)).natDegree = 3 := by
    rcases (show (minpoly ℚ (ξ ^ g)).natDegree = 2 ∨ (minpoly ℚ (ξ ^ g)).natDegree = 3 by
      omega) with h | h
    · exfalso
      refine not_natDegree_two hpis h (n := fun k => C k / g) (K := max (max k₅ k₆) (k₂ + 1))
        ?_ ?_ ?_ ?_
      · intro k hk
        show (⌊(ξ ^ g) ^ (C k / g)⌋₊).Prime
        rw [hpowg k (by omega)]
        exact hξS.2 k (by omega)
      · intro k hk
        show Int.fract ((ξ ^ g) ^ (C k / g)) < 1 / 2
        rw [hpowg k (by omega)]
        exact hhalf k (by omega)
      · intro M
        obtain ⟨b, hb, hdvd, -⟩ := h5 (M + k₅ + 1) (by omega)
        refine ⟨M + k₅ + 1, by omega, b, hb, ?_, ?_⟩
        · obtain ⟨e, he⟩ := hdvd
          refine ⟨e, ?_⟩
          have hg := hgC (M + k₅ + 1) (by omega)
          obtain ⟨u, hu⟩ := hg
          rw [he, hu, Nat.mul_div_cancel_left _ (by omega), mul_assoc,
            Nat.mul_div_cancel_left _ (by omega)]
        · have hlt := C_strictMonoOn h1 h2 (a := M + k₅ + 1) (b := b) (by omega) hb
          obtain ⟨u, hu⟩ := hgC (M + k₅ + 1) (by omega)
          obtain ⟨v, hv⟩ := hgC b (by omega)
          rw [hu, hv] at hlt ⊢
          rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
          exact Nat.lt_of_mul_lt_mul_left hlt
      · -- `C k / g → ∞`
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨max k₅ (b * g + 1), fun a ha => ?_⟩
        have hCa : a ≤ C a := le_C h1 h2 a (by omega)
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
    · exact h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (powTrace_eq_floor hpis)
  refine ⟨g, hg1, hpis, hdeg3, max (max k₅ k₆) (max k₂ (N₀ * g + 1)), fun k hk _ => ⟨hgC k
    (by omega), ?_⟩⟩
  have hN : N₀ ≤ C k / g := by
    have := le_C h1 h2 k (by omega)
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have := hN₀ (C k / g) hN (by rw [hpowg k (by omega)]; exact hhalf k (by omega))
  rw [this, hpowg k (by omega)]


end LeanFormalizations.Mills.SaitoTypeB
