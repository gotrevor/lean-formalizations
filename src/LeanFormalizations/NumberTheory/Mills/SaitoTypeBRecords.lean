/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBNoGap
import LeanFormalizations.NumberTheory.Mills.E2Skolem

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

/-- Decay at large records: `|ξ^(C m) − round| ≤ 4 ξ^(−(151/400) C m)`. -/
theorem record_decay (hB : BakerHarmanPintz2001) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) :
    ∃ k₀, ∀ m ≥ k₀, IsRecord C ξ m →
      |ξ ^ C m - (round (ξ ^ C m) : ℝ)| ≤ 4 * ξ ^ (-((151 / 400 : ℝ) * C m)) := by
  obtain ⟨k₀, hk₀⟩ := window_at_record hB h1 h2 hEv hξ
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  refine ⟨max k₀ (max K₀ 1), fun m hm hrec => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hCk : 0 < C m := C_ge_one h1 h2 m hm1
  have hc : (29 : ℝ) / 10 ≤ ratio C m := by
    have hCk' : (0 : ℝ) < C m := by exact_mod_cast hCk
    rw [ratio, le_div_iff₀ hCk']; exact hEv m (by omega)
  set x := ξ ^ C m with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ ratio C m < (⌊ξ ^ C (m + 1)⌋₊ : ℝ) + 1 := by
    rw [hx, pow_ratio hξ0 hCk]; exact Nat.lt_floor_add_one _
  have hw := fract_le_of_window (θ := 21 / 40) hx1 (by linarith) (by norm_num) (by norm_num) hxc
    (hk₀ m (by omega) hrec)
  set p : ℝ := (⌊x⌋₊ : ℝ) with hp
  have hp1 : 1 ≤ p := by have := Nat.floor_pos.2 hx1; rw [hp]; exact_mod_cast this
  have hA : p ^ (151 / 400 : ℝ) ≤ p ^ ((1 - 21 / 40) * ratio C m - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hA0 : 0 < p ^ (151 / 400 : ℝ) := by positivity
  have hf : Int.fract x ≤ 2 * p ^ (-(151 / 400 : ℝ)) := by
    calc Int.fract x ≤ 2 / (ratio C m * p ^ ((1 - 21 / 40) * ratio C m - 1)) := hw
      _ ≤ 2 / p ^ (151 / 400 : ℝ) := by
          apply div_le_div_of_nonneg_left (by norm_num) hA0
          nlinarith
      _ = 2 * p ^ (-(151 / 400 : ℝ)) := by
          rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
  have hxfl : x ≤ 2 * p := by
    have := Nat.lt_floor_add_one x; rw [hp]; linarith
  have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
    have := round_le x ⌊x⌋
    rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
  have hpow : p ^ (-(151 / 400 : ℝ)) ≤ 2 * x ^ (-(151 / 400 : ℝ)) := by
    have hxpos : 0 < x := by linarith
    have h1' : p ^ (-(151 / 400 : ℝ)) ≤ (x / 2) ^ (-(151 / 400 : ℝ)) :=
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
  have hxe : x ^ (-(151 / 400 : ℝ)) = ξ ^ (-((151 / 400 : ℝ) * C m)) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
  calc |x - (round x : ℝ)| ≤ Int.fract x := hround
    _ ≤ 2 * p ^ (-(151 / 400 : ℝ)) := hf
    _ ≤ 2 * (2 * x ^ (-(151 / 400 : ℝ))) := by linarith
    _ = 4 * ξ ^ (-((151 / 400 : ℝ) * C m)) := by rw [hxe]; ring

/-- **Step 1 (records give a Pisot power).**  Decay at records (`window_at_record` + Saito (5.17))
and Dubickas 2022 Lemma 6 along the records give `ξ^g` Pisot with `g ∣ C m` at large records. -/
theorem records_pisot (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree ∧
      ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m := by
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  have hK₀ : ∀ k ≥ 19 * s.natAbs + 1, (29 : ℝ) / 10 * C k ≤ C (k + 1) := fun k hk =>
    shiftC_ratio hj1 (by omega) (by omega)
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hnot := not_intCast_pow h1 h2 h5 hξS
  have hCge := C_ge_one h1 h2
  obtain ⟨k₀, hk₀⟩ := record_decay hB h1 h2 hK₀ hξ
  -- decay along any infinite family of large records gives a Pisot power dividing it
  have key : ∀ P : ℕ → Prop, (∃ᶠ m in atTop, P m) → (∀ m, P m → k₀ + 1 ≤ m ∧ IsRecord C ξ m) →
      ∃ g', 1 ≤ g' ∧ IsPisot (ξ ^ g') ∧ ∃ m, P m ∧ g' ∣ C m := by
    intro P hP hPr
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hP
    have hφ1 : ∀ n, 1 ≤ φ n := fun n => by have := (hPr _ (hφP n)).1; omega
    have hsm : StrictMono (fun n => C (φ n)) := fun a b hab =>
      C_strictMonoOn h1 h2 (hφ1 a) (hφ hab)
    obtain ⟨g', hg', hpis', hdiv', -⟩ := exists_pisot_of_decay_subseq' hD halg hξ1 hsm
      (hCge _ (hφ1 0)) (by norm_num) (by norm_num)
      (Eventually.of_forall fun n => hk₀ _ (by have := (hPr _ (hφP n)).1; omega)
        (hPr _ (hφP n)).2) (fun n t => hnot _ (hφ1 n) t)
    obtain ⟨n, hn⟩ := hdiv'.exists
    exact ⟨g', hg', hpis', φ n, hφP n, hn⟩
  have hfr : ∃ᶠ m in atTop, k₀ + 1 ≤ m ∧ IsRecord C ξ m :=
    (frequently_record h1 h2 hξ hnot).and_eventually (eventually_ge_atTop _) |>.mono
      fun m h => ⟨h.2, h.1⟩
  have hex : ∃ g, 1 ≤ g ∧ IsPisot (ξ ^ g) := by
    obtain ⟨g', hg', hp', -⟩ := key _ hfr (fun m h => h)
    exact ⟨g', hg', hp'⟩
  set g := Nat.find hex with hg
  obtain ⟨hg1, hpis⟩ := Nat.find_spec hex
  have hgmin : ∀ g' < g, ¬ (1 ≤ g' ∧ IsPisot (ξ ^ g')) := fun g' h => Nat.find_min hex h
  have hdiv : ∃ K, ∀ m ≥ K, IsRecord C ξ m → g ∣ C m := by
    by_contra hcon
    push_neg at hcon
    have hP : ∃ᶠ m in atTop, (k₀ + 1 ≤ m ∧ IsRecord C ξ m) ∧ ¬ g ∣ C m := by
      rw [frequently_atTop]
      intro a
      obtain ⟨m, hm, hr, hnd⟩ := hcon (max a (k₀ + 1))
      exact ⟨m, by omega, ⟨by omega, hr⟩, hnd⟩
    obtain ⟨g', hg', hp', m, ⟨⟨hmk, -⟩, hnd⟩, hgm⟩ := key _ hP (fun m h => h.1)
    have hgcd := isPisot_pow_gcd hξ1 (by omega) (by omega) hpis hp'
    have hle : Nat.gcd g g' ≤ g := Nat.gcd_le_left _ (by omega)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hgmin _ hlt ⟨Nat.gcd_pos_of_pos_left _ (by omega), hgcd⟩
    · exact hnd (dvd_trans (heq ▸ Nat.gcd_dvd_right g g') hgm)
  obtain ⟨K, hK⟩ := hdiv
  obtain ⟨m, hm⟩ := (hfr.and_eventually (eventually_ge_atTop K)).exists
  have hgm := hK m hm.2 hm.1.2
  refine ⟨g, hg1, hpis, ?_, K, hK⟩
  refine pisot_two_le_natDegree hpis fun t ht => ?_
  have h := (show (ξ ^ g) ^ (C m / g) = ξ ^ C m by rw [← pow_mul, Nat.mul_div_cancel' hgm])
  rw [ht] at h
  exact hnot m (by omega) (t ^ (C m / g)) (by rw [← h]; push_cast; ring)

open Polynomial in
/-- The norm of `β^n − t` as a resultant: a nonzero integer. -/
theorem one_le_norm_prod_pow_sub {β : ℝ} (hint : IsIntegral ℤ β) (n : ℕ) (t : ℤ)
    (hne : β ^ n ≠ (t : ℝ)) :
    1 ≤ ‖(((minpoly ℚ β).aroots ℂ).map (fun w => w ^ n - (t : ℂ))).prod‖ := by
  classical
  have hQ : IsIntegral ℚ β := hint.tower_top
  set f := minpoly ℤ β with hf
  have hfm : f.Monic := minpoly.monic hint
  set G : ℤ[X] := X ^ n - C t with hG
  have hGdeg : G.natDegree ≤ n := by
    rw [hG]
    refine (natDegree_sub_le _ _).trans ?_
    simp
  set φ := Int.castRingHom ℂ
  have hmapQ : (minpoly ℚ β).map (algebraMap ℚ ℂ) = f.map φ := by
    rw [hf, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, Polynomial.map_map]
    congr 1
  have hdeg : (f.map φ).natDegree = f.natDegree := hfm.natDegree_map φ
  have hres : resultant (f.map φ) (G.map φ) (f.map φ).natDegree n =
      φ (resultant f G f.natDegree n) := by
    rw [hdeg]; exact resultant_map_map f G f.natDegree n φ
  rw [resultant_eq_prod_eval (f.map φ) (G.map φ) n (natDegree_map_le.trans hGdeg)
    (IsAlgClosed.splits _), (hfm.map φ).leadingCoeff, one_pow, one_mul] at hres
  have hprod : (((minpoly ℚ β).aroots ℂ).map (fun w => w ^ n - (t : ℂ))).prod =
      ((resultant f G f.natDegree n : ℤ) : ℂ) := by
    rw [← eq_intCast φ (resultant f G f.natDegree n), ← hres, aroots_def, hmapQ]
    congr 1
    refine Multiset.map_congr rfl fun w _ => ?_
    simp [hG, φ]
  rw [hprod, Complex.norm_intCast]
  have hR : resultant f G f.natDegree n ≠ 0 := by
    intro h0
    have h0' : (((minpoly ℚ β).aroots ℂ).map (fun w => w ^ n - (t : ℂ))).prod = 0 := by
      rw [hprod, h0]; simp
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h0')
    rw [mem_aroots] at hz
    have hmin : minpoly ℚ z = minpoly ℚ β :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hQ) hz.2 (minpoly.monic hQ)).symm
    have hzr : aeval z (X ^ n - C (t : ℚ)) = 0 := by
      simp; linear_combination hz0
    have hdvd := minpoly.dvd ℚ z hzr
    rw [hmin] at hdvd
    obtain ⟨q, hq⟩ := hdvd
    have := congrArg (aeval β) hq
    rw [map_mul, minpoly.aeval, zero_mul] at this
    simp at this
    exact hne (by linarith)
  exact_mod_cast Int.one_le_abs hR

/-- **Norm lower bound**: for Pisot `β` and integer `t ≠ β^n`,
`|β^n − t| · (|t| + 1)^(ℓ−1) ≥ 1`. -/
theorem abs_pow_sub_mul_ge_one {β : ℝ} (hβ : IsPisot β) (n : ℕ) (t : ℤ)
    (hne : β ^ n ≠ (t : ℝ)) :
    1 ≤ |β ^ n - t| * (|(t : ℝ)| + 1) ^ Multiset.card (otherConj β) := by
  have hint := hβ.2.1
  have h := one_le_norm_prod_pow_sub hint n t hne
  have hsplit : (minpoly ℚ β).aroots ℂ = (β : ℂ) ::ₘ otherConj β :=
    (Multiset.cons_erase (beta_mem_aroots hint.tower_top)).symm
  rw [hsplit, Multiset.map_cons, Multiset.prod_cons, norm_mul] at h
  have h1 : ‖(β : ℂ) ^ n - (t : ℂ)‖ = |β ^ n - t| := by
    have e : (((β ^ n - t : ℝ)) : ℂ) = (β : ℂ) ^ n - (t : ℂ) := by push_cast; ring
    rw [← e, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((otherConj β).map (fun w => w ^ n - (t : ℂ))).prod‖ ≤
      (|(t : ℝ)| + 1) ^ Multiset.card (otherConj β) := by
    have hn : ∀ u : Multiset ℂ, ‖(u.map (fun w => w ^ n - (t : ℂ))).prod‖ =
        (u.map (fun w => ‖w ^ n - (t : ℂ)‖)).prod := by
      intro u
      induction u using Multiset.induction with
      | empty => simp
      | cons a u ih => rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]; simp
    rw [hn]
    have := Multiset.prod_le_pow_card_of_le (s := (otherConj β).map (fun w => ‖w ^ n - (t : ℂ)‖))
      (M := |(t : ℝ)| + 1) (by positivity) ?_
    · simpa using this
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
      refine ⟨norm_nonneg _, ?_⟩
      have hz1 : ‖z‖ < 1 := hβ.2.2 z hz
      calc ‖z ^ n - (t : ℂ)‖ ≤ ‖z ^ n‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + |(t : ℝ)| := by
            rw [norm_pow, Complex.norm_intCast]
            have : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            push_cast; linarith
        _ = |(t : ℝ)| + 1 := by ring
  rw [h1] at h
  calc (1 : ℝ) ≤ |β ^ n - t| * ‖((otherConj β).map (fun w => w ^ n - (t : ℂ))).prod‖ := h
    _ ≤ |β ^ n - t| * (|(t : ℝ)| + 1) ^ Multiset.card (otherConj β) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- **Step 2 (record gaps are bounded).**  After a record `r`, a run of non-records up to `m`
forces `e {ξ^(C r)} p_r^(e−1) < 1`, `e = C m / C r ≥ 2^(m−r)` (Saito (5.1)), while the norm of
`β^(C r/g) − p_r` is a nonzero integer: `{ξ^(C r)} ≥ (p_r+1)^(−(ℓ−1))`. -/
theorem record_gap_bounded
    {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) {g : ℕ} (hg1 : 1 ≤ g)
    (hpis : IsPisot (ξ ^ g)) {K : ℕ} (hK : ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m) :
    ∃ T K', ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ IsRecord (shiftC j s) ξ r := by
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hnot := not_intCast_pow h1 h2 h5 hξS
  have hCge := C_ge_one h1 h2
  set L := Multiset.card (otherConj (ξ ^ g)) with hL
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  obtain ⟨K2, hK2⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop ((2 : ℝ) ^ L + 1))
  obtain ⟨r0, ⟨hr0rec, hr0ge⟩⟩ := ((frequently_record h1 h2 hξ hnot).and_eventually
    (eventually_ge_atTop (K + K2 + 1))).exists
  refine ⟨L + 2, r0, fun m hm => ?_⟩
  by_contra hcon
  push_neg at hcon
  set r := Nat.findGreatest (IsRecord C ξ) m with hr
  have hr0r : r0 ≤ r := Nat.le_findGreatest hm hr0rec
  have hrrec : IsRecord C ξ r := Nat.findGreatest_spec hm hr0rec
  have hrm : r ≤ m := Nat.findGreatest_le m
  set M := m + (L + 2) with hM
  have hnr : ∀ k, r < k → k ≤ M → ¬ IsRecord C ξ k := by
    intro k hk1 hk2
    rcases le_or_gt k m with h | h
    · exact Nat.findGreatest_is_greatest hk1 h
    · exact hcon k h hk2
  have hmax : ∀ k, 1 ≤ k → k ≤ M → root (p k) (C k) ≤ root (p r) (C r) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hkM
      rcases le_or_gt k r with hkr | hkr
      · exact hrrec k hk hkr
      · have h' := hnr k hkr hkM
        unfold IsRecord at h'
        push_neg at h'
        obtain ⟨k', hk'1, hk'k, hlt⟩ := h'
        rcases Nat.lt_or_ge k' k with h | h
        · exact le_trans hlt.le (ih k' h hk'1 (by omega))
        · have : k' = k := by omega
          subst this; exact absurd hlt (lt_irrefl _)
  have hr1 : 1 ≤ r := by omega
  have hlt : root (p M) (C M) < root (p r) (C r) := by
    have h' := hnr M (by omega) le_rfl
    unfold IsRecord at h'
    push_neg at h'
    obtain ⟨k', hk'1, hk'M, hlt⟩ := h'
    exact lt_of_lt_of_le hlt (hmax k' hk'1 hk'M)
  -- `C M ≥ 2^(L+2) C r`
  have hCpow : ∀ i, 2 ^ i * C r ≤ C (r + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := h2 (r + i) (by omega)
      rw [pow_succ, show r + (i + 1) = r + i + 1 by ring]
      nlinarith
  have hCr : 0 < C r := hCge r hr1
  have hCM : 2 ^ (L + 2) * C r ≤ C M := by
    have := hCpow (M - r)
    rw [show r + (M - r) = M by omega] at this
    exact le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))) this
  set c : ℝ := (C M : ℝ) / C r with hc
  have hCr' : (0 : ℝ) < C r := by exact_mod_cast hCr
  have hc2 : ((2 : ℝ) ^ (L + 2)) ≤ c := by
    rw [hc, le_div_iff₀ hCr']; exact_mod_cast hCM
  have hLc : (L : ℝ) + 2 ≤ c := by
    have : ((L + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (L + 2) := by
      exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    push_cast at this; linarith
  set x := ξ ^ C r with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ c = ξ ^ C M := by
    rw [hx, ← Real.rpow_natCast ξ (C r), ← Real.rpow_mul hξ0.le, hc,
      mul_div_cancel₀ _ hCr'.ne', Real.rpow_natCast]
  have hfl : (⌊x ^ c⌋₊ : ℝ) < (⌊x⌋₊ : ℝ) ^ c := by
    rw [hxc]
    have hpM := root_pow (Nat.cast_nonneg (p M)) (hCge M (by omega))
    have hpos : 0 ≤ root (p M) (C M) := by rw [root]; positivity
    have h3 : (p M : ℝ) < root (p r) (C r) ^ C M := by
      rw [← hpM]; exact pow_lt_pow_left₀ hlt hpos (by have := hCge M (by omega); omega)
    have h4 : root (p r) (C r) ^ C M = (p r : ℝ) ^ c := by
      rw [root, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), hc]
      congr 1; field_simp
    rw [h4] at h3
    exact h3
  have hkey := fract_lt_of_floor_lt hx1 (by linarith) hfl
  -- the norm bound
  have hgr : g ∣ C r := hK r (by omega) hrrec
  have hβn : (ξ ^ g) ^ (C r / g) = x := by rw [hx, ← pow_mul, Nat.mul_div_cancel' hgr]
  set P : ℝ := (⌊x⌋₊ : ℝ) with hP
  have hfr : Int.fract x = x - P := by
    rw [hP, Int.fract, ← Int.natCast_floor_eq_floor (by linarith)]; push_cast; ring
  have hxne : (ξ ^ g) ^ (C r / g) ≠ ((⌊x⌋₊ : ℤ) : ℝ) := by
    rw [hβn]; exact hnot r hr1 _
  have hnorm := abs_pow_sub_mul_ge_one hpis (C r / g) (⌊x⌋₊ : ℤ) hxne
  rw [hβn] at hnorm
  have habs : |x - ((⌊x⌋₊ : ℤ) : ℝ)| = Int.fract x := by
    rw [hfr, hP]; push_cast
    exact abs_of_nonneg (by linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ x)])
  have habsP : |(((⌊x⌋₊ : ℤ) : ℝ))| = P := by rw [hP]; push_cast; exact abs_of_nonneg (by positivity)
  rw [habs, habsP] at hnorm
  -- `P ≥ 2^L + 1`
  have hPbig : (2 : ℝ) ^ L + 1 ≤ P := hK2 r (by omega)
  have hP1 : 1 ≤ P := by have : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num); linarith
  have hP0 : 0 < P := by linarith
  have hfr0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  -- `P^(c−1) ≥ P^(L+1)`
  have hpw : P ^ (L + 1) ≤ P ^ (c - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by push_cast; linarith)
  have hA : Int.fract x * P ^ (L + 1) < 1 := by
    have e1 : Int.fract x * P ^ (L + 1) ≤ Int.fract x * P ^ (c - 1) :=
      mul_le_mul_of_nonneg_left hpw hfr0
    have e0 : 0 ≤ Int.fract x * P ^ (c - 1) := mul_nonneg hfr0 (by positivity)
    have e2 : Int.fract x * P ^ (c - 1) ≤ c * Int.fract x * P ^ (c - 1) := by
      rw [mul_assoc]; nlinarith
    linarith
  have hB : (P + 1) ^ L ≤ 2 ^ L * P ^ L := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) L
  -- `1 ≤ fract (P+1)^L ≤ fract 2^L P^L` and `fract P^(L+1) < 1` give `P < 2^L`
  have hC1 : 1 ≤ Int.fract x * (2 ^ L * P ^ L) :=
    le_trans hnorm (mul_le_mul_of_nonneg_left hB hfr0)
  set y := Int.fract x * P ^ L with hy
  have hA' : P * y < 1 := by
    have e : Int.fract x * P ^ (L + 1) = P * y := by rw [hy]; ring
    linarith
  have hC1' : 1 ≤ 2 ^ L * y := by
    have e : Int.fract x * (2 ^ L * P ^ L) = 2 ^ L * y := by rw [hy]; ring
    linarith
  have hy0 : 0 < y := by
    by_contra h; push_neg at h
    have : (2 : ℝ) ^ L * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have : P < 2 ^ L := lt_of_mul_lt_mul_right (by linarith : P * y < 2 ^ L * y) hy0.le
  linarith

/-- **Step 3 (degree `≤ 3`, no Baker).**  Decay `151/400` at records, records with bounded gaps,
and the orbit `n ↦ 3n − d` (Mignotte/Smyth: the dominant other conjugates are one real or one
complex pair; `a_r² → −1` along records is incompatible with `a_(r+t)² = a_r^(2·3^t) v^(3^t−1)`,
`v^(3^t−1) ≠ 1`). -/
theorem card_le_two_of_records (hB : BakerHarmanPintz2001)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) {g : ℕ} (hg1 : 1 ≤ g)
    (hpis : IsPisot (ξ ^ g)) (hdeg : 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree)
    {K : ℕ} (hK : ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m)
    {T K' : ℕ} (hT : ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ IsRecord (shiftC j s) ξ r) :
    Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
  sorry

/-- The last record before a non-record `M` beats it. -/
theorem exists_last_record {C : ℕ → ℕ} {ξ : ℝ} {r0 M : ℕ} (hr0 : IsRecord C ξ r0) (h : r0 < M)
    (hM : ¬ IsRecord C ξ M) :
    ∃ r, r0 ≤ r ∧ r < M ∧ IsRecord C ξ r ∧
      root ⌊ξ ^ C M⌋₊ (C M) < root ⌊ξ ^ C r⌋₊ (C r) := by
  classical
  set r := Nat.findGreatest (IsRecord C ξ) (M - 1) with hr
  have hr0r : r0 ≤ r := Nat.le_findGreatest (by omega) hr0
  have hrrec : IsRecord C ξ r := Nat.findGreatest_spec (m := r0) (by omega) hr0
  have hrM : r ≤ M - 1 := Nat.findGreatest_le _
  have hnr : ∀ k, r < k → k ≤ M → ¬ IsRecord C ξ k := by
    intro k hk1 hk2
    rcases lt_or_eq_of_le hk2 with h' | h'
    · exact Nat.findGreatest_is_greatest hk1 (by omega)
    · rw [h']; exact hM
  have hmax : ∀ k, 1 ≤ k → k ≤ M →
      root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C r⌋₊ (C r) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hkM
      rcases le_or_gt k r with hkr | hkr
      · exact hrrec k hk hkr
      · have h' := hnr k hkr hkM
        unfold IsRecord at h'
        push_neg at h'
        obtain ⟨k', hk'1, hk'k, hlt⟩ := h'
        rcases Nat.lt_or_ge k' k with h | h
        · exact le_trans hlt.le (ih k' h hk'1 (by omega))
        · have : k' = k := by omega
          subst this; exact absurd hlt (lt_irrefl _)
  refine ⟨r, hr0r, by omega, hrrec, ?_⟩
  have h' := hM
  unfold IsRecord at h'
  push_neg at h'
  obtain ⟨k', hk'1, hk'M, hlt⟩ := h'
  exact lt_of_lt_of_le hlt (hmax k' hk'1 hk'M)

/-- **The non-record inequalities.**  If `r < M`, `p_M^(1/C M) < p_r^(1/C r)` and `ξ^g` is Pisot
with `g ∣ C r`, then with `x = ξ^(C r)`, `P = ⌊x⌋`, `c = C M / C r`:
`c {x} P^(c−1) < 1` (Saito (5.1)) and `1 ≤ {x} (P+1)^(ℓ−1)` (norm). -/
theorem nonrecord_ineq {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ1 : 1 < ξ) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ)) {g : ℕ}
    (hpis : IsPisot (ξ ^ g)) {r M : ℕ} (hr1 : 1 ≤ r) (hrM : r < M) (hgr : g ∣ C r)
    (hlt : root ⌊ξ ^ C M⌋₊ (C M) < root ⌊ξ ^ C r⌋₊ (C r)) :
    (C M : ℝ) / C r * Int.fract (ξ ^ C r) * (⌊ξ ^ C r⌋₊ : ℝ) ^ ((C M : ℝ) / C r - 1) < 1 ∧
      1 ≤ Int.fract (ξ ^ C r) * ((⌊ξ ^ C r⌋₊ : ℝ) + 1) ^ Multiset.card (otherConj (ξ ^ g)) ∧
      (2 : ℝ) ^ (M - r) ≤ (C M : ℝ) / C r := by
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  have hCpow : ∀ i, 2 ^ i * C r ≤ C (r + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := h2 (r + i) (by omega)
      rw [pow_succ, show r + (i + 1) = r + i + 1 by ring]
      nlinarith
  have hCr : 0 < C r := hCge r hr1
  have hCr' : (0 : ℝ) < C r := by exact_mod_cast hCr
  set c : ℝ := (C M : ℝ) / C r with hc
  have hc2 : (2 : ℝ) ^ (M - r) ≤ c := by
    have := hCpow (M - r)
    rw [show r + (M - r) = M by omega] at this
    rw [hc, le_div_iff₀ hCr']; exact_mod_cast this
  have hc1 : 1 ≤ c := le_trans (one_le_pow₀ (by norm_num)) hc2
  set x := ξ ^ C r with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ c = ξ ^ C M := by
    rw [hx, ← Real.rpow_natCast ξ (C r), ← Real.rpow_mul hξ0.le, hc,
      mul_div_cancel₀ _ hCr'.ne', Real.rpow_natCast]
  have hfl : (⌊x ^ c⌋₊ : ℝ) < (⌊x⌋₊ : ℝ) ^ c := by
    rw [hxc]
    have hpM := root_pow (Nat.cast_nonneg (⌊ξ ^ C M⌋₊)) (hCge M (by omega))
    have hpos : 0 ≤ root (⌊ξ ^ C M⌋₊ : ℝ) (C M) := by rw [root]; positivity
    have h3 : (⌊ξ ^ C M⌋₊ : ℝ) < root (⌊ξ ^ C r⌋₊ : ℝ) (C r) ^ C M := by
      rw [← hpM]; exact pow_lt_pow_left₀ hlt hpos (by have := hCge M (by omega); omega)
    have h4 : root (⌊ξ ^ C r⌋₊ : ℝ) (C r) ^ C M = (⌊ξ ^ C r⌋₊ : ℝ) ^ c := by
      rw [root, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), hc]
      congr 1; field_simp
    rw [h4] at h3
    exact h3
  refine ⟨fract_lt_of_floor_lt hx1 hc1 hfl, ?_, hc2⟩
  have hβn : (ξ ^ g) ^ (C r / g) = x := by rw [hx, ← pow_mul, Nat.mul_div_cancel' hgr]
  have hxne : (ξ ^ g) ^ (C r / g) ≠ ((⌊x⌋₊ : ℤ) : ℝ) := by
    rw [hβn]; exact hnot r hr1 _
  have hnorm := abs_pow_sub_mul_ge_one hpis (C r / g) (⌊x⌋₊ : ℤ) hxne
  rw [hβn] at hnorm
  have hfr : Int.fract x = x - (⌊x⌋₊ : ℝ) := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (by linarith)]; push_cast; ring
  have habs : |x - ((⌊x⌋₊ : ℤ) : ℝ)| = Int.fract x := by
    rw [hfr]; push_cast
    exact abs_of_nonneg (by linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ x)])
  have habsP : |(((⌊x⌋₊ : ℤ) : ℝ))| = (⌊x⌋₊ : ℝ) := by
    push_cast; exact abs_of_nonneg (by positivity)
  rw [habs, habsP] at hnorm
  exact hnorm

/-- The second elementary symmetric function of the conjugates of `β^n`, for cubic `β`:
`e₂(β^n) = β^n S(n) + (∏ other conjugates)^n`. -/
noncomputable def e2pow (β : ℝ) (n : ℕ) : ℂ :=
  (β : ℂ) ^ n * conjPowSum β n + (otherConj β).prod ^ n

set_option maxHeartbeats 1600000 in
/-- **Step 4a (degree 3, a non-record forces an exact zero).**  For cubic Pisot `β = ξ^g`, a
record `r` followed by a non-record at `r + 1` has `N_r := |N(β^n − p_r)| < ξ^(2s)/3 + o(1)`
(Saito (5.1) with `c − 1 = 2 − 2s/C r`); `N_r = |p_r e₂ − N(β)^n|` with `|N(β)|^n ≤ β^n R^(2n)`
forces `e₂(β^n) = 0` (and `|N β| = 1`), `n = C r / g`.  Confidence ~85%. -/
theorem e2_zero_of_nonrecord
    {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) {g : ℕ} (hg1 : 1 ≤ g)
    (hpis : IsPisot (ξ ^ g)) (hcard : Multiset.card (otherConj (ξ ^ g)) = 2) :
    ∃ R, ∀ r ≥ R, g ∣ shiftC j s r →
      root ⌊ξ ^ shiftC j s (r + 1)⌋₊ (shiftC j s (r + 1)) <
        root ⌊ξ ^ shiftC j s r⌋₊ (shiftC j s r) →
      e2pow (ξ ^ g) (shiftC j s r / g) = 0 := by
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hnot := not_intCast_pow h1 h2 h5 hξS
  have hCge := C_ge_one h1 h2
  set β := ξ ^ g with hβ
  set R := conjMax β with hRdef
  have hR1 : R < 1 := conjMax_lt_one hpis
  have hR0 : 0 ≤ R := conjMax_nonneg β
  obtain ⟨γ1, γ2, hoc⟩ := Multiset.card_eq_two.1 hcard
  have hγ1 : ‖γ1‖ ≤ R := norm_le_conjMax (by rw [hoc]; simp)
  have hγ2 : ‖γ2‖ ≤ R := norm_le_conjMax (by rw [hoc]; simp)
  -- eventual constraints
  have hRn : ∀ᶠ n : ℕ in atTop, R ^ n < 1 / 8 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1).eventually (gt_mem_nhds (by norm_num))
  have hnt : Tendsto (fun r => C r / g) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * g + 1, fun a ha => ?_⟩
    have := le_C h1 h2 a (by omega)
    rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have hP9 : Tendsto (fun r => (⌊ξ ^ C r⌋₊ : ℝ) ^ (9 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (floor_tendsto h1 h2 hξ1)
  obtain ⟨R0, hR0'⟩ := eventually_atTop.1 ((hnt.eventually hRn).and
    ((hP9.eventually_ge_atTop 16).and ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop 2)))
  refine ⟨R0 + 19 * s.natAbs + 1, fun r hr hgr hlt => ?_⟩
  obtain ⟨hRr, hP16, hP2⟩ := hR0' r (by omega)
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hA, -, hc⟩ := nonrecord_ineq h1 h2 hξ1 hnot hpis hr1 (Nat.lt_succ_self r) hgr hlt
  set n := C r / g with hn
  set x := ξ ^ C r with hx
  set P : ℝ := (⌊x⌋₊ : ℝ) with hP
  set f := Int.fract x with hf
  set c : ℝ := (C (r + 1) : ℝ) / C r with hcdef
  have hβn : β ^ n = x := by rw [hβ, hx, ← pow_mul, Nat.mul_div_cancel' hgr]
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hfx : x = P + f := by
    rw [hf, hP, Int.fract, ← Int.natCast_floor_eq_floor (by linarith)]; push_cast; ring
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hP1 : 1 ≤ P := by linarith
  -- ratio `≥ 29/10`
  have hCr : (0 : ℝ) < C r := by exact_mod_cast hCge r hr1
  have hc29 : (29 : ℝ) / 10 ≤ c := by
    rw [hcdef, le_div_iff₀ hCr]; exact shiftC_ratio hj1 hr1 (by omega)
  -- `f P^(19/10) < 1/2`
  have hpw : P ^ (19 / 10 : ℝ) ≤ P ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hfP : f * P ^ (19 / 10 : ℝ) < 1 / 2 := by
    have e1 : f * P ^ (19 / 10 : ℝ) ≤ f * P ^ (c - 1) := mul_le_mul_of_nonneg_left hpw hf0
    have e0 : 0 ≤ f * P ^ (c - 1) := mul_nonneg hf0 (by positivity)
    have e2 : 2 * (f * P ^ (c - 1)) ≤ c * f * P ^ (c - 1) := by
      have : c * f * P ^ (c - 1) = c * (f * P ^ (c - 1)) := by ring
      rw [this]; nlinarith
    linarith
  have hsplitP : P ^ (2 : ℝ) = P ^ (1 / 10 : ℝ) * P ^ (19 / 10 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hsplitP' : P = P ^ (1 / 10 : ℝ) * P ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hP110 : 0 < P ^ (1 / 10 : ℝ) := by positivity
  -- `f (P+1)² ≤ P/8`
  have hfsq : f * (P + 1) ^ 2 ≤ P / 8 := by
    have hsq : (P + 1) ^ 2 ≤ 4 * P ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
    have : f * (4 * P ^ (2 : ℝ)) = 4 * P ^ (1 / 10 : ℝ) * (f * P ^ (19 / 10 : ℝ)) := by
      rw [hsplitP]; ring
    have h16 : 16 * P ^ (1 / 10 : ℝ) ≤ P := by
      conv_rhs => rw [hsplitP']
      nlinarith
    calc f * (P + 1) ^ 2 ≤ f * (4 * P ^ (2 : ℝ)) := mul_le_mul_of_nonneg_left hsq hf0
      _ = 4 * P ^ (1 / 10 : ℝ) * (f * P ^ (19 / 10 : ℝ)) := this
      _ ≤ 4 * P ^ (1 / 10 : ℝ) * (1 / 2) := by
          apply mul_le_mul_of_nonneg_left hfP.le; positivity
      _ ≤ P / 8 := by linarith
  have hf14 : f < 1 / 4 := by
    have h19 : P ^ (1 : ℝ) ≤ P ^ (19 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
    rw [Real.rpow_one] at h19
    have : f * P ≤ f * P ^ (19 / 10 : ℝ) := mul_le_mul_of_nonneg_left h19 hf0
    nlinarith
  -- the conjugate powers
  set A := γ1 ^ n with hA'
  set B := γ2 ^ n with hB'
  have hS : conjPowSum β n = A + B := by
    rw [conjPowSum, hoc]; simp [hA', hB']
  have hS2 : conjPowSum β (2 * n) = A ^ 2 + B ^ 2 := by
    rw [conjPowSum, hoc]; simp [hA', hB', ← pow_mul, mul_comm]
  have hAn : ‖A‖ ≤ R ^ n := by rw [hA', norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hγ1 n
  have hBn : ‖B‖ ≤ R ^ n := by rw [hB', norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hγ2 n
  have hRn0 : 0 ≤ R ^ n := pow_nonneg hR0 n
  obtain ⟨t1, ht1⟩ := pisot_conjPowSum_add_mem_int hpis n
  obtain ⟨t2, ht2⟩ := pisot_conjPowSum_add_mem_int hpis (2 * n)
  have hX : ((β : ℂ)) ^ n = (x : ℂ) := by rw [← hβn]; push_cast; ring
  -- `t1 = P`
  have ht1P : (t1 : ℝ) = P := by
    have hcl : ‖((t1 : ℂ)) - (P : ℂ)‖ < 1 / 2 := by
      have e : (t1 : ℂ) - (P : ℂ) = (A + B) + ((f : ℝ) : ℂ) := by
        rw [← ht1, hS, hX, hfx]; push_cast; ring
      rw [e]
      calc ‖(A + B) + ((f : ℝ) : ℂ)‖ ≤ ‖A‖ + ‖B‖ + ‖((f : ℝ) : ℂ)‖ := by
            exact le_trans (norm_add_le _ _) (by linarith [norm_add_le A B])
        _ < 1 / 2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0]; linarith
    have hP' : P = ((⌊x⌋₊ : ℤ) : ℝ) := by rw [hP]; push_cast; rfl
    rw [hP'] at hcl ⊢
    have : ((t1 - (⌊x⌋₊ : ℤ) : ℤ) : ℂ) = (t1 : ℂ) - (((⌊x⌋₊ : ℤ) : ℝ) : ℂ) := by push_cast; rfl
    rw [← this, Complex.norm_intCast] at hcl
    have hz : t1 - (⌊x⌋₊ : ℤ) = 0 := by
      by_contra h
      have := Int.one_le_abs h
      have : (1 : ℝ) ≤ |((t1 - (⌊x⌋₊ : ℤ) : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    have : t1 = (⌊x⌋₊ : ℤ) := by omega
    rw [this]
  clear_value A B c x P f n R
  -- `2 e₂ = t1² − t2`
  set E := e2pow β n with hE
  have hE' : E = (x : ℂ) * (A + B) + A * B := by
    rw [hE, e2pow, hS, hX, hoc]; simp [hA', hB', mul_pow]
  have h2E : 2 * E = ((t1 ^ 2 - t2 : ℤ) : ℂ) := by
    push_cast
    rw [← ht1, ← ht2, hS, hS2, hE', pow_mul', hX]; ring
  by_contra hE0
  have hm : t1 ^ 2 - t2 ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at h2E
    exact hE0 ((mul_eq_zero.1 h2E).resolve_left two_ne_zero)
  have hEhalf : 1 / 2 ≤ ‖E‖ := by
    have := congrArg norm h2E
    rw [norm_mul, Complex.norm_intCast] at this
    have h1' : (1 : ℝ) ≤ |((t1 ^ 2 - t2 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    linarith
  -- `P E = x A B − (x − P)(A − P)(B − P)`
  have hsum : (x : ℂ) + A + B = (P : ℂ) := by
    have e : ((P : ℝ) : ℂ) = ((t1 : ℝ) : ℂ) := by rw [ht1P]
    rw [e]; push_cast; rw [← ht1, hS, hX]; ring
  have hid : (P : ℂ) * E = (x : ℂ) * A * B - ((x : ℂ) - P) * (A - P) * (B - P) := by
    have hx' : (x : ℂ) = P - A - B := by rw [← hsum]; ring
    rw [hE', hx']; ring
  have hnorm1 : ‖(x : ℂ) * A * B‖ ≤ (P + 1) * (R ^ n * R ^ n) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have : x ≤ P + 1 := by linarith
    have hAB : ‖A‖ * ‖B‖ ≤ R ^ n * R ^ n := mul_le_mul hAn hBn (norm_nonneg _) hRn0
    calc x * ‖A‖ * ‖B‖ = x * (‖A‖ * ‖B‖) := by ring
      _ ≤ (P + 1) * (R ^ n * R ^ n) := mul_le_mul this hAB (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by linarith)
  have hnorm2 : ‖((x : ℂ) - P) * (A - P) * (B - P)‖ ≤ f * (P + 1) ^ 2 := by
    have e : (x : ℂ) - P = ((f : ℝ) : ℂ) := by rw [hfx]; push_cast; ring
    rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0]
    have hA1 : ‖A - P‖ ≤ P + 1 := by
      calc ‖A - P‖ ≤ ‖A‖ + ‖(P : ℂ)‖ := norm_sub_le _ _
        _ ≤ P + 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have hB1 : ‖B - P‖ ≤ P + 1 := by
      calc ‖B - P‖ ≤ ‖B‖ + ‖(P : ℂ)‖ := norm_sub_le _ _
        _ ≤ P + 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    calc f * ‖A - P‖ * ‖B - P‖ = f * (‖A - P‖ * ‖B - P‖) := by ring
      _ ≤ f * ((P + 1) * (P + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hA1 hB1 (norm_nonneg _) (by linarith)) hf0
      _ = f * (P + 1) ^ 2 := by ring
  have hPE : P / 2 ≤ ‖(P : ℂ) * E‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith
  rw [hid] at hPE
  have := le_trans hPE (norm_sub_le _ _)
  have hRR : R ^ n * R ^ n ≤ 1 / 64 := by nlinarith
  nlinarith

/-- **Step 4b (Skolem; no Baker).**  For cubic Pisot `β`, `e₂(β^n) = 0` holds for only finitely
many `n` at all (`E2Skolem.eventually_e2_ne_zero`: `e₂(β^n)` is a non-degenerate integer
recurrence of order 3, and Skolem's `p`-adic method at an odd prime `p ∤ N(β)` applies), in
particular along the orbit `n_r = (3^(r+j) + s)/g`. -/
theorem finite_e2_zero_orbit
    {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) {g : ℕ} (hg1 : 1 ≤ g) {β : ℝ}
    (hpis : IsPisot β) (hcard : Multiset.card (otherConj β) = 2) :
    ∀ᶠ r in atTop, g ∣ shiftC j s r → e2pow β (shiftC j s r / g) ≠ 0 := by
  have hnt : Tendsto (fun r => shiftC j s r / g) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ : ∃ N, N = b * g := ⟨_, rfl⟩
    refine ⟨N + s.natAbs + 1, fun r hr => ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega), ← hN]
    have hc := shiftC_cast hj1 (k := r) (by omega)
    have h3 : r + 1 ≤ 3 ^ (r + j) :=
      le_trans (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h3' : (r : ℤ) + 1 ≤ 3 ^ (r + j) := by exact_mod_cast h3
    have : (N : ℤ) ≤ (shiftC j s r : ℤ) := by rw [hc]; omega
    exact_mod_cast this
  filter_upwards [hnt.eventually (E2Skolem.eventually_e2_ne_zero hpis hcard)] with r hr _
  exact hr

/-- **Step 4 (no non-records for degree `≤ 3`).**  Degree 2: the norm bound beats Saito (5.1)
outright.  Degree 3: a non-record at `r + 1` forces `|N β| = 1` and
`e₂(β^n) = β^n S(n) + (∏ other conj)^n = 0` at `n = C r / g`; such exact zeros along the
3-adically convergent orbit are finite (Skolem's 3-adic method; no Baker). -/
theorem eventually_record_of_card_le_two
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) {g : ℕ} (hg1 : 1 ≤ g)
    (hpis : IsPisot (ξ ^ g)) (hcard : Multiset.card (otherConj (ξ ^ g)) ≤ 2)
    {K : ℕ} (hK : ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m)
    {T K' : ℕ} (hT : ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ IsRecord (shiftC j s) ξ r) :
    ∃ K'', ∀ m ≥ K'', IsRecord (shiftC j s) ξ m := by
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hnot := not_intCast_pow h1 h2 h5 hξS
  set L := Multiset.card (otherConj (ξ ^ g)) with hL
  obtain ⟨K2, hK2⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop (2 : ℝ))
  have hRR : ∃ R, ∀ r ≥ R, L = 2 → g ∣ C r →
      root ⌊ξ ^ C (r + 1)⌋₊ (C (r + 1)) < root ⌊ξ ^ C r⌋₊ (C r) → False := by
    by_cases hc2 : L = 2
    · obtain ⟨R, hR⟩ := e2_zero_of_nonrecord hj1 hj2 hξ hg1 hpis hc2
      obtain ⟨R2, hR2⟩ := eventually_atTop.1 (finite_e2_zero_orbit (s := s) (j := j) hj1 hg1 hpis hc2)
      exact ⟨max R R2, fun r hr _ hgr hlt =>
        hR2 r (le_trans (le_max_right _ _) hr) hgr (hR r (le_trans (le_max_left _ _) hr) hgr hlt)⟩
    · exact ⟨0, fun r _ h => absurd h hc2⟩
  obtain ⟨R, hR⟩ := hRR
  obtain ⟨r0, ⟨hr0rec, hr0ge⟩⟩ := ((frequently_record h1 h2 hξ hnot).and_eventually
    (eventually_ge_atTop (K + K2 + R + 1))).exists
  refine ⟨r0 + 1, fun M hM => ?_⟩
  by_contra hMn
  obtain ⟨r, hr0r, hrM, hrrec, hlt⟩ := exists_last_record hr0rec (by omega) hMn
  have hgr : g ∣ C r := hK r (by omega) hrrec
  obtain ⟨hA, hB, hc⟩ := nonrecord_ineq h1 h2 hξ1 hnot hpis (by omega) hrM hgr hlt
  set P : ℝ := (⌊ξ ^ C r⌋₊ : ℝ) with hP
  set f := Int.fract (ξ ^ C r) with hf
  set c : ℝ := (C M : ℝ) / C r with hcdef
  have hP2 : 2 ≤ P := hK2 r (by omega)
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hc2' : 2 ≤ c := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ (M - r) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  -- the key comparison `(P+1)^L ≤ c P^(c−1)` outside the exact-zero case
  have hcmp : ¬ (L = 2 ∧ M = r + 1) → (P + 1) ^ L ≤ c * P ^ (c - 1) := by
    intro hcase
    have hLle : L ≤ 2 := hcard
    have hP1 : 1 ≤ P := by linarith
    have hpc1 : P ^ (1 : ℝ) ≤ P ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
    rw [Real.rpow_one] at hpc1
    interval_cases L
    · simp; nlinarith [Real.one_le_rpow hP1 (by linarith : (0:ℝ) ≤ c - 1)]
    · simp; nlinarith
    · have hM2 : r + 2 ≤ M := by
        by_contra h; exact hcase ⟨rfl, by omega⟩
      have hc4 : 4 ≤ c := by
        have : (2 : ℝ) ^ 2 ≤ 2 ^ (M - r) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have hpc3 : P ^ ((3 : ℕ) : ℝ) ≤ P ^ (c - 1) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by push_cast; linarith)
      rw [Real.rpow_natCast] at hpc3
      have hP3 : 2 * P ^ 2 ≤ P ^ 3 := by
        have : 0 ≤ P ^ 2 := by positivity
        nlinarith
      have : (P + 1) ^ 2 ≤ 4 * P ^ 3 := by nlinarith
      nlinarith
  by_cases hcase : L = 2 ∧ M = r + 1
  · obtain ⟨hL2, hMr⟩ := hcase
    subst hMr
    exact hR r (by omega) hL2 hgr hlt
  · have h := hcmp hcase
    have : f * (P + 1) ^ L ≤ c * f * P ^ (c - 1) := by
      calc f * (P + 1) ^ L ≤ f * (c * P ^ (c - 1)) := mul_le_mul_of_nonneg_left h hf0
        _ = c * f * P ^ (c - 1) := by ring
    linarith

/-- **All large indices are records** for the E+ exponents, if `ξ` is algebraic. -/
theorem eventually_record_shift (hB : BakerHarmanPintz2001) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m := by
  obtain ⟨g, hg1, hpis, hdeg, K, hK⟩ := records_pisot hB hD hj1 hj2 hξ halg
  obtain ⟨T, K', hT⟩ := record_gap_bounded hj1 hj2 hξ hg1 hpis hK
  exact eventually_record_of_card_le_two hs hj1 hj2 hξ hg1 hpis
    (card_le_two_of_records hB hs hj1 hj2 hξ hg1 hpis hdeg hK hT) hK hT

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
