/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDMixed
import LeanFormalizations.NumberTheory.Mills.ShiftedMills
import LeanFormalizations.Literature.Saito2025
import LeanFormalizations.Literature.Siegel1944

/-!
# Phase 58: shifted Mills constants `ξ(3^k + s)` are transcendental for even `s ≥ 8`, `3 ∤ s`
(conditional only on Saito 2025 Type B and Siegel 1944; no rigidity node)

Let `j` be least-ish with `3^(j+1) ≥ s` and `C_k = 3^(k+j) + s`.  Let `ξ` be the least `A > 1` with
`⌊A^(C_k)⌋` prime for every `k ≥ 1`.

## Route
1. **Saito's hypotheses** for `C` (`Literature.Saito2025TypeBTrace`): `C 1 ≥ 1`; `2 C_k ≤ C_(k+1)`
   (⇔ `s ≤ 3^(k+j)`, from `hj`); ratio `≥ 29/10` for all large `k` (ratios `→ 3`); `(B5′)`: `3 ∤ C_m`
   (`3 ∤ s`), so `C_m ∣ 3^(j+m)·(3^t − 1) = C_(m+t) − C_m` for `t = ord_(C_m)(3)` (or `φ(C_m)`), and
   every multiple `t·i` works, giving a large `k` with ratio `≥ 29/10`.
2. **`IsLeast` is unique**, so Saito's `ξ` is ours.  Branch 1: transcendental, done.
3. **Branch 2: `g = 1`.**  `g ∣ C_k` and `g ∣ C_(k+1)` for large `k` ⇒ `g ∣ 3C_k − C_(k+1) = 2s`;
   `C_k` is odd (`s` even), so `g` is odd, `g ∣ s`; then `g ∣ 3^(k+j)` and `gcd(g, 3) = 1` (as `3 ∤ s`),
   so `g = 1`.  Hence `ξ` is a cubic Pisot number.
4. **Contradiction with Theorem D** (`TheoremDMixed.floor_pow_prime_pow_add_not_prime_full`, `c = 3`,
   `f` = the integer minimal polynomial of `ξ`, `d = 3`):
   - `hs`: `ξ ≥ κ` (Siegel) and `κ^8 > 4`, so `ξ^s > 4 = d + 1`.
   - If `f ≢ X³ (mod 3)`: Theorem D gives infinitely many `n` with `⌊ξ^(3^n + s)⌋` not prime; take
     one with `n ≥ j + 1`, i.e. `n = k + j`, `k ≥ 1`: contradiction.
   - If `f ≡ X³ (mod 3)`: every root is a non-unit above 3, so `powTrace ξ N ≡ 0 (mod 3)` for
     `N ≥ 3` (Newton / `σ₁ ≡ σ₂ ≡ σ₃ ≡ 0`), and by branch 2's trace identity the prime `⌊ξ^(C_k)⌋`
     is divisible by 3 for all large `k`, yet it tends to infinity: contradiction.

Frozen: the statement below; all earlier statements; `Literature/` (the new
`Literature/Siegel1944.lean` def is frozen too).  No `private`.  Decomposing is progress.
-/

namespace LeanFormalizations.Mills.ShiftedMillsLarge

open Filter Polynomial LeanFormalizations.Literature
  LeanFormalizations.Mills.TheoremDGeneral LeanFormalizations.Mills.TheoremDMixed

/-! ### Step 1: the exponent sequence `C_k = 3^(k+j) + s` -/

/-- The exponent sequence `C_k = 3^(k+j) + s`. -/
def largeC (j s k : ℕ) : ℕ := 3 ^ (k + j) + s

theorem largeC_succ (j s k : ℕ) : largeC j s (k + 1) = 3 * 3 ^ (k + j) + s := by
  simp only [largeC, show k + 1 + j = (k + j) + 1 from by ring, pow_succ]
  ring

theorem largeC_pos (j s k : ℕ) : 0 < largeC j s k := by
  have : 0 < 3 ^ (k + j) := Nat.pow_pos (by norm_num)
  simp only [largeC]; omega

/-- `C_k` is odd when `s` is even. -/
theorem largeC_odd {s : ℕ} (hs : Even s) (j k : ℕ) : Odd (largeC j s k) := by
  have ho : Odd (3 ^ (k + j)) := Odd.pow (by decide)
  rw [Nat.even_iff] at hs
  rw [Nat.odd_iff] at ho ⊢
  simp only [largeC]
  omega

/-- `3 ∤ C_k` when `3 ∤ s` and `k ≥ 1`. -/
theorem three_not_dvd_largeC {s : ℕ} (hs : ¬ 3 ∣ s) {j k : ℕ} (hk : 1 ≤ k) :
    ¬ (3 ∣ largeC j s k) := by
  intro hd
  refine hs ?_
  have h3 : (3 : ℕ) ∣ 3 ^ (k + j) := dvd_pow_self 3 (by omega)
  simpa [largeC] using (Nat.dvd_sub hd h3)

/-- Doubling: `2 C_k ≤ C_(k+1)` as soon as `s ≤ 3^(k+j)`. -/
theorem largeC_two_mul_le {s j : ℕ} (hj : s ≤ 3 ^ (j + 1)) {k : ℕ} (hk : 1 ≤ k) :
    2 * largeC j s k ≤ largeC j s (k + 1) := by
  have hmono : (3 : ℕ) ^ (j + 1) ≤ 3 ^ (k + j) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [largeC_succ]
  simp only [largeC]
  omega

/-- The ratio bound, from `19 s ≤ 3^(k+j)`. -/
theorem largeC_ratio {s j k : ℕ} (h : 19 * s ≤ 3 ^ (k + j)) :
    (29 : ℝ) / 10 * largeC j s k ≤ largeC j s (k + 1) := by
  have hc1 : ((largeC j s k : ℕ) : ℝ) = (3 : ℝ) ^ (k + j) + s := by
    simp only [largeC]; push_cast; ring
  have hc2 : ((largeC j s (k + 1) : ℕ) : ℝ) = 3 * (3 : ℝ) ^ (k + j) + s := by
    rw [largeC_succ]; push_cast; ring
  have hR : (19 : ℝ) * s ≤ (3 : ℝ) ^ (k + j) := by exact_mod_cast h
  rw [hc1, hc2]
  linarith

/-- A large exponent makes the ratio bound automatic. -/
theorem largeC_ratio_of_le {s j k : ℕ} (h : 19 * s ≤ k) :
    (29 : ℝ) / 10 * largeC j s k ≤ largeC j s (k + 1) := by
  refine largeC_ratio ?_
  have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : (3 : ℕ) ^ k ≤ 3 ^ (k + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Step 2: the divisibility hypothesis `(B5′)` -/

/-- If `C_m ∣ 3^t − 1` then `C_m ∣ C_(m+t)`. -/
theorem largeC_dvd_shift {j s m t : ℕ} (ht : largeC j s m ∣ 3 ^ t - 1) :
    largeC j s m ∣ largeC j s (m + t) := by
  set n := largeC j s m with hn
  have hmod : (3 : ℕ) ^ t ≡ 1 [MOD n] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr ht).symm
  have hrw : largeC j s (m + t) = 3 ^ (m + j) * 3 ^ t + s := by
    simp only [largeC, ← pow_add]
    ring_nf
  have hchain : largeC j s (m + t) ≡ n [MOD n] := by
    rw [hrw, hn, largeC]
    calc 3 ^ (m + j) * 3 ^ t + s
        ≡ 3 ^ (m + j) * 1 + s [MOD n] := Nat.ModEq.add_right s (Nat.ModEq.mul_left _ hmod)
      _ = 3 ^ (m + j) + s := by ring
  have h0 : largeC j s (m + t) ≡ 0 [MOD n] := hchain.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  exact Nat.modEq_zero_iff_dvd.mp h0

/-- `(B5′)` for `C`: every `m ≥ 1` has a large `k > m` with `C_m ∣ C_k` and the ratio bound.
Take `t = φ(C_m)·i` with `i` large: Euler gives `C_m ∣ 3^t − 1` (`3 ∤ C_m`), and `t ≥ i` pushes
`k = m + t` past `19 s`. -/
theorem largeC_B5 {s : ℕ} (hs3 : ¬ 3 ∣ s) {j m : ℕ} (hm : 1 ≤ m) :
    ∃ k > m, largeC j s m ∣ largeC j s k ∧
      (29 : ℝ) / 10 * largeC j s k ≤ largeC j s (k + 1) := by
  set n := largeC j s m with hn
  have hnpos : 0 < n := largeC_pos j s m
  have hcop : Nat.Coprime 3 n := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    exact three_not_dvd_largeC hs3 hm
  have hphi : 1 ≤ n.totient := Nat.totient_pos.mpr hnpos
  set i := 19 * s + m + 1 with hi
  set t := n.totient * i with hti
  have hti1 : i ≤ t := Nat.le_mul_of_pos_left i hphi
  have heuler : 3 ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
  have hpow : (3 : ℕ) ^ t ≡ 1 [MOD n] := by
    rw [hti, pow_mul]
    simpa using heuler.pow i
  have hdvd : n ∣ 3 ^ t - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hpow.symm
  refine ⟨m + t, by omega, largeC_dvd_shift hdvd, largeC_ratio_of_le (by omega)⟩

/-! ### Step 3: `g = 1` -/

/-- If `g` divides `C_k` for all large `k`, then `g = 1`:
`g ∣ 3 C_k − C_(k+1) = 2 s`, `C_k` is odd, so `g ∣ s`, hence `g ∣ 3^(k+j)` and `3 ∤ g`. -/
theorem eq_one_of_eventually_dvd {s : ℕ} (hs_even : Even s) (hs3 : ¬ 3 ∣ s) {j g : ℕ}
    (hg : ∀ᶠ k in atTop, g ∣ largeC j s k) : g = 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  set k := max N 1 with hk
  have h1 : g ∣ largeC j s k := hN k (le_max_left _ _)
  have h2 : g ∣ largeC j s (k + 1) := hN (k + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  -- `3 C_k = C_(k+1) + 2 s`
  have hid : 3 * largeC j s k = largeC j s (k + 1) + 2 * s := by
    rw [largeC_succ]; simp only [largeC]; ring
  have hg2s : g ∣ 2 * s := by
    have h3 : g ∣ 3 * largeC j s k := h1.mul_left 3
    rw [hid] at h3
    simpa using (Nat.dvd_sub h3 h2)
  have hgodd : Odd g := (largeC_odd hs_even j k).of_dvd_nat h1
  have hg2 : Nat.Coprime g 2 := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    rw [Nat.odd_iff] at hgodd
    omega
  have hgs : g ∣ s := (Nat.Coprime.dvd_of_dvd_mul_left hg2 hg2s)
  have hgpow : g ∣ 3 ^ (k + j) := by
    have := Nat.dvd_sub h1 hgs
    simpa [largeC] using this
  have hg3 : ¬ (3 ∣ g) := fun h => hs3 (h.trans hgs)
  have hcop : Nat.Coprime g 3 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hg3))
  have : g ∣ Nat.gcd g (3 ^ (k + j)) := Nat.dvd_gcd dvd_rfl hgpow
  rw [Nat.Coprime.gcd_eq_one (hcop.pow_right _)] at this
  exact Nat.dvd_one.mp this

/-! ### Step 4: the integer minimal polynomial of a Pisot number -/

/-- The rational minimal polynomial is the integer one, pushed to `ℚ`. -/
theorem minpoly_map_rat {β : ℝ} (hint : IsIntegral ℤ β) :
    minpoly ℚ β = (minpoly ℤ β).map (algebraMap ℤ ℚ) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint

/-- The complex roots of `minpoly ℚ β` are the complex roots of `minpoly ℤ β`. -/
theorem aroots_eq_roots {β : ℝ} (hint : IsIntegral ℤ β) :
    (minpoly ℚ β).aroots ℂ = ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
  rw [Polynomial.aroots, minpoly_map_rat hint, Polynomial.map_map]
  congr 2

theorem minpoly_int_monic {β : ℝ} (hint : IsIntegral ℤ β) : (minpoly ℤ β).Monic :=
  minpoly.monic hint

theorem minpoly_int_irreducible {β : ℝ} (hint : IsIntegral ℤ β) : Irreducible (minpoly ℤ β) :=
  (minpoly.prime_of_isIntegrallyClosed hint).irreducible

theorem minpoly_int_natDegree {β : ℝ} (hint : IsIntegral ℤ β) :
    (minpoly ℤ β).natDegree = (minpoly ℚ β).natDegree := by
  rw [minpoly_map_rat hint, (minpoly_int_monic hint).natDegree_map]

/-- The Pisot conjugate bound, transported to the integer minimal polynomial. -/
theorem minpoly_int_conj_small {β : ℝ} (hβ : IsPisot β) :
    ∀ z ∈ ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots, z ≠ (β : ℂ) → ‖z‖ < 1 := by
  intro z hz hzβ
  refine hβ.2.2 z ?_
  rw [aroots_eq_roots hβ.2.1]
  exact (Multiset.mem_erase_of_ne hzβ).mpr hz

/-! ### Step 5: `powTrace` is the companion-matrix trace -/

/-- **Saito's `Tr(β^N)` is our integer `traceSeq`.**  The complex roots of `minpoly ℤ β` are
exactly the (distinct) values of the injective enumeration `e`, so the multiset power sum is the
`Finset` power sum, which is the trace of the companion power. -/
theorem powTrace_eq_traceSeq {β : ℝ} (hint : IsIntegral ℤ β) (N : ℕ) :
    powTrace β N = ((traceSeq (minpoly ℤ β) N : ℤ) : ℂ) := by
  classical
  set f := minpoly ℤ β with hf
  have hmon : f.Monic := minpoly_int_monic hint
  have hirr : Irreducible f := minpoly_int_irreducible hint
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum f hmon hirr
  set fC := f.map (Int.castRingHom ℂ) with hfC
  have hfC0 : fC ≠ 0 := (hmon.map (Int.castRingHom ℂ)).ne_zero
  -- the roots multiset is the image of `e`
  have hnd : fC.natDegree = f.natDegree := hmon.natDegree_map _
  have hcard : fC.roots.card = f.natDegree := by
    rw [← hnd]; exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits fC)
  set M : Multiset ℂ := (Finset.univ : Finset (Fin f.natDegree)).val.map e with hM
  have hMnodup : M.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
  have hMsub : M ⊆ fC.roots := by
    intro z hz
    rw [hM, Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact (Polynomial.mem_roots hfC0).2 (he i)
  have hMcard : M.card = f.natDegree := by simp [hM]
  have hMeq : M = fC.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.le_iff_subset hMnodup |>.2 hMsub)
      (by rw [hcard, hMcard])
  -- power sums
  have hsum : ((traceSeq f N : ℤ) : ℂ) = ∑ i, (e i) ^ N :=
    traceSeq_eq_root_sum f hmon e he hinj N
  rw [hsum, powTrace, aroots_eq_roots hint, ← hfC, ← hMeq, hM, Multiset.map_map]
  rfl

/-! ### Step 6: the size input (Siegel) -/

/-- The plastic number exists: `x³ = x + 1` has a root in `(1, 2)`. -/
theorem exists_plastic : ∃ κ : ℝ, κ ^ 3 = κ + 1 ∧ 1 < κ := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by continuity))
  have hmem : (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3 - 1 - 1) ((2 : ℝ) ^ 3 - 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨κ, hκmem, hκ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont hmem
  refine ⟨κ, by linarith [hκ], ?_⟩
  rcases lt_or_ge 1 κ with h | h
  · exact h
  · exfalso
    have h1 : (1 : ℝ) ≤ κ := hκmem.1
    have : κ = 1 := le_antisymm h h1
    rw [this] at hκ
    norm_num at hκ

/-- **The size input.**  A Pisot number to the power `s ≥ 8` exceeds `4 = d + 1` (`d = 3`):
Siegel gives `β ≥ κ`, and `κ^8 = 2κ² + 3κ + 2 > 4`. -/
theorem four_lt_pisot_pow (hSieg : Siegel1944SmallestPisot) {β : ℝ} (hβ : IsPisot β) {s : ℕ}
    (hs : 8 ≤ s) : (4 : ℝ) < β ^ s := by
  obtain ⟨κ, hκ, hκ1⟩ := exists_plastic
  have hle : κ ≤ β := hSieg β hβ κ hκ hκ1
  have hβ1 : 1 < β := hβ.1
  have hexp : κ ^ 8 = 2 * κ ^ 2 + 3 * κ + 2 := by
    linear_combination (κ ^ 5 + κ ^ 3 + κ ^ 2 + κ + 2) * hκ
  have hκ8 : (4 : ℝ) < κ ^ 8 := by nlinarith [hexp, hκ1]
  have h1 : κ ^ 8 ≤ β ^ 8 := pow_le_pow_left₀ (by linarith) hle 8
  have h2 : β ^ 8 ≤ β ^ s := pow_le_pow_right₀ (le_of_lt hβ1) hs
  linarith

/-! ### Step 7: the excluded class `f ≡ X^d (mod 3)` has traces divisible by 3 -/

/-- If `f ≡ X^d (mod c)` then the companion matrix is nilpotent mod `c`, so every power sum
`traceSeq f N` with `N ≥ d` is divisible by `c`. -/
theorem dvd_traceSeq_of_map_eq_X_pow (f : ℤ[X]) (hmon : f.Monic) (hd : 1 ≤ f.natDegree)
    {c : ℕ} (hc : c.Prime) (hX : f.map (Int.castRingHom (ZMod c)) = X ^ f.natDegree)
    {N : ℕ} (hN : f.natDegree ≤ N) : (c : ℤ) ∣ traceSeq f N := by
  classical
  haveI : Fact c.Prime := ⟨hc⟩
  have hnil : compM (ZMod c) f ^ f.natDegree = 0 := by
    have h := aeval_compM_self (K := ZMod c) f hmon hd
    rw [hX, map_pow, Polynomial.aeval_X] at h
    exact h
  have hzero : compM (ZMod c) f ^ N = 0 := by
    have : N = f.natDegree + (N - f.natDegree) := by omega
    rw [this, pow_add, hnil, zero_mul]
  have hcast : ((traceSeq f N : ℤ) : ZMod c) = 0 := by
    rw [traceSeq_cast, hzero, Matrix.trace_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast

/-- **Transcendence of `ξ(3^(k+j) + s)`** for even `s ≥ 8` with `3 ∤ s`. -/
theorem xi_shifted_large_transcendental (hS : Saito2025TypeBTrace)
    (hSieg : Siegel1944SmallestPisot) {s j : ℕ} (hs_even : Even s) (hs3 : ¬ 3 ∣ s) (hs8 : 8 ≤ s)
    (hj : s ≤ 3 ^ (j + 1)) {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ (3 ^ (k + j) + s)⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  classical
  -- Saito's hypotheses for `C_k = 3^(k+j) + s`
  have hC1 : 1 ≤ largeC j s 1 := largeC_pos j s 1
  have hC2 : ∀ k ≥ 1, 2 * largeC j s k ≤ largeC j s (k + 1) := fun k hk => largeC_two_mul_le hj hk
  have hC3 : ∀ K : ℕ, ∃ k ≥ K, (29 : ℝ) / 10 * largeC j s k ≤ largeC j s (k + 1) := fun K =>
    ⟨max K (19 * s), le_max_left _ _, largeC_ratio_of_le (le_max_right _ _)⟩
  obtain ⟨ξ', hleast, hdisj⟩ :=
    hS (largeC j s) hC1 hC2 hC3 (fun m hm => largeC_B5 hs3 hm)
  have hxi : ξ' = ξ := hleast.unique hξ
  rw [hxi] at hdisj hleast
  rcases hdisj with htr | ⟨g, hg1, hpisot, hdegQ, K, hK⟩
  · exact htr
  exfalso
  -- Step 3: `g = 1`
  have hgone : g = 1 := by
    refine eq_one_of_eventually_dvd (s := s) hs_even hs3 (j := j) (g := g) ?_
    filter_upwards [eventually_ge_atTop (max K (19 * s))] with k hk
    exact (hK k (le_trans (le_max_left _ _) hk)
      (largeC_ratio_of_le (le_trans (le_max_right _ _) hk))).1
  subst hgone
  rw [pow_one] at hpisot hdegQ
  -- the integer minimal polynomial
  have hint : IsIntegral ℤ ξ := hpisot.2.1
  set f : ℤ[X] := minpoly ℤ ξ with hfdef
  have hmon : f.Monic := minpoly_int_monic hint
  have hirr : Irreducible f := minpoly_int_irreducible hint
  have hdeg3 : f.natDegree = 3 := by rw [hfdef, minpoly_int_natDegree hint, hdegQ]
  have hroot : aeval ξ f = 0 := minpoly.aeval ℤ ξ
  have hα : 1 < ξ := hpisot.1
  have hconj : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (ξ : ℂ) → ‖z‖ < 1 :=
    minpoly_int_conj_small hpisot
  have hc3 : Nat.Prime 3 := by norm_num
  by_cases hX : f.map (Int.castRingHom (ZMod 3)) = X ^ f.natDegree
  · -- Branch 2: `f ≡ X³ (mod 3)`, so every large trace is divisible by 3
    obtain ⟨n₀, hn₀⟩ := exists_floor_gt hα (c := 3) (by norm_num) s 3
    set k := max (max K 1) (max (19 * s) n₀) with hk
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
    have hkK : K ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
    have hks : 19 * s ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkn : n₀ ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have hratio := largeC_ratio_of_le (s := s) (j := j) hks
    have htrace := (hK k hkK hratio).2
    rw [pow_one, Nat.div_one] at htrace
    have hprime : (⌊ξ ^ largeC j s k⌋₊).Prime := hleast.1.2 k hk1
    -- the trace is the integer `traceSeq`
    have hts : ((traceSeq f (largeC j s k) : ℤ) : ℂ) = ((⌊ξ ^ largeC j s k⌋₊ : ℕ) : ℂ) := by
      rw [← powTrace_eq_traceSeq hint]; exact htrace
    have htsZ : traceSeq f (largeC j s k) = ((⌊ξ ^ largeC j s k⌋₊ : ℕ) : ℤ) := by
      exact_mod_cast hts
    have hdvd3 : (3 : ℤ) ∣ traceSeq f (largeC j s k) := by
      refine dvd_traceSeq_of_map_eq_X_pow f hmon (by omega) hc3 hX ?_
      have : 3 ≤ largeC j s k := by
        have : (3 : ℕ) ≤ 3 ^ (k + j) := Nat.le_self_pow (by omega) 3
        simp only [largeC]; omega
      omega
    have hdvdN : (3 : ℕ) ∣ ⌊ξ ^ largeC j s k⌋₊ := by
      rw [htsZ] at hdvd3
      exact_mod_cast hdvd3
    have heq3 : ⌊ξ ^ largeC j s k⌋₊ = 3 := ((Nat.Prime.eq_one_or_self_of_dvd hprime 3 hdvdN).resolve_left
      (by norm_num)).symm
    -- but the floor exceeds 3
    have hgt := hn₀ (k + j) (by omega)
    have hfl : ((⌊ξ ^ largeC j s k⌋₊ : ℕ) : ℤ) = ⌊ξ ^ (3 ^ (k + j) + s)⌋ := by
      simp only [largeC]
      exact Int.natCast_floor_eq_floor (by positivity)
    rw [heq3] at hfl
    omega
  · -- Branch 1: Theorem D applies
    have hsize : ((f.natDegree : ℝ)) + 1 < ξ ^ s := by
      rw [hdeg3]
      have := four_lt_pisot_pow hSieg hpisot hs8
      push_cast
      linarith
    have hfreq := floor_pow_prime_pow_add_not_prime_full f hmon hirr (by omega) hroot hα hconj
      hc3 hX hsize
    obtain ⟨n, hnp, hnj⟩ := (hfreq.and_eventually (eventually_ge_atTop (j + 1))).exists
    refine hnp ?_
    have hn : n = (n - j) + j := by omega
    have hk1 : 1 ≤ n - j := by omega
    rw [hn]
    exact hleast.1.2 (n - j) hk1

end LeanFormalizations.Mills.ShiftedMillsLarge
