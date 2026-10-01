/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385
import LeanFormalizations.NumberTheory.Erdos385.Brun.GLower
import LeanFormalizations.NumberTheory.Erdos385.Brun.Density
import LeanFormalizations.NumberTheory.Erdos385.Brun.Selberg
import LeanFormalizations.NumberTheory.Erdos385.Brun.PairSieve

/-!
# Erdős #385, phase E2b: discharge `Literature.BrunUniformGap`

Side quest (Trevor, 2026-10-01): turn the cited uniform Brun bound for prime pairs into a theorem, so
that `Erdos385.card_bad_le` (Count.lean) becomes unconditional.

**Frozen statement:** `brunUniformGap_holds : LeanFormalizations.Literature.BrunUniformGap`, i.e.
`∃ C, ∀ X h, 3 ≤ X → 1 ≤ h → #{n ≤ X : n, n + h prime} ≤ C · (h/φ(h)) · X / log² X`.

**Route (upper-bound sieve, dimension 2).**  Sieve `A = {n(n+h) : n ≤ X}` by primes `p < z`,
`z = X^c`.  For `p ∤ h` two residue classes are removed (`n ≡ 0, −h`), for `p ∣ h` one.  Mathlib's
`Mathlib/NumberTheory/SelbergSieve.lean` gives the Selberg upper bound `S(A, z) ≤ |A|/G(z) + R`;
bound `G(z) ≫ (φ(h)/h) log² z` via the multiplicative density `ν(p)/p` and Mertens, and the
remainder `R ≪ z² · (log z)^k` by the level-`z²` error terms (each `|r_d| ≤ 2^ω(d)`).  Pairs with
`n < z` contribute at most `z`.  Then `C` absorbs `c`.  Fallback: Brun's pure sieve (weaker exponent is
NOT acceptable here: the bound must be `X / log² X` up to the `h/φ(h)` factor).

If the `G(z)` lower bound or the remainder bookkeeping gets hard, leave it as a NAMED sub-lemma with
a disclosed hole and an English paragraph with a confidence; that is an acceptable finish.
-/

namespace Erdos385

open LeanFormalizations.Literature Finset

lemma brun_log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (by norm_num : (0 : ℝ) < 1 / 2)
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc Real.log x ^ 2 ≤ (x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := by gcongr
    _ = 4 * x := by rw [div_pow, hs]; ring

lemma coprime_primorial_of_prime_gt {y p : ℕ} (hp : p.Prime) (hy : y < p) :
    Nat.Coprime (primorial y) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
    have := hp.dvd_primorial_iff.mp hd; omega).symm

/-- The uniform Brun bound for prime pairs, proved (discharges `Literature.BrunUniformGap`). -/
theorem brunUniformGap_holds : BrunUniformGap := by
  refine ⟨20000, fun X h hX hh => ?_⟩
  have hh0 : h ≠ 0 := by omega
  set R : ℝ := (h : ℝ) / Nat.totient h with hRdef
  have hφpos : (0 : ℝ) < Nat.totient h := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hR : 1 ≤ R := by
    rw [hRdef, le_div_iff₀ hφpos, one_mul]; exact_mod_cast Nat.totient_le h
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  set S := (range (X + 1)).filter (fun n => n.Prime ∧ (n + h).Prime) with hSdef
  have hS : ({n : ℕ | n ≤ X ∧ n.Prime ∧ (n + h).Prime}.ncard) = S.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext n
    simp [hSdef]
  clear_value R
  rw [hS, show (20000 : ℝ) * R * X / Real.log X ^ 2 = 20000 * R * X / Real.log X ^ 2 from rfl,
    le_div_iff₀ (by positivity)]
  have hlog2 := brun_log_sq_le hX1
  have hRX : (X : ℝ) ≤ R * X := le_mul_of_one_le_left (by linarith) hR
  by_cases hodd : ¬ 2 ∣ h
  · -- `n, n + h` both prime with `h` odd forces `n = 2`.
    have hsub : S ⊆ {2} := by
      intro n hn
      simp only [hSdef, mem_filter, mem_range] at hn
      obtain ⟨-, hp, hq⟩ := hn
      rcases hp.eq_two_or_odd with h2 | h2
      · simp [h2]
      · exfalso
        have hev : 2 ∣ n + h := by omega
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp hev
        have := hp.two_le; omega
    have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast (card_le_card hsub).trans (by simp)
    nlinarith [sq_nonneg (Real.log X)]
  push Not at hodd
  set t := Nat.findGreatest (fun t => t ^ 16 ≤ X) X with htdef
  have ht16 : t ^ 16 ≤ X := Nat.findGreatest_spec (P := fun t => t ^ 16 ≤ X) (Nat.zero_le X)
    (by simp)
  have hlt : X < (t + 1) ^ 16 := by
    by_contra hge; push Not at hge
    have htX : t + 1 ≤ X := le_trans (Nat.le_self_pow (by norm_num) _) hge
    exact Nat.findGreatest_is_greatest (P := fun t => t ^ 16 ≤ X) (Nat.lt_succ_self t) htX hge
  clear_value t
  by_cases ht2 : t < 2
  · have hX : X < 2 ^ 16 := lt_of_lt_of_le hlt (Nat.pow_le_pow_left (by omega) 16)
    have hc : (S.card : ℝ) ≤ X + 1 := by
      have : S.card ≤ X + 1 := (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hlogle : Real.log X ≤ 12 := by
      have hA : Real.log X ≤ Real.log ((2 : ℝ) ^ 16) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hX.le)
      rw [Real.log_pow] at hA
      have hB := Real.log_two_lt_d9
      push_cast at hA; norm_num at hB; linarith
    have h144 : Real.log X ^ 2 ≤ 144 := by
      have := pow_le_pow_left₀ hlogX.le hlogle 2; norm_num at this; linarith
    calc (S.card : ℝ) * Real.log X ^ 2 ≤ ((X : ℝ) + 1) * 144 :=
          mul_le_mul hc h144 (sq_nonneg _) (by positivity)
      _ ≤ 20000 * R * X := by linarith
  push Not at ht2
  set y := t * t with hydef
  have hy' : (y : ℝ) = (t : ℝ) ^ 2 := by rw [hydef]; push_cast; ring
  set F := (range (X + 1)).filter (fun n => Nat.Coprime (primorial y) (n * (n + h))) with hF
  have hsub : S ⊆ range (y + 1) ∪ F := by
    intro n hn
    simp only [hSdef, mem_filter, mem_range] at hn
    obtain ⟨hnX, hp, hq⟩ := hn
    by_cases hny : n ≤ y
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · refine mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr hnX, ?_⟩)
      exact Nat.Coprime.mul_right (coprime_primorial_of_prime_gt hp (by omega))
        (coprime_primorial_of_prime_gt hq (by omega))
  have hcardS : (S.card : ℝ) ≤ (y + 1 : ℝ) + F.card := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at this; exact_mod_cast this
  have hFle := Erdos385.Brun.card_sifted_le hodd hh0 (le_refl y) ht2 (X + 1)
  rw [← hF] at hFle
  clear_value F S y
  -- logarithmic comparisons
  have ht2' : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  set a := Real.log t with hadef
  clear_value a
  have ha : 0 < a := by rw [hadef]; exact Real.log_pos (by linarith)
  have hat : a ≤ t := by rw [hadef]; have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t by linarith); linarith
  have hlogXa : Real.log X ≤ 32 * a := by
    have h1 : Real.log X ≤ 16 * Real.log (t + 1) := by
      have : Real.log X ≤ Real.log (((t : ℝ) + 1) ^ 16) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hlt.le)
      rwa [Real.log_pow] at this
    have h2 : Real.log (t + 1) ≤ 2 * a := by
      rw [hadef, show 2 * Real.log (t : ℝ) = Real.log ((t : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by linarith) (by rw [sq]; linarith [mul_le_mul_of_nonneg_right ht2' (show (0:ℝ) ≤ t by linarith)])
    linarith
  have hlogsq : Real.log X ^ 2 ≤ 1024 * a ^ 2 :=
    (pow_le_pow_left₀ hlogX.le hlogXa 2).trans (le_of_eq (by ring))
  have ht16' : (t : ℝ) ^ 16 ≤ X := by exact_mod_cast ht16
  have hsmall : ((y : ℝ) + 1 + (y : ℝ) ^ 6) * Real.log X ^ 2 ≤ 3072 * X := by
    rw [hy']
    have hpow : (t : ℝ) ^ 2 + 1 + ((t : ℝ) ^ 2) ^ 6 ≤ 3 * (t : ℝ) ^ 12 := by
      have h12 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h1 : (1 : ℝ) ≤ (t : ℝ) ^ 12 := one_le_pow₀ (by linarith)
      have h6 : ((t : ℝ) ^ 2) ^ 6 = (t : ℝ) ^ 12 := by ring
      linarith
    have hl : Real.log X ^ 2 ≤ 1024 * (t : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ ha.le hat 2; linarith
    calc ((t : ℝ) ^ 2 + 1 + ((t : ℝ) ^ 2) ^ 6) * Real.log X ^ 2
        ≤ (3 * (t : ℝ) ^ 12) * (1024 * (t : ℝ) ^ 2) := by gcongr
      _ = 3072 * ((t : ℝ) ^ 14) := by ring
      _ ≤ 3072 * (t : ℝ) ^ 16 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (by norm_num : 14 ≤ 16)) (by norm_num)
      _ ≤ 3072 * X := by linarith
  have hmain : ((X + 1 : ℕ) : ℝ) * (4 * h / (Nat.totient h * a ^ 2)) * Real.log X ^ 2 ≤
      8192 * R * X := by
    have hexp : ((X + 1 : ℕ) : ℝ) * (4 * h / (Nat.totient h * a ^ 2)) * Real.log X ^ 2 =
        4 * R * ((X : ℝ) + 1) * (Real.log X ^ 2 / a ^ 2) := by
      rw [hRdef]; push_cast; field_simp
    have hq : Real.log X ^ 2 / a ^ 2 ≤ 1024 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    rw [hexp]
    have : 0 ≤ 4 * R * ((X : ℝ) + 1) := by positivity
    calc 4 * R * ((X : ℝ) + 1) * (Real.log X ^ 2 / a ^ 2) ≤ 4 * R * ((X : ℝ) + 1) * 1024 := by
          gcongr
      _ ≤ 8192 * R * X := by
          have : R * 1 ≤ R * X := mul_le_mul_of_nonneg_left hX1 (by linarith)
          linarith
  have hlog0 : 0 ≤ Real.log X ^ 2 := sq_nonneg _
  calc (S.card : ℝ) * Real.log X ^ 2
      ≤ ((y + 1 : ℝ) + ((X + 1 : ℕ) * (4 * h / (Nat.totient h * a ^ 2)) + (y : ℝ) ^ 6)) *
          Real.log X ^ 2 := by
        gcongr; linarith
    _ = ((y : ℝ) + 1 + (y : ℝ) ^ 6) * Real.log X ^ 2 +
          ((X + 1 : ℕ) : ℝ) * (4 * h / (Nat.totient h * a ^ 2)) * Real.log X ^ 2 := by ring
    _ ≤ 3072 * X + 8192 * R * X := add_le_add hsmall hmain
    _ ≤ 20000 * R * X := by linarith

end Erdos385
