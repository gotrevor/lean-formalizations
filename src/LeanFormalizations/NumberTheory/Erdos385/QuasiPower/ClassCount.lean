/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Sieve
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385, phase E8: the per-class count through the minimal-prime expansion

Fix `s` mod `y#` and a set `A` of positions with `n − a` coprime to every prime `≤ y` (for
`n ≡ s`).  For bad `n` and `a ∈ A`, `n − a` is prime or has its least prime factor in `(y, a]`
(`bad_dichotomy`).  Expanding `∏_{a ∈ A} (∑_{p ∈ (y,a]} 1_{p ∣ n−a} + 1_{n−a avoids the pool})`
over the set `B` of positions using the first option and the primes `f(a)`, each term is a
large-sieve count with `E = {p ≤ y} ∪ f(B)` fixed residues and `|A \ B|` classes per pool prime.
If `diam A < y` then `f` is injective (`p > y` cannot divide `a − a'`), and

  `#bad_s · ∏_{p ≤ y}(p − 1) ≤ C (X + Q²) ∏_{a ∈ A} (ρ + ∑_{y < p ≤ a} 1/(p − 1))`

whenever `ρ^K e_K(pool) ≥ 1` for every `K ≤ |A|` (`class_count`).
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open LeanFormalizations.Erdos385 LeanFormalizations.Erdos385.Exceptional Finset

/-- **The dichotomy.**  For bad `n` and `n − a` coprime to the primes `≤ y`, either `n − a` is
prime or its least prime factor lies in `(y, a]`. -/
theorem bad_dichotomy {n a y : ℕ} (hn : 5 ≤ n) (hb : Bad n) (ha : 1 ≤ a) (han : a + 2 ≤ n)
    (hcop : ∀ p, p.Prime → p ≤ y → n % p ≠ a % p) :
    (∃ p ∈ (Ioc y a).filter Nat.Prime, n % p = a % p) ∨ (n - a).Prime := by
  by_cases hpr : (n - a).Prime
  · exact Or.inr hpr
  left
  have hcomp : Composite (n - a) := ⟨by omega, hpr⟩
  have hmin := (bad_iff_forall_sub hn).1 hb a ha (by omega) hcomp
  have hp : (n - a).minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : (n - a).minFac ∣ n - a := Nat.minFac_dvd _
  have hmod : n % (n - a).minFac = a % (n - a).minFac :=
    ((Nat.modEq_iff_dvd' (by omega)).2 hdvd).symm
  refine ⟨(n - a).minFac, mem_filter.2 ⟨mem_Ioc.2 ⟨?_, hmin⟩, hp⟩, hmod⟩
  by_contra hle
  exact hcop _ hp (by omega) hmod

/-- A prime `n − a` avoids every smaller prime modulus. -/
theorem mod_ne_of_prime_sub {n a q : ℕ} (hpr : (n - a).Prime) (hq : q.Prime) (haq : a < q)
    (hqn : q < n - a) : n % q ≠ a := by
  intro h
  have hdvd : q ∣ n - a := (Nat.modEq_iff_dvd' (by omega)).1 (by
    rw [Nat.ModEq, h, Nat.mod_eq_of_lt haq])
  rcases (Nat.dvd_prime hpr).1 hdvd with h1 | h1
  · exact hq.one_lt.ne' h1
  · omega

/-- The expansion `∏ (∑ w + v) = ∑_B ∑_f ∏_B w · ∏_{A∖B} v`. -/
theorem prod_expand (A : Finset ℕ) (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (v : ℕ → ℝ) :
    ∏ a ∈ A, (∑ p ∈ P a, w a p + v a) =
      ∑ B ∈ A.powerset, ∑ f ∈ B.pi P, (∏ x ∈ B.attach, w x.1 (f x.1 x.2)) * ∏ a ∈ A \ B, v a := by
  rw [prod_add]
  refine sum_congr rfl fun B _ => ?_
  rw [prod_sum, sum_mul]

open scoped Classical in
theorem class_count {C : ℝ} (h1 : LSWith C) (hC : 0 ≤ C) {X y Y Q R : ℕ} (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (s : ℕ) (A pool : Finset ℕ) (hyY : y ≤ Y) (hR : 1 ≤ R)
    (hA1 : ∀ a ∈ A, 1 ≤ a ∧ a ≤ Y)
    (hAy : ∀ a ∈ A, ∀ p, p.Prime → p ≤ y → s % p ≠ a % p)
    (hAdiam : ∀ a ∈ A, ∀ b ∈ A, b < a + y)
    (hpool : ∀ q ∈ pool, q.Prime ∧ Y < q ∧ q ≤ R)
    (hQ : primorial y * Y ^ A.card * R ^ A.card ≤ Q)
    (hw : ∀ K ≤ A.card, 1 ≤ ρ ^ K * poolWeight pool K K) :
    (((Icc 1 X).filter fun n => n % primorial y = s % primorial y ∧ R + Y < n ∧ 5 ≤ n ∧
        Bad n).card : ℝ) * ∏ p ∈ ps y, ((p : ℝ) - 1) ≤
      C * (X + (Q : ℝ) ^ 2) * ∏ a ∈ A, (ρ + ∑ p ∈ (Ioc y a).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
  classical
  set P := primorial y with hP
  set Pa : ℕ → Finset ℕ := fun a => (Ioc y a).filter Nat.Prime with hPa
  set W0 : ℝ := ∏ p ∈ ps y, ((p : ℝ) - 1) with hW0
  have hW0pos : 0 < W0 := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    linarith
  set Kc : ℝ := C * (X + (Q : ℝ) ^ 2) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set N := (Icc 1 X).filter fun n => n % P = s % P with hN
  set S := (Icc 1 X).filter fun n => n % P = s % P ∧ R + Y < n ∧ 5 ≤ n ∧ Bad n with hS
  set u : ℕ → ℕ → ℕ → ℝ := fun n a p => if n % p = a % p then 1 else 0 with hu
  set v : ℕ → ℕ → ℝ := fun n a => if ∀ q ∈ pool, n % q ≠ a then 1 else 0 with hv
  have hmodp : ∀ n, n % P = s % P → ∀ p, p.Prime → p ≤ y → n % p = s % p := by
    intro n hn p hp hpy
    have hd : p ∣ P := Finset.dvd_prod_of_mem _ (mem_filter.2 ⟨mem_range.2 (by omega), hp⟩)
    rw [← Nat.mod_mod_of_dvd n hd, hn, Nat.mod_mod_of_dvd s hd]
  -- Step 1: the indicator inequality
  have hstep1 : (S.card : ℝ) ≤ ∑ n ∈ N, ∏ a ∈ A, (∑ p ∈ Pa a, u n a p + v n a) := by
    have hnn : ∀ n, ∀ a, 0 ≤ ∑ p ∈ Pa a, u n a p + v n a := fun n a => by
      have : 0 ≤ ∑ p ∈ Pa a, u n a p := sum_nonneg fun p _ => by simp only [hu]; split_ifs <;> norm_num
      have : 0 ≤ v n a := by simp only [hv]; split_ifs <;> norm_num
      linarith
    calc (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, ∏ a ∈ A, (∑ p ∈ Pa a, u n a p + v n a) := by
          refine sum_le_sum fun n hn => ?_
          obtain ⟨hnI, hns, hnRY, hn5, hb⟩ := mem_filter.1 hn
          refine Finset.one_le_prod fun a ha => ?_
          obtain ⟨ha1, haY⟩ := hA1 a ha
          have hcop : ∀ p, p.Prime → p ≤ y → n % p ≠ a % p := fun p hp hpy => by
            rw [hmodp n hns p hp hpy]; exact hAy a ha p hp hpy
          rcases bad_dichotomy hn5 hb ha1 (by omega) hcop with ⟨p, hp, hpm⟩ | hpr
          · have h1 : u n a p ≤ ∑ p ∈ Pa a, u n a p :=
              single_le_sum (f := fun p => u n a p) (fun p _ => by
                simp only [hu]; split_ifs <;> norm_num) hp
            have h2 : u n a p = 1 := by simp only [hu]; rw [if_pos hpm]
            have h3 : 0 ≤ v n a := by simp only [hv]; split_ifs <;> norm_num
            linarith
          · have h2 : v n a = 1 := by
              simp only [hv]
              rw [if_pos]
              intro q hq
              obtain ⟨hqp, hYq, hqR⟩ := hpool q hq
              exact mod_ne_of_prime_sub hpr hqp (by omega) (by omega)
            have h1 : 0 ≤ ∑ p ∈ Pa a, u n a p := sum_nonneg fun p _ => by
              simp only [hu]; split_ifs <;> norm_num
            linarith
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => prod_nonneg fun a _ => hnn n a
          obtain ⟨hnI, hns, -⟩ := mem_filter.1 hn
          exact mem_filter.2 ⟨hnI, hns⟩
  -- Step 2: the per-term bound
  have hstep3 : ∀ B ∈ A.powerset, ∀ f ∈ B.pi Pa,
      ∑ n ∈ N, (∏ x ∈ B.attach, u n x.1 (f x.1 x.2)) * ∏ a ∈ A \ B, v n a ≤
        Kc / W0 * ((∏ x ∈ B.attach, 1 / ((f x.1 x.2 : ℝ) - 1)) * ∏ _a ∈ A \ B, ρ) := by
    intro B hB f hf
    have hBA : B ⊆ A := mem_powerset.1 hB
    have hfP : ∀ x (hx : x ∈ B), f x hx ∈ Pa x := fun x hx => mem_pi.1 hf x hx
    have hfprime : ∀ x (hx : x ∈ B), (f x hx).Prime := fun x hx => (mem_filter.1 (hfP x hx)).2
    have hfy : ∀ x (hx : x ∈ B), y < f x hx ∧ f x hx ≤ x := fun x hx =>
      mem_Ioc.1 (mem_filter.1 (hfP x hx)).1
    set T := N.filter fun n => (∀ x ∈ B.attach, n % f x.1 x.2 = x.1 % f x.1 x.2) ∧
      ∀ a ∈ A \ B, ∀ q ∈ pool, n % q ≠ a with hT
    have hsumT : ∑ n ∈ N, (∏ x ∈ B.attach, u n x.1 (f x.1 x.2)) * ∏ a ∈ A \ B, v n a =
        (T.card : ℝ) := by
      rw [hT, card_filter]
      push_cast
      refine sum_congr rfl fun n _ => ?_
      simp only [hu, hv]
      rw [prod_boole, prod_boole]
      by_cases h1 : ∀ x ∈ B.attach, n % f x.1 x.2 = x.1 % f x.1 x.2
      · by_cases h2 : ∀ a ∈ A \ B, ∀ q ∈ pool, n % q ≠ a
        · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
        · rw [if_neg h2, mul_zero, if_neg]; exact fun h => h2 h.2
      · rw [if_neg h1, zero_mul, if_neg]; exact fun h => h1 h.1
    rw [hsumT]
    have hRHS0 : 0 ≤ Kc / W0 * ((∏ x ∈ B.attach, 1 / ((f x.1 x.2 : ℝ) - 1)) * ∏ _a ∈ A \ B, ρ) := by
      refine mul_nonneg (div_nonneg hKc0 hW0pos.le) (mul_nonneg (prod_nonneg fun x _ => ?_)
        (prod_nonneg fun _ _ => hρ0))
      have : (2 : ℝ) ≤ f x.1 x.2 := by exact_mod_cast (hfprime x.1 x.2).two_le
      exact div_nonneg zero_le_one (by linarith)
    rcases T.eq_empty_or_nonempty with hTe | ⟨n0, hn0⟩
    · rw [hTe, card_empty]; simpa using hRHS0
    -- injectivity of `f` from a witness
    have hinj : ∀ x (hx : x ∈ B) x' (hx' : x' ∈ B), f x hx = f x' hx' → x = x' := by
      intro x hx x' hx' hff
      obtain ⟨-, hcong, -⟩ := mem_filter.1 hn0
      have h1 := hcong ⟨x, hx⟩ (mem_attach _ _)
      have h2 := hcong ⟨x', hx'⟩ (mem_attach _ _)
      simp only at h1 h2
      rw [hff] at h1
      have hxx : x % f x' hx' = x' % f x' hx' := h1.symm.trans h2
      have hy1 := (hfy x' hx').1
      have hd1 := hAdiam x (hBA hx) x' (hBA hx')
      have hd2 := hAdiam x' (hBA hx') x (hBA hx)
      rcases lt_trichotomy x x' with hlt | heq | hgt
      · have hdvd : f x' hx' ∣ x' - x := (Nat.modEq_iff_dvd' hlt.le).1 hxx
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · exact heq
      · have hdvd : f x' hx' ∣ x - x' := (Nat.modEq_iff_dvd' hgt.le).1 hxx.symm
        have := Nat.le_of_dvd (by omega) hdvd
        omega
    set img := B.attach.image fun x => f x.1 x.2 with himg
    have himg_inj : Set.InjOn (fun x : B => f x.1 x.2) (B.attach : Set B) := by
      intro x _ x' _ h
      exact Subtype.ext (hinj x.1 x.2 x'.1 x'.2 h)
    set E := ps y ∪ img with hE
    have hdisjE : Disjoint (ps y) img := by
      rw [disjoint_left]
      intro p hp hpi
      obtain ⟨x, -, rfl⟩ := mem_image.1 hpi
      have := mem_range.1 (mem_filter.1 hp).1
      have := (hfy x.1 x.2).1
      omega
    set c : ℕ → ℕ := fun p => if p ∈ ps y then s else
      if h : ∃ x ∈ B.attach, f x.1 x.2 = p then (Classical.choose h).1 else 0 with hc
    have hc_img : ∀ x ∈ B.attach, c (f x.1 x.2) = x.1 := by
      intro x hx
      have hnot : f x.1 x.2 ∉ ps y := fun h => disjoint_left.1 hdisjE h (mem_image_of_mem _ hx)
      have hex : ∃ x' ∈ B.attach, f x'.1 x'.2 = f x.1 x.2 := ⟨x, hx, rfl⟩
      simp only [hc, if_neg hnot, dif_pos hex]
      have := (Classical.choose_spec hex).2
      exact hinj _ _ _ _ this
    have hEprime : ∀ p ∈ E, p.Prime := by
      intro p hp
      rcases mem_union.1 hp with h | h
      · exact (mem_filter.1 h).2
      · obtain ⟨x, -, rfl⟩ := mem_image.1 h; exact hfprime x.1 x.2
    have hpoolE : ∀ q ∈ pool, q.Prime ∧ q ∉ E ∧ q ≤ R := by
      intro q hq
      obtain ⟨hqp, hYq, hqR⟩ := hpool q hq
      refine ⟨hqp, fun h => ?_, hqR⟩
      rcases mem_union.1 h with h | h
      · have := mem_range.1 (mem_filter.1 h).1; omega
      · obtain ⟨x, -, hx⟩ := mem_image.1 h
        have := (hfy x.1 x.2).2
        have := (hA1 x.1 (hBA x.2)).2
        omega
    have hAB : ∀ q ∈ pool, ∀ a ∈ A \ B, 1 ≤ a ∧ a < q := by
      intro q hq a ha
      have := hA1 a (mem_sdiff.1 ha).1
      have := (hpool q hq).2.1
      omega
    have hprodE : ∏ p ∈ E, p ≤ P * Y ^ A.card := by
      rw [hE, prod_union hdisjE, ← primorial_eq_prod_ps]
      apply Nat.mul_le_mul_left
      calc ∏ p ∈ img, p ≤ ∏ x ∈ B.attach, f x.1 x.2 := by
            rw [himg, prod_image himg_inj]
        _ ≤ ∏ _x ∈ B.attach, Y := prod_le_prod' fun x _ =>
            (hfy x.1 x.2).2.trans (hA1 x.1 (hBA x.2)).2
        _ = Y ^ B.card := by rw [prod_const, card_attach]
        _ ≤ Y ^ A.card := by
            rcases Nat.eq_zero_or_pos Y with hY0 | hY0
            · have hAe : A = ∅ := eq_empty_of_forall_notMem fun a ha => by
                have := hA1 a ha; omega
              have hBe : B = ∅ := subset_empty.1 (hAe ▸ hBA)
              simp [hAe, hBe]
            · exact Nat.pow_le_pow_right hY0 (card_le_card hBA)
    have hcardAB : (A \ B).card ≤ A.card := card_le_card sdiff_subset
    have hQ' : (∏ p ∈ E, p) * R ^ (A \ B).card ≤ Q := by
      calc (∏ p ∈ E, p) * R ^ (A \ B).card ≤ (P * Y ^ A.card) * R ^ A.card :=
            Nat.mul_le_mul hprodE (Nat.pow_le_pow_right hR hcardAB)
        _ ≤ Q := hQ
    have hsieve := sieve_count_gen h1 (X := X) (Q := Q) (R := R) (j := (A \ B).card) E c (A \ B)
      pool hEprime hpoolE hAB hQ'
    have hTsub : T ⊆ (Icc 1 X).filter fun n => (∀ p ∈ E, n % p = c p % p) ∧
        ∀ q ∈ pool, n % q ∉ A \ B := by
      intro n hn
      obtain ⟨hnN, hcong, havoid⟩ := mem_filter.1 hn
      obtain ⟨hnI, hns⟩ := mem_filter.1 hnN
      refine mem_filter.2 ⟨hnI, fun p hp => ?_, fun q hq ha => havoid _ ha q hq rfl⟩
      rcases mem_union.1 hp with h | h
      · have hpp := mem_filter.1 h
        have hpy : p ≤ y := by have := mem_range.1 hpp.1; omega
        simp only [hc, if_pos h]
        exact hmodp n hns p hpp.2 hpy
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
        rw [hc_img x hx]
        exact hcong x hx
    have hProdE : ∏ p ∈ E, ((p : ℝ) - 1) = W0 * ∏ x ∈ B.attach, ((f x.1 x.2 : ℝ) - 1) := by
      rw [hE, prod_union hdisjE, himg, prod_image himg_inj]
    have hpw := hw (A \ B).card hcardAB
    have hpw0 : 0 < poolWeight pool (A \ B).card (A \ B).card := by
      by_contra hneg
      push_neg at hneg
      have : ρ ^ (A \ B).card * poolWeight pool (A \ B).card (A \ B).card ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hρ0 _) hneg
      linarith
    have hfm : 0 < ∏ x ∈ B.attach, ((f x.1 x.2 : ℝ) - 1) := prod_pos fun x _ => by
      have : (2 : ℝ) ≤ f x.1 x.2 := by exact_mod_cast (hfprime x.1 x.2).two_le
      linarith
    set G := ∏ x ∈ B.attach, ((f x.1 x.2 : ℝ) - 1) with hG
    set pw := poolWeight pool (A \ B).card (A \ B).card with hpwdef
    set S' := (Icc 1 X).filter fun n => (∀ p ∈ E, n % p = c p % p) ∧
        ∀ q ∈ pool, n % q ∉ A \ B with hS'
    have hTS : (T.card : ℝ) ≤ S'.card := by exact_mod_cast card_le_card hTsub
    rw [hProdE] at hsieve
    have hS'le : (S'.card : ℝ) ≤ Kc / (W0 * G * pw) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h1pw : 1 / pw ≤ ρ ^ (A \ B).card := by
      rw [div_le_iff₀ hpw0]; linarith
    have hprod1 : ∏ x ∈ B.attach, 1 / ((f x.1 x.2 : ℝ) - 1) = 1 / G := by
      rw [hG, prod_div_distrib, prod_const_one]
    rw [hprod1, prod_const]
    calc (T.card : ℝ) ≤ Kc / (W0 * G * pw) := hTS.trans hS'le
      _ = Kc / W0 * (1 / G) * (1 / pw) := by field_simp
      _ ≤ Kc / W0 * (1 / G) * ρ ^ (A \ B).card := by
          gcongr
      _ = _ := by ring
  -- Step 3: assemble
  have hexp1 := prod_expand A Pa (fun a p => 1 / ((p : ℝ) - 1)) (fun _ => ρ)
  calc (S.card : ℝ) * W0 ≤ (∑ n ∈ N, ∏ a ∈ A, (∑ p ∈ Pa a, u n a p + v n a)) * W0 :=
        mul_le_mul_of_nonneg_right hstep1 hW0pos.le
    _ = (∑ B ∈ A.powerset, ∑ f ∈ B.pi Pa, ∑ n ∈ N,
          (∏ x ∈ B.attach, u n x.1 (f x.1 x.2)) * ∏ a ∈ A \ B, v n a) * W0 := by
        congr 1
        rw [sum_congr rfl fun n _ => prod_expand A Pa (u n) (v n), sum_comm]
        refine sum_congr rfl fun B _ => ?_
        rw [sum_comm]
    _ ≤ (∑ B ∈ A.powerset, ∑ f ∈ B.pi Pa,
          Kc / W0 * ((∏ x ∈ B.attach, 1 / ((f x.1 x.2 : ℝ) - 1)) * ∏ _a ∈ A \ B, ρ)) * W0 := by
        gcongr with B hB f hf
        exact hstep3 B hB f hf
    _ = Kc * ∏ a ∈ A, (ρ + ∑ p ∈ Pa a, 1 / ((p : ℝ) - 1)) := by
        simp_rw [← mul_sum]
        rw [show ∏ a ∈ A, (ρ + ∑ p ∈ Pa a, 1 / ((p : ℝ) - 1)) =
            ∏ a ∈ A, (∑ p ∈ Pa a, 1 / ((p : ℝ) - 1) + ρ) from prod_congr rfl fun _ _ => add_comm _ _,
          hexp1]
        field_simp
