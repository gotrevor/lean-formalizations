/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 E2b: multiplicative sums over squarefree numbers

`prodPF f n = ∏_{p ∣ n} f p`, and the decoupling inequality
`∑_{a ∈ S} F a ≤ (∑_{d ∣ m, d sqfree} F d) · ∑_{a ∈ S, (a,m)=1} F a`.
-/

namespace Erdos385.Brun

open Finset

/-- `∏_{p ∣ n} f p`. -/
noncomputable def prodPF (f : ℕ → ℝ) (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, f p

lemma prodPF_mul (f : ℕ → ℝ) {a b : ℕ} (h : Nat.Coprime a b) :
    prodPF f (a * b) = prodPF f a * prodPF f b := by
  unfold prodPF; rw [Nat.Coprime.primeFactors_mul h, prod_union h.disjoint_primeFactors]

lemma prodPF_nonneg {f : ℕ → ℝ} (hf : ∀ p, p.Prime → 0 ≤ f p) (n : ℕ) : 0 ≤ prodPF f n :=
  prod_nonneg fun p hp => hf p (Nat.prime_of_mem_primeFactors hp)

lemma prodPF_prod_finset (f : ℕ → ℝ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    prodPF f (∏ p ∈ T, p) = ∏ p ∈ T, f p := by
  unfold prodPF; rw [Nat.primeFactors_prod hT]

lemma sum_sqfree_divisors_prodPF (f : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors with Squarefree d, prodPF f d = ∏ p ∈ m.primeFactors, (1 + f p) := by
  rw [Nat.sum_divisors_filter_squarefree hm, prod_one_add, Nat.factors_eq]
  change ∑ i ∈ m.primeFactors.powerset, _ = _
  refine sum_congr rfl fun T hT => ?_
  rw [show T.val.prod = ∏ p ∈ T, p by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']]
  exact prodPF_prod_finset f T fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)

/-- Decoupling: split `a = gcd(a,m) · (a / gcd(a,m))`. -/
lemma sum_le_sum_sqfree_divisors_mul_sum_coprime {f : ℕ → ℝ} (hf : ∀ p, p.Prime → 0 ≤ f p)
    (S : Finset ℕ) (hS : ∀ a ∈ S, Squarefree a) (hcl : ∀ a ∈ S, ∀ d, d ∣ a → a / d ∈ S)
    {m : ℕ} (hm : m ≠ 0) :
    ∑ a ∈ S, prodPF f a ≤
      (∑ d ∈ m.divisors with Squarefree d, prodPF f d) *
        ∑ a ∈ S with Nat.Coprime a m, prodPF f a := by
  classical
  set φ : ℕ → ℕ × ℕ := fun a => (Nat.gcd a m, a / Nat.gcd a m) with hφ
  have hsplit : ∀ a ∈ S, prodPF f a = prodPF f (φ a).1 * prodPF f (φ a).2 := by
    intro a ha
    have hmul : Nat.gcd a m * (a / Nat.gcd a m) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a m)
    have hc : Nat.Coprime (Nat.gcd a m) (a / Nat.gcd a m) :=
      Nat.coprime_of_squarefree_mul (hmul.symm ▸ hS a ha)
    simp only [hφ]
    rw [← prodPF_mul f hc, hmul]
  have hinj : Set.InjOn φ S := by
    intro a _ b _ hab
    have h1 := congrArg (fun x : ℕ × ℕ => x.1 * x.2) hab
    simp only [hφ] at h1
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left a m),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left b m)] at h1
  have hsub : S.image φ ⊆ (m.divisors.filter Squarefree) ×ˢ (S.filter (Nat.Coprime · m)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    have hmul : Nat.gcd a m * (a / Nat.gcd a m) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a m)
    have hsq := hS a ha
    have hc : Nat.Coprime (Nat.gcd a m) (a / Nat.gcd a m) :=
      Nat.coprime_of_squarefree_mul (hmul.symm ▸ hsq)
    simp only [hφ, mem_product, mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨Nat.gcd_dvd_right a m, hm⟩, hsq.squarefree_of_dvd (Nat.gcd_dvd_left a m)⟩,
      hcl a ha _ (Nat.gcd_dvd_left a m), ?_⟩
    have hpos : 0 < Nat.gcd a m := Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hm)
    have h2 : Nat.Coprime (a / Nat.gcd a m) (m / Nat.gcd a m) :=
      Nat.coprime_div_gcd_div_gcd hpos |>.coprime_dvd_left (dvd_refl _)
    have := Nat.Coprime.mul_right hc.symm h2
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right a m)] at this
  calc ∑ a ∈ S, prodPF f a = ∑ a ∈ S, prodPF f (φ a).1 * prodPF f (φ a).2 :=
        sum_congr rfl hsplit
    _ = ∑ x ∈ S.image φ, prodPF f x.1 * prodPF f x.2 := (sum_image (f := fun x => prodPF f x.1 * prodPF f x.2) hinj).symm
    _ ≤ ∑ x ∈ (m.divisors.filter Squarefree) ×ˢ (S.filter (Nat.Coprime · m)),
          prodPF f x.1 * prodPF f x.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          mul_nonneg (prodPF_nonneg hf _) (prodPF_nonneg hf _)
    _ = _ := by rw [sum_mul_sum, sum_product]

lemma div_prod_of_squarefree_eq {l : ℕ} (hl : Squarefree l) (T : Finset ℕ)
    (hT : T ⊆ l.primeFactors) : l / ∏ p ∈ T, p = ∏ p ∈ l.primeFactors \ T, p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hl, ← prod_sdiff hT]
  have hpos : 0 < ∏ p ∈ T, p :=
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hT hp)).pos
  rw [Nat.mul_div_cancel _ hpos]

/-- For squarefree `l`, `∑_{ab = l} F(a) G(b) = ∏_{p ∣ l} (f p + g p)`. -/
lemma sum_antidiag_prodPF (f g : ℕ → ℝ) {l : ℕ} (hl : Squarefree l) :
    ∑ x ∈ l.divisorsAntidiagonal, prodPF f x.1 * prodPF g x.2 =
      ∏ p ∈ l.primeFactors, (f p + g p) := by
  rw [Nat.sum_divisorsAntidiagonal (fun a b => prodPF f a * prodPF g b),
    ← Nat.divisors_filter_squarefree_of_squarefree hl,
    Nat.sum_divisors_filter_squarefree hl.ne_zero, prod_add, Nat.factors_eq]
  change ∑ i ∈ l.primeFactors.powerset, _ = _
  refine sum_congr rfl fun T hT => ?_
  have hT' := mem_powerset.mp hT
  rw [show T.val.prod = ∏ p ∈ T, p by rw [Finset.prod_eq_multiset_prod, Multiset.map_id'],
    div_prod_of_squarefree_eq hl T hT',
    prodPF_prod_finset f T fun p hp => Nat.prime_of_mem_primeFactors (hT' hp),
    prodPF_prod_finset g _ fun p hp => Nat.prime_of_mem_primeFactors (sdiff_subset hp)]

lemma prodPF_inv_of_squarefree {a : ℕ} (ha : Squarefree a) :
    prodPF (fun p => 1 / (p : ℝ)) a = 1 / (a : ℝ) := by
  unfold prodPF
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree ha]
  push_cast
  rw [prod_div_distrib, prod_const_one]

/-- `∑_{a ≤ t, a squarefree} 1/a ≥ (log t)/2`. -/
lemma half_log_le_sum_sqfree_inv (t : ℕ) :
    Real.log t / 2 ≤ ∑ a ∈ (Icc 1 t).filter Squarefree, 1 / (a : ℝ) := by
  classical
  set A := (Icc 1 t).filter Squarefree
  have hH : Real.log t ≤ ∑ n ∈ Icc 1 t, 1 / (n : ℝ) := by
    have := log_le_harmonic_floor (t : ℝ) (Nat.cast_nonneg t)
    rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at this
    simpa using this
  choose α β hαβ hα using fun n : ℕ => Nat.sq_mul_squarefree n
  have hmapsub : (Icc 1 t).image (fun n => (α n, β n)) ⊆ A ×ˢ Icc 1 t := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    obtain ⟨hn1, hnt⟩ := mem_Icc.mp hn
    have he := hαβ n
    have hα0 : α n ≠ 0 := by rintro h; rw [h] at he; omega
    have hβ0 : β n ≠ 0 := by rintro h; rw [h] at he; simp at he; omega
    have hαle : α n ≤ n := by
      have := Nat.le_mul_of_pos_left (α n) (pow_pos (Nat.pos_of_ne_zero hβ0) 2)
      rwa [he] at this
    have hβle : β n ≤ n := by
      have : β n ≤ β n ^ 2 * α n := by
        calc β n ≤ β n ^ 2 := by nlinarith [Nat.pos_of_ne_zero hβ0]
          _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hα0)
      omega
    simp only [A, mem_product, mem_filter, mem_Icc]
    exact ⟨⟨⟨Nat.pos_of_ne_zero hα0, hαle.trans hnt⟩, hα n⟩, Nat.pos_of_ne_zero hβ0, hβle.trans hnt⟩
  have hinj : Set.InjOn (fun n => (α n, β n)) (Icc 1 t) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    rw [← hαβ a, ← hαβ b, hab.1, hab.2]
  have hval : ∀ n ∈ Icc 1 t, 1 / (n : ℝ) = 1 / (α n : ℝ) * (1 / ((β n : ℝ) ^ 2)) := by
    intro n _
    conv_lhs => rw [← hαβ n]
    push_cast; field_simp
  have hsq : ∑ b ∈ Icc 1 t, 1 / ((b : ℝ) ^ 2) ≤ 2 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (t + 1)
    have hI : Ioo 0 (t + 1) = Icc 1 t := by ext; simp [mem_Ioo, mem_Icc]; omega
    rw [hI] at this
    simpa using this
  have hA0 : 0 ≤ ∑ a ∈ A, 1 / (a : ℝ) := sum_nonneg fun _ _ => by positivity
  have key : ∑ n ∈ Icc 1 t, 1 / (n : ℝ) ≤ (∑ a ∈ A, 1 / (a : ℝ)) * 2 := by
    calc ∑ n ∈ Icc 1 t, 1 / (n : ℝ)
        = ∑ n ∈ Icc 1 t, (fun x : ℕ × ℕ => 1 / (x.1 : ℝ) * (1 / ((x.2 : ℝ) ^ 2))) (α n, β n) :=
          sum_congr rfl hval
      _ = ∑ x ∈ (Icc 1 t).image (fun n => (α n, β n)), 1 / (x.1 : ℝ) * (1 / ((x.2 : ℝ) ^ 2)) :=
          (sum_image (f := fun x : ℕ × ℕ => 1 / (x.1 : ℝ) * (1 / ((x.2 : ℝ) ^ 2))) hinj).symm
      _ ≤ ∑ x ∈ A ×ˢ Icc 1 t, 1 / (x.1 : ℝ) * (1 / ((x.2 : ℝ) ^ 2)) :=
          sum_le_sum_of_subset_of_nonneg hmapsub fun _ _ _ => by positivity
      _ = (∑ a ∈ A, 1 / (a : ℝ)) * ∑ b ∈ Icc 1 t, 1 / ((b : ℝ) ^ 2) := by
          rw [sum_mul_sum, sum_product]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq hA0
  linarith

/-- Selberg terms `g(p) = ν(p)/(1 − ν(p))` for the prime-pair sieve with gap `h`. -/
noncomputable def gS (h p : ℕ) : ℝ := if p ∣ h then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)
/-- `1/(p − 1)`. -/
noncomputable def g1 (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)
/-- `1/(p − 1)` on primes not dividing `h`. -/
noncomputable def g2 (h p : ℕ) : ℝ := if p ∣ h then 0 else 1 / ((p : ℝ) - 1)
/-- `1/p` on primes not dividing `h`. -/
noncomputable def g2' (h p : ℕ) : ℝ := if p ∣ h then 0 else 1 / (p : ℝ)
/-- `1/p`. -/
noncomputable def ginv (p : ℕ) : ℝ := 1 / (p : ℝ)

lemma g1_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ g1 p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold g1; apply div_nonneg <;> linarith

lemma g2_nonneg (h : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ g2 h p := by
  unfold g2; split_ifs
  · exact le_rfl
  · exact g1_nonneg hp

lemma g2'_nonneg (h : ℕ) (p : ℕ) : 0 ≤ g2' h p := by
  unfold g2'; split_ifs <;> positivity

lemma ginv_nonneg (p : ℕ) : 0 ≤ ginv p := by unfold ginv; positivity

lemma g1_add_g2_le_gS {h : ℕ} (h2 : 2 ∣ h) {p : ℕ} (hp : p.Prime) : g1 p + g2 h p ≤ gS h p := by
  unfold g1 g2 gS
  split_ifs with hph
  · simp
  · have hp2 : p ≠ 2 := by rintro rfl; exact hph h2
    have : (3 : ℝ) ≤ p := by
      have := hp.two_le; exact_mod_cast (show 3 ≤ p by omega)
    rw [← add_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

lemma ginv_le_g1 {p : ℕ} (hp : p.Prime) : ginv p ≤ g1 p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold ginv g1
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma sqfree_div_mem {t a d : ℕ} (ha : a ∈ (Icc 1 t).filter Squarefree) (hd : d ∣ a) :
    a / d ∈ (Icc 1 t).filter Squarefree := by
  simp only [mem_filter, mem_Icc] at ha ⊢
  obtain ⟨⟨h1, ht⟩, hsq⟩ := ha
  refine ⟨⟨Nat.div_pos (Nat.le_of_dvd h1 hd) (Nat.pos_of_dvd_of_pos hd h1),
    (Nat.div_le_self a d).trans ht⟩, hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)⟩

lemma prod_one_add_inv_le (h : ℕ) :
    (Nat.totient h : ℝ) * ∏ p ∈ h.primeFactors, (1 + ginv p) ≤ h := by
  have key := Nat.totient_mul_prod_primeFactors h
  have hkey : (Nat.totient h : ℝ) * ∏ p ∈ h.primeFactors, (p : ℝ) =
      (h : ℝ) * ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    push_cast at this
    rw [this]; congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  have hpos : 0 < ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hle : (∏ p ∈ h.primeFactors, (1 + ginv p)) * ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) ≤
      ∏ p ∈ h.primeFactors, (p : ℝ) := by
    rw [← prod_mul_distrib]
    refine prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      unfold ginv; apply mul_nonneg <;> [positivity; linarith]
    · have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      unfold ginv
      rw [add_mul, one_div_mul_eq_div, div_eq_mul_inv]
      have : ((p : ℝ) - 1) * (p : ℝ)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
      linarith
  have htot0 : (0 : ℝ) ≤ Nat.totient h := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hle htot0
  rw [← mul_assoc, hkey] at this
  exact le_of_mul_le_mul_right this hpos

/-- **The `G(z)` lower bound.**  For even `h ≠ 0` and `t² ≤ y`,
`∑_{l ≤ y sqfree} ∏_{p ∣ l} g(p) ≥ (φ(h)/h) (log t)² / 4`. -/
theorem G_lower {h : ℕ} (h2 : 2 ∣ h) (hh : h ≠ 0) {t y : ℕ} (hty : t * t ≤ y) :
    (Nat.totient h : ℝ) / h * Real.log t ^ 2 / 4 ≤
      ∑ l ∈ (Icc 1 y).filter Squarefree, prodPF (gS h) l := by
  classical
  set A := (Icc 1 t).filter Squarefree with hA
  set L := (Icc 1 y).filter Squarefree with hL
  set F : ℕ × ℕ → ℝ := fun x => prodPF g1 x.1 * prodPF (g2 h) x.2 with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x =>
    mul_nonneg (prodPF_nonneg (fun p hp => g1_nonneg hp) _)
      (prodPF_nonneg (fun p hp => g2_nonneg h hp) _)
  -- Step 1: pointwise `∑_{ab=l} g₁(a) g₂(b) ≤ g(l)`.
  have step1 : ∀ l ∈ L, ∑ x ∈ l.divisorsAntidiagonal, F x ≤ prodPF (gS h) l := by
    intro l hl
    have hsq : Squarefree l := (mem_filter.mp hl).2
    rw [sum_antidiag_prodPF g1 (g2 h) hsq]
    exact prod_le_prod (fun p hp => add_nonneg (g1_nonneg (Nat.prime_of_mem_primeFactors hp))
      (g2_nonneg h (Nat.prime_of_mem_primeFactors hp)))
      (fun p hp => g1_add_g2_le_gS h2 (Nat.prime_of_mem_primeFactors hp))
  -- Step 2: coprime pairs of `A` inject into the antidiagonals.
  set Pairs := (A ×ˢ A).filter (fun x => Nat.Coprime x.1 x.2) with hPairs
  have hmaps : ∀ x ∈ Pairs, x.1 * x.2 ∈ L := by
    intro x hx
    simp only [hPairs, hA, hL, mem_filter, mem_product, mem_Icc] at hx ⊢
    obtain ⟨⟨⟨⟨a1, at'⟩, asq⟩, ⟨⟨b1, bt⟩, bsq⟩⟩, hc⟩ := hx
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), (Nat.mul_le_mul at' bt).trans hty⟩,
      Nat.squarefree_mul_iff.mpr ⟨hc, asq, bsq⟩⟩
  have step2 : ∑ x ∈ Pairs, F x ≤ ∑ l ∈ L, prodPF (gS h) l := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_le_sum fun l hl => le_trans ?_ (step1 l hl)
    refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hF0 x)
    simp only [mem_filter] at hx
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hx.2, by have := (mem_filter.mp hl).1; simp only [mem_Icc] at this; omega⟩
  -- Step 3: factor the pair sum.
  have step3 : ∑ x ∈ Pairs, F x =
      ∑ b ∈ A, prodPF (g2 h) b * ∑ a ∈ A.filter (Nat.Coprime · b), prodPF g1 a := by
    rw [hPairs, sum_filter, sum_product_right]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum, Finset.sum_filter (p := fun a => Nat.Coprime a b)]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hF, mul_comm]
  have hAsq : ∀ a ∈ A, Squarefree a := fun a ha => (mem_filter.mp ha).2
  have hAcl : ∀ a ∈ A, ∀ d, d ∣ a → a / d ∈ A := fun a ha d hd => sqfree_div_mem ha hd
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => by
    have := (mem_filter.mp ha).1; simp only [mem_Icc] at this; omega
  set K := ∑ a ∈ A, prodPF g1 a with hK
  set S := ∑ a ∈ A, prodPF ginv a with hSdef
  -- Step 4: decouple `(a, b) = 1` at the cost `∏_{p ∣ b} (1 + g₁(p))`.
  have step4 : ∀ b ∈ A, prodPF (g2' h) b * K ≤
      prodPF (g2 h) b * ∑ a ∈ A.filter (Nat.Coprime · b), prodPF g1 a := by
    intro b hb
    have hdec := sum_le_sum_sqfree_divisors_mul_sum_coprime (fun p hp => g1_nonneg hp) A hAsq
      hAcl (hA0 b hb)
    rw [sum_sqfree_divisors_prodPF g1 (hA0 b hb)] at hdec
    have hfac : prodPF (g2 h) b = prodPF (g2' h) b * ∏ p ∈ b.primeFactors, (1 + g1 p) := by
      unfold prodPF; rw [← prod_mul_distrib]; refine prod_congr rfl fun p hp => ?_
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) ≠ 0 := by linarith
      unfold g2 g2' g1; split_ifs
      · simp
      · field_simp; ring
    rw [hfac, mul_assoc]
    exact mul_le_mul_of_nonneg_left hdec (prodPF_nonneg (fun p _ => g2'_nonneg h p) b)
  -- Step 5: the `h/φ(h)` loss.
  have hg2' : ∀ b, b ≠ 0 → prodPF (g2' h) b = if Nat.Coprime b h then prodPF ginv b else 0 := by
    intro b hb0; split_ifs with hc
    · unfold prodPF; refine prod_congr rfl fun p hp => ?_
      have hp' := Nat.prime_of_mem_primeFactors hp
      have : ¬ p ∣ h := (Nat.Prime.coprime_iff_not_dvd hp').mp
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc)
      unfold g2' ginv; rw [if_neg this]
    · obtain ⟨p, hp, hpb, hph⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      unfold prodPF
      exact prod_eq_zero (i := p) (Nat.mem_primeFactors.mpr ⟨hp, hpb, hb0⟩) (by unfold g2'; simp [hph])
  have step5 : (Nat.totient h : ℝ) / h * S ≤ ∑ b ∈ A, prodPF (g2' h) b := by
    rw [sum_congr rfl (fun b hb => hg2' b (hA0 b hb)), ← sum_filter]
    have hdec := sum_le_sum_sqfree_divisors_mul_sum_coprime (fun p _ => ginv_nonneg p) A hAsq
      hAcl hh
    rw [sum_sqfree_divisors_prodPF ginv hh] at hdec
    have hprod := prod_one_add_inv_le h
    have hT0 : 0 ≤ ∑ a ∈ A.filter (Nat.Coprime · h), prodPF ginv a :=
      sum_nonneg fun a _ => prodPF_nonneg (fun p _ => ginv_nonneg p) a
    have hh' : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh
    calc (Nat.totient h : ℝ) / h * S
        ≤ (Nat.totient h : ℝ) / h * ((∏ p ∈ h.primeFactors, (1 + ginv p)) *
            ∑ a ∈ A.filter (Nat.Coprime · h), prodPF ginv a) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = (Nat.totient h : ℝ) * (∏ p ∈ h.primeFactors, (1 + ginv p)) / h *
            ∑ a ∈ A.filter (Nat.Coprime · h), prodPF ginv a := by ring
      _ ≤ (h : ℝ) / h * ∑ a ∈ A.filter (Nat.Coprime · h), prodPF ginv a :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hprod hh'.le) hT0
      _ = _ := by rw [div_self hh'.ne', one_mul]
  -- Step 6: `K ≥ S ≥ (log t)/2`.
  have hS : Real.log t / 2 ≤ S := by
    refine (half_log_le_sum_sqfree_inv t).trans (le_of_eq (sum_congr rfl fun a ha => ?_))
    exact (prodPF_inv_of_squarefree (hAsq a ha)).symm
  have hKS : S ≤ K := sum_le_sum fun a _ =>
    prod_le_prod (fun p _ => ginv_nonneg p) (fun p hp => ginv_le_g1 (Nat.prime_of_mem_primeFactors hp))
  have hlog0 : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hφh : (0 : ℝ) ≤ (Nat.totient h : ℝ) / h := by positivity
  have hK0 : 0 ≤ K := by linarith
  calc (Nat.totient h : ℝ) / h * Real.log t ^ 2 / 4
      = (Nat.totient h : ℝ) / h * (Real.log t / 2) * (Real.log t / 2) := by ring
    _ ≤ (Nat.totient h : ℝ) / h * S * K :=
        mul_le_mul (mul_le_mul_of_nonneg_left hS hφh) (hS.trans hKS) (by positivity)
          (mul_nonneg hφh (by linarith))
    _ ≤ (∑ b ∈ A, prodPF (g2' h) b) * K := mul_le_mul_of_nonneg_right step5 hK0
    _ = ∑ b ∈ A, prodPF (g2' h) b * K := sum_mul _ _ _
    _ ≤ _ := sum_le_sum step4
    _ = ∑ x ∈ Pairs, F x := step3.symm
    _ ≤ _ := step2

end Erdos385.Brun
