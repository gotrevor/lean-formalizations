/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Montgomery's lemma (phase E4c)

For a finite set `S` of naturals avoiding the classes `Ω p` modulo every prime `p ≤ Q`, and any
weights `w`, `‖Σ_{n∈S} w n‖² · h(q) ≤ Σ*_{a mod q} |Σ_{n∈S} w n e(na/q)|²` for squarefree `q`
with prime factors `≤ Q`, where `h(q) = ∏_{p∣q} ω(p)/(p − ω(p))`.

Prime case: Parseval over residues plus Cauchy–Schwarz on the `p − ω(p)` allowed classes.
General case: induction peeling off `p = minFac q`, applying the prime case to the twisted weights
`w n e(n a₁/q₁)` (still supported on `S`), and the injective CRT map `(a₁, a₂) ↦ a₁p + a₂q₁ mod q`.
-/

namespace LeanFormalizations.Erdos385.LargeSieve

open Complex Finset


noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_int (k : ℤ) : ee k = 1 := by
  unfold ee; rw [show (2 * Real.pi * I * ((k:ℝ):ℂ)) = k * (2 * Real.pi * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma ee_nat (k : ℕ) : ee k = 1 := by exact_mod_cast ee_int k

lemma ee_add_int (x : ℝ) (k : ℤ) : ee (x + k) = ee x := by rw [ee_add, ee_int, mul_one]

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee; rw [show (2 * Real.pi * I * (x:ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1; simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma ee_neg_mul (x : ℝ) : ee x * ee (-x) = 1 := by rw [← ee_add, add_neg_cancel]; simpa using ee_nat 0

/-- Orthogonality: `Σ_{a<q} e(ka/q) = q·[q ∣ k]`. -/
lemma sum_ee_div (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ a ∈ range q, ee (k * a / q) = if (q:ℤ) ∣ k then (q:ℂ) else 0 := by
  have hz : ∀ a : ℕ, ee (k * a / q) = (ee (k / q)) ^ a := by
    intro a; unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  simp_rw [hz]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have : ee (((q:ℤ) * m : ℤ) / q) = 1 := by
      rw [show ((((q:ℤ) * m : ℤ)) : ℝ) / q = (m:ℤ) by push_cast; field_simp]; exact ee_int m
    rw [this]; simp
  · have hne : ee (k / q) ≠ 1 := by
      intro h1
      unfold ee at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply h; refine ⟨n, ?_⟩
      have h2 : (((k:ℝ) / q : ℝ) : ℂ) = n := by
        have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
        apply mul_left_cancel₀ hpi; rw [hn]; ring
      have h3 : (k:ℝ) / q = n := by exact_mod_cast h2
      have hq' : (q:ℝ) ≠ 0 := by positivity
      have : (k:ℝ) = q * n := by field_simp at h3; linarith
      exact_mod_cast this
    have hpow : (ee (k / q)) ^ q = 1 := by
      rw [← hz q] ; rw [show (k:ℝ) * (q:ℕ) / q = (k:ℤ) by field_simp]; exact ee_int k
    rw [geom_sum_eq hne, hpow]; simp

noncomputable def expSum (S : Finset ℕ) (w : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ S, w n * ee (n * x)

lemma normSq_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Parseval over residues mod `q`. -/
lemma sum_norm_expSum_sq (S : Finset ℕ) (w : ℕ → ℂ) (q : ℕ) (hq : 0 < q) :
    ∑ a ∈ range q, ‖expSum S w (a / q)‖ ^ 2
      = q * ∑ h ∈ range q, ‖∑ n ∈ S with n % q = h, w n‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow, normSq_eq_mul_conj]
  have key : ∀ n m : ℕ, ∑ a ∈ range q, ee (n * (a / q : ℝ)) * (starRingEnd ℂ) (ee (m * (a / q : ℝ)))
      = if n % q = m % q then (q:ℂ) else 0 := by
    intro n m
    have := sum_ee_div q hq ((n:ℤ) - m)
    have e : ∀ a : ℕ, ee (n * (a / q : ℝ)) * (starRingEnd ℂ) (ee (m * (a / q : ℝ)))
        = ee ((((n:ℤ) - m : ℤ) : ℝ) * a / q) := by
      intro a; rw [conj_ee, ← ee_add]; congr 1; push_cast; ring
    simp_rw [e, this]
    have hiff : ((q:ℤ) ∣ (n:ℤ) - m) ↔ n % q = m % q := by
      rw [← Nat.modEq_iff_dvd]; exact eq_comm
    simp only [hiff]
  have lhs : ∑ a ∈ range q, expSum S w (a / q) * (starRingEnd ℂ) (expSum S w (a / q))
      = ∑ n ∈ S, ∑ m ∈ S, w n * (starRingEnd ℂ) (w m) * (if n % q = m % q then (q:ℂ) else 0) := by
    simp_rw [← key, expSum, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have rhs : ∑ h ∈ range q, (∑ n ∈ S with n % q = h, w n) * (starRingEnd ℂ) (∑ n ∈ S with n % q = h, w n)
      = ∑ n ∈ S, ∑ m ∈ S, w n * (starRingEnd ℂ) (w m) * (if n % q = m % q then 1 else 0) := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_ite_eq (range q) (n % q), if_pos (Finset.mem_range.2 (Nat.mod_lt _ hq))]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : m % q = n % q
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  rw [lhs, rhs, Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

lemma expSum_zero (S : Finset ℕ) (w : ℕ → ℂ) : expSum S w 0 = ∑ n ∈ S, w n := by
  simp [expSum, ee]

/-- Montgomery's lemma at a prime. -/
lemma montgomery_prime (S : Finset ℕ) (w : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (Ω : Finset ℕ)
    (hΩ : Ω ⊆ range p) (hc : Ω.card < p) (hS : ∀ n ∈ S, n % p ∉ Ω) :
    ‖∑ n ∈ S, w n‖ ^ 2 * ((Ω.card : ℝ) / ((p : ℝ) - Ω.card))
      ≤ ∑ a ∈ range p with Nat.Coprime a p, ‖expSum S w (a / p)‖ ^ 2 := by
  have hp0 := hp.pos
  set Z : ℕ → ℂ := fun h => ∑ n ∈ S with n % p = h, w n with hZ
  have hall := sum_norm_expSum_sq S w p hp0
  have hsplit := Finset.sum_filter_add_sum_filter_not (range p) (fun a => Nat.Coprime a p)
    (fun a => ‖expSum S w (a / p)‖ ^ 2)
  have h0 : (range p).filter (fun a => ¬ Nat.Coprime a p) = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hn⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not] at hn
      by_contra h0; exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hn) (by omega)
    · rintro rfl; exact ⟨hp0, by simp [hp.one_lt.ne']⟩
  rw [h0, Finset.sum_singleton] at hsplit
  simp only [Nat.cast_zero, zero_div, expSum_zero] at hsplit
  -- Cauchy–Schwarz over the allowed classes
  have hsumZ : ∑ n ∈ S, w n = ∑ h ∈ range p \ Ω, Z h := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := range p)
      (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hp0))]
    rw [← Finset.sum_sdiff hΩ, Finset.sum_eq_zero (s := Ω), add_zero]
    intro h hh
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    exact absurd (hn.2 ▸ hh) (hS n hn.1)
  have hcard : ((range p \ Ω).card : ℝ) = p - Ω.card := by
    rw [Finset.card_sdiff_of_subset hΩ, Finset.card_range, Nat.cast_sub hc.le]
  have hCS : ‖∑ n ∈ S, w n‖ ^ 2 ≤ ((p:ℝ) - Ω.card) * ∑ h ∈ range p, ‖Z h‖ ^ 2 := by
    rw [hsumZ]
    calc ‖∑ h ∈ range p \ Ω, Z h‖ ^ 2 ≤ (∑ h ∈ range p \ Ω, ‖Z h‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (range p \ Ω).card * ∑ h ∈ range p \ Ω, ‖Z h‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ ((p:ℝ) - Ω.card) * ∑ h ∈ range p, ‖Z h‖ ^ 2 := by
          rw [hcard]
          have : (0:ℝ) ≤ p - Ω.card := by
            have : (Ω.card : ℝ) < p := by exact_mod_cast hc
            linarith
          gcongr
          · exact Finset.sdiff_subset
  have hd : (0:ℝ) < p - Ω.card := by
    have : (Ω.card : ℝ) < p := by exact_mod_cast hc
    linarith
  set X := ‖∑ n ∈ S, w n‖ ^ 2
  set Y := ∑ h ∈ range p, ‖Z h‖ ^ 2
  have hgoal : ∑ a ∈ range p with Nat.Coprime a p, ‖expSum S w (a / p)‖ ^ 2 = p * Y - X := by
    linarith
  rw [hgoal, mul_div_assoc', div_le_iff₀ hd]
  nlinarith

/-- The sieve density `h(q) = ∏_{p ∣ q} ω(p)/(p − ω(p))`. -/
noncomputable def sieveH (Ω : ℕ → Finset ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)

lemma expSum_mod (S : Finset ℕ) (w : ℕ → ℂ) (m q : ℕ) :
    expSum S w ((m % q : ℕ) / q) = expSum S w (m / q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  unfold expSum; refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hm : (m : ℝ) = (m % q : ℕ) + q * (m / q : ℕ) := by exact_mod_cast (Nat.mod_add_div m q).symm
  have hq' : (q:ℝ) ≠ 0 := by positivity
  generalize m % q = r at hm ⊢
  generalize m / q = k at hm ⊢
  rw [show (n:ℝ) * (m / q) = n * (r / q) + ((n * k : ℕ) : ℤ) by
    rw [hm]; push_cast; field_simp, ee_add_int]

lemma expSum_shift (S : Finset ℕ) (w : ℕ → ℂ) (x y : ℝ) :
    expSum S w (x + y) = expSum S (fun n => w n * ee (n * x)) y := by
  unfold expSum; refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_add, ee_add]; ring

/-- **Montgomery's lemma** for squarefree moduli. -/
theorem montgomery (S : Finset ℕ) (Ω : ℕ → Finset ℕ) (Q : ℕ)
    (hΩ : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ range p ∧ (Ω p).card < p)
    (hS : ∀ n ∈ S, ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) :
    ∀ q, Squarefree q → (∀ p ∈ q.primeFactors, p ≤ Q) → ∀ w : ℕ → ℂ,
      ‖∑ n ∈ S, w n‖ ^ 2 * sieveH Ω q
        ≤ ∑ a ∈ range q with Nat.Coprime a q, ‖expSum S w (a / q)‖ ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hsq hQ w
  rcases Nat.lt_trichotomy q 1 with h | rfl | h
  · have : q = 0 := by omega
    subst this; exact absurd hsq not_squarefree_zero
  · have : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    simp [sieveH, expSum_zero]
  set p := q.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set q1 := q / p with hq1
  have hqq : q = p * q1 := (Nat.mul_div_cancel' (Nat.minFac_dvd q)).symm
  have hq1pos : 0 < q1 := by
    rcases Nat.eq_zero_or_pos q1 with h0 | h0
    · rw [h0, mul_zero] at hqq; omega
    · exact h0
  have hcop : Nat.Coprime p q1 := by
    rw [hp.coprime_iff_not_dvd]
    rintro ⟨k, hk⟩
    exact hp.not_isUnit (hsq p ⟨k, by rw [hqq, hk]; ring⟩)
  have hq1lt : q1 < q := by
    rw [hqq]; exact lt_mul_left hq1pos hp.one_lt
  have hsq1 : Squarefree q1 := by
    have h2 : Squarefree (p * q1) := hqq ▸ hsq
    exact h2.of_mul_right
  have hpf : q.primeFactors = {p} ∪ q1.primeFactors := by
    rw [hqq, Nat.primeFactors_mul hp.ne_zero hq1pos.ne', hp.primeFactors]
  have hdisj : Disjoint ({p} : Finset ℕ) q1.primeFactors := by
    rw [Finset.disjoint_singleton_left, Nat.mem_primeFactors]
    rintro ⟨-, hd, -⟩; exact (hp.coprime_iff_not_dvd.1 hcop) hd
  have hH : sieveH Ω q = sieveH Ω p * sieveH Ω q1 := by
    unfold sieveH; rw [hpf, Finset.prod_union hdisj, hp.primeFactors]
  have hpQ : p ≤ Q := hQ p (by rw [hpf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self p))
  have hQ1 : ∀ r ∈ q1.primeFactors, r ≤ Q := fun r hr => hQ r (by rw [hpf]; exact Finset.mem_union_right _ hr)
  have hHp : 0 ≤ sieveH Ω p := by
    unfold sieveH; rw [hp.primeFactors, Finset.prod_singleton]
    have := (hΩ p hp hpQ).2
    have : ((Ω p).card : ℝ) < p := by exact_mod_cast this
    apply div_nonneg (Nat.cast_nonneg _); linarith
  -- the CRT map
  let A : ℕ → Finset ℕ := fun r => (range r).filter (fun a => Nat.Coprime a r)
  let f : ℕ × ℕ → ℕ := fun x => (x.1 * p + x.2 * q1) % q
  have hfval : ∀ x : ℕ × ℕ, expSum S w ((f x : ℕ) / q)
      = expSum S (fun n => w n * ee (n * ((x.1 : ℝ) / q1))) ((x.2 : ℝ) / p) := by
    intro x
    simp only [f]
    rw [expSum_mod, ← expSum_shift]
    congr 1
    rw [hqq]; push_cast
    have : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (q1:ℝ) ≠ 0 := by exact_mod_cast hq1pos.ne'
    field_simp
  have hmaps : ∀ x ∈ A q1 ×ˢ A p, f x ∈ A q := by
    rintro ⟨a1, a2⟩ hx
    simp only [A, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    simp only [f]
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm, ← Nat.Coprime, hqq,
      Nat.coprime_mul_iff_right]
    constructor
    · rw [add_comm, Nat.coprime_add_mul_right_left]
      exact Nat.Coprime.mul_left hx.2.2 hcop.symm
    · rw [Nat.coprime_add_mul_right_left]
      exact Nat.Coprime.mul_left hx.1.2 hcop
  have hinj : Set.InjOn f ↑(A q1 ×ˢ A p) := by
    rintro ⟨a1, a2⟩ hx ⟨b1, b2⟩ hy hxy
    simp only [A, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx hy
    simp only [f] at hxy
    have hm : a1 * p + a2 * q1 ≡ b1 * p + b2 * q1 [MOD p * q1] := by rw [← hqq]; exact hxy
    have h1 : a1 * p + a2 * q1 ≡ b1 * p + b2 * q1 [MOD q1] := Nat.ModEq.of_mul_left p hm
    have h2 : a1 * p + a2 * q1 ≡ b1 * p + b2 * q1 [MOD p] := Nat.ModEq.of_mul_right q1 hm
    have h1' : a1 * p ≡ b1 * p [MOD q1] :=
      Nat.ModEq.add_right_cancel (by simp [Nat.ModEq, Nat.mul_mod_left]) h1
    have h2' : a2 * q1 ≡ b2 * q1 [MOD p] :=
      Nat.ModEq.add_left_cancel (by simp [Nat.ModEq, Nat.mul_mod_left]) h2
    have e1 := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hcop.symm) h1'
    have e2 := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hcop) h2'
    unfold Nat.ModEq at e1 e2
    rw [Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1] at e1
    rw [Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1] at e2
    rw [e1, e2]
  calc ‖∑ n ∈ S, w n‖ ^ 2 * sieveH Ω q
      = sieveH Ω p * (‖∑ n ∈ S, w n‖ ^ 2 * sieveH Ω q1) := by rw [hH]; ring
    _ ≤ sieveH Ω p * ∑ a ∈ A q1, ‖expSum S w (a / q1)‖ ^ 2 := by
        gcongr; exact ih q1 hq1lt hsq1 hQ1 w
    _ = ∑ a1 ∈ A q1, ‖∑ n ∈ S, w n * ee (n * ((a1 : ℝ) / q1))‖ ^ 2 * sieveH Ω p := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a1 _ => ?_; rw [expSum]; ring
    _ ≤ ∑ a1 ∈ A q1, ∑ a2 ∈ A p,
          ‖expSum S (fun n => w n * ee (n * ((a1 : ℝ) / q1))) ((a2 : ℝ) / p)‖ ^ 2 := by
        gcongr with a1 ha1
        unfold sieveH; rw [hp.primeFactors, Finset.prod_singleton]
        exact montgomery_prime S _ hp (Ω p) (hΩ p hp hpQ).1 (hΩ p hp hpQ).2
          (fun n hn => hS n hn p hp hpQ)
    _ = ∑ x ∈ A q1 ×ˢ A p, ‖expSum S w ((f x : ℕ) / q)‖ ^ 2 := by
        rw [Finset.sum_product]; simp_rw [hfval]
    _ = ∑ a ∈ (A q1 ×ˢ A p).image f, ‖expSum S w (a / q)‖ ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ a ∈ A q, ‖expSum S w (a / q)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha; exact hmaps x hx
        · intros; positivity

end LeanFormalizations.Erdos385.LargeSieve
