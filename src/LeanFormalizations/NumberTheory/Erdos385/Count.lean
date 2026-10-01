/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Erdos385
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385: the elementary count of bad `n` (phase E2, DONE 2026-10-01, axiom-clean)

`DOOR-EXCEPTIONAL-ERDOS-385.md` A1 (90% correct as stated): `#{bad n ≤ X} ≪ X log log X / log² X`.

## Frozen statement

* `card_bad_le`, from `Literature.BrunUniformGap`.

## Route

Pick `y` with `y# ≥ (log X)²` (so `y ≍ log log X`, Chebyshev: mathlib's `primorial_le_4_pow`
bounds the other side).  By `primorial_dvd_or_exists_prime_pair_of_bad`, a bad `n ≤ X` with
`n ≥ y + 2` is either a multiple of `y#` (at most `X / y# + 1 ≤ X / log² X + 1` of them) or has
`n − p`, `n − 1` both prime for a prime `3 ≤ p ≤ y`: a prime pair at gap `h = p − 1`, at most
`C (h/φ(h)) X / log² X` per `p` by Brun.  Sum over the primes `p ≤ y`: with
`h/φ(h) ≪ log log h ≤ log log y` and `π(y) ≪ y / log y`, the total is
`≪ (y / log y) · log log y · X / log² X ≪ X log log X / log² X` (since `y ≍ log log X`).  The crude
`h/φ(h) ≤ h` would lose a factor `y / log log y`, so avoid it.  The `n < y + 2` part is
`O(log log X)`.
-/

namespace LeanFormalizations.Erdos385

open Real Finset Filter Asymptotics LeanFormalizations.Literature

/-! ## Helpers -/

/-- Telescoping: `∏ s/(s−1) ≤ |S| + 1` over a set of integers `≥ 2`. -/
theorem prod_div_sub_one_le_card_add_one (S : Finset ℕ) (hS : ∀ s ∈ S, 2 ≤ s) :
    ∏ s ∈ S, ((s : ℝ) / ((s : ℝ) - 1)) ≤ S.card + 1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := hS a (mem_insert_self _ _)
    have ih' := ih (fun x hx => hS x (mem_insert_of_mem hx))
    have hsub : s ⊆ Ico 2 a := fun x hx =>
      mem_Ico.2 ⟨hS x (mem_insert_of_mem hx), hlt x hx⟩
    have hcard : s.card + 2 ≤ a := by
      have := card_le_card hsub; simp at this; omega
    rw [prod_insert has, card_insert_of_notMem has]
    have ha1 : (0:ℝ) < (a:ℝ) - 1 := by
      have : (2:ℝ) ≤ a := by exact_mod_cast ha2
      linarith
    have hk : ((s.card : ℝ) + 2) ≤ a := by exact_mod_cast hcard
    have hnn : 0 ≤ (a:ℝ) / ((a:ℝ) - 1) := by positivity
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ x ∈ s, ((x:ℝ) / ((x:ℝ) - 1))
        ≤ (a:ℝ) / ((a:ℝ) - 1) * (s.card + 1) := mul_le_mul_of_nonneg_left ih' hnn
      _ ≤ ((s.card + 1 : ℕ) : ℝ) + 1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ ha1]; push_cast; nlinarith

theorem div_totient_le (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) / (Nat.totient h : ℝ) ≤ 1 + Real.logb 2 h := by
  have hφ : (0:ℝ) < Nat.totient h := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have key := Nat.totient_mul_prod_primeFactors h
  have hP : ∀ p ∈ h.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : (0:ℝ) < ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    apply prod_pos; intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hP p hp
    linarith
  have heq : (h : ℝ) / (Nat.totient h : ℝ) = ∏ p ∈ h.primeFactors, ((p:ℝ) / ((p:ℝ) - 1)) := by
    rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    push_cast at this
    have h2 : ∏ p ∈ h.primeFactors, ((p - 1 : ℕ) : ℝ) = ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
      apply prod_congr rfl; intro p hp; rw [Nat.cast_sub (by have := hP p hp; omega)]; simp
    rw [h2] at this
    linarith
  rw [heq]
  refine (prod_div_sub_one_le_card_add_one _ hP).trans ?_
  have hcard : 2 ^ h.primeFactors.card ≤ h := by
    calc 2 ^ h.primeFactors.card = ∏ _p ∈ h.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ h.primeFactors, p := prod_le_prod' hP
      _ ≤ h := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd h)
  have : (h.primeFactors.card : ℝ) ≤ Real.logb 2 h := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hh)]
    rw [Real.rpow_natCast]; exact_mod_cast hcard
  linarith

/-- Chebyshev's lower bound, in the eventual form `log(n#) ≥ (log 2 / 2) n`. -/
theorem eventually_half_log_two_mul_le_log_primorial :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n : ℝ) * Real.log 2 / 2 ≤ Real.log (primorial n) := by
  have h1 : (fun x : ℝ => Real.log (x + 1)) =o[atTop] (fun x => x) := by
    have := Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_right _ 1 tendsto_id)
    refine this.trans_isBigO ?_
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    simp only [Function.comp, id, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have h2 : (fun x : ℝ => 2 * √x * Real.log x) =o[atTop] (fun x => x) := by
    have hl := isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)
    have := (isBigO_refl (fun x : ℝ => 2 * √x) atTop).mul_isLittleO hl
    refine this.trans_isBigO ?_
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc,
      Real.mul_self_sqrt hx, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h3 := (h1.add h2).bound (c := Real.log 2 / 2) (by positivity)
  obtain ⟨a, ha⟩ := eventually_atTop.1 h3
  refine ⟨⌈a⌉₊ + 1, fun n hn => ?_⟩
  have hna : a ≤ n := (Nat.le_ceil a).trans (by exact_mod_cast (by omega : ⌈a⌉₊ ≤ n))
  have hb := ha n hna
  have hθ := Chebyshev.theta_ge n
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hθ
  have hn0 : (0:ℝ) ≤ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn0] at hb
  have := le_abs_self (Real.log (↑n + 1) + 2 * √↑n * Real.log ↑n)
  nlinarith

theorem card_filter_dvd_range_le (X d : ℕ) :
    ((range (X + 1)).filter (fun n => d ∣ n)).card ≤ X / d + 1 := by
  have : (range (X + 1)).filter (fun n => d ∣ n) ⊆ insert 0 ((Ioc 0 X).filter (fun n => d ∣ n)) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact mem_insert_of_mem (mem_filter.2 ⟨mem_Ioc.2 ⟨h, by omega⟩, hn.2⟩)
  calc _ ≤ _ := card_le_card this
    _ ≤ _ := card_insert_le _ _
    _ = X / d + 1 := by rw [Nat.Ioc_filter_dvd_card_eq_div]

/-- The set-up of the count: a bad `n ≤ X` is small, a multiple of `y#`, or `m + p` with
`m, m + (p − 1)` prime and `p ≤ y` prime. -/
theorem bad_subset (X y : ℕ) :
    {n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n} ⊆
      ↑(range (y + 2) ∪ (range (X + 1)).filter (fun n => primorial y ∣ n) ∪
        (Nat.primesLE y).biUnion (fun p =>
          ((range (X + 1)).filter (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p))) := by
  rintro n ⟨hX, h5, hb⟩
  simp only [coe_union, coe_biUnion, coe_image, coe_filter, mem_range, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, mem_coe, Nat.mem_primesLE]
  by_cases hy : n < y + 2
  · exact Or.inl (Or.inl hy)
  rcases primorial_dvd_or_exists_prime_pair_of_bad (y := y) h5 hb (by omega) with hd | ⟨p, hp, hp3, hpy, hq⟩
  · exact Or.inl (Or.inr ⟨by omega, hd⟩)
  · right
    refine ⟨p, ⟨hpy, hp⟩, n - p, ⟨by omega, hq, ?_⟩, by omega⟩
    rw [show n - p + (p - 1) = n - 1 by omega]
    exact prime_sub_one_of_bad h5 hb

/-- One Brun term, with `h/φ(h)` traded for `log p`. -/
theorem card_prime_pair_le (CB : ℝ)
    (hCB : ∀ X h : ℕ, 3 ≤ X → 1 ≤ h →
      ({n : ℕ | n ≤ X ∧ n.Prime ∧ (n + h).Prime}.ncard : ℝ)
        ≤ CB * ((h : ℝ) / (Nat.totient h : ℝ)) * X / Real.log X ^ 2)
    (hdt : ∀ h : ℕ, 1 ≤ h → (h : ℝ) / (Nat.totient h : ℝ) ≤ 1 + Real.logb 2 h)
    {X p : ℕ} (hX : 3 ≤ X) (hp : p.Prime) :
    ((((range (X + 1)).filter (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p)).card : ℝ)
      ≤ max CB 0 * (2 / Real.log 2) * Real.log p * X / Real.log X ^ 2 := by
  have hp2 := hp.two_le
  have h1 : (((range (X + 1)).filter (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p)).card
      ≤ ({n : ℕ | n ≤ X ∧ n.Prime ∧ (n + (p - 1)).Prime}.ncard) := by
    refine (card_image_le).trans ?_
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard _ ((Set.finite_Iic X).subset fun n hn => hn.1)
    intro m hm
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
    exact ⟨by omega, hm.2⟩
  have hb := hCB X (p - 1) hX (by omega)
  have hdp := hdt (p - 1) (by omega)
  have hL : 0 ≤ (X : ℝ) / Real.log X ^ 2 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp1 : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hlog : Real.logb 2 ((p - 1 : ℕ) : ℝ) ≤ Real.logb 2 p := by
    have : (0:ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
    exact Real.logb_le_logb_of_le (by norm_num) this hp1
  have hlog1 : 1 ≤ Real.logb 2 p := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hp.pos)]
    simp; exact_mod_cast hp2
  have hrat : ((p - 1 : ℕ) : ℝ) / (Nat.totient (p - 1) : ℝ) ≤ (2 / Real.log 2) * Real.log p := by
    have : (2 / Real.log 2) * Real.log p = 2 * Real.logb 2 p := by
      rw [Real.logb]; ring
    rw [this]; linarith
  have hnn : 0 ≤ ((p - 1 : ℕ) : ℝ) / (Nat.totient (p - 1) : ℝ) := by positivity
  calc _ ≤ ({n : ℕ | n ≤ X ∧ n.Prime ∧ (n + (p - 1)).Prime}.ncard : ℝ) := by exact_mod_cast h1
    _ ≤ CB * (((p - 1 : ℕ) : ℝ) / (Nat.totient (p - 1) : ℝ)) * X / Real.log X ^ 2 := hb
    _ = CB * (((p - 1 : ℕ) : ℝ) / (Nat.totient (p - 1) : ℝ)) * (X / Real.log X ^ 2) := by ring
    _ ≤ max CB 0 * ((2 / Real.log 2) * Real.log p) * (X / Real.log X ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hL
        exact mul_le_mul (le_max_left _ _) hrat hnn (le_max_right _ _)
    _ = _ := by ring

theorem card_bad_le (hB : BrunUniformGap) :
    ∃ C : ℝ, ∀ X : ℕ, 16 ≤ X →
      ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
        ≤ C * X * Real.log (Real.log X) / Real.log X ^ 2 := by
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨N₀, hN₀⟩ := eventually_half_log_two_mul_le_log_primorial
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ max CB 0 := le_max_right _ _
  set K : ℝ := 4 / Real.log 2 + 1 + N₀ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨4 * (K + 3) + 1 + 4 * max CB 0 * K, fun X hX => ?_⟩
  have hX0 : (16:ℝ) ≤ X := by exact_mod_cast hX
  set L := Real.log X with hLdef
  have hLe : Real.exp 1 ≤ L := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hX0
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hl : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  set y := ⌈(4 / Real.log 2) * Real.log L⌉₊ + N₀ with hydef
  have hnn : 0 ≤ (4 / Real.log 2) * Real.log L := by positivity
  have hyc : (4 / Real.log 2) * Real.log L ≤ (⌈(4 / Real.log 2) * Real.log L⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hyc' : (⌈(4 / Real.log 2) * Real.log L⌉₊ : ℝ) < (4 / Real.log 2) * Real.log L + 1 :=
    Nat.ceil_lt_add_one hnn
  have hycast : (y : ℝ) = (⌈(4 / Real.log 2) * Real.log L⌉₊ : ℝ) + N₀ := by
    rw [hydef]; push_cast; ring
  have hy_le : (y : ℝ) ≤ K * Real.log L := by
    have : ((N₀ : ℝ) + 1) * 1 ≤ ((N₀ : ℝ) + 1) * Real.log L :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    rw [hycast, hK]; nlinarith
  have hprim : L ^ 2 ≤ (primorial y : ℝ) := by
    have h1 := hN₀ y (Nat.le_add_left _ _)
    have h2 : 2 * Real.log L ≤ (y : ℝ) * Real.log 2 / 2 := by
      have : (4 / Real.log 2) * Real.log L * Real.log 2 / 2 = 2 * Real.log L := by
        field_simp; ring
      rw [hycast]
      have : (0:ℝ) ≤ N₀ := by positivity
      nlinarith
    have hpp : (0:ℝ) < primorial y := by exact_mod_cast primorial_pos y
    rw [← Real.log_le_log_iff (by positivity) hpp, Real.log_pow]
    push_cast; linarith
  have hL4 : L ^ 2 ≤ 4 * X := by
    have h := Real.log_le_rpow_div (x := X) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ X by positivity)
    have : L ≤ 2 * √(X : ℝ) := by rw [hLdef]; linarith
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  set u := (X : ℝ) / L ^ 2 with hudef
  have hL2 : 0 < L ^ 2 := by positivity
  have hu1 : 1 ≤ 4 * u := by rw [hudef, mul_div_assoc', le_div_iff₀ hL2]; linarith
  -- the count
  have hsub := bad_subset X y
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  have hU := (card_union_le (range (y + 2) ∪ (range (X + 1)).filter (fun n => primorial y ∣ n))
    ((Nat.primesLE y).biUnion (fun p =>
      ((range (X + 1)).filter (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p)))).trans
    (add_le_add_left (card_union_le _ _) _)
  have hbi := card_biUnion_le (s := Nat.primesLE y) (t := fun p =>
    ((range (X + 1)).filter (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p))
  have hdv := card_filter_dvd_range_le X (primorial y)
  have hcardR : (({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℕ) : ℝ) ≤
      ((y + 2 : ℕ) : ℝ) + ((X / primorial y : ℕ) : ℝ) + 1 +
        ∑ p ∈ Nat.primesLE y, ((((range (X + 1)).filter
          (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p)).card : ℝ) := by
    have := hcard.trans (hU.trans (add_le_add (add_le_add (card_range (y + 2)).le hdv) hbi))
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast at this ⊢; linarith
  have hdivR : ((X / primorial y : ℕ) : ℝ) ≤ u := by
    refine (Nat.cast_div_le).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hL2 hprim
  have hsum : ∑ p ∈ Nat.primesLE y, ((((range (X + 1)).filter
        (fun m => m.Prime ∧ (m + (p - 1)).Prime)).image (· + p)).card : ℝ)
      ≤ 4 * max CB 0 * y * u := by
    calc _ ≤ ∑ p ∈ Nat.primesLE y,
          max CB 0 * (2 / Real.log 2) * Real.log p * X / Real.log X ^ 2 :=
          sum_le_sum fun p hp => card_prime_pair_le CB hCB div_totient_le (by omega)
            (Nat.prime_of_mem_primesLE hp)
      _ = max CB 0 * (2 / Real.log 2) * u * ∑ p ∈ Nat.primesLE y, Real.log p := by
          rw [mul_sum]; apply sum_congr rfl; intro p _; rw [hudef]; ring
      _ ≤ max CB 0 * (2 / Real.log 2) * u * (Real.log 4 * y) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Chebyshev.theta_eq_sum_primesLE_log]
          exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = 4 * max CB 0 * y * u := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; field_simp; ring
  have e1 : (y : ℝ) + 3 ≤ 4 * (K + 3) * u * Real.log L := by
    have : (y : ℝ) + 3 ≤ (K + 3) * Real.log L := by linarith
    have h3 : 0 ≤ (K + 3) * Real.log L := by positivity
    nlinarith
  have e2 : u ≤ u * Real.log L := by
    have : 0 ≤ u := by positivity
    nlinarith
  have e3 : 4 * max CB 0 * y * u ≤ 4 * max CB 0 * K * u * Real.log L := by
    have : 0 ≤ 4 * max CB 0 * u := by positivity
    have := mul_le_mul_of_nonneg_left hy_le this
    linarith
  have hgoal : (4 * (K + 3) + 1 + 4 * max CB 0 * K) * X * Real.log L / L ^ 2
      = (4 * (K + 3) + 1 + 4 * max CB 0 * K) * u * Real.log L := by
    rw [hudef]; ring
  rw [hgoal]
  push_cast at hcardR
  nlinarith

end LeanFormalizations.Erdos385
