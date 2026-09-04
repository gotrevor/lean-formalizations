/-
# The integrality lattice for partial fractions (SIGMA Lemma 1, derivative-free)

`Rep n σ f` says that the function `f : ℚ → ℚ` agrees, away from the poles `t = 0, -1, …, -n`,
with a partial-fraction sum `Σ_{k ≤ n} Σ_{i < σ} a_{i,k} / (t+k)^{i+1}` whose coefficients satisfy
`d_n^{σ-1-i} a_{i,k} ∈ ℤ` (`d_n = lcm(1,…,n)`).  The one substantive fact is

    Rep n σ f  →  Rep n (σ+1) (f · (c + Σ_j e_j/(t+j)))       (c, e_j ∈ ℤ)

(`Rep.mul_simple`): multiplying by a *simple* fraction with integer residues raises the level by
exactly one.  Its proof is the elementary identity

    1/(x^{i+1}(x+D)) = Σ_{p ≤ i} (-1)^{i-p}/(D^{i-p+1} x^{p+1}) + (-1)^{i+1}/(D^{i+1}(x+D)),

with `D = j - k` dividing `d_n`.  This is Zudilin's Lemma 1 without derivatives.
-/
import Mathlib

namespace LeanFormalizations.DirichletBeta

open Finset

/-- `t` is not a pole: `t + k ≠ 0` for `k = 0, …, n`. -/
def NonPole (n : ℕ) (t : ℚ) : Prop := ∀ k ∈ range (n + 1), t + k ≠ 0

/-- `Σ_{k ≤ n} Σ_{i < σ} a i k / (t+k)^{i+1}`. -/
def pfSum (n σ : ℕ) (a : ℕ → ℕ → ℚ) (t : ℚ) : ℚ :=
  ∑ k ∈ range (n + 1), ∑ i ∈ range σ, a i k / (t + k) ^ (i + 1)

/-- `d_n^{σ-1-i} a i k ∈ ℤ` for `i < σ`, `k ≤ n`. -/
def IntCoeffs (n σ : ℕ) (a : ℕ → ℕ → ℚ) : Prop :=
  ∀ i ∈ range σ, ∀ k ∈ range (n + 1), ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ (σ - 1 - i) * a i k = z

/-- `f` is a level-`σ` partial-fraction sum with `d_n`-integral coefficients, away from poles. -/
def Rep (n σ : ℕ) (f : ℚ → ℚ) : Prop :=
  ∃ a, IntCoeffs n σ a ∧ ∀ t, NonPole n t → f t = pfSum n σ a t

lemma Rep.congr {n σ : ℕ} {f g : ℚ → ℚ} (h : Rep n σ f) (hfg : ∀ t, NonPole n t → f t = g t) :
    Rep n σ g := by
  obtain ⟨a, ha, hf⟩ := h
  exact ⟨a, ha, fun t ht => (hfg t ht).symm.trans (hf t ht)⟩

lemma Rep.zero (n σ : ℕ) : Rep n σ (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ _ _ _ => ⟨0, by simp⟩, fun t _ => by simp [pfSum]⟩

lemma Rep.add {n σ : ℕ} {f g : ℚ → ℚ} (hf : Rep n σ f) (hg : Rep n σ g) :
    Rep n σ (fun t => f t + g t) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun i k => a i k + b i k, fun i hi k hk => ?_, fun t ht => ?_⟩
  · obtain ⟨z, hz⟩ := ha i hi k hk
    obtain ⟨w, hw⟩ := hb i hi k hk
    exact ⟨z + w, by push_cast; rw [← hz, ← hw]; ring⟩
  · show f t + g t = _
    rw [hfa t ht, hgb t ht]
    simp only [pfSum, ← sum_add_distrib, add_div]

lemma Rep.sum {n σ : ℕ} {ι : Type*} (s : Finset ι) (F : ι → ℚ → ℚ)
    (h : ∀ i ∈ s, Rep n σ (F i)) : Rep n σ (fun t => ∑ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.zero n σ
  | insert x s hx ih =>
    have h1 := h x (mem_insert_self x s)
    have h2 := ih fun i hi => h i (mem_insert_of_mem hi)
    refine (h1.add h2).congr fun t _ => ?_
    rw [sum_insert hx]

lemma Rep.intMul {n σ : ℕ} {f : ℚ → ℚ} (z : ℤ) (hf : Rep n σ f) :
    Rep n σ (fun t => z * f t) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun i k => z * a i k, fun i hi k hk => ?_, fun t ht => ?_⟩
  · obtain ⟨w, hw⟩ := ha i hi k hk
    exact ⟨z * w, by push_cast; rw [← hw]; ring⟩
  · show (z : ℚ) * f t = _
    rw [hfa t ht]
    simp only [pfSum, Finset.mul_sum, mul_div_assoc]

lemma Rep.mono {n σ : ℕ} {f : ℚ → ℚ} (hf : Rep n σ f) : Rep n (σ + 1) f := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun i k => if i < σ then a i k else 0, fun i hi k hk => ?_, fun t ht => ?_⟩
  · by_cases h : i < σ
    · obtain ⟨z, hz⟩ := ha i (mem_range.2 h) k hk
      refine ⟨Nat.lcmUpto n * z, ?_⟩
      simp only [h, if_true]
      rw [Nat.add_sub_cancel, show σ - i = (σ - 1 - i) + 1 by omega, pow_succ]
      push_cast
      rw [← hz]; ring
    · exact ⟨0, by simp [h]⟩
  · rw [hfa t ht]
    simp only [pfSum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_range_succ]
    simp only [lt_self_iff_false, if_false, zero_div, add_zero]
    refine sum_congr rfl fun i hi => ?_
    simp [mem_range.1 hi]

/-- A single term `a / (t+k)^{i+1}` is a level-`σ` representation when `d_n^{σ-1-i} a ∈ ℤ`. -/
lemma Rep.basic {n σ : ℕ} (i k : ℕ) (hi : i < σ) (hk : k < n + 1) (a : ℚ)
    (ha : ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ (σ - 1 - i) * a = z) :
    Rep n σ (fun t => a / (t + k) ^ (i + 1)) := by
  refine ⟨fun i' k' => if i' = i ∧ k' = k then a else 0, fun i' _ k' _ => ?_, fun t _ => ?_⟩
  · by_cases h : i' = i ∧ k' = k
    · obtain ⟨rfl, rfl⟩ := h
      simpa using ha
    · exact ⟨0, by simp [h]⟩
  · simp only [pfSum]
    rw [sum_eq_single k, sum_eq_single i]
    · simp
    · intro i' _ hi'; simp [hi']
    · intro h; exact absurd (mem_range.2 hi) h
    · intro k' _ hk'; simp [hk']
    · intro h; exact absurd (mem_range.2 hk) h

/-- The elementary partial-fraction identity. -/
lemma one_div_pow_mul_add (D x : ℚ) (hD : D ≠ 0) (hx : x ≠ 0) (hxD : x + D ≠ 0) (i : ℕ) :
    1 / (x ^ (i + 1) * (x + D))
      = ∑ p ∈ range (i + 1), (-1 : ℚ) ^ (i - p) / (D ^ (i - p + 1) * x ^ (p + 1))
        + (-1) ^ (i + 1) / (D ^ (i + 1) * (x + D)) := by
  induction i with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.sub_zero, pow_zero, pow_one]
    field_simp
    ring
  | succ i ih =>
    have hsplit : 1 / (x ^ (i + 1 + 1) * (x + D)) = (1 / x) * (1 / (x ^ (i + 1) * (x + D))) := by
      field_simp
      ring
    rw [hsplit, ih, mul_add, Finset.mul_sum]
    conv_rhs => rw [sum_range_succ', add_assoc]
    congr 1
    · refine sum_congr rfl fun p hp => ?_
      have := mem_range.1 hp
      rw [Nat.add_sub_add_right]
      field_simp
      ring
    · rw [Nat.sub_zero]
      field_simp
      ring

/-- `d_n / D ∈ ℤ` for a nonzero integer `D` with `|D| ≤ n`. -/
lemma lcmUpto_div_int (n : ℕ) (D : ℤ) (hD : D ≠ 0) (hle : D.natAbs ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℚ) / D = z := by
  have h1 : D.natAbs ∣ Nat.lcmUpto n := by
    have hmem : D.natAbs ∈ Icc 1 n := mem_Icc.2 ⟨Int.natAbs_pos.2 hD, hle⟩
    simpa [Nat.lcmUpto] using Finset.dvd_lcm (f := id) hmem
  have h2 : D ∣ (Nat.lcmUpto n : ℤ) := Int.natAbs_dvd.1 (by exact_mod_cast h1)
  obtain ⟨z, hz⟩ := h2
  refine ⟨z, ?_⟩
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [div_eq_iff hD', mul_comm]
  exact_mod_cast hz

lemma lcmUpto_pow_div_int (n : ℕ) (D : ℤ) (hD : D ≠ 0) (hle : D.natAbs ≤ n) (m : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ m / D ^ m = z := by
  obtain ⟨z, hz⟩ := lcmUpto_div_int n D hD hle
  exact ⟨z ^ m, by rw [← div_pow, hz]; push_cast; ring⟩

/-- Multiplying one term by `1/(t+j)` stays representable one level up. -/
lemma Rep.elem_mul {n σ : ℕ} (i k j : ℕ) (hi : i < σ) (hk : k < n + 1) (hj : j < n + 1) (a : ℚ)
    (ha : ∃ z : ℤ, (Nat.lcmUpto n : ℚ) ^ (σ - 1 - i) * a = z) :
    Rep n (σ + 1) (fun t => a / (t + k) ^ (i + 1) * (1 / (t + j))) := by
  by_cases hjk : j = k
  · subst hjk
    refine (Rep.basic (i + 1) j (by omega) hk a ?_).congr fun t _ => ?_
    · rw [show σ + 1 - 1 - (i + 1) = σ - 1 - i by omega]; exact ha
    · rw [pow_succ]; field_simp
  · -- `D = j - k ≠ 0`, `|D| ≤ n`
    set D : ℤ := (j : ℤ) - k with hDdef
    have hD : D ≠ 0 := by rw [hDdef]; omega
    have hDle : D.natAbs ≤ n := by rw [hDdef]; omega
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    obtain ⟨z, hz⟩ := ha
    -- the representation
    have hrep : Rep n (σ + 1) (fun t =>
        (∑ p ∈ range (i + 1), (a * (-1) ^ (i - p) / (D : ℚ) ^ (i - p + 1)) / (t + k) ^ (p + 1))
          + (a * (-1) ^ (i + 1) / (D : ℚ) ^ (i + 1)) / (t + j) ^ (0 + 1)) := by
      refine Rep.add (Rep.sum _ _ fun p hp => ?_) (Rep.basic 0 j (by omega) hj _ ?_)
      · have hp := mem_range.1 hp
        refine Rep.basic p k (by omega) hk _ ?_
        obtain ⟨w, hw⟩ := lcmUpto_pow_div_int n D hD hDle (i - p + 1)
        refine ⟨z * w * (-1) ^ (i - p), ?_⟩
        push_cast
        rw [← hz, ← hw, show σ - p = (σ - 1 - i) + (i - p + 1) by omega, pow_add]
        field_simp
      · obtain ⟨w, hw⟩ := lcmUpto_pow_div_int n D hD hDle (i + 1)
        refine ⟨z * w * (-1) ^ (i + 1), ?_⟩
        push_cast
        rw [← hz, ← hw, show σ - 0 = (σ - 1 - i) + (i + 1) by omega, pow_add]
        field_simp
    refine hrep.congr fun t ht => ?_
    have hx : t + k ≠ 0 := ht k (mem_range.2 hk)
    have hxD : t + k + D ≠ 0 := by
      have := ht j (mem_range.2 hj)
      rw [hDdef]; push_cast
      convert this using 1; ring
    have key := one_div_pow_mul_add (D : ℚ) (t + k) hDq hx hxD i
    have hj' : (t + (j : ℚ)) = t + k + D := by rw [hDdef]; push_cast; ring
    rw [hj', show a / (t + k) ^ (i + 1) * (1 / (t + k + D))
        = a * (1 / ((t + k) ^ (i + 1) * (t + k + D))) by field_simp, key, mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      field_simp
    · rw [pow_one]; field_simp

/-- **The lattice step.**  Multiplying a level-`σ` representation by a simple fraction with
integer residues (and an integer constant term) gives a level-`σ+1` representation. -/
theorem Rep.mul_simple {n σ : ℕ} {f : ℚ → ℚ} (hf : Rep n σ f) (c : ℤ) (e : ℕ → ℤ) :
    Rep n (σ + 1) (fun t => f t * (c + ∑ j ∈ range (n + 1), (e j : ℚ) / (t + j))) := by
  obtain ⟨a, ha, hfa⟩ := hf
  have hrep : Rep n (σ + 1) (fun t => c * f t
      + ∑ j ∈ range (n + 1), (e j : ℚ) * ∑ k ∈ range (n + 1), ∑ i ∈ range σ,
          (a i k / (t + k) ^ (i + 1) * (1 / (t + j)))) := by
    refine Rep.add (Rep.intMul c (Rep.mono ⟨a, ha, hfa⟩)) (Rep.sum _ _ fun j hj => ?_)
    refine Rep.intMul (e j) (Rep.sum _ _ fun k hk => Rep.sum _ _ fun i hi => ?_)
    exact Rep.elem_mul i k j (mem_range.1 hi) (mem_range.1 hk) (mem_range.1 hj) _ (ha i hi k hk)
  refine hrep.congr fun t ht => ?_
  rw [hfa t ht, mul_add, mul_comm _ (c : ℚ)]
  congr 1
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [pfSum, Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
  ring

end LeanFormalizations.DirichletBeta
