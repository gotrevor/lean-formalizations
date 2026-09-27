/-
# Saito §4, Lemma 4.1: the Pisot degree bound

This is the *route-decisive* half of Saito's Theorem 1.5 (and hence of Theorems 1.1/1.2,
`Mills/Transcendental.lean`).  It is stated here **abstractly**, decoupled from the
Mills-specific §3 estimates: the only input from §3 is the single hypothesis

    ‖Σ_{j≥2} β_jⁿ‖ ≤ K · β^(−μn)   for all large n,

which is exactly (4.1)+(4.2) after `β := ξ^(C_m)` and `μ := b θ_b`.  Saito's Claim then reads
`(ℓ − 1) μ ≤ 1` where `ℓ = deg β` — `pisot_degree_bound` below.  Everything downstream
(`b ≥ 5 ⇒ ℓ ≤ 1`, contradicting `ℓ ≥ 2`; `b = 4 ⇒ ℓ = 2`; `b = 3 ⇒ ℓ ∈ {2,3}`) is arithmetic.

## What is proved here and what is open

Proved, axiom-clean:
* `le_of_pow_le_const_mul_pow` — the limiting step "`Mⁿ n^(−λ) ≤ K ρⁿ` eventually ⇒ `M ≤ ρ`",
  which is Saito's "By taking `k → ∞`".  Polynomial-vs-exponential via
  `isLittleO_pow_const_const_pow_of_one_lt`, after `n^λ ≤ n^⌈λ⌉₊`.
* `conjMax_pow_card_le` — `∏_{j≥2} |β_j| ≤ |β₂|^(ℓ−1)`.
* `pisot_degree_bound` — the Claim, from those two plus the two algebraic-number facts below.

Open (two named leaves, both standard algebraic number theory, neither Mills-specific):
* `pisot_conjPowSum_add_mem_int` — `βⁿ + Σ_{j≥2} β_jⁿ ∈ ℤ` (the trace of an algebraic integer).
* `pisot_one_le_prod_norm` — `1 ≤ |N(β)| = β · ∏_{j≥2}|β_j|` (a nonzero algebraic integer has
  norm of absolute value `≥ 1`).

`pisot_conjPowSum_add_mem_int` is not used by `pisot_degree_bound` itself — it is the bridge
that turns Saito's `‖ξ^{C_k}‖` estimate into the `‖Σ_{j≥2} β_jⁿ‖` hypothesis, i.e. it is needed
one level up, in `Transcendental.lean`.  It is stated here because it is about the same objects.
-/
import Mathlib
import LeanFormalizations.Literature.Pisot

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature Filter Polynomial

/-! ### The conjugates of a real algebraic number, other than itself -/

/-- The conjugates of `β` over `ℚ` other than `β` itself, as a multiset of complex numbers. -/
noncomputable def otherConj (β : ℝ) : Multiset ℂ := ((minpoly ℚ β).aroots ℂ).erase (β : ℂ)

/-- `Σ_{j ≥ 2} β_jⁿ`, the power sum over the *other* conjugates. -/
noncomputable def conjPowSum (β : ℝ) (n : ℕ) : ℂ := ((otherConj β).map (· ^ n)).sum

/-- `|β₂|`, the largest modulus among the conjugates other than `β`. -/
noncomputable def conjMax (β : ℝ) : ℝ := ((otherConj β).map (‖·‖)).fold max 0

theorem conjMax_nonneg (β : ℝ) : 0 ≤ conjMax β := by
  unfold conjMax
  induction ((otherConj β).map (‖·‖)) using Multiset.induction with
  | empty => simp
  | cons a s ih => rw [Multiset.fold_cons_left]; exact le_max_of_le_right ih

theorem norm_le_conjMax {β : ℝ} {z : ℂ} (hz : z ∈ otherConj β) : ‖z‖ ≤ conjMax β := by
  unfold conjMax
  have : ‖z‖ ∈ (otherConj β).map (‖·‖) := Multiset.mem_map_of_mem _ hz
  revert this
  induction ((otherConj β).map (‖·‖)) using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      intro h
      rw [Multiset.fold_cons_left]
      rcases Multiset.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih h)

/-- A multiset of reals in `[0, M]` has product at most `M ^ card`. -/
theorem Multiset.prod_le_pow_card_of_le {s : Multiset ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ s, 0 ≤ x ∧ x ≤ M) : s.prod ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have ha := h a (Multiset.mem_cons_self a t)
      have ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ M := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      have htp : (0 : ℝ) ≤ t.prod :=
        Multiset.prod_nonneg fun x hx => (ht x hx).1
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
      calc a * t.prod ≤ M * t.prod := mul_le_mul_of_nonneg_right ha.2 htp
        _ ≤ M * M ^ Multiset.card t :=
            mul_le_mul_of_nonneg_left (ih ht) hM
        _ = M ^ Multiset.card t * M := by ring

/-- `∏_{j ≥ 2} |β_j| ≤ |β₂|^(ℓ − 1)`. -/
theorem conjMax_pow_card_le (β : ℝ) :
    (((otherConj β).map (‖·‖)).prod) ≤ conjMax β ^ Multiset.card (otherConj β) := by
  have := Multiset.prod_le_pow_card_of_le (s := (otherConj β).map (‖·‖))
    (M := conjMax β) (conjMax_nonneg β) ?_
  · simpa using this
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨norm_nonneg _, norm_le_conjMax hz⟩

/-! ### The limiting step -/

/-- **Saito's "by taking `k → ∞`"**: if `Mⁿ ≤ K · n^d · ρⁿ` for all large `n` with `ρ > 0`,
then `M ≤ ρ`.  (The `n^(−λ)` of Lemma 2.7 is absorbed into the polynomial factor via
`n^λ ≤ n^⌈λ⌉₊`.) -/
theorem le_of_pow_le_const_mul_pow {M ρ K : ℝ} (d : ℕ) (hM : 0 ≤ M) (hρ : 0 < ρ) (hK : 0 < K)
    (h : ∀ᶠ n : ℕ in atTop, M ^ n ≤ K * (n : ℝ) ^ d * ρ ^ n) : M ≤ ρ := by
  by_contra hlt
  push_neg at hlt
  set r : ℝ := M / ρ with hr
  have hr1 : 1 < r := (one_lt_div hρ).2 hlt
  -- eventually `r ^ n ≤ K * n ^ d`, contradicting `n ^ d = o(r ^ n)`.
  have hpoly : (fun n : ℕ => ((n : ℝ) ^ d)) =o[atTop] fun n : ℕ => r ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt d hr1
  have hb := hpoly.bound (c := (2 * K)⁻¹) (by positivity)
  obtain ⟨n, hn, hbn⟩ := (h.and hb).exists
  have hρn : (0 : ℝ) < ρ ^ n := pow_pos hρ n
  have hrn : r ^ n = M ^ n / ρ ^ n := by rw [hr, div_pow]
  have h1 : r ^ n ≤ K * (n : ℝ) ^ d := by
    rw [hrn, div_le_iff₀ hρn]; linarith [hn]
  have h2 : (n : ℝ) ^ d ≤ (2 * K)⁻¹ * r ^ n := by
    have := hbn
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) ^ d),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ n)] at this
  have hrpos : (0 : ℝ) < r ^ n := pow_pos (by linarith) n
  have h3 : K * (n : ℝ) ^ d ≤ K * ((2 * K)⁻¹ * r ^ n) := by
    exact mul_le_mul_of_nonneg_left h2 hK.le
  have h4 : K * ((2 * K)⁻¹ * r ^ n) = r ^ n / 2 := by
    field_simp
  rw [h4] at h3
  linarith

/-! ### The two algebraic-number leaves -/

/-- **`βⁿ + Σ_{j≥2} β_jⁿ ∈ ℤ`** for `β` a Pisot number: the left side is the trace of the
algebraic integer `βⁿ` from `ℚ(β)` to `ℚ`, hence a rational integer.

Route: `Algebra.trace_eq_sum_embeddings` over `ℚ⟮β⟯` identifies the trace with `Σ_σ σ(β)ⁿ`,
`IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots` identifies the embeddings' images of
`β` with the roots of `minpoly ℚ β`, and `Algebra.isIntegral_trace` + `IsIntegrallyClosed`
puts the trace in `ℤ`. -/
theorem pisot_conjPowSum_add_mem_int {β : ℝ} (hβ : IsPisot β) (n : ℕ) :
    ∃ t : ℤ, ((β : ℂ)) ^ n + conjPowSum β n = (t : ℂ) := by
  sorry

/-- **`1 ≤ β · ∏_{j≥2} |β_j|`**: the field norm of the nonzero algebraic integer `β` is a
nonzero rational integer, and its absolute value is the product of the moduli of all
conjugates. -/
theorem pisot_one_le_prod_norm {β : ℝ} (hβ : IsPisot β) :
    1 ≤ β * ((otherConj β).map (‖·‖)).prod := by
  sorry

/-! ### Saito's Claim (Lemma 4.1) -/

/-- **Saito (2024), Lemma 4.1, Claim.**  Let `β` be a Pisot number of degree `ℓ ≥ 2` whose
other-conjugate power sums decay like `β^(−μn)`.  Then `(ℓ − 1) μ ≤ 1`.

This is exactly Saito's `ℓ ≤ (bθ_b)^(−1) + 1` with `μ = bθ_b`.  Note the hypothesis is only
needed along a subsequence in Saito (`k ∈ I_b`); here `I_b = ℕ`, matching `c_k ≡ c`. -/
theorem pisot_degree_bound (hG : Dubickas2022PisotGap) {β : ℝ} (hβ : IsPisot β)
    (hdeg : 2 ≤ (minpoly ℚ β).natDegree) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K)
    (hdecay : ∀ᶠ n : ℕ in atTop, ‖conjPowSum β n‖ ≤ K * (β ^ (-(μ * n)) : ℝ)) :
    ((Multiset.card (otherConj β) : ℝ)) * μ ≤ 1 := by
  obtain ⟨lam, hlam, n₀, hgap⟩ := hG β hβ hdeg
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  set ρ : ℝ := β ^ (-μ) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hβ0 _
  -- Step 1: `conjMax β ≤ ρ`.
  have hmax : conjMax β ≤ ρ := by
    refine le_of_pow_le_const_mul_pow ⌈lam⌉₊ (conjMax_nonneg β) hρ0 hK ?_
    filter_upwards [hdecay, eventually_ge_atTop n₀, eventually_ge_atTop 1] with n hn hn0 hn1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hg : conjMax β ^ n * (n : ℝ) ^ (-lam) ≤ ‖conjPowSum β n‖ := hgap n hn0
    -- `(n : ℝ) ^ (-lam) ≥ (n : ℝ) ^ (-(⌈lam⌉₊ : ℝ))`
    have hpow : ((n : ℝ) ^ (⌈lam⌉₊ : ℕ))⁻¹ ≤ (n : ℝ) ^ (-lam) := by
      have hle : -(⌈lam⌉₊ : ℝ) ≤ -lam := by
        simpa using Nat.le_ceil lam
      have := Real.rpow_le_rpow_of_exponent_le hnR hle
      rwa [Real.rpow_neg (by linarith), Real.rpow_natCast] at this
    have hMn : (0 : ℝ) ≤ conjMax β ^ n := pow_nonneg (conjMax_nonneg β) n
    have hden : (0 : ℝ) < (n : ℝ) ^ (⌈lam⌉₊ : ℕ) := by positivity
    -- combine
    have hrho : (β ^ (-(μ * n)) : ℝ) = ρ ^ n := by
      rw [hρdef, ← Real.rpow_natCast (β ^ (-μ)) n, ← Real.rpow_mul hβ0.le]
      ring_nf
    have e1 : conjMax β ^ n * ((n : ℝ) ^ (⌈lam⌉₊ : ℕ))⁻¹ * (n : ℝ) ^ (⌈lam⌉₊ : ℕ)
        = conjMax β ^ n := by field_simp
    calc conjMax β ^ n
        = conjMax β ^ n * ((n : ℝ) ^ (⌈lam⌉₊ : ℕ))⁻¹ * (n : ℝ) ^ (⌈lam⌉₊ : ℕ) := e1.symm
      _ ≤ conjMax β ^ n * (n : ℝ) ^ (-lam) * (n : ℝ) ^ (⌈lam⌉₊ : ℕ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hMn) hden.le
      _ ≤ ‖conjPowSum β n‖ * (n : ℝ) ^ (⌈lam⌉₊ : ℕ) := by nlinarith [hden]
      _ ≤ (K * (β ^ (-(μ * n)) : ℝ)) * (n : ℝ) ^ (⌈lam⌉₊ : ℕ) := by nlinarith [hden]
      _ = K * (n : ℝ) ^ (⌈lam⌉₊ : ℕ) * ρ ^ n := by rw [hrho]; ring
  -- Step 2: `∏_{j≥2}|β_j| ≤ ρ ^ (ℓ - 1)`.
  set L : ℕ := Multiset.card (otherConj β) with hL
  have hprod : ((otherConj β).map (‖·‖)).prod ≤ ρ ^ L :=
    le_trans (conjMax_pow_card_le β) (pow_le_pow_left₀ (conjMax_nonneg β) hmax L)
  -- Step 3: `1 ≤ β * ∏ ≤ β * ρ ^ L = β ^ (1 - μ L)`.
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

end LeanFormalizations.Mills
