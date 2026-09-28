/-
# The conjugate-power symmetric functions `eₖ(N)` and `Eₖ(N)`

Bridge layer of the Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`) between the general
machinery (`MultisetNewton.lean`, `MultisetGraeffe.lean`) and the Pisot estimates of
`DubickasPisot.lean` / `Mills/SaitoPisot.lean`.

For a Pisot number `β` with conjugates `β = β₁, β₂, …, β_d`:

* `eSmall β k N` = `eₖ(β₂^N, …, β_d^N)` (the *small* conjugates only);
* `eFull β k N` = `eₖ(β₁^N, …, β_d^N)`.

The three facts the route needs:

* `eFull_succ`  : `E_{k+1} = e_{k+1} + β^N · e_k`;
* `isRatInt_factorial_mul_eFull` : `k! · Eₖ(N) ∈ ℤ` — all power sums of the full conjugate
  multiset are rational integers (`pisot_conjPowSum_add_mem_int`), so multiset Newton applies;
* `norm_eSmall_le` : `‖eₖ(N)‖ ≤ C(L,k)·ρ^(kN)` with `ρ = conjMax β < 1`.

Together with `eq_zero_of_isRatInt_of_norm_lt_one` these give the *odd* step of the
parity-weight induction: `Eₙ → 0` for odd `n` forces `Eₙ = 0`, hence `eₙ = −β^N e_{n−1}`.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.MultisetNewton
import LeanFormalizations.NumberTheory.Transcendence.MultisetGraeffe
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot

namespace LeanFormalizations.Transcendence.Dubickas

open LeanFormalizations.Transcendence LeanFormalizations.Mills LeanFormalizations.Literature

/-- All conjugates of `β` over `ℚ`, as a multiset of complex numbers. -/
noncomputable def allConj (β : ℝ) : Multiset ℂ := (minpoly ℚ β).aroots ℂ

/-- `eₖ(β₂^N, …, β_d^N)`. -/
noncomputable def eSmall (β : ℝ) (k N : ℕ) : ℂ := (((otherConj β).map (· ^ N)).esymm k)

/-- `eₖ(β₁^N, …, β_d^N)`. -/
noncomputable def eFull (β : ℝ) (k N : ℕ) : ℂ := (((allConj β).map (· ^ N)).esymm k)

theorem allConj_eq_cons {β : ℝ} (halg : IsIntegral ℚ β) :
    allConj β = (β : ℂ) ::ₘ otherConj β :=
  (Multiset.cons_erase (beta_mem_aroots halg)).symm

/-- **`E_{k+1} = e_{k+1} + β^N · e_k`.** -/
theorem eFull_succ {β : ℝ} (halg : IsIntegral ℚ β) (k N : ℕ) :
    eFull β (k + 1) N = eSmall β (k + 1) N + (β : ℂ) ^ N * eSmall β k N := by
  rw [eFull, allConj_eq_cons halg, Multiset.map_cons, Multiset.esymm_cons, eSmall, eSmall]

theorem eFull_zero {β : ℝ} (N : ℕ) : eFull β 0 N = 1 := Multiset.esymm_zero' _

/-! ### Integrality -/

/-- Every power sum of the full conjugate multiset is a rational integer. -/
theorem isRatInt_psum_allConj {β : ℝ} (hβ : IsPisot β) (n : ℕ) :
    IsRatInt ((allConj β).psum n) := by
  obtain ⟨t, ht⟩ := pisot_conjPowSum_add_mem_int hβ n
  refine ⟨t, ?_⟩
  rw [← ht, Multiset.psum_def, allConj_eq_cons hβ.2.1.tower_top, Multiset.map_cons,
    Multiset.sum_cons, conjPowSum]

/-- **`k! · Eₖ(N) ∈ ℤ`.** -/
theorem isRatInt_factorial_mul_eFull {β : ℝ} (hβ : IsPisot β) (k N : ℕ) :
    IsRatInt ((k.factorial : ℂ) * eFull β k N) := by
  refine multiset_isRatInt_factorial_mul_esymm _ k fun j _ => ?_
  have h : ((allConj β).map (· ^ N)).psum j = (allConj β).psum (N * j) := by
    rw [Multiset.psum_def, Multiset.psum_def, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun z _ => by rw [Function.comp_apply, ← pow_mul])
  rw [h]
  exact isRatInt_psum_allConj hβ _

/-- A rational integer of modulus `< 1` is zero. -/
theorem eq_zero_of_isRatInt_of_norm_lt_one {x : ℂ} (hx : IsRatInt x) (h : ‖x‖ < 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  have : (|z| : ℝ) < 1 := by rwa [Complex.norm_intCast] at h
  have hz : z = 0 := by
    by_contra hne
    exact absurd this (not_lt.2 (by exact_mod_cast Int.one_le_abs hne))
  simp [hz]

/-! ### The crude bound on `eₖ` -/

theorem norm_multiset_prod_eq (t : Multiset ℂ) : ‖t.prod‖ = (t.map (‖·‖)).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

/-- If every element of `s` has norm `≤ M`, then `‖eₖ(s)‖ ≤ (card s).choose k · M^k`. -/
theorem norm_esymm_le {s : Multiset ℂ} {M : ℝ} (hM : 0 ≤ M) (h : ∀ z ∈ s, ‖z‖ ≤ M) (k : ℕ) :
    ‖s.esymm k‖ ≤ ((Multiset.card s).choose k : ℝ) * M ^ k := by
  have hprod : ∀ t ∈ s.powersetCard k, ‖t.prod‖ ≤ M ^ k := by
    intro t ht
    have hcard : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
    have hle : t ≤ s := (Multiset.mem_powersetCard.1 ht).1
    rw [norm_multiset_prod_eq, ← hcard, ← Multiset.card_map (‖·‖) t]
    refine Multiset.prod_le_pow_card_of_le hM fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨norm_nonneg _, h z (Multiset.mem_of_le hle hz)⟩
  calc ‖s.esymm k‖ = ‖((s.powersetCard k).map Multiset.prod).sum‖ := rfl
    _ ≤ (((s.powersetCard k).map Multiset.prod).map (‖·‖)).sum := by
        simpa using norm_multiset_sum_le (((s.powersetCard k).map Multiset.prod))
    _ ≤ ((Multiset.card s).choose k : ℝ) * M ^ k := by
        have hcard : Multiset.card ((s.powersetCard k).map Multiset.prod)
            = (Multiset.card s).choose k := by
          rw [Multiset.card_map, Multiset.card_powersetCard]
        have hb : ∀ x ∈ (((s.powersetCard k).map Multiset.prod).map (‖·‖)), x ≤ M ^ k := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
          obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
          exact hprod t ht
        calc (((s.powersetCard k).map Multiset.prod).map (‖·‖)).sum
            ≤ (Multiset.card (((s.powersetCard k).map Multiset.prod).map (‖·‖)) : ℝ) * M ^ k := by
              have := Multiset.sum_le_card_nsmul
                (((s.powersetCard k).map Multiset.prod).map (‖·‖)) (M ^ k) hb
              simpa [nsmul_eq_mul] using this
          _ = ((Multiset.card s).choose k : ℝ) * M ^ k := by rw [Multiset.card_map, hcard]

/-- **`‖eₖ(N)‖ ≤ C(L,k) · ρ^(kN)`**, the crude bound on the small-conjugate symmetric functions. -/
theorem norm_eSmall_le (β : ℝ) (k N : ℕ) :
    ‖eSmall β k N‖
      ≤ ((Multiset.card (otherConj β)).choose k : ℝ) * (conjMax β ^ N) ^ k := by
  have h := norm_esymm_le (s := (otherConj β).map (· ^ N)) (M := conjMax β ^ N)
    (pow_nonneg (conjMax_nonneg β) N) ?_ k
  · rwa [Multiset.card_map] at h
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg w) (norm_le_conjMax hw) N

end LeanFormalizations.Transcendence.Dubickas
