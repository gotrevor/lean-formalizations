/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The shifted nested-interval construction for a general exponent `c ≥ 2`

`Chain.lean` is this file at `c = 3`.  Given primes `b 0, b 1, …` with `(b k)ᶜ < b (k+1)` and
`b (k+1) + 1 < (b k + 1)ᶜ`, it produces `A > 1` with `⌊A^(c^(k+1))⌋₊ = b k` for every `k`.

Saito's Lemma 3.6 needs exactly this: the rich-prime chain it builds must be glued onto a
finite prefix of the digits of `ξ_c` and turned back into a Mills number of exponent `c`.
-/
import Mathlib

namespace LeanFormalizations.Mills

namespace ChainC

variable {c : ℕ}

/-- `(xᶜ) ^ (c^(k+1))⁻¹ = x ^ (c^k)⁻¹`: one `c`-th power eats one level of the root. -/
private lemma pow_root_step (hc : 2 ≤ c) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ c) ^ ((((c ^ (k+1) : ℕ)) : ℝ))⁻¹ = x ^ ((((c ^ k : ℕ)) : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast x c, ← Real.rpow_mul hx]
  congr 1
  have hc0 : (0:ℕ) < c := by omega
  have hk : (((c ^ k : ℕ)) : ℝ) ≠ 0 := by
    have : (0:ℕ) < c ^ k := Nat.pow_pos hc0
    positivity
  have hcne : ((c:ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

variable (c) (b : ℕ → ℕ)

/-- Left endpoints of the shifted nested intervals. -/
private noncomputable def mu (k : ℕ) : ℝ := (b k : ℝ) ^ ((((c ^ (k+1) : ℕ)) : ℝ))⁻¹
/-- Right endpoints of the shifted nested intervals. -/
private noncomputable def nu (k : ℕ) : ℝ := ((b k : ℝ) + 1) ^ ((((c ^ (k+1) : ℕ)) : ℝ))⁻¹

private lemma exp_pos (hc : 2 ≤ c) (k : ℕ) : (0:ℝ) < ((((c ^ k : ℕ)) : ℝ))⁻¹ := by
  have : (0:ℕ) < c ^ k := Nat.pow_pos (by omega)
  positivity

variable (hc : 2 ≤ c)
variable (hlo : ∀ k, (b k) ^ c < b (k + 1)) (hhi : ∀ k, b (k + 1) + 1 < (b k + 1) ^ c)

include hc hlo in
private lemma mu_lt_succ (k : ℕ) : mu c b k < mu c b (k + 1) := by
  have hlt : ((b k : ℝ)) ^ c < (b (k+1) : ℝ) := by exact_mod_cast hlo k
  have := Real.rpow_lt_rpow (by positivity) hlt (exp_pos c hc (k+2))
  rwa [pow_root_step hc (x := (b k : ℝ)) (by positivity) (k+1)] at this

include hc hhi in
private lemma nu_succ_lt (k : ℕ) : nu c b (k + 1) < nu c b k := by
  have hlt : (b (k+1) : ℝ) + 1 < ((b k : ℝ) + 1) ^ c := by
    have hcc : ((b (k+1) + 1 : ℕ) : ℝ) < (((b k + 1) ^ c : ℕ) : ℝ) := by exact_mod_cast hhi k
    push_cast at hcc; linarith
  have := Real.rpow_lt_rpow (by positivity) hlt (exp_pos c hc (k+2))
  rwa [pow_root_step hc (x := (b k : ℝ) + 1) (by positivity) (k+1)] at this

include hc in
private lemma mu_lt_nu (k : ℕ) : mu c b k < nu c b k :=
  Real.rpow_lt_rpow (by positivity) (by linarith) (exp_pos c hc (k+1))

include hc hlo hhi in
private lemma mu_le_nu (m k : ℕ) : mu c b m ≤ nu c b k := by
  have hmono : Monotone (mu c b) := monotone_nat_of_le_succ fun n => (mu_lt_succ c b hc hlo n).le
  have hanti : Antitone (nu c b) := antitone_nat_of_succ_le fun n => (nu_succ_lt c b hc hhi n).le
  rcases le_total m k with hmk | hmk
  · exact le_trans (hmono hmk) (mu_lt_nu c b hc k).le
  · exact le_trans (mu_lt_nu c b hc m).le (hanti hmk)

include hc hlo hhi in
private lemma mu_bddAbove : BddAbove (Set.range (mu c b)) :=
  ⟨nu c b 0, by rintro _ ⟨m, rfl⟩; exact mu_le_nu c b hc hlo hhi m 0⟩

include hc in
private lemma pow_mu (k : ℕ) : (mu c b k) ^ (c ^ (k+1)) = (b k : ℝ) :=
  Real.rpow_inv_natCast_pow (by positivity) (by have : (0:ℕ) < c ^ (k+1) := Nat.pow_pos (by omega)
                                                positivity)

include hc in
private lemma pow_nu (k : ℕ) : (nu c b k) ^ (c ^ (k+1)) = (b k : ℝ) + 1 :=
  Real.rpow_inv_natCast_pow (by positivity) (by have : (0:ℕ) < c ^ (k+1) := Nat.pow_pos (by omega)
                                                positivity)

include hc hlo hhi in
private lemma floor_pow_iSup (k : ℕ) :
    ⌊(⨆ n, mu c b n) ^ (c ^ (k+1))⌋₊ = b k := by
  set A : ℝ := ⨆ n, mu c b n with hA
  have hcpos : (0:ℕ) < c ^ (k+1) := Nat.pow_pos (by omega)
  have hlo' : mu c b k < A :=
    lt_of_lt_of_le (mu_lt_succ c b hc hlo k) (le_ciSup (mu_bddAbove c b hc hlo hhi) (k+1))
  have hhi' : A < nu c b k :=
    lt_of_le_of_lt (ciSup_le fun m => mu_le_nu c b hc hlo hhi m (k+1)) (nu_succ_lt c b hc hhi k)
  have hmupos : (0:ℝ) ≤ mu c b k := by unfold mu; positivity
  have h1 : (b k : ℝ) < A ^ (c ^ (k+1)) := by
    rw [← pow_mu c b hc k]; exact pow_lt_pow_left₀ hlo' hmupos (by omega)
  have h2 : A ^ (c ^ (k+1)) < (b k : ℝ) + 1 := by
    rw [← pow_nu c b hc k]
    exact pow_lt_pow_left₀ hhi' (le_of_lt (lt_of_le_of_lt hmupos hlo')) (by omega)
  have hnn : (0:ℝ) ≤ A ^ (c ^ (k+1)) := le_trans (Nat.cast_nonneg _) h1.le
  rw [Nat.floor_eq_iff hnn]
  exact ⟨h1.le, h2⟩

end ChainC

/-- **The shifted construction for exponent `c`.**  A prime chain with `(b k)ᶜ < b (k+1)` and
`b (k+1) + 1 < (b k + 1)ᶜ`, starting at `b 0 ≥ 2`, yields a real `A > 1` whose floors at the
exponents `c^(k+1)` are exactly the chain. -/
theorem exists_shifted_of_chainC {c : ℕ} {b : ℕ → ℕ} (hc : 2 ≤ c) (h2 : 2 ≤ b 0)
    (hlo : ∀ k, (b k) ^ c < b (k + 1)) (hhi : ∀ k, b (k + 1) + 1 < (b k + 1) ^ c) :
    ∃ A : ℝ, 1 < A ∧ ∀ k, ⌊A ^ (c ^ (k+1))⌋₊ = b k := by
  refine ⟨(⨆ n, ChainC.mu c b n), ?_, fun k => ChainC.floor_pow_iSup c b hc hlo hhi k⟩
  have hfl := ChainC.floor_pow_iSup c b hc hlo hhi 0
  have hApos : 0 < (⨆ n, ChainC.mu c b n) := by
    have hle : ChainC.mu c b 0 ≤ (⨆ n, ChainC.mu c b n) :=
      le_ciSup (ChainC.mu_bddAbove c b hc hlo hhi) 0
    refine lt_of_lt_of_le ?_ hle
    unfold ChainC.mu
    have : (0:ℕ) < c ^ (0+1) := Nat.pow_pos (by omega)
    positivity
  have hge : (2:ℝ) ≤ (⨆ n, ChainC.mu c b n) ^ (c ^ (0+1)) := by
    refine le_trans ?_ (Nat.floor_le (by positivity))
    rw [hfl]; exact_mod_cast h2
  by_contra hcon
  push Not at hcon
  have := pow_le_one₀ hApos.le hcon (n := c ^ (0+1))
  linarith

end LeanFormalizations.Mills
