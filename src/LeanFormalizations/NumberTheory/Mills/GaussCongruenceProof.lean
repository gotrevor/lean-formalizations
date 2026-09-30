/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.UnipotentTrace

/-!
# Phase 49: the Gauss (Dold) congruence for matrix traces, proved; phase 29 becomes unconditional in it

Discharges the Literature hypothesis `Literature.GaussCongruenceTrace` (Steinlein, AMM 2017) by the
elementary necklace argument, and restates phase 29's 3-adic Mills results without it.

## Route (necklace counting)
`tr(A^N) = Σ_(w : Fin N → Fin n) ∏_t A (w t) (w (t+1 mod N))` (closed walks).  The cyclic group
`ℤ/N` acts by rotation, and the weight `f(w)` is rotation-invariant.  Take `N = p^(k+1)`.
1. Words **not** fixed by rotation by `p^k` have trivial stabilizer, since stabilizers are subgroups of
   the cyclic `p`-group `ℤ/p^(k+1)`.  So their orbits have size `p^(k+1)` and their total weight is
   `≡ 0 (mod p^(k+1))`.  (Sum over orbits; e.g. `Finset.sum_partition`/`MulAction` orbit–stabilizer; or
   avoid group actions by grouping words `w` with their rotations explicitly.)
2. Words fixed by rotation by `p^k` are exactly `w = u^p` with `u` of length `p^k`, and
   `f(u^p) = f(u)^p`.  So that part equals `Σ_u f(u)^p`.
3. **Lemma:** `Σ_(u : length p^k) f(u)^p ≡ Σ_u f(u) (mod p^(k+1))`.  Induct on `k`, or group `u` by
   minimal period `p^j` (`u = v^(p^(k−j))`, `v` primitive).  An orbit of size `p^j` contributes
   `p^j (f(v)^(p^(k−j+1)) − f(v)^(p^(k−j)))`, and `a^(p^(m+1)) ≡ a^(p^m) (mod p^(m+1))`
   (`Int.ModEq.pow_card_sub_one_eq_one`-style / LTE; this is the classical Euler–Fermat for prime powers).
   **Alternative (often easier in Lean):** strong induction on `k`, using step 2 at level `k` and the
   statement at level `k − 1` applied to the matrix whose "walk weights" are `f(u)`: that is, apply the
   statement to `A^(p^?)` or to Kronecker powers.  Choose whatever closes.
4. Assemble: `tr A^(p^(k+1)) = (≡ 0) + Σ_u f(u)^p ≡ Σ_u f(u) = tr A^(p^k)`.

A known short alternative proof: via `Matrix.charpoly` and Newton's identities over `ZMod (p^(k+1))`
— more Mathlib-heavy.  The necklace route is fully elementary.

Frozen: the statements below; all earlier statements (ThreeAdic's hypothesised theorems stay as they
are); `Literature/` (the def `GaussCongruenceTrace` is frozen; we PROVE it here).  No `private`.
-/

namespace LeanFormalizations.Mills.GaussCongruenceProof

open LeanFormalizations.Literature LeanFormalizations.Mills LeanFormalizations.Mills.ThreeAdic Filter

/-! ## Closed walks and the rotation action -/

section Necklace

open Finset


variable {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)

/-- weight of a path with `M` edges given by its `M+1` nodes -/
def plw (M : ℕ) (v : Fin (M + 1) → Fin n) : ℤ :=
  ∏ t : Fin M, C (v t.castSucc) (v t.succ)

/-- cyclic weight of a closed walk of length `N` -/
def cw (N : ℕ) [NeZero N] (w : Fin N → Fin n) : ℤ :=
  ∏ t : Fin N, C (w t) (w (t + 1))

lemma plw_cons (M : ℕ) (x : Fin n) (v : Fin (M + 1) → Fin n) :
    plw C (M + 1) (Fin.cons x v) = C x (v 0) * plw C M v := by
  rw [plw, plw, Fin.prod_univ_succ]
  simp [Fin.cons_succ]

lemma pow_apply_eq_sum (m : ℕ) (i j : Fin n) :
    (C ^ (m + 1)) i j = ∑ w : Fin m → Fin n, plw C (m + 1) (Fin.snoc (Fin.cons i w) j) := by
  induction m generalizing i with
  | zero =>
    rw [pow_one]
    simp only [plw, Fin.prod_univ_succ, Fin.snoc_castSucc, Finset.univ_unique,
      Finset.sum_singleton, Finset.prod_singleton, Fin.cons_zero, pow_one, Fin.prod_univ_zero,
      mul_one, Fin.castSucc_zero]
    congr 1
  | succ m ih =>
    rw [pow_succ' C (m+1), Matrix.mul_apply]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Fin n))
      (fun q : Fin n × (Fin m → Fin n) => C i q.1 * plw C (m+1) (Fin.snoc (Fin.cons q.1 q.2) j))
      (fun w => plw C (m+2) (Fin.snoc (Fin.cons i w) j)) ?_]
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun a _ => by rw [ih a, Finset.mul_sum])
    · intro q
      show C i q.1 * plw C (m+1) (Fin.snoc (Fin.cons q.1 q.2) j)
        = plw C (m+2) (Fin.snoc (Fin.cons i (Fin.cons q.1 q.2)) j)
      simp only [← Fin.cons_snoc_eq_snoc_cons, plw_cons, Fin.cons_zero]


lemma cw_eq_plw (m : ℕ) (v : Fin (m + 1) → Fin n) :
    cw C (m + 1) v = plw C (m + 1) (Fin.snoc v (v 0)) := by
  rw [cw, plw]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [Fin.snoc_castSucc]
  congr 1
  induction t using Fin.lastCases with
  | last =>
    have h1 : (Fin.last m).succ = Fin.last (m + 1) := rfl
    have h2 : (Fin.last m) + 1 = 0 := Fin.last_add_one m
    rw [h1, h2, Fin.snoc_last]
  | cast s =>
    have h1 : (s.castSucc).succ = (s.succ).castSucc := rfl
    have h2 : (s.castSucc : Fin (m+1)) + 1 = s.succ := Fin.coeSucc_eq_succ
    rw [h1, h2, Fin.snoc_castSucc]

lemma trace_pow_eq_sum_cw (m : ℕ) :
    (C ^ (m + 1)).trace = ∑ w : Fin (m + 1) → Fin n, cw C (m + 1) w := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have key : (∑ w : Fin (m + 1) → Fin n, cw C (m + 1) w)
      = ∑ q : Fin n × (Fin m → Fin n), cw C (m + 1) (Fin.cons q.1 q.2) :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n))
      (fun q : Fin n × (Fin m → Fin n) => cw C (m + 1) (Fin.cons q.1 q.2))
      (fun w : (i : Fin (m + 1)) → Fin n => cw C (m + 1) w) (fun q => rfl)).symm
  rw [key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_apply_eq_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [cw_eq_plw]
  simp


open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- the `g`-orbit of `x`, as the image of `Fin N` -/
def orb (g : Equiv.Perm X) (N : ℕ) (x : X) : Finset X :=
  Finset.image (fun j : Fin N => (g ^ (j : ℕ)) x) Finset.univ

variable {g : Equiv.Perm X} {N : ℕ}

lemma pow_mod (hgN : g ^ N = 1) (a : ℕ) (x : X) : (g ^ (a % N)) x = (g ^ a) x := by
  conv_rhs => rw [← Nat.div_add_mod a N, pow_add, pow_mul, hgN, one_pow, one_mul]

lemma pow_congr (hgN : g ^ N = 1) {a b : ℕ} (h : a % N = b % N) (x : X) :
    (g ^ a) x = (g ^ b) x := by
  rw [← pow_mod hgN a, ← pow_mod hgN b, h]

lemma mem_orb_iff (hgN : g ^ N = 1) (hN : 0 < N) (x y : X) :
    y ∈ orb g N x ↔ ∃ j : ℕ, (g ^ j) x = y := by
  simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j % N, Nat.mod_lt _ hN⟩, pow_mod hgN j x⟩

lemma self_mem_orb (hN : 0 < N) (x : X) : x ∈ orb g N x := by
  simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨0, hN⟩, by simp⟩

lemma comp_pow (a b : ℕ) (x : X) : (g ^ a) ((g ^ b) x) = (g ^ (a + b)) x := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]

lemma orb_pow (hgN : g ^ N = 1) (hN : 0 < N) (j : ℕ) (x : X) :
    orb g N ((g ^ j) x) = orb g N x := by
  ext y
  rw [mem_orb_iff hgN hN, mem_orb_iff hgN hN]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i + j, by rw [pow_add]; simpa using hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i + j * (N - 1), ?_⟩
    rw [comp_pow]
    have he : i + j * (N - 1) + j = i + N * j := by
      have : 1 ≤ N := hN
      cases N with
      | zero => omega
      | succ M => simp only [Nat.add_sub_cancel]; ring
    rw [he, pow_add, pow_mul, hgN, one_pow, mul_one, hi]


/-- On a set `A` where the `N`-cycle `g` acts freely, the sum of a `g`-invariant function is
divisible by `N`. -/
lemma dvd_sum_of_free (hgN : g ^ N = 1) (hN : 0 < N) (F : X → ℤ)
    (hF : ∀ x, F (g x) = F x) (A : Finset X)
    (hclosed : ∀ x ∈ A, g x ∈ A)
    (hfree : ∀ x ∈ A, ∀ j, 0 < j → j < N → (g ^ j) x ≠ x)
    (q : ℤ) (hq : ∀ x, q ∣ F x) :
    (N : ℤ) * q ∣ ∑ x ∈ A, F x := by
  classical
  have hFpow : ∀ (j : ℕ) (x : X), F ((g ^ j) x) = F x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hF, ih]
  have hclosedpow : ∀ x ∈ A, ∀ j : ℕ, (g ^ j) x ∈ A := by
    intro x hx j
    induction j with
    | zero => simpa using hx
    | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hclosed _ ih
  rw [← Finset.sum_fiberwise_of_maps_to (f := F) (g := orb g N) (s := A)
    (t := A.image (orb g N)) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.dvd_sum (fun S hS => ?_)
  obtain ⟨x₀, hx₀A, rfl⟩ := Finset.mem_image.1 hS
  have hfib : A.filter (fun x => orb g N x = orb g N x₀) = orb g N x₀ := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hy⟩
      rw [← hy]; exact self_mem_orb hN y
    · intro hy
      obtain ⟨j, rfl⟩ := (mem_orb_iff hgN hN _ _).1 hy
      exact ⟨hclosedpow _ hx₀A j, orb_pow hgN hN j x₀⟩
  rw [hfib]
  have hconst : ∑ y ∈ orb g N x₀, F y = (orb g N x₀).card * F x₀ := by
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul]
    obtain ⟨j, rfl⟩ := (mem_orb_iff hgN hN _ _).1 hy
    exact hFpow j x₀
  have key : ∀ a b : ℕ, a < b → b < N → (g ^ a) x₀ ≠ (g ^ b) x₀ := by
    intro a b hab hbN hEq
    refine hfree _ (hclosedpow _ hx₀A a) (b - a) (by omega) (by omega) ?_
    rw [comp_pow, Nat.sub_add_cancel (le_of_lt hab)]
    exact hEq.symm
  have hcard : (orb g N x₀).card = N := by
    rw [orb, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro a b hab
    by_contra hne
    have hne' : (a : ℕ) ≠ (b : ℕ) := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact key a b h b.isLt hab
    · exact key b a h a.isLt hab.symm
  rw [hconst, hcard]
  exact mul_dvd_mul_left (N : ℤ) (hq x₀)


end Necklace

/-- **The Gauss congruence for traces holds** (discharging the Literature hypothesis). -/
theorem gaussCongruenceTrace_holds : GaussCongruenceTrace := by
  sorry

/-- Phase 29 (`ThreeAdic.mills_threeAdic`) without the Gauss-congruence hypothesis. -/
theorem mills_threeAdic' (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) (halg : IsAlgebraic ℚ A) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨ (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e] := by
  sorry

/-- Phase 29 (`ThreeAdic.transcendental_of_not_pm_one`) without the Gauss-congruence hypothesis. -/
theorem transcendental_of_not_pm_one' (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) {e : ℕ}
    (h : ∃ᶠ k in atTop, ¬ ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e])) :
    Transcendental ℚ A := by
  sorry

end LeanFormalizations.Mills.GaussCongruenceProof
