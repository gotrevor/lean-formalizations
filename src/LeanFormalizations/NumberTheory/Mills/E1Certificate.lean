/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Phase 61, E1: the finite certificate over `ℤ[C₁₃]`

Exact arithmetic in the group ring `ℤ[C₁₃]` (lists of 13 coefficients), the bridge
`a ↦ a(ζ)` to any field with `ζ^13 = 1`, and the Cramer soundness lemma `cert_sound`: three
conjugate equations with a certificate force the eigenvalue codes or the unknowns `w` constant.
`cert_all` checks the certificate for all `2 · 27³` cases (`native_decide`).
-/

namespace E1Cert

/-- An element of `ℤ[C₁₃]`, as a list of 13 coefficients. -/
abbrev Cyc := List ℤ

def cget (a : Cyc) (i : ℕ) : ℤ := a.getD i 0

def cadd (a b : Cyc) : Cyc := List.ofFn (n := 13) fun k => cget a k + cget b k
def csub (a b : Cyc) : Cyc := List.ofFn (n := 13) fun k => cget a k - cget b k
def cmul (a b : Cyc) : Cyc :=
  List.ofFn (n := 13) fun k => ∑ i : Fin 13, cget a i * cget b (k - i : Fin 13)
def cunit (e : ℕ) (sg : ℤ) : Cyc := List.ofFn (n := 13) fun k => if (k : ℕ) = e % 13 then sg else 0
def czero : Cyc := List.ofFn (n := 13) fun _ => 0
def cone : Cyc := cunit 0 1

/-- `v(ζ) = 0` iff all coefficients agree. -/
def IsZ (a : Cyc) : Prop := ∀ i : Fin 13, cget a i = cget a 0
instance (a : Cyc) : Decidable (IsZ a) := by unfold IsZ; infer_instance

/-- Eigenvalue codes: `0 ↦ 0`, `1 + a ↦ ζ^a`, `14 + a ↦ -ζ^a`. -/
def code (c : Fin 27) (m : ℕ) : Cyc :=
  if (c : ℕ) = 0 then czero
  else if (c : ℕ) ≤ 13 then cunit (((c : ℕ) - 1) * 2 ^ m) 1
  else cunit (((c : ℕ) - 14) * 2 ^ m) (-1)

/-- Row `m` of the conjugate system: coefficient of `w col` in `τ^m (Σ u_k w_k)`. -/
def row (u : Fin 3 → Fin 27) (t : Fin 3) (m : Fin 12) (col : Fin 3) : Cyc :=
  code (u (col - (Fin.ofNat 3 (m : ℕ)) * t)) m

def det3 (M : Fin 3 → Fin 3 → Cyc) : Cyc :=
  let t := fun a b c => cmul (cmul a b) c
  csub (cadd (cadd (csub (csub (t (M 0 0) (M 1 1) (M 2 2)) (t (M 0 0) (M 1 2) (M 2 1)))
    (t (M 0 1) (M 1 0) (M 2 2))) (t (M 0 1) (M 1 2) (M 2 0))) (t (M 0 2) (M 1 0) (M 2 1)))
    (t (M 0 2) (M 1 1) (M 2 0))

def upd (M : Fin 3 → Fin 3 → Cyc) (j : Fin 3) : Fin 3 → Fin 3 → Cyc :=
  fun a b => if b = j then cone else M a b

def rowsM (u : Fin 3 → Fin 27) (t : Fin 3) (r : Fin 3 → Fin 12) : Fin 3 → Fin 3 → Cyc :=
  fun a col => row u t (r a) col

def dot (u : Fin 3 → Fin 27) (t : Fin 3) (m : Fin 12) (D : Fin 3 → Cyc) : Cyc :=
  cadd (cadd (cmul (row u t m 0) (D 0)) (cmul (row u t m 1) (D 1))) (cmul (row u t m 2) (D 2))

/-- The certificate on rows `0, 1, 2`: `d = det`, `D j` = Cramer numerators. -/
def CertP (u : Fin 3 → Fin 27) (t : Fin 3) (d : Cyc) (D : Fin 3 → Cyc) : Prop :=
  (¬ IsZ d ∧ IsZ (csub (D 0) (D 1)) ∧ IsZ (csub (D 1) (D 2))) ∨
  (∃ m : Fin 12, ¬ IsZ (csub (dot u t m D) d)) ∨
  (IsZ d ∧ ∃ j : Fin 3, ¬ IsZ (D j))

instance (u t d D) : Decidable (CertP u t d D) := by unfold CertP; infer_instance

def Mrows (u : Fin 3 → Fin 27) (t : Fin 3) : Fin 3 → Fin 3 → Cyc := rowsM u t ![0, 1, 2]

def Cert (u : Fin 3 → Fin 27) (t : Fin 3) : Prop :=
  (u 1 = u 0 ∧ u 2 = u 0) ∨
    CertP u t (det3 (Mrows u t)) ![det3 (upd (Mrows u t) 0), det3 (upd (Mrows u t) 1),
      det3 (upd (Mrows u t) 2)]

instance (u t) : Decidable (Cert u t) := by unfold Cert; infer_instance


/-! ### The bridge: `ℤ[C₁₃] → K`, `a ↦ a(ζ)` -/

section Bridge

variable {K : Type*} [Field K] {ζ : K}

/-- Evaluation at `ζ`. -/
def ev (ζ : K) (a : Cyc) : K := ∑ i : Fin 13, (cget a i : K) * ζ ^ (i : ℕ)

theorem cget_ofFn (f : Fin 13 → ℤ) (i : Fin 13) : cget (List.ofFn f) i = f i := by
  unfold cget
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem ev_add (a b : Cyc) : ev ζ (cadd a b) = ev ζ a + ev ζ b := by
  simp only [ev, cadd, cget_ofFn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem ev_sub (a b : Cyc) : ev ζ (csub a b) = ev ζ a - ev ζ b := by
  simp only [ev, csub, cget_ofFn, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem pow_fin_add (h13 : ζ ^ 13 = 1) (i j : Fin 13) :
    ζ ^ ((i + j : Fin 13) : ℕ) = ζ ^ (i : ℕ) * ζ ^ (j : ℕ) := by
  rw [← pow_add, Fin.val_add]
  conv_rhs => rw [← Nat.div_add_mod ((i : ℕ) + j) 13, pow_add, pow_mul, h13, one_pow, one_mul]

theorem ev_mul (h13 : ζ ^ 13 = 1) (a b : Cyc) : ev ζ (cmul a b) = ev ζ a * ev ζ b := by
  simp only [ev, cmul, cget_ofFn]
  push_cast
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [pow_fin_add h13]; ring

theorem ev_cunit (h13 : ζ ^ 13 = 1) (e : ℕ) (sg : ℤ) : ev ζ (cunit e sg) = sg * ζ ^ e := by
  have hmod : ζ ^ e = ζ ^ (e % 13) := by
    conv_lhs => rw [← Nat.div_add_mod e 13, pow_add, pow_mul, h13, one_pow, one_mul]
  simp only [ev, cunit, cget_ofFn]
  rw [Finset.sum_eq_single (⟨e % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13)]
  · simp [hmod]
  · intro b _ hb
    have : (b : ℕ) ≠ e % 13 := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem ev_czero : ev ζ czero = 0 := by simp only [ev, czero, cget_ofFn]; simp

theorem ev_cone (h13 : ζ ^ 13 = 1) : ev ζ cone = 1 := by
  rw [cone, ev_cunit h13]; simp

theorem ev_of_isZ (hsum : ∑ i : Fin 13, ζ ^ (i : ℕ) = 0) {a : Cyc} (h : IsZ a) : ev ζ a = 0 := by
  have : ev ζ a = (cget a 0 : K) * ∑ i : Fin 13, ζ ^ (i : ℕ) := by
    rw [ev, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]
  rw [this, hsum, mul_zero]

/-- The matrix of values. -/
def evM (ζ : K) (M : Fin 3 → Fin 3 → Cyc) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun a b => ev ζ (M a b)

theorem det_evM (h13 : ζ ^ 13 = 1) (M : Fin 3 → Fin 3 → Cyc) :
    (evM ζ M).det = ev ζ (det3 M) := by
  rw [Matrix.det_fin_three]
  simp only [evM, Matrix.of_apply, det3, ev_add, ev_sub, ev_mul h13]

end Bridge

/-! ### Soundness -/

section Sound

open Matrix

variable {K : Type*} [Field K] {ζ : K}

theorem ev_dot (h13 : ζ ^ 13 = 1) (u : Fin 3 → Fin 27) (t : Fin 3) (m : Fin 12) (D : Fin 3 → Cyc) :
    ev ζ (dot u t m D) = ∑ col, ev ζ (row u t m col) * ev ζ (D col) := by
  simp only [dot, ev_add, ev_mul h13, Fin.sum_univ_three]

theorem cert_sound (h13 : ζ ^ 13 = 1) (hsum : ∑ i : Fin 13, ζ ^ (i : ℕ) = 0)
    (hnz : ∀ a : Cyc, ev ζ a = 0 → IsZ a) {u : Fin 3 → Fin 27} {t : Fin 3} {w : Fin 3 → K}
    {c : K} (hc : c ≠ 0) (heq : ∀ m : Fin 12, ∑ col, ev ζ (row u t m col) * w col = c)
    (hcert : Cert u t) : (u 1 = u 0 ∧ u 2 = u 0) ∨ (∀ k, w k = w 0) := by
  classical
  rcases hcert with h | h
  · exact Or.inl h
  right
  set M := Mrows u t with hM
  set B := evM ζ M with hB
  have hBw : B *ᵥ w = fun _ => c := by
    funext a
    simp only [Matrix.mulVec, dotProduct, hB, evM, Matrix.of_apply, hM, Mrows, rowsM]
    fin_cases a
    · exact heq 0
    · exact heq 1
    · exact heq 2
  have key : ∀ j, ev ζ (det3 M) * w j = c * ev ζ (det3 (upd M j)) := by
    intro j
    have h1 : B.adjugate *ᵥ (B *ᵥ w) = B.det • w := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hBw, ← Matrix.cramer_eq_adjugate_mulVec] at h1
    have h2 := congrFun h1 j
    rw [Matrix.cramer_apply, show (fun _ : Fin 3 => c) = c • (fun _ : Fin 3 => (1 : K)) by
      funext; simp, Matrix.det_updateCol_smul] at h2
    have h3 : B.updateCol j (fun _ => (1 : K)) = evM ζ (upd M j) := by
      ext a b
      simp only [Matrix.updateCol_apply, hB, evM, upd, Matrix.of_apply]
      split_ifs <;> simp [ev_cone h13]
    rw [h3, det_evM h13, hB, det_evM h13] at h2
    simpa [Pi.smul_apply, smul_eq_mul] using h2.symm
  rcases h with ⟨hd, h01, h12⟩ | ⟨m, hm⟩ | ⟨hd, j, hj⟩
  · have hd' : ev ζ (det3 M) ≠ 0 := fun h0 => hd (hnz _ h0)
    have e01 := ev_of_isZ hsum h01
    have e12 := ev_of_isZ hsum h12
    rw [ev_sub] at e01 e12
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e01 e12
    have hw : ∀ k, w k = c * ev ζ (det3 (upd M k)) / ev ζ (det3 M) := fun k => by
      rw [eq_div_iff hd', mul_comm, key k]
    intro k
    rw [hw k, hw 0]
    fin_cases k
    · rfl
    · simp only [Fin.mk_one]; rw [sub_eq_zero.1 e01]
    · simp only [Fin.reduceFinMk]; rw [← sub_eq_zero.1 e12, ← sub_eq_zero.1 e01]
  · exfalso
    apply hm
    apply hnz
    rw [ev_sub, ev_dot h13]
    have := heq m
    have hmul : c * (∑ col, ev ζ (row u t m col) * ev ζ (![det3 (upd M 0), det3 (upd M 1),
        det3 (upd M 2)] col) - ev ζ (det3 M)) = 0 := by
      have e : ∀ col : Fin 3, ev ζ (![det3 (upd M 0), det3 (upd M 1), det3 (upd M 2)] col)
          = ev ζ (det3 (upd M col)) := fun col => by fin_cases col <;> rfl
      simp_rw [e]
      rw [mul_sub, Finset.mul_sum]
      have : ∑ col, c * (ev ζ (row u t m col) * ev ζ (det3 (upd M col)))
          = ev ζ (det3 M) * ∑ col, ev ζ (row u t m col) * w col := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun col _ => ?_
        linear_combination (ev ζ (row u t m col)) * (key col).symm
      rw [this, heq m]; ring
    exact (mul_eq_zero.1 hmul).resolve_left hc
  · exfalso
    apply hj
    apply hnz
    have := key j
    rw [ev_of_isZ hsum hd, zero_mul] at this
    have h0 := (mul_eq_zero.1 this.symm).resolve_left hc
    fin_cases j <;> simpa using h0

end Sound

theorem cert_all : ∀ t : Fin 3, t = 1 ∨ t = 2 → ∀ a b c : Fin 27, Cert ![a, b, c] t := by
  native_decide

end E1Cert
