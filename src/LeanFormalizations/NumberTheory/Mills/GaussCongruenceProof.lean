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


lemma trace_pow_eq_sum_cw' (N : ℕ) [NeZero N] :
    (C ^ N).trace = ∑ w : Fin N → Fin n, cw C N w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  exact trace_pow_eq_sum_cw C m



/-- rotation of words -/
def rotE (N n : ℕ) [NeZero N] : Equiv.Perm (Fin N → Fin n) where
  toFun w := fun t => w (t + 1)
  invFun w := fun t => w (t - 1)
  left_inv w := funext fun t => by simp
  right_inv w := funext fun t => by simp

variable {N : ℕ} [NeZero N]

lemma ofNat_succ (j : ℕ) : Fin.ofNat N (j + 1) = Fin.ofNat N j + 1 := by
  ext; simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

lemma ofNat_zero' : Fin.ofNat N 0 = 0 := by ext; simp [Fin.ofNat]

lemma rotE_pow (j : ℕ) : ∀ (w : Fin N → Fin n) (t : Fin N),
    ((rotE N n) ^ j) w t = w (t + Fin.ofNat N j) := by
  induction j with
  | zero => intro w t; rw [ofNat_zero', add_zero, pow_zero]; rfl
  | succ j ih =>
    intro w t
    rw [pow_succ, Equiv.Perm.mul_apply, ih ((rotE N n) w) t, ofNat_succ]
    show w (t + Fin.ofNat N j + 1) = w (t + (Fin.ofNat N j + 1))
    rw [add_assoc]

lemma cw_rotE (w : Fin N → Fin n) : cw C N ((rotE N n) w) = cw C N w := by
  rw [cw, cw]
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin N)) (fun t => C (w t) (w (t + 1)))

/-- if a word has a period `j` with `0 < j < N` and `N = p^(k+1)`, it has period `p^k`. -/
lemma pow_dvd_period {p k : ℕ} (hp : p.Prime) (hN : N = p ^ (k + 1))
    (w : Fin N → Fin n) (j : ℕ) (hj : 0 < j) (hjN : j < N)
    (hfix : ((rotE N n) ^ j) w = w) : ((rotE N n) ^ (p ^ k)) w = w := by
  classical
  set g := rotE N n with hg
  have hgN : g ^ N = 1 := by
    ext w t
    rw [hg, rotE_pow]
    have : Fin.ofNat N N = 0 := by ext; simp [Fin.ofNat]
    rw [this, add_zero]
    rfl
  -- multiples of a period are periods
  have hmul : ∀ d : ℕ, (g ^ d) w = w → ∀ q : ℕ, (g ^ (d * q)) w = w := by
    intro d hd q
    induction q with
    | zero => simp
    | succ q ih =>
      have : d * (q + 1) = d * q + d := by ring
      rw [this, pow_add, Equiv.Perm.mul_apply, hd, ih]
  -- minimal period
  have hex : ∃ d, 0 < d ∧ (g ^ d) w = w := ⟨j, hj, hfix⟩
  classical
  let d := Nat.find hex
  have hd : 0 < d ∧ (g ^ d) w = w := Nat.find_spec hex
  have hmin : ∀ e, e < d → ¬ (0 < e ∧ (g ^ e) w = w) := fun e he => Nat.find_min hex he
  have hdvd : ∀ e : ℕ, (g ^ e) w = w → d ∣ e := by
    intro e he
    have h1 : (g ^ (e % d)) w = w := by
      have heq : e = e % d + d * (e / d) := (Nat.mod_add_div e d).symm
      have h2 : (g ^ (e % d + d * (e / d))) w = w := by rw [← heq]; exact he
      rw [pow_add, Equiv.Perm.mul_apply, hmul d hd.2 (e / d)] at h2
      exact h2
    by_contra hnd
    have : 0 < e % d := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
    exact hmin _ (Nat.mod_lt _ hd.1) ⟨this, h1⟩
  -- d divides N = p^(k+1) and d ≤ j < N, so d ∣ p^k
  have hdN : d ∣ p ^ (k + 1) := hN ▸ hdvd N (by rw [hgN]; rfl)
  have hdj : d ≤ j := Nat.find_le ⟨hj, hfix⟩
  obtain ⟨i, hik, hdi⟩ := (Nat.dvd_prime_pow hp).1 hdN
  have hik' : i ≤ k := by
    by_contra hc
    have hik2 : i = k + 1 := by omega
    rw [hik2] at hdi
    omega
  have : d * p ^ (k - i) = p ^ k := by
    rw [hdi, ← pow_add]
    congr 1
    omega
  rw [← this]
  exact hmul d hd.2 (p ^ (k - i))




lemma ofNat_add (N : ℕ) [NeZero N] (a b : ℕ) :
    Fin.ofNat N (a + b) = Fin.ofNat N a + Fin.ofNat N b := by
  ext; simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

lemma ofNat_val_lt {N : ℕ} [NeZero N] (t : Fin N) : Fin.ofNat N t.val = t := by
  ext; simp [Fin.ofNat, Nat.mod_eq_of_lt t.isLt]

lemma ofNat_mod_dvd {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (a : ℕ) :
    Fin.ofNat M (Fin.ofNat N a).val = Fin.ofNat M a := by
  ext
  simp only [Fin.ofNat, Fin.val_mk]
  exact Nat.mod_mod_of_dvd a hMN

/-- the `p`-fold repetition of a word of length `M` -/
def repw (M p n : ℕ) [NeZero M] (u : Fin M → Fin n) : Fin (M * p) → Fin n :=
  fun t => u (Fin.ofNat M t.val)

/-- restriction of a word of length `M * p` to its first `M` letters -/
def resw (M p n : ℕ) [NeZero (M * p)] (w : Fin (M * p) → Fin n) : Fin M → Fin n :=
  fun s => w (Fin.ofNat (M * p) s.val)

lemma prod_ofNat_mod (M : ℕ) [NeZero M] (H : Fin M → ℤ) (p : ℕ) :
    ∏ t : Fin (M * p), H (Fin.ofNat M t.val) = (∏ s : Fin M, H s) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h : M * (p + 1) = M * p + M := Nat.mul_succ M p
    rw [Fintype.prod_equiv (finCongr h) (fun t : Fin (M * (p+1)) => H (Fin.ofNat M t.val))
      (fun t : Fin (M * p + M) => H (Fin.ofNat M t.val)) (fun t => by simp)]
    rw [Fin.prod_univ_add]
    have e1 : ∀ i : Fin (M * p), H (Fin.ofNat M (Fin.castAdd M i).val) = H (Fin.ofNat M i.val) :=
      fun i => by simp
    have e2 : ∀ i : Fin M, H (Fin.ofNat M (Fin.natAdd (M * p) i).val) = H i := by
      intro i
      congr 1
      ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_congr rfl (fun i _ => e2 i), ih,
      pow_succ]




lemma ofNat_add_one_of_dvd {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N) (t : Fin N) :
    Fin.ofNat M (t + 1).val = Fin.ofNat M t.val + 1 := by
  ext
  simp only [Fin.ofNat, Fin.val_mk, Fin.val_add, Fin.val_one']
  rw [Nat.mod_mod_of_dvd _ h, Nat.add_mod t.val (1 % N) M, Nat.mod_mod_of_dvd _ h,
    Nat.add_mod (t.val % M) (1 % M) M, Nat.mod_mod]

/-- the walk weight of a `p`-fold repetition is the walk weight for the entrywise `p`-th power -/
lemma cw_repw (M p : ℕ) [NeZero M] [NeZero (M * p)] (u : Fin M → Fin n) :
    cw C (M * p) (repw M p n u) = cw (C.map (fun a => a ^ p)) M u := by
  have hdvd : M ∣ M * p := Dvd.intro p rfl
  set H : Fin M → ℤ := fun s => C (u s) (u (s + 1)) with hH
  have hstep : ∀ t : Fin (M * p),
      C (repw M p n u t) (repw M p n u (t + 1)) = H (Fin.ofNat M t.val) := by
    intro t
    show C (u (Fin.ofNat M t.val)) (u (Fin.ofNat M (t + 1).val)) = H (Fin.ofNat M t.val)
    rw [ofNat_add_one_of_dvd hdvd t, hH]
  rw [cw, Finset.prod_congr rfl (fun t (_ : t ∈ Finset.univ) => hstep t), prod_ofNat_mod, cw,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [hH]
  simp [Matrix.map_apply, mul_pow]

/-- words fixed by rotation by `M` are exactly the `p`-fold repetitions -/
lemma sum_over_fixed (M p : ℕ) [NeZero M] [NeZero (M * p)] (F : (Fin (M * p) → Fin n) → ℤ) :
    ∑ w ∈ Finset.univ.filter
        (fun w : Fin (M * p) → Fin n => ¬ ((rotE (M * p) n) ^ M) w ≠ w), F w
      = ∑ u : Fin M → Fin n, F (repw M p n u) := by
  classical
  have hdvd : M ∣ M * p := Dvd.intro p rfl
  have hper : ∀ w : Fin (M * p) → Fin n, ((rotE (M * p) n) ^ M) w = w →
      ∀ (q : ℕ) (t : Fin (M * p)), w (t + Fin.ofNat (M * p) (M * q)) = w t := by
    intro w hw q t
    have hq : ((rotE (M * p) n) ^ (M * q)) w = w := by
      induction q with
      | zero => simp
      | succ q ih =>
        have he : M * (q + 1) = M * q + M := by ring
        rw [he, pow_add, Equiv.Perm.mul_apply, hw, ih]
    calc w (t + Fin.ofNat (M * p) (M * q)) = ((rotE (M * p) n) ^ (M * q)) w t :=
          (rotE_pow _ w t).symm
      _ = w t := by rw [hq]
  -- the restriction of a fixed word rebuilds it
  have hrebuild : ∀ w : Fin (M * p) → Fin n, ((rotE (M * p) n) ^ M) w = w →
      repw M p n (resw M p n w) = w := by
    intro w hw
    funext t
    show w (Fin.ofNat (M * p) (Fin.ofNat M t.val).val) = w t
    have h1 : Fin.ofNat (M * p) (Fin.ofNat M t.val).val
        = Fin.ofNat (M * p) (t.val % M) := rfl
    have h4 : Fin.ofNat (M * p) t.val
        = Fin.ofNat (M * p) (t.val % M) + Fin.ofNat (M * p) (M * (t.val / M)) := by
      rw [← ofNat_add]
      congr 1
      exact (Nat.mod_add_div _ _).symm
    rw [h1]
    calc w (Fin.ofNat (M * p) (t.val % M))
        = w (Fin.ofNat (M * p) (t.val % M) + Fin.ofNat (M * p) (M * (t.val / M))) :=
          (hper w hw (t.val / M) _).symm
      _ = w (Fin.ofNat (M * p) t.val) := by rw [← h4]
      _ = w t := by rw [ofNat_val_lt]
  refine Finset.sum_nbij' (resw M p n) (repw M p n) (fun w _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    funext t
    rw [rotE_pow]
    show u (Fin.ofNat M (t + Fin.ofNat (M * p) M).val) = u (Fin.ofNat M t.val)
    refine congrArg u ?_
    ext
    simp only [Fin.ofNat, Fin.val_mk, Fin.val_add]
    rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod t.val (M % (M * p)) M,
      Nat.mod_mod_of_dvd _ hdvd, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
    exact hrebuild w hw
  · intro u _
    funext s
    show u (Fin.ofNat M (Fin.ofNat (M * p) s.val).val) = u s
    rw [ofNat_mod_dvd hdvd, ofNat_val_lt]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
    rw [hrebuild w hw]



lemma dvd_pow_sub_pow_step {p m : ℕ} {a b : ℤ} (h : (p : ℤ) ^ (m + 1) ∣ a - b) :
    (p : ℤ) ^ (m + 2) ∣ a ^ p - b ^ p := by
  have hp1 : (p : ℤ) ∣ a - b :=
    dvd_trans (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero m)) h
  have h1 : (p : ℤ) ∣ ∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i) :=
    dvd_geom_sum₂_self (by exact_mod_cast hp1)
  have hgeom : (∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i)) * (a - b) = a ^ p - b ^ p :=
    (Commute.all a b).geom_sum₂_mul p
  rw [← hgeom, pow_succ' (p : ℤ) (m + 1)]
  exact mul_dvd_mul h1 h

lemma dvd_pow_sub_self {p : ℕ} (hp : p.Prime) (a : ℤ) : (p : ℤ) ∣ a ^ p - a := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card]
  ring




lemma rotE_pow_self (N : ℕ) [NeZero N] : (rotE N n) ^ N = 1 := by
  ext w t
  rw [rotE_pow]
  have h0 : Fin.ofNat N N = 0 := by ext; simp [Fin.ofNat]
  rw [h0, add_zero]
  rfl

/-- the free part of the walk sum is divisible by the length times the common divisor -/
lemma dvd_sum_nonfixed (p k : ℕ) (hp : p.Prime) [NeZero (p ^ k * p)]
    (F : (Fin (p ^ k * p) → Fin n) → ℤ)
    (hinv : ∀ w, F ((rotE (p ^ k * p) n) w) = F w) (q : ℤ) (hq : ∀ w, q ∣ F w) :
    ((p : ℤ) ^ (k + 1) * q) ∣
      ∑ w ∈ Finset.univ.filter
        (fun w : Fin (p ^ k * p) → Fin n => ((rotE (p ^ k * p) n) ^ (p ^ k)) w ≠ w), F w := by
  classical
  have hN : p ^ k * p = p ^ (k + 1) := (pow_succ p k).symm
  have main : ((p ^ k * p : ℕ) : ℤ) * q ∣
      ∑ w ∈ Finset.univ.filter
        (fun w : Fin (p ^ k * p) → Fin n => ((rotE (p ^ k * p) n) ^ (p ^ k)) w ≠ w), F w := by
    refine dvd_sum_of_free (rotE_pow_self (p ^ k * p)) (NeZero.pos _) F hinv _ ?_ ?_ q hq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro hc
      refine hw ?_
      have hcomm : ((rotE (p ^ k * p) n) ^ (p ^ k)) ((rotE (p ^ k * p) n) w)
          = (rotE (p ^ k * p) n) (((rotE (p ^ k * p) n) ^ (p ^ k)) w) := by
        simp only [← Equiv.Perm.mul_apply]
        rw [((Commute.refl (rotE (p ^ k * p) n)).pow_left (p ^ k)).eq]
      rw [hcomm] at hc
      exact (rotE (p ^ k * p) n).injective hc
    · intro w hw j hj hjN
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      intro hc
      exact hw (pow_dvd_period hp hN w j hj hjN hc)
  have hcast : ((p ^ k * p : ℕ) : ℤ) = (p : ℤ) ^ (k + 1) := by push_cast; ring
  rwa [hcast] at main

/-- walk sum split into the free part and the `p`-fold repetitions -/
lemma sum_split (p k : ℕ) [NeZero (p ^ k)] [NeZero (p ^ k * p)]
    (F : (Fin (p ^ k * p) → Fin n) → ℤ) :
    ∑ w : Fin (p ^ k * p) → Fin n, F w
      = (∑ w ∈ Finset.univ.filter
          (fun w : Fin (p ^ k * p) → Fin n => ((rotE (p ^ k * p) n) ^ (p ^ k)) w ≠ w), F w)
        + ∑ u : Fin (p ^ k) → Fin n, F (repw (p ^ k) p n u) := by
  classical
  rw [← sum_over_fixed (p ^ k) p F]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ F).symm




lemma dvd_prod_sub_prod {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (d : ℤ)
    (h : ∀ i ∈ s, d ∣ f i - g i) : d ∣ (∏ i ∈ s, f i) - ∏ i ∈ s, g i := by
  have h' : ∀ i ∈ s, f i ≡ g i [ZMOD d] := by
    intro i hi
    exact Int.modEq_iff_dvd.2 (dvd_sub_comm.mp (h i hi))
  have := Int.ModEq.prod h'
  exact (Int.modEq_iff_dvd.1 this.symm)

lemma dvd_cw_sub_cw (N : ℕ) [NeZero N] (A B : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (h : ∀ i j, d ∣ A i j - B i j) (w : Fin N → Fin n) :
    d ∣ cw A N w - cw B N w := by
  rw [cw, cw]
  exact dvd_prod_sub_prod _ _ _ d (fun t _ => h _ _)

/-- **The key induction.** -/
lemma key (p : ℕ) (hp : p.Prime) :
    ∀ (k m : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ),
      (∀ i j, (p : ℤ) ^ (m + 1) ∣ A i j - B i j) →
      (p : ℤ) ^ (k + m + 1) ∣ (A ^ (p ^ k)).trace - (B ^ (p ^ k)).trace := by
  intro k
  induction k with
  | zero =>
    intro m A B h
    rw [pow_zero, pow_one, pow_one, zero_add, ← Matrix.trace_sub]
    refine Finset.dvd_sum (fun i _ => ?_)
    exact h i i
  | succ k ih =>
    intro m A B h
    haveI hz1 : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    haveI hz2 : NeZero (p ^ k * p) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') hp.pos.ne'⟩
    rw [show p ^ (k + 1) = p ^ k * p from pow_succ p k, trace_pow_eq_sum_cw' A (p ^ k * p), trace_pow_eq_sum_cw' B (p ^ k * p),
      ← Finset.sum_sub_distrib,
      sum_split p k (fun w => cw A (p ^ k * p) w - cw B (p ^ k * p) w)]
    refine dvd_add ?_ ?_
    · have hfree := dvd_sum_nonfixed p k hp (fun w => cw A (p ^ k * p) w - cw B (p ^ k * p) w)
        (fun w => by rw [cw_rotE, cw_rotE]) ((p : ℤ) ^ (m + 1))
        (fun w => dvd_cw_sub_cw _ A B _ h w)
      have hpow : (p : ℤ) ^ (k + 1) * (p : ℤ) ^ (m + 1) = (p : ℤ) ^ (k + 1 + m + 1) := by
        rw [← pow_add]
        congr 1
      rwa [hpow] at hfree
    · have hrep : ∀ u : Fin (p ^ k) → Fin n,
          (cw A (p ^ k * p) (repw (p ^ k) p n u) - cw B (p ^ k * p) (repw (p ^ k) p n u))
            = cw (A.map (fun a => a ^ p)) (p ^ k) u - cw (B.map (fun a => a ^ p)) (p ^ k) u := by
        intro u; rw [cw_repw, cw_repw]
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hrep u), Finset.sum_sub_distrib,
        ← trace_pow_eq_sum_cw' _ (p ^ k), ← trace_pow_eq_sum_cw' _ (p ^ k)]
      have := ih (m + 1) (A.map (fun a => a ^ p)) (B.map (fun a => a ^ p)) (by
        intro i j
        simpa [Matrix.map_apply] using dvd_pow_sub_pow_step (h i j))
      have he : k + (m + 1) + 1 = k + 1 + m + 1 := by ring
      rwa [he] at this


end Necklace

/-- **The Gauss congruence for traces holds** (discharging the Literature hypothesis). -/
theorem gaussCongruenceTrace_holds : GaussCongruenceTrace := by
  intro n C p k hp
  haveI hz1 : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI hz2 : NeZero (p ^ k * p) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') hp.pos.ne'⟩
  set C' := C.map (fun a : ℤ => a ^ p) with hC'
  have h1 : (p : ℤ) ^ (k + 1) ∣ (C ^ (p ^ (k + 1))).trace - (C' ^ (p ^ k)).trace := by
    rw [show p ^ (k + 1) = p ^ k * p from pow_succ p k, trace_pow_eq_sum_cw' C (p ^ k * p),
      sum_split p k (cw C (p ^ k * p))]
    have hfix : ∑ u : Fin (p ^ k) → Fin n, cw C (p ^ k * p) (repw (p ^ k) p n u)
        = (C' ^ (p ^ k)).trace := by
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => cw_repw C (p ^ k) p u),
        ← trace_pow_eq_sum_cw' C' (p ^ k)]
    rw [hfix, add_sub_cancel_right]
    have hfree := dvd_sum_nonfixed p k hp (cw C (p ^ k * p)) (fun w => cw_rotE C w) 1
      (fun w => one_dvd _)
    rwa [mul_one] at hfree
  have h2 : (p : ℤ) ^ (k + 1) ∣ (C' ^ (p ^ k)).trace - (C ^ (p ^ k)).trace := by
    have hkey := key p hp k 0 C' C (fun i j => by
      simpa [hC', Matrix.map_apply] using dvd_pow_sub_self hp (C i j))
    simpa using hkey
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- Phase 29 (`ThreeAdic.mills_threeAdic`) without the Gauss-congruence hypothesis. -/
theorem mills_threeAdic' (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) (halg : IsAlgebraic ℚ A) :
    ∀ e : ℕ, ∃ K, ∀ k ≥ K,
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨ (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e] :=
  ThreeAdic.mills_threeAdic gaussCongruenceTrace_holds hB hM hD hG hA halg

/-- Phase 29 (`ThreeAdic.transcendental_of_not_pm_one`) without the Gauss-congruence hypothesis. -/
theorem transcendental_of_not_pm_one' (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) {e : ℕ}
    (h : ∃ᶠ k in atTop, ¬ ((⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ 1 [ZMOD 3 ^ e] ∨
      (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℤ) ≡ -1 [ZMOD 3 ^ e])) :
    Transcendental ℚ A :=
  ThreeAdic.transcendental_of_not_pm_one gaussCongruenceTrace_holds hB hM hD hG hA h

/-! ## Numeric anchors (faithfulness of the frozen statement)

`GaussCongruenceTrace` is a `Literature` def we are not allowed to restate, so these four
computations check it against real arithmetic: that it HOLDS where it should, that its exponent
`k+1` is sharp, and that primality of `p` is load-bearing (so we did not prove something weaker
or vacuous).  `C = !![1,2;3,4]` (non-symmetric, `det = -2`). -/

local notation "Cex" => (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ)

/-- anchor 1: the congruence itself, `p = 2`, `k = 2`. -/
theorem gauss_anchor_two : ((2:ℤ) ^ 3) ∣ ((Cex ^ (2 ^ 3)).trace - (Cex ^ (2 ^ 2)).trace) := by
  norm_num [pow_succ, Matrix.trace_fin_two, Matrix.mul_fin_two]

/-- anchor 2: the exponent `k+1` is SHARP — `2^3` does not divide the `k = 1` difference. -/
theorem gauss_anchor_sharp : ¬ (((2:ℤ) ^ 3) ∣ ((Cex ^ (2 ^ 2)).trace - (Cex ^ (2 ^ 1)).trace)) := by
  norm_num [pow_succ, Matrix.trace_fin_two, Matrix.mul_fin_two]

/-- anchor 3: `3^3` divides the `p = 3, k = 2` difference, and `3^4` does not. -/
theorem gauss_anchor_three : ((3:ℤ) ^ 3) ∣ ((Cex ^ (3 ^ 3)).trace - (Cex ^ (3 ^ 2)).trace) ∧
    ¬ (((3:ℤ) ^ 4) ∣ ((Cex ^ (3 ^ 3)).trace - (Cex ^ (3 ^ 2)).trace)) := by
  norm_num [pow_succ, Matrix.trace_fin_two, Matrix.mul_fin_two]

/-- anchor 4: PRIMALITY is load-bearing — for the composite base `9` and `k = 1`, `9^2` does NOT
divide `tr(C^(9^2)) - tr(C^9)`, so the prime hypothesis cannot be dropped. -/
theorem gauss_anchor_composite :
    ¬ (((9:ℤ) ^ 2) ∣ ((Cex ^ (9 ^ 2)).trace - (Cex ^ (9 ^ 1)).trace)) := by
  norm_num [pow_succ, Matrix.trace_fin_two, Matrix.mul_fin_two]


end LeanFormalizations.Mills.GaussCongruenceProof
