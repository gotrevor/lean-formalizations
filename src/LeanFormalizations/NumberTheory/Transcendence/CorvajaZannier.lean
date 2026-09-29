/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Corvaja–Zannier (2004) from Stephan's Subspace Theorem — closing the phase-9 wall

Phase 9 (`DubickasNoSubspace.lean`, `PROBE-DUBICKAS-NOSUBSPACE.md`) reduced Dubickas's Lemma 6
to Corvaja–Zannier's Main Theorem, which needs the `p`-adic Subspace Theorem, and left two
disclosed `sorry`s: `corvajaZannier_dichotomy` and `corvajaZannier_lemma4`.  R. Stephan has now
machine-checked the Subspace Theorem with several places (`Literature.Stephan2026Subspace`,
verbatim) and Ridout/Roth (`Literature.Stephan2026Ridout`).  This file derives the two phase-9
statements, and then `Dubickas2022`, from those two `Prop`s.  Once the toolchains meet
(`PROBE-ROTH.md`) the whole Dubickas Theorem 1 chain becomes unconditional.

## Source

P. Corvaja, U. Zannier, *On the rational approximations to the powers of an algebraic number:
solution of two problems of Mahler and Mendès France*, Acta Math. **193** (2004), 175–191,
arXiv:math/0403522; local text `papers/corvaja-zannier-2004-powers-algebraic.txt` (gitignored).
12 pages.  They apply the Subspace Theorem "in the form [S, Theorem 1D′]" (Schmidt, LNM 1467):
number field `K`, finite set of places `S`, linearly independent forms per place — which is
exactly `Stephan2026Subspace`.

## Route (CZ's numbering)

Setting: `K` Galois over `ℚ` containing `α`, `S` a Galois-stable finite set of places containing
the archimedean ones with `α` an `S`-unit; places normalised as in CZ §2 (Stephan's `approxProd`
raises archimedean factors to `v.mult`, which is CZ's `d(σ)/[K:ℚ]` normalisation up to the global
`1/[K:ℚ]` power — check the exponent bookkeeping once, early).

* **Lemma 1** (from Subspace): an infinite set of `S`-units `u` with
  `|Σ λ_i σ_i(u)|_w < max_i |σ_i(u)|_w · H(u)^(−ε)` has infinitely many members on one nontrivial
  linear relation `Σ a_i σ_i(u) = 0`.  Proof in CZ p. 3: forms `L_{w,1} = Σ λ_i X_i`, coordinate
  forms elsewhere, product formula for `S`-units.
* **Lemma 2** (unit equation, from Subspace, CZ cite [S, Ch. 4]): infinitely many solutions of
  `Σ a_i σ_i(u) = 0` ⇒ infinitely many on some `a σ_i(u) + b σ_j(u) = 0`.  Induction on `n`
  with Lemma 1-style Subspace applications (every vanishing subsum argument).
* **Lemma 3** (the key, from Subspace + Roth): infinitely many `(q, u) ∈ ℤ × (O_S^× ∩ k)` with
  `|δqu| > 1`, `δqu` not pseudo-Pisot, `0 < ‖δqu‖ < H(u)^(−ε) q^(−d−ε)` ⇒ some `u/δ′` lies in a
  proper subfield `k′ ⊂ k` along an infinite subsequence.
* **Main Theorem**: iterate Lemma 3 down the finite subfield lattice to `ℚ`, where Roth
  (`Stephan2026Ridout` ⇒ `Roth1955`, `StephanEdges.lean`) finishes.
* **Lemma 4** (from Lemma 1): if `Tr(q_n αⁿ) ∈ ℤ ∖ {0}` for infinitely many `n` with
  `log q_n = o(n)`, then `α` is an algebraic integer or an `h`-th root of a rational.

Our application needs only `Γ = ⟨α⟩`, `δ = 1`, `q` fixed, `u = α^(s n)`.  Specialise the Main
Theorem as far as it helps; the frozen targets are only the three theorems at the bottom.  Split
any `sorry` into further named leaves freely, restate a leaf if the proof wants another shape.
A precise obstruction written into `PROBE-DUBICKAS-NOSUBSPACE.md` (which step needs what beyond
the two `Prop`s) also counts as progress.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Pisot
import LeanFormalizations.NumberTheory.Diophantine.StephanEdges
import LeanFormalizations.NumberTheory.Transcendence.DubickasNoSubspace

set_option maxRecDepth 20000

namespace LeanFormalizations.Transcendence.Dubickas

open LeanFormalizations.Literature

/-!
## Step 0 — the Subspace Theorem in the shape Corvaja–Zannier actually use

CZ apply "[S, Theorem 1D′]" and immediately read off *one* nontrivial linear relation satisfied
by infinitely many of the points.  `Stephan2026Subspace` gives a `Finset` of proper subspaces
instead; the bridge is pigeonhole plus "a proper subspace of a finite-dimensional space is cut
out by a nonzero linear form".
-/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
open Height in
/-- **Subspace Theorem, CZ's usable form.**  An infinite set of nonzero solutions of the
approximation inequality satisfies one fixed nontrivial linear relation along an infinite
subset. -/
theorem exists_dual_infinite_of_stephan (hSub : Stephan2026Subspace)
    {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [Nontrivial ι]
    (Sinf : Finset (NumberField.InfinitePlace K)) (Sfin : Finset (NumberField.FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K))
    (hLi : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLf : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    {ε : ℝ} (hε : 0 < ε) (Ξ : Set (ι → K)) (hΞ : Ξ.Infinite) (h0 : ∀ x ∈ Ξ, x ≠ 0)
    (hle : ∀ x ∈ Ξ, approxProd Sinf Sfin (fun v ↦ v) L x ≤
      mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)) :
    ∃ a : Module.Dual K (ι → K), a ≠ 0 ∧ {x ∈ Ξ | a x = 0}.Infinite := by
  classical
  obtain ⟨T, hTne, hT⟩ := hSub Sinf Sfin L hLi hLf hε
  -- pigeonhole: `Ξ` is covered by the finitely many `Ξ ∩ W`
  have hcov : Ξ ⊆ ⋃ W ∈ T, {x ∈ Ξ | x ∈ W} := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := hT x (h0 x hx) (hle x hx)
    exact Set.mem_biUnion hW ⟨hx, hxW⟩
  have : ∃ W ∈ T, {x ∈ Ξ | x ∈ W}.Infinite := by
    by_contra hcon
    push Not at hcon
    refine hΞ ?_
    refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet ?_) hcov
    intro W hW
    exact hcon W hW
  obtain ⟨W, hW, hWinf⟩ := this
  obtain ⟨y, hy⟩ : ∃ y : ι → K, y ∉ W := by
    by_contra hc
    push Not at hc
    exact hTne W hW (eq_top_iff.2 fun z _ ↦ hc z)
  have hq : W.mkQ y ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  haveI : Module.Free K ((ι → K) ⧸ W) := Module.Free.of_divisionRing K _
  haveI : Module.Projective K ((ι → K) ⧸ W) := Module.Projective.of_free
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K hq
  refine ⟨f ∘ₗ W.mkQ, ?_, hWinf.mono ?_⟩
  · intro hzero
    exact hf (by rw [show f (W.mkQ y) = (f ∘ₗ W.mkQ) y from rfl, hzero]; simp)
  · rintro x ⟨hx, hxW⟩
    refine ⟨hx, ?_⟩
    show f (W.mkQ x) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hxW, map_zero]

/-!
## Step 1 — `S`-units and the product formula restricted to `S`

CZ work with `S` containing all archimedean places and stable under Galois; in mathlib's
normalisation the infinite part is therefore `Finset.univ` and only the finite part `Sfin`
carries information.  Everything CZ get "from the product formula" is the two lemmas below.
-/

namespace CZ

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- `u` is an `S`-unit: nonzero, with `|u|_v = 1` at every finite place outside `Sfin`. -/
def IsSUnit (Sfin : Finset (FinitePlace K)) (u : K) : Prop :=
  u ≠ 0 ∧ ∀ v : FinitePlace K, v ∉ Sfin → v u = 1

/-- For an `S`-unit the infinite product over all finite places collapses to `Sfin`. -/
theorem finprod_finitePlace_eq_prod {Sfin : Finset (FinitePlace K)} {u : K}
    (hu : IsSUnit Sfin u) : (∏ᶠ v : FinitePlace K, v u) = ∏ v ∈ Sfin, v u := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
  simp only [Function.mem_mulSupport] at hv
  by_contra h
  exact hv (hu.2 v (by simpa using h))

/-- **Product formula for an `S`-unit**, in the shape CZ use it: the product over `S` alone
is `1`. -/
theorem prod_places_eq_one_of_isSUnit {Sfin : Finset (FinitePlace K)} {u : K}
    (hu : IsSUnit Sfin u) :
    ((∏ v : InfinitePlace K, v u ^ v.mult) * ∏ v ∈ Sfin, v u) = 1 := by
  rw [← finprod_finitePlace_eq_prod hu]
  exact prod_abs_eq_one hu.1

/-- Off `S` the `v`-norm of a tuple of `S`-units is `1`. -/
theorem iSup_eq_one_of_isSUnit {ι : Type*} [Nonempty ι] {Sfin : Finset (FinitePlace K)}
    {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i)) {v : FinitePlace K} (hv : v ∉ Sfin) :
    (⨆ i, v (x i)) = 1 := by
  have : ∀ i, v (x i) = 1 := fun i ↦ (hx i).2 v hv
  simp [this]

/-- **The height of a tuple of `S`-units is a product over `S` alone.** -/
theorem mulHeight_eq_prod_S {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i)) :
    Height.mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i) := by
  have hx0 : x ≠ 0 := by
    intro h
    exact (hx (Classical.arbitrary ι)).1 (by rw [h]; rfl)
  rw [NumberField.mulHeight_eq hx0]
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
  simp only [Function.mem_mulSupport] at hv
  by_contra h
  exact hv (iSup_eq_one_of_isSUnit hx (by simpa using h))

/-- The `S`-unit tuple has strictly positive `v`-norm at every place. -/
theorem iSup_pos_of_isSUnit {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i))
    (v : AbsoluteValue K ℝ) : 0 < ⨆ j, v (x j) := by
  refine lt_of_lt_of_le (v.pos (hx (Classical.arbitrary ι)).1) ?_
  exact le_ciSup (f := fun j ↦ v (x j)) (Set.Finite.bddAbove (Set.finite_range _)) _

/-- The product of the `v`-norms of an `S`-unit tuple over the places of `S` is `1`. -/
theorem prod_prod_eq_one_of_isSUnit {ι : Type*} [Fintype ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i)) :
    ((∏ v : InfinitePlace K, (∏ i, v (x i)) ^ v.mult) * ∏ v ∈ Sfin, ∏ i, v (x i)) = 1 := by
  have h1 : (∏ v : InfinitePlace K, (∏ i, v (x i)) ^ v.mult)
      = ∏ i, ∏ v : InfinitePlace K, v (x i) ^ v.mult := by
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun v _ ↦ (Finset.prod_pow _ _ _).symm
  have h2 : (∏ v ∈ Sfin, ∏ i, v (x i)) = ∏ i, ∏ v ∈ Sfin, v (x i) := Finset.prod_comm
  rw [h1, h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ ↦ prod_places_eq_one_of_isSUnit (hx i)

open Literature in
/-- **The `approxProd` evaluation.**  If at every place the product of the linear forms on the
`S`-unit tuple `x` differs from `∏ᵢ |xᵢ|_v` by the factor `c v`, then Stephan's double product is
exactly `(∏_S c) / H(x)^n`.  This is CZ's "multiplying and dividing by `|x₁|_w`" computation
(Lemma 1) and its Lemma-3 analogue, packaged once. -/
theorem approxProd_of_prod_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i))
    (L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)) (c : AbsoluteValue K ℝ → ℝ)
    (hL : ∀ v : AbsoluteValue K ℝ, ∏ i, v (L v i x) = c v * ∏ i, v (x i)) :
    approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v) L x
      = ((∏ v : InfinitePlace K, c v.1 ^ v.mult) * ∏ v ∈ Sfin, c v.1)
        / Height.mulHeight x ^ (Fintype.card ι) := by
  classical
  set n := Fintype.card ι with hn
  have hD : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ j, v (x j) := iSup_pos_of_isSUnit hx
  have key : ∀ v : AbsoluteValue K ℝ,
      (∏ i, v (L v i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = c v * (∏ i, v (x i)) / (⨆ j, v (x j)) ^ n := by
    intro v
    have hxx : (fun j ↦ algebraMap K K (x j)) = x := by funext j; simp
    rw [hxx, Finset.prod_div_distrib, hL v, Finset.prod_const, hn, Finset.card_univ]
  have keyI : ∀ v : InfinitePlace K,
      (∏ i, v.1 (L v.1 i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = c v.1 * (∏ i, v (x i)) / (⨆ j, v (x j)) ^ n := fun v ↦ key v.1
  have keyF : ∀ v : FinitePlace K,
      (∏ i, v.1 (L v.1 i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = c v.1 * (∏ i, v (x i)) / (⨆ j, v (x j)) ^ n := fun v ↦ key v.1
  have hone := prod_prod_eq_one_of_isSUnit (Sfin := Sfin) hx
  have hnum : (∏ v : InfinitePlace K, (c v.1 * ∏ i, v (x i)) ^ v.mult) *
      ∏ v ∈ Sfin, (c v.1 * ∏ i, v (x i))
      = (∏ v : InfinitePlace K, c v.1 ^ v.mult) * ∏ v ∈ Sfin, c v.1 := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    rw [mul_mul_mul_comm, hone, mul_one]
  have hden : (∏ v : InfinitePlace K, ((⨆ j, v (x j)) ^ n) ^ v.mult) *
      ∏ v ∈ Sfin, ((⨆ j, v (x j)) ^ n)
      = ((∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i)) ^ n := by
    rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun v _ ↦ ?_) rfl
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [approxProd]
  simp only [keyI, keyF]
  rw [mulHeight_eq_prod_S hx]
  simp only [div_pow, Finset.prod_div_distrib]
  rw [div_mul_div_comm, hnum, hden]

/-!
## Step 3 — CZ's linear forms and their independence

At the distinguished place `w` one coordinate form is replaced by `Σ λⱼ xⱼ`; everywhere else the
forms are the coordinates.  Independence is the only hypothesis `Stephan2026Subspace` asks for.
-/

/-- The linear form `x ↦ Σⱼ λⱼ xⱼ`. -/
noncomputable def czForm {ι : Type*} [Fintype ι] (lam : ι → K) : Module.Dual K (ι → K) :=
  ∑ j, lam j • (LinearMap.proj j : Module.Dual K (ι → K))

@[simp] theorem czForm_apply {ι : Type*} [Fintype ι] (lam x : ι → K) :
    czForm lam x = ∑ j, lam j * x j := by
  simp [czForm]

/-- The coordinate forms are linearly independent. -/
theorem linearIndependent_proj {ι : Type*} [Fintype ι] [DecidableEq ι] :
    LinearIndependent K (fun i : ι ↦ (LinearMap.proj i : Module.Dual K (ι → K))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := DFunLike.congr_fun hg (Pi.single j (1 : K))
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, LinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_ite_eq' Finset.univ j g] at h
  simpa using h

/-- CZ's forms at a place: the coordinate forms, with the `i₀`-th replaced by `Σ λⱼ xⱼ`. -/
noncomputable def czFormFamily {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (lam : ι → K) :
    ι → Module.Dual K (ι → K) :=
  fun i ↦ if i = i₀ then czForm lam else LinearMap.proj i

/-- **Independence of CZ's forms** at the distinguished place: needs only `λ_{i₀} ≠ 0`. -/
theorem linearIndependent_czFormFamily {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι}
    {lam : ι → K} (h0 : lam i₀ ≠ 0) : LinearIndependent K (czFormFamily i₀ lam) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hF : ∀ i j : ι, (czFormFamily i₀ lam i) (Pi.single j (1 : K))
      = if i = i₀ then lam j else (if i = j then 1 else 0) := by
    intro i j
    by_cases hi : i = i₀
    · subst hi; simp [czFormFamily, Pi.single_apply, eq_comm]
    · simp [czFormFamily, hi, Pi.single_apply]
  have hsum : ∀ j : ι,
      ∑ i, g i * (if i = i₀ then lam j else (if i = j then (1 : K) else 0)) = 0 := by
    intro j
    have h := DFunLike.congr_fun hg (Pi.single j (1 : K))
    simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, hF] using h
  have hi0 : g i₀ = 0 := by
    have h := hsum i₀
    rw [Finset.sum_congr rfl (g := fun i ↦ if i = i₀ then g i * lam i₀ else 0)
      (fun i _ ↦ by by_cases hi : i = i₀ <;> simp [hi])] at h
    rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i ↦ g i * lam i₀)] at h
    simp only [Finset.mem_univ, if_pos] at h
    exact (mul_eq_zero.mp h).resolve_right h0
  intro i
  by_cases hi : i = i₀
  · rw [hi]; exact hi0
  · have h := hsum i
    rw [Finset.sum_congr rfl (g := fun k ↦ (if k = i₀ then g i₀ * lam i else 0)
        + (if k = i then g k else 0))
      (fun k _ ↦ by
        by_cases hk : k = i₀
        · subst hk; simp [Ne.symm hi]
        · by_cases hk2 : k = i <;> simp [hk, hk2, hi])] at h
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i₀ (fun _ ↦ g i₀ * lam i),
      Finset.sum_ite_eq' Finset.univ i g] at h
    simp only [Finset.mem_univ, if_pos, hi0, zero_mul, zero_add] at h
    exact h

/-- A finite place and an infinite place are never the same absolute value. -/
theorem finitePlace_val_ne_infinitePlace_val (v : FinitePlace K) (w : InfinitePlace K) :
    v.1 ≠ w.1 := by
  intro h
  obtain ⟨φ, hφ⟩ := w.2
  have hw2 : w.1 ((1 : K) + 1) = 2 := by
    rw [← hφ]
    simp [NumberField.place_apply]
    norm_num
  have hv2 : v.1 ((1 : K) + 1) ≤ 1 := by
    refine le_trans (FinitePlace.add_le v (1 : K) 1) ?_
    simp [FinitePlace.coe_apply]
  rw [h, hw2] at hv2
  norm_num at hv2

open scoped Classical in
/-- CZ's family of linear forms: the coordinate forms everywhere, except that at the
distinguished place `w` the `i₀`-th form is `Σ λⱼ xⱼ`. -/
noncomputable def czL {ι : Type*} [Fintype ι] [DecidableEq ι] (w : AbsoluteValue K ℝ) (i₀ : ι)
    (lam : ι → K) : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K) :=
  fun v i ↦ if v = w then czFormFamily i₀ lam i else LinearMap.proj i

open scoped Classical in
/-- The deviation factor of `czL` at a place: `1` away from `w`. -/
noncomputable def czC {ι : Type*} [Fintype ι] (w : AbsoluteValue K ℝ) (i₀ : ι) (lam : ι → K)
    (x : ι → K) : AbsoluteValue K ℝ → ℝ := fun v ↦
  if v = w then w (∑ j, lam j * x j) / w (x i₀) else 1

open scoped Classical in
/-- `czL` realises `czC` as its deviation factor, in the sense `approxProd_of_prod_eq` wants. -/
theorem prod_czL {ι : Type*} [Fintype ι] [DecidableEq ι] {w : AbsoluteValue K ℝ} {i₀ : ι}
    {lam : ι → K} {x : ι → K} (hx0 : x i₀ ≠ 0) (v : AbsoluteValue K ℝ) :
    ∏ i, v (czL w i₀ lam v i x) = czC w i₀ lam x v * ∏ i, v (x i) := by
  by_cases hv : v = w
  · subst hv
    simp only [czL, czC, czFormFamily, eq_self_iff_true, if_true]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i ↦ v (x i)) (Finset.mem_univ i₀)]
    have hrest : ∀ i ∈ Finset.univ.erase i₀,
        v ((if i = i₀ then czForm lam else LinearMap.proj i) x) = v (x i) := by
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
      rfl
    rw [Finset.prod_congr rfl hrest, if_pos rfl, czForm_apply]
    rw [div_mul_eq_mul_div, mul_comm (v (x i₀)), ← mul_assoc, mul_div_assoc,
      div_self (v.pos hx0).ne', mul_one]
  · simp [czL, czC, hv]

/-- **Corvaja–Zannier, Lemma 1** (archimedean distinguished place), from Stephan's Subspace
Theorem.  An infinite set of `S`-unit tuples on which `Σ λᵢ xᵢ` is smaller than the `w`-norm of
the tuple times `H(x)^(−ε)` satisfies one fixed nontrivial linear relation infinitely often. -/
theorem czLemma1_arch (hSub : Stephan2026Subspace) {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] [Nontrivial ι] [DecidableEq ι]
    (Sfin : Finset (FinitePlace K)) (w : InfinitePlace K) (lam : ι → K) (i₀ : ι)
    (h0 : lam i₀ ≠ 0) (Ξ : Set (ι → K)) (hΞ : Ξ.Infinite)
    (hS : ∀ x ∈ Ξ, ∀ i, IsSUnit Sfin (x i)) {ε : ℝ} (hε : 0 < ε)
    (hineq : ∀ x ∈ Ξ, w (∑ i, lam i * x i) ≤ w (x i₀) * Height.mulHeight x ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {x ∈ Ξ | ∑ i, a i * x i = 0}.Infinite := by
  classical
  have hx0 : ∀ x ∈ Ξ, ∀ i, x i ≠ 0 := fun x hx i ↦ (hS x hx i).1
  have hxne : ∀ x ∈ Ξ, x ≠ 0 := fun x hx h ↦ hx0 x hx i₀ (by rw [h]; rfl)
  -- the deviation product collapses to the distinguished place
  have hcprod : ∀ x : ι → K,
      ((∏ v : InfinitePlace K, czC w.1 i₀ lam x v.1 ^ v.mult) * ∏ v ∈ Sfin, czC w.1 i₀ lam x v.1)
        = (czC w.1 i₀ lam x w.1) ^ w.mult := by
    intro x
    have hfin : ∀ v ∈ Sfin, czC w.1 i₀ lam x v.1 = 1 := fun v _ ↦ by
      simp [czC, finitePlace_val_ne_infinitePlace_val v w]
    rw [Finset.prod_congr rfl hfin, Finset.prod_const_one, mul_one,
      Finset.prod_eq_single w (fun v _ hvw ↦ by
        have hv : v.1 ≠ w.1 := fun h ↦ hvw (Subtype.ext h)
        simp [czC, hv]) (fun h ↦ absurd (Finset.mem_univ w) h)]
  -- the approximation bound
  have hbound : ∀ x ∈ Ξ, approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v)
      (czL w.1 i₀ lam) x ≤ Height.mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
    intro x hx
    rw [approxProd_of_prod_eq (hS x hx) _ _ (fun v ↦ prod_czL (hx0 x hx i₀) v), hcprod x]
    set H := Height.mulHeight x with hH
    have hH1 : (1 : ℝ) ≤ H := Height.one_le_mulHeight x
    have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
    have hc0 : 0 ≤ czC w.1 i₀ lam x w.1 := by
      simp only [czC, if_true]
      exact div_nonneg (w.1.nonneg _) (w.1.nonneg _)
    have hcle : czC w.1 i₀ lam x w.1 ≤ H ^ (-ε) := by
      simp only [czC, if_true]
      rw [div_le_iff₀ (w.1.pos (hx0 x hx i₀))]
      exact (hineq x hx).trans_eq (mul_comm _ _)
    have hrle : H ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH1 (by linarith)
    have hpow : czC w.1 i₀ lam x w.1 ^ w.mult ≤ H ^ (-ε) :=
      le_trans (pow_le_of_le_one hc0 (hcle.trans hrle) NumberField.InfinitePlace.mult_ne_zero) hcle
    rw [div_le_iff₀ (pow_pos hHpos _)]
    refine hpow.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast H (Fintype.card ι), ← Real.rpow_add hHpos]
    ring_nf
  -- independence of the forms
  have hLi : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)),
      LinearIndependent K (czL w.1 i₀ lam v.1) := by
    intro v _
    by_cases hv : v = w
    · have : czL w.1 i₀ lam v.1 = czFormFamily i₀ lam := by
        funext i; simp [czL, hv]
      rw [this]; exact linearIndependent_czFormFamily h0
    · have hv' : v.1 ≠ w.1 := fun h ↦ hv (Subtype.ext h)
      have : czL w.1 i₀ lam v.1 = fun i ↦ (LinearMap.proj i : Module.Dual K (ι → K)) := by
        funext i; simp [czL, hv']
      rw [this]; exact linearIndependent_proj
  have hLf : ∀ v ∈ Sfin, LinearIndependent K (czL w.1 i₀ lam v.1) := by
    intro v _
    have hv' : v.1 ≠ w.1 := finitePlace_val_ne_infinitePlace_val v w
    have : czL w.1 i₀ lam v.1 = fun i ↦ (LinearMap.proj i : Module.Dual K (ι → K)) := by
      funext i; simp [czL, hv']
    rw [this]; exact linearIndependent_proj
  obtain ⟨a, ha, hainf⟩ := exists_dual_infinite_of_stephan hSub (Finset.univ) Sfin
    (czL w.1 i₀ lam) hLi hLf hε Ξ hΞ hxne hbound
  refine ⟨fun i ↦ a (fun j ↦ if i = j then (1 : K) else 0), ?_, hainf.mono ?_⟩
  · intro hA
    refine ha (LinearMap.ext fun x ↦ ?_)
    rw [LinearMap.pi_apply_eq_sum_univ a x]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [congrFun hA i]
    simp
  · rintro x ⟨hx, hax⟩
    refine ⟨hx, ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ a x] at hax
    refine Eq.trans ?_ hax
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]


/-- **Corvaja–Zannier, Lemma 1** with a *finite* distinguished place `w ∈ S` — the form CZ's
Lemma 4 uses.  Same proof as `czLemma1_arch`, with the deviation product collapsing on the
finite side instead. -/
theorem czLemma1_fin (hSub : Stephan2026Subspace) {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] [Nontrivial ι] [DecidableEq ι]
    (Sfin : Finset (FinitePlace K)) (w : FinitePlace K) (hw : w ∈ Sfin) (lam : ι → K) (i₀ : ι)
    (h0 : lam i₀ ≠ 0) (Ξ : Set (ι → K)) (hΞ : Ξ.Infinite)
    (hS : ∀ x ∈ Ξ, ∀ i, IsSUnit Sfin (x i)) {ε : ℝ} (hε : 0 < ε)
    (hineq : ∀ x ∈ Ξ, w (∑ i, lam i * x i) ≤ w (x i₀) * Height.mulHeight x ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {x ∈ Ξ | ∑ i, a i * x i = 0}.Infinite := by
  classical
  have hx0 : ∀ x ∈ Ξ, ∀ i, x i ≠ 0 := fun x hx i ↦ (hS x hx i).1
  have hxne : ∀ x ∈ Ξ, x ≠ 0 := fun x hx h ↦ hx0 x hx i₀ (by rw [h]; rfl)
  have hcprod : ∀ x : ι → K,
      ((∏ v : InfinitePlace K, czC w.1 i₀ lam x v.1 ^ v.mult) * ∏ v ∈ Sfin, czC w.1 i₀ lam x v.1)
        = czC w.1 i₀ lam x w.1 := by
    intro x
    have hinf : ∀ v : InfinitePlace K, czC w.1 i₀ lam x v.1 ^ v.mult = 1 := fun v ↦ by
      simp [czC, (finitePlace_val_ne_infinitePlace_val w v).symm]
    rw [Finset.prod_congr rfl (fun v _ ↦ hinf v), Finset.prod_const_one, one_mul,
      Finset.prod_eq_single w (fun v _ hvw ↦ by
        have hv : v.1 ≠ w.1 := fun h ↦ hvw (Subtype.ext h)
        simp [czC, hv]) (fun h ↦ absurd hw h)]
  have hbound : ∀ x ∈ Ξ, approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v)
      (czL w.1 i₀ lam) x ≤ Height.mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
    intro x hx
    rw [approxProd_of_prod_eq (hS x hx) _ _ (fun v ↦ prod_czL (hx0 x hx i₀) v), hcprod x]
    set H := Height.mulHeight x with hH
    have hH1 : (1 : ℝ) ≤ H := Height.one_le_mulHeight x
    have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
    have hcle : czC w.1 i₀ lam x w.1 ≤ H ^ (-ε) := by
      simp only [czC, if_true]
      rw [div_le_iff₀ (w.1.pos (hx0 x hx i₀))]
      exact (hineq x hx).trans_eq (mul_comm _ _)
    rw [div_le_iff₀ (pow_pos hHpos _)]
    refine hcle.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast H (Fintype.card ι), ← Real.rpow_add hHpos]
    ring_nf
  have hLi : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)),
      LinearIndependent K (czL w.1 i₀ lam v.1) := by
    intro v _
    have hv' : v.1 ≠ w.1 := (finitePlace_val_ne_infinitePlace_val w v).symm
    have : czL w.1 i₀ lam v.1 = fun i ↦ (LinearMap.proj i : Module.Dual K (ι → K)) := by
      funext i; simp [czL, hv']
    rw [this]; exact linearIndependent_proj
  have hLf : ∀ v ∈ Sfin, LinearIndependent K (czL w.1 i₀ lam v.1) := by
    intro v _
    by_cases hv : v = w
    · have : czL w.1 i₀ lam v.1 = czFormFamily i₀ lam := by
        funext i; simp [czL, hv]
      rw [this]; exact linearIndependent_czFormFamily h0
    · have hv' : v.1 ≠ w.1 := fun h ↦ hv (Subtype.ext h)
      have : czL w.1 i₀ lam v.1 = fun i ↦ (LinearMap.proj i : Module.Dual K (ι → K)) := by
        funext i; simp [czL, hv']
      rw [this]; exact linearIndependent_proj
  obtain ⟨a, ha, hainf⟩ := exists_dual_infinite_of_stephan hSub (Finset.univ) Sfin
    (czL w.1 i₀ lam) hLi hLf hε Ξ hΞ hxne hbound
  refine ⟨fun i ↦ a (fun j ↦ if i = j then (1 : K) else 0), ?_, hainf.mono ?_⟩
  · intro hA
    refine ha (LinearMap.ext fun x ↦ ?_)
    rw [LinearMap.pi_apply_eq_sum_univ a x]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [congrFun hA i]
    simp
  · rintro x ⟨hx, hax⟩
    refine ⟨hx, ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ a x] at hax
    refine Eq.trans ?_ hax
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]

/-- At any place, the `v`-norm of a tuple is at most the product of the local heights. -/
theorem iSup_le_prod_max_one {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (⨆ i, f i) ≤ ∏ i, max (f i) 1 := by
  classical
  have h1 : ∀ j : ι, (1 : ℝ) ≤ max (f j) 1 := fun j ↦ le_max_right _ _
  refine ciSup_le fun i ↦ le_trans (le_max_left (f i) 1) ?_
  rw [← Finset.prod_erase_mul Finset.univ (fun j ↦ max (f j) 1) (Finset.mem_univ i)]
  refine le_mul_of_one_le_left (le_trans zero_le_one (h1 i)) ?_
  calc (1 : ℝ) = ∏ _j ∈ Finset.univ.erase i, (1 : ℝ) := by rw [Finset.prod_const_one]
    _ ≤ _ := Finset.prod_le_prod (fun j _ ↦ zero_le_one) (fun j _ ↦ h1 j)

/-- For an `S`-unit the `mulHeight₁` product over finite places collapses to `Sfin`. -/
theorem mulHeight₁_eq_prod_S {Sfin : Finset (FinitePlace K)} {u : K} (hu : IsSUnit Sfin u) :
    Height.mulHeight₁ u
      = (∏ v : InfinitePlace K, max (v u) 1 ^ v.mult) * ∏ v ∈ Sfin, max (v u) 1 := by
  rw [NumberField.mulHeight₁_eq]
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
  simp only [Function.mem_mulSupport] at hv
  by_contra h
  exact hv (by rw [hu.2 v (by simpa using h)]; simp)

/-- **`H(x) ≤ ∏ᵢ H(xᵢ)`** for a tuple of `S`-units.  This is how CZ compare the height of
`(σ₁(u), …, σₙ(u))` with that of `u`; combined with `mulHeight₁_mul_le` it gives the exponential
bound the applications need, with no place-permutation argument. -/
theorem mulHeight_le_prod_mulHeight₁ {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : ∀ i, IsSUnit Sfin (x i)) :
    Height.mulHeight x ≤ ∏ i, Height.mulHeight₁ (x i) := by
  classical
  have hregroup : (∏ i, Height.mulHeight₁ (x i))
      = (∏ v : InfinitePlace K, (∏ i, max (v (x i)) 1) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ i, max (v (x i)) 1 := by
    rw [Finset.prod_congr rfl (fun i _ ↦ mulHeight₁_eq_prod_S (hx i)), Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun v _ ↦ Finset.prod_pow _ _ _
    · exact Finset.prod_comm
  rw [mulHeight_eq_prod_S hx, hregroup]
  have hnn : ∀ (v : AbsoluteValue K ℝ), (⨆ i, v (x i)) ≤ ∏ i, max (v (x i)) 1 := fun v ↦
    iSup_le_prod_max_one _ fun i ↦ v.nonneg _
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Finset.prod_le_prod (fun v _ ↦ pow_nonneg (le_of_lt (iSup_pos_of_isSUnit hx v.1)) _)
      (fun v _ ↦ pow_le_pow_left₀ (le_of_lt (iSup_pos_of_isSUnit hx v.1)) (hnn v.1) _)
  · exact Finset.prod_le_prod (fun v _ ↦ le_of_lt (iSup_pos_of_isSUnit hx v.1))
      (fun v _ ↦ hnn v.1)
  · exact Finset.prod_nonneg fun v _ ↦ le_of_lt (iSup_pos_of_isSUnit hx v.1)
  · exact Finset.prod_nonneg fun v _ ↦ pow_nonneg
      (Finset.prod_nonneg fun i _ ↦ le_trans (v.1.nonneg _) (le_max_left _ _)) _

/-!
## Step 7 — `S`-integral tuples: the inequality form of the `approxProd` evaluation

CZ's Lemma 3 applies the Subspace Theorem to `x = (p, qσ₁(u), …, qσ_d(u))`, whose coordinates are
only `S`-*integers*.  Then `∏_{v∈S} ‖x‖_v ≥ H(x)` (the places off `S` contribute `≤ 1`), which is
the right direction for an upper bound on `approxProd`.
-/

/-- The `v`-norm of a nonzero tuple is `1` for all but finitely many finite places. -/
theorem hasFiniteMulSupport_iSup {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  classical
  obtain ⟨i₁, hi₁'⟩ := Function.ne_iff.mp hx
  have hi₁ : x i₁ ≠ 0 := by simpa using hi₁'
  set J : Finset ι := Finset.univ.filter (fun i ↦ x i ≠ 0) with hJdef
  have hi₁J : i₁ ∈ J := by simp [hJdef, hi₁]
  refine Set.Finite.subset (Set.Finite.biUnion J.finite_toSet
    (fun i hi ↦ NumberField.FinitePlace.hasFiniteMulSupport
      (x := x i) (by simpa [hJdef] using hi))) ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  by_contra hc
  simp only [Set.mem_iUnion₂, Function.mem_mulSupport, not_exists, not_and, not_not] at hc
  refine hv (le_antisymm (ciSup_le fun i ↦ ?_) ?_)
  · by_cases hxi : x i = 0
    · simp [hxi]
    · exact le_of_eq (hc i (by simp [hJdef, hxi]))
  · have h1 : v (x i₁) = 1 := hc i₁ (by simpa using hi₁J)
    calc (1 : ℝ) = v (x i₁) := h1.symm
      _ ≤ ⨆ i, v (x i) :=
        le_ciSup (f := fun i ↦ v (x i)) (Set.Finite.bddAbove (Set.finite_range _)) i₁

/-- For an `S`-integral tuple the height is at most the product of the `v`-norms over `S`. -/
theorem mulHeight_le_prod_S_of_sIntegral {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : x ≠ 0)
    (hint : ∀ v : FinitePlace K, v ∉ Sfin → (⨆ i, v (x i)) ≤ 1) :
    Height.mulHeight x ≤
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i) := by
  classical
  have hnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i, v (x i) := fun v ↦
    Real.iSup_nonneg fun i ↦ v.nonneg _
  rw [NumberField.mulHeight_eq hx]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hnn v.1) _)
  set f : FinitePlace K → ℝ := fun v ↦ ⨆ i, v (x i) with hf
  set g : FinitePlace K → ℝ := fun v ↦ if v ∈ Sfin then f v else 1 with hg
  have hgsupp : Function.mulSupport g ⊆ (Sfin : Set (FinitePlace K)) := by
    intro v hv
    simp only [Function.mem_mulSupport, hg] at hv
    by_contra h
    exact hv (if_neg (by simpa using h))
  have hgprod : (∏ᶠ v : FinitePlace K, g v) = ∏ v ∈ Sfin, f v := by
    rw [finprod_eq_prod_of_mulSupport_subset g hgsupp]
    exact Finset.prod_congr rfl fun v hv ↦ if_pos hv
  rw [← hgprod]
  refine finprod_le_finprod (hasFiniteMulSupport_iSup hx) (fun v ↦ hnn v.1)
    (Set.Finite.subset Sfin.finite_toSet hgsupp) fun v ↦ ?_
  by_cases hv : v ∈ Sfin
  · exact le_of_eq (if_pos hv).symm
  · simp only [hg, if_neg hv]
    exact hint v hv

open Literature in
/-- **The `approxProd` bound for `S`-integral tuples.**  If the double product of the linear
forms over `S` is at most `B`, then `approxProd ≤ B / H(x)^n`.  This is the inequality CZ derive
just before applying [S, Theorem 1D′] in the proof of Lemma 3. -/
theorem approxProd_le_of_prod_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {x : ι → K} (hx : x ≠ 0)
    (hint : ∀ v : FinitePlace K, v ∉ Sfin → (⨆ i, v (x i)) ≤ 1)
    (L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)) {B : ℝ}
    (hnum : ((∏ v : InfinitePlace K, (∏ i, v.1 (L v.1 i x)) ^ v.mult) *
      ∏ v ∈ Sfin, ∏ i, v.1 (L v.1 i x)) ≤ B) :
    approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v) L x
      ≤ B / Height.mulHeight x ^ (Fintype.card ι) := by
  classical
  set n := Fintype.card ι with hn
  have hnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i, v (x i) := fun v ↦
    Real.iSup_nonneg fun i ↦ v.nonneg _
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ i, v (x i) := by
    intro v
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (v.pos (by simpa using hi))
      (le_ciSup (f := fun j ↦ v (x j)) (Set.Finite.bddAbove (Set.finite_range _)) i)
  -- rewrite `approxProd` as numerator / denominator
  have hxx : (fun j ↦ algebraMap K K (x j)) = x := by funext j; simp
  have hsplit : ∀ v : AbsoluteValue K ℝ,
      (∏ i, v (L v i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = (∏ i, v (L v i x)) / (⨆ j, v (x j)) ^ n := by
    intro v
    rw [hxx, Finset.prod_div_distrib, Finset.prod_const, hn, Finset.card_univ]
  have keyI : ∀ v : InfinitePlace K,
      (∏ i, v.1 (L v.1 i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = (∏ i, v.1 (L v.1 i x)) / (⨆ j, v (x j)) ^ n := fun v ↦ hsplit v.1
  have keyF : ∀ v : FinitePlace K,
      (∏ i, v.1 (L v.1 i fun j ↦ algebraMap K K (x j)) / ⨆ j, v (x j))
        = (∏ i, v.1 (L v.1 i x)) / (⨆ j, v (x j)) ^ n := fun v ↦ hsplit v.1
  set P := (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i) with hP
  have hPpos : 0 < P :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hpos v.1) _) (Finset.prod_pos fun v _ ↦ hpos v.1)
  have hden : (∏ v : InfinitePlace K, ((⨆ j, v (x j)) ^ n) ^ v.mult) *
      ∏ v ∈ Sfin, ((⨆ j, v (x j)) ^ n) = P ^ n := by
    rw [hP, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun v _ ↦ ?_) rfl
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hrw : approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v) L x
      = ((∏ v : InfinitePlace K, (∏ i, v.1 (L v.1 i x)) ^ v.mult) *
          ∏ v ∈ Sfin, ∏ i, v.1 (L v.1 i x)) / P ^ n := by
    rw [approxProd]
    simp only [keyI, keyF, div_pow, Finset.prod_div_distrib]
    rw [div_mul_div_comm, hden]
  rw [hrw]
  have hH : Height.mulHeight x ≤ P := mulHeight_le_prod_S_of_sIntegral hx hint
  have hHpos : (0 : ℝ) < Height.mulHeight x := Height.mulHeight_pos x
  have hN0 : 0 ≤ (∏ v : InfinitePlace K, (∏ i, v.1 (L v.1 i x)) ^ v.mult) *
      ∏ v ∈ Sfin, ∏ i, v.1 (L v.1 i x) :=
    mul_nonneg (Finset.prod_nonneg fun v _ ↦
        pow_nonneg (Finset.prod_nonneg fun i _ ↦ v.1.nonneg _) _)
      (Finset.prod_nonneg fun v _ ↦ Finset.prod_nonneg fun i _ ↦ v.1.nonneg _)
  have hB0 : 0 ≤ B := le_trans hN0 hnum
  have hHn : (0 : ℝ) < Height.mulHeight x ^ n := pow_pos hHpos n
  have hHPn : Height.mulHeight x ^ n ≤ P ^ n := pow_le_pow_left₀ hHpos.le hH n
  calc _ ≤ B / P ^ n := by gcongr
    _ ≤ B / Height.mulHeight x ^ n := by gcongr

/-!
## Step 9 — CZ's identity (2.4)

For `K` Galois over `ℚ` the Galois group acts transitively on the infinite places (they all lie
over the unique infinite place of `ℚ`), so every `v` is `σ_v • v₀`.  CZ's (2.3)–(2.4) then say:
each archimedean factor `|ρ_v(δqu) − p|_v` equals `‖δqu‖` raised to `v`'s weight, because `p` is
rational and therefore fixed.  In mathlib's normalisation the product is `v₀(y − p)^[K:ℚ]`.
-/

/-- The Galois group of `K/ℚ` acts transitively on the infinite places of `K`. -/
theorem exists_smul_infinitePlace [IsGalois ℚ K] (v₀ v : InfinitePlace K) :
    ∃ σ : K ≃ₐ[ℚ] K, σ • v₀ = v :=
  NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (Subsingleton.elim _ _)

/-- **Corvaja–Zannier (2.4)** in mathlib's normalisation: the archimedean double product of
`|σ_v(y) − c|_v` collapses to `|y − c|_{v₀}^{[K:ℚ]}`, for `c` rational. -/
theorem prod_infinitePlace_sub_ratCast [IsGalois ℚ K] (v₀ : InfinitePlace K) (y : K) (c : ℚ)
    (σ : InfinitePlace K → (K ≃ₐ[ℚ] K)) (hσ : ∀ v, σ v • v₀ = v) :
    (∏ v : InfinitePlace K, v ((σ v) y - algebraMap ℚ K c) ^ v.mult)
      = v₀ (y - algebraMap ℚ K c) ^ (Module.finrank ℚ K) := by
  have key0 : ∀ τ : K ≃ₐ[ℚ] K,
      (τ • v₀) (τ y - algebraMap ℚ K c) = v₀ (y - algebraMap ℚ K c) := by
    intro τ
    rw [NumberField.InfinitePlace.smul_apply, map_sub, AlgEquiv.symm_apply_apply,
      AlgEquiv.commutes]
  have key : ∀ v : InfinitePlace K,
      v ((σ v) y - algebraMap ℚ K c) = v₀ (y - algebraMap ℚ K c) := by
    intro v
    have h := key0 (σ v)
    rwa [hσ v] at h
  rw [Finset.prod_congr rfl (fun v _ ↦ by rw [key v]), Finset.prod_pow_eq_pow_sum,
    NumberField.InfinitePlace.sum_mult_eq]

/-!
## Step 10 — CZ's estimate (2.6): the `S`-unit coordinates contribute at most `|q|^[K:ℚ]`
-/

/-- An infinite place sends a rational to its absolute value. -/
theorem infinitePlace_ratCast (v : InfinitePlace K) (c : ℚ) :
    v (algebraMap ℚ K c) = |c| := by
  have h := Rat.infinitePlace_apply (v.comap (algebraMap ℚ K)) c
  rwa [NumberField.InfinitePlace.comap_apply] at h

/-- A finite place sends a rational integer into the closed unit disc. -/
theorem finitePlace_intCast_le_one (v : FinitePlace K) (q : ℤ) : v ((q : K)) ≤ 1 := by
  have h : (algebraMap (𝓞 K) K (q : 𝓞 K)) = (q : K) := by push_cast [map_intCast]; rfl
  have h2 := NumberField.FinitePlace.norm_le_one
    (v := NumberField.FinitePlace.maximalIdeal v) (K := K) (R := 𝓞 K) (q : 𝓞 K)
  rw [h, NumberField.FinitePlace.norm_embedding_eq] at h2
  exact h2

/-- **CZ (2.6).**  For `q` a nonzero rational integer and `u` an `S`-unit, the `S`-product of
`|q u|` is at most `|q|^[K:ℚ]`. -/
theorem prod_S_int_mul_sUnit_le {Sfin : Finset (FinitePlace K)} (q : ℤ) {u : K}
    (hu : IsSUnit Sfin u) :
    ((∏ v : InfinitePlace K, v ((q : K) * u) ^ v.mult) * ∏ v ∈ Sfin, v ((q : K) * u))
      ≤ (|q| : ℝ) ^ (Module.finrank ℚ K) := by
  have hsplit : ((∏ v : InfinitePlace K, v ((q : K) * u) ^ v.mult) * ∏ v ∈ Sfin, v ((q : K) * u))
      = ((∏ v : InfinitePlace K, v ((q : K)) ^ v.mult) * ∏ v ∈ Sfin, v ((q : K))) *
        ((∏ v : InfinitePlace K, v u ^ v.mult) * ∏ v ∈ Sfin, v u) := by
    simp only [map_mul, mul_pow, Finset.prod_mul_distrib]
    ring
  rw [hsplit, prod_places_eq_one_of_isSUnit hu, mul_one]
  have hfin : (∏ v ∈ Sfin, v ((q : K))) ≤ 1 := by
    calc (∏ v ∈ Sfin, v ((q : K))) ≤ ∏ _v ∈ Sfin, (1 : ℝ) :=
          Finset.prod_le_prod (fun v _ ↦ v.1.nonneg _) (fun v _ ↦ finitePlace_intCast_le_one v q)
      _ = 1 := Finset.prod_const_one
  have hinf : (∏ v : InfinitePlace K, v ((q : K)) ^ v.mult) = (|q| : ℝ) ^ Module.finrank ℚ K := by
    have hq : ∀ v : InfinitePlace K, v ((q : K)) = (|q| : ℝ) := by
      intro v
      have : ((q : ℚ) : K) = (q : K) := by push_cast; ring
      have h2 := infinitePlace_ratCast v (q : ℚ)
      rw [show algebraMap ℚ K (q : ℚ) = ((q : ℚ) : K) from rfl, this] at h2
      rw [h2]
      push_cast
      ring
    rw [Finset.prod_congr rfl (fun v _ ↦ by rw [hq v]), Finset.prod_pow_eq_pow_sum,
      NumberField.InfinitePlace.sum_mult_eq]
  rw [hinf]
  have hnn : (0 : ℝ) ≤ (|q| : ℝ) ^ Module.finrank ℚ K := by positivity
  calc (|q| : ℝ) ^ Module.finrank ℚ K * ∏ v ∈ Sfin, v ((q : K))
      ≤ (|q| : ℝ) ^ Module.finrank ℚ K * 1 := by
        exact mul_le_mul_of_nonneg_left hfin hnn
    _ = _ := mul_one _

/-!
## Step 11 — CZ's Lemma-3 forms

Index the `d+1` coordinates by `Option ι` (`none ↦ x₀ = p`, `some i ↦ qσᵢ(u)`).  At an
archimedean place `v ∈ S_i` the exceptional form is `x₀ − ρ_v(δ) x_i`; everywhere else the forms
are the coordinates.  Independence again needs nothing but the shape.
-/

/-- The form `x ↦ x_none − c · x_(some i)`. -/
noncomputable def czSubForm {ι : Type*} (i : ι) (c : K) : Module.Dual K (Option ι → K) :=
  (LinearMap.proj none : Module.Dual K (Option ι → K)) -
    c • (LinearMap.proj (some i) : Module.Dual K (Option ι → K))

@[simp] theorem czSubForm_apply {ι : Type*} (i : ι) (c : K) (x : Option ι → K) :
    czSubForm i c x = x none - c * x (some i) := rfl

/-- CZ's Lemma-3 family at a place: coordinates, with the `none`-th replaced by
`x_none − c · x_(some i)`. -/
noncomputable def czSubFamily {ι : Type*} [DecidableEq ι] (i : ι) (c : K) :
    Option ι → Module.Dual K (Option ι → K) :=
  fun j ↦ match j with
    | none => czSubForm i c
    | some j' => LinearMap.proj (some j')

/-- **Independence of CZ's Lemma-3 forms** — unconditional: the change of basis is unipotent. -/
theorem linearIndependent_czSubFamily {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (c : K) :
    LinearIndependent K (czSubFamily i c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hF : ∀ (j k : Option ι), (czSubFamily i c j) (Pi.single k (1 : K))
      = (if j = none then (if k = none then (1 : K) else if k = some i then -c else 0)
         else if j = k then 1 else 0) := by
    rintro (_ | j') k
    · simp only [czSubFamily, czSubForm_apply, if_pos rfl, Pi.single_apply]
      rcases k with _ | k'
      · simp
      · by_cases hk : k' = i
        · subst hk; simp
        · simp [hk, Ne.symm hk]
    · simp only [czSubFamily, reduceIte, LinearMap.proj_apply, Pi.single_apply]
      by_cases hk : some j' = k
      · subst hk; simp
      · simp [hk]
  have hsum : ∀ k : Option ι, ∑ j, g j * (czSubFamily i c j) (Pi.single k (1 : K)) = 0 := by
    intro k
    have h := DFunLike.congr_fun hg (Pi.single k (1 : K))
    simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using h
  -- at `k = none` only the `none`-th form survives
  have hnone : g none = 0 := by
    have h := hsum none
    rw [Finset.sum_congr rfl (g := fun j ↦ if j = none then g none else 0)
      (fun j _ ↦ by rcases j with _ | j' <;> simp [hF])] at h
    rwa [Finset.sum_ite_eq' Finset.univ (none : Option ι) (fun _ ↦ g none),
      if_pos (Finset.mem_univ _)] at h
  intro j
  rcases j with _ | j'
  · exact hnone
  · have h := hsum (some j')
    rw [Finset.sum_congr rfl (g := fun j ↦ if j = some j' then g (some j') else 0)
      (fun j _ ↦ by
        rcases j with _ | j''
        · by_cases hj : j' = i <;> simp [hF, hnone, hj]
        · by_cases hj : j'' = j' <;> simp [hF, hj]
          )] at h
    rwa [Finset.sum_ite_eq' Finset.univ (some j') (fun _ ↦ g (some j')),
      if_pos (Finset.mem_univ _)] at h

/-!
## Step 12 — the Lemma-3 Subspace application, packaged

The three ingredients are now in place, so the Subspace step of CZ's Lemma 3 becomes a single
statement: an infinite family of `S`-integral points whose Lemma-3 double product is small lies
on one nontrivial hyperplane, i.e. satisfies `a₀p + Σ aⱼ q σⱼ(u) = 0` infinitely often.

`czL3` is the place-indexed family: at the archimedean place `v` the exceptional form uses the
index `idx v` and the coefficient `coef v` (CZ's `i` with `v ∈ S_i`, and `ρ_v(δ)`); at every
finite place the forms are the coordinates.
-/

open scoped Classical in
/-- CZ's Lemma-3 family of linear forms, place by place. -/
noncomputable def czL3 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : AbsoluteValue K ℝ → ι) (coef : AbsoluteValue K ℝ → K)
    (arch : AbsoluteValue K ℝ → Prop) :
    AbsoluteValue K ℝ → Option ι → Module.Dual K (Option ι → K) :=
  fun v j ↦ if arch v then czSubFamily (idx v) (coef v) j else LinearMap.proj j

/-- **The Subspace step of CZ's Lemma 3.**  An infinite set of nonzero `S`-integral points whose
Lemma-3 double product over `S` is at most `H(x)^(−ε)` satisfies one fixed nontrivial linear
relation `Σ_j a_j x_j = 0` infinitely often. -/
theorem czLemma3_subspace (hSub : Stephan2026Subspace) {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Sfin : Finset (FinitePlace K)) (idx : InfinitePlace K → ι) (coef : InfinitePlace K → K)
    (Ξ : Set (Option ι → K)) (hΞ : Ξ.Infinite) (hne : ∀ x ∈ Ξ, x ≠ 0)
    (hint : ∀ x ∈ Ξ, ∀ v : FinitePlace K, v ∉ Sfin → (⨆ j, v (x j)) ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hnum : ∀ x ∈ Ξ,
      ((∏ v : InfinitePlace K,
          (∏ j, v (czSubFamily (idx v) (coef v) j x)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ j, v (x j))
        ≤ Height.mulHeight x ^ (-ε)) :
    ∃ a : Option ι → K, a ≠ 0 ∧ {x ∈ Ξ | ∑ j, a j * x j = 0}.Infinite := by
  classical
  -- the place-indexed family: exceptional exactly at the infinite places
  set L : AbsoluteValue K ℝ → Option ι → Module.Dual K (Option ι → K) :=
    fun v j ↦ if h : ∃ w : InfinitePlace K, w.1 = v then
      czSubFamily (idx h.choose) (coef h.choose) j else LinearMap.proj j with hL
  have hLinf : ∀ v : InfinitePlace K, L v.1 = czSubFamily (idx v) (coef v) := by
    intro v
    have hex : ∃ w : InfinitePlace K, w.1 = v.1 := ⟨v, rfl⟩
    have hch : hex.choose = v := Subtype.ext hex.choose_spec
    funext j
    simp only [hL, dif_pos hex, hch]
  have hLfin : ∀ v : FinitePlace K, L v.1 = fun j ↦ (LinearMap.proj j :
      Module.Dual K (Option ι → K)) := by
    intro v
    have hex : ¬ ∃ w : InfinitePlace K, w.1 = v.1 := by
      rintro ⟨w, hw⟩
      exact finitePlace_val_ne_infinitePlace_val v w hw.symm
    funext j
    simp only [hL, dif_neg hex]
  have hLi : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), LinearIndependent K (L v.1) := by
    intro v _
    rw [hLinf v]
    exact linearIndependent_czSubFamily _ _
  have hLf : ∀ v ∈ Sfin, LinearIndependent K (L v.1) := by
    intro v _
    rw [hLfin v]
    exact linearIndependent_proj
  have hbound : ∀ x ∈ Ξ, approxProd (Finset.univ : Finset (InfinitePlace K)) Sfin (fun v ↦ v) L x
      ≤ Height.mulHeight x ^ (-(Fintype.card (Option ι) : ℝ) - ε) := by
    intro x hx
    have hHpos : (0 : ℝ) < Height.mulHeight x := Height.mulHeight_pos x
    have hnumL : ((∏ v : InfinitePlace K, (∏ j, v.1 (L v.1 j x)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ j, v.1 (L v.1 j x)) ≤ Height.mulHeight x ^ (-ε) := by
      have h := hnum x hx
      simp only [hLinf, hLfin, LinearMap.proj_apply]
      exact h
    refine le_trans (approxProd_le_of_prod_le (hne x hx) (hint x hx) L hnumL) ?_
    rw [div_le_iff₀ (pow_pos hHpos _), ← Real.rpow_natCast (Height.mulHeight x)
      (Fintype.card (Option ι)), ← Real.rpow_add hHpos]
    exact le_of_eq (by ring_nf)
  obtain ⟨a, ha, hainf⟩ := exists_dual_infinite_of_stephan hSub (Finset.univ) Sfin L hLi hLf
    hε Ξ hΞ hne hbound
  refine ⟨fun j ↦ a (fun k ↦ if j = k then (1 : K) else 0), ?_, hainf.mono ?_⟩
  · intro hA
    refine ha (LinearMap.ext fun x ↦ ?_)
    rw [LinearMap.pi_apply_eq_sum_univ a x]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [congrFun hA j]
    simp
  · rintro x ⟨hx, hax⟩
    refine ⟨hx, ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ a x] at hax
    refine Eq.trans ?_ hax
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_eq_mul, mul_comm]

/-!
## Step 13 — CZ's Lemma 2 (the unit equation) and the Skolem–Mahler–Lech replacement

CZ prove Lemma 1 but *cite* Lemma 2 (Evertse, van der Poorten–Schlickewei; [S, Ch. 4]).  It is a
separate application of the Subspace Theorem and is the only Subspace input of the paper not
discharged here; it enters as the named leaf `czLemma2`.

Its value beyond Lemma 3 is that it **replaces Skolem–Mahler–Lech** in CZ's Lemma 4: a two-term
relation `bβᵢ^m + cβⱼ^m = 0` holding at two different exponents forces `(βᵢ/βⱼ)^(m−m′) = 1`
outright.  mathlib has no SML, so this route is strictly cheaper.
-/

/-- Powers of `S`-units are `S`-units. -/
theorem IsSUnit.pow {Sfin : Finset (FinitePlace K)} {u : K} (hu : IsSUnit Sfin u) (m : ℕ) :
    IsSUnit Sfin (u ^ m) :=
  ⟨pow_ne_zero _ hu.1, fun v hv ↦ by rw [map_pow, hu.2 v hv, one_pow]⟩

/-- **Corvaja–Zannier, Lemma 2** (the unit-equation theorem of Evertse and
van der Poorten–Schlickewei, CZ's reference [S, Chapter 4]).  An infinite set of `S`-unit tuples
satisfying a fixed nontrivial linear relation satisfies a *two-term* relation along an infinite
subset.

DISCLOSED LEAF: this is the one Subspace-Theorem application of the paper that is not derived
here.  It is a genuine second theorem (finiteness of nondegenerate solutions of the `S`-unit
equation, up to scaling, plus induction on vanishing subsums), not a corollary of `czLemma1_*`. -/
theorem czLemma2 (hSub : Stephan2026Subspace) {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (Sfin : Finset (FinitePlace K))
    (Ξ : Set (ι → K)) (hΞ : Ξ.Infinite) (hS : ∀ x ∈ Ξ, ∀ i, IsSUnit Sfin (x i))
    (a : ι → K) (ha : ∀ i, a i ≠ 0) (hrel : ∀ x ∈ Ξ, ∑ i, a i * x i = 0) :
    ∃ i j : ι, i ≠ j ∧ ∃ b c : K, b ≠ 0 ∧ c ≠ 0 ∧ {x ∈ Ξ | b * x i + c * x j = 0}.Infinite := by
  sorry

/-- **The Skolem–Mahler–Lech step, from CZ's Lemma 2.**  If a fixed nontrivial linear combination
of the `m`-th powers of `S`-units vanishes for infinitely many `m`, then two of them have a ratio
that is a root of unity.  (This is what CZ get from SML in the proof of Lemma 4; Lemma 2 gives it
directly, which matters because mathlib has no Skolem–Mahler–Lech.) -/
theorem exists_pow_ratio_eq_one (hSub : Stephan2026Subspace) {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (Sfin : Finset (FinitePlace K))
    (β : ι → K) (hβ : ∀ i, IsSUnit Sfin (β i)) (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (M : Set ℕ) (hM : M.Infinite) (hrel : ∀ m ∈ M, ∑ i, a i * β i ^ m = 0) :
    ∃ i j : ι, i ≠ j ∧ ∃ N : ℕ, 0 < N ∧ (β i / β j) ^ N = 1 := by
  classical
  set f : ℕ → (ι → K) := fun m i ↦ β i ^ m with hf
  by_cases hinj : Set.InjOn f M
  · have hΞ : (f '' M).Infinite := hM.image hinj
    obtain ⟨i, j, hij, b, c, hb, hc, hinf⟩ :=
      czLemma2 hSub Sfin (f '' M) hΞ
        (fun x hx i ↦ by obtain ⟨m, _, rfl⟩ := hx; exact (hβ i).pow m)
        a ha (fun x hx ↦ by obtain ⟨m, hm, rfl⟩ := hx; exact hrel m hm)
    obtain ⟨x, hx, y, hy, hxy⟩ := hinf.nontrivial
    obtain ⟨⟨m, hm, hxm⟩, hxrel⟩ := hx
    obtain ⟨⟨n, hn, hyn⟩, hyrel⟩ := hy
    have hmn : m ≠ n := by rintro rfl; exact hxy (hxm.symm.trans hyn)
    have hkey : ∀ k : ℕ, b * β i ^ k + c * β j ^ k = 0 → (β i / β j) ^ k = -c / b := by
      intro k hk
      have hbj : β j ^ k ≠ 0 := pow_ne_zero _ (hβ j).1
      rw [div_pow, div_eq_div_iff hbj hb]
      linear_combination hk
    have h1 : (β i / β j) ^ m = -c / b := by
      refine hkey m ?_
      rw [← hxm] at hxrel
      simpa [hf] using hxrel
    have h2 : (β i / β j) ^ n = -c / b := by
      refine hkey n ?_
      rw [← hyn] at hyrel
      simpa [hf] using hyrel
    have hr : β i / β j ≠ 0 := div_ne_zero (hβ i).1 (hβ j).1
    rcases lt_or_gt_of_ne hmn with h | h
    · refine ⟨i, j, hij, n - m, by omega, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero m hr) ?_
      rw [← pow_add, mul_one, show m + (n - m) = n by omega, h2, h1]
    · refine ⟨i, j, hij, m - n, by omega, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero n hr) ?_
      rw [← pow_add, mul_one, show n + (m - n) = m by omega, h1, h2]
  · -- the power map is not injective on `M`: then *every* ratio is already a root of unity
    rw [Set.InjOn] at hinj
    push Not at hinj
    obtain ⟨m, hm, n, hn, hfe, hmn⟩ := hinj
    have hall : ∀ i, β i ^ m = β i ^ n := fun i ↦ congrFun hfe i
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    have hr : β i / β j ≠ 0 := div_ne_zero (hβ i).1 (hβ j).1
    have hdiv : ∀ k : ℕ, (β i / β j) ^ k = β i ^ k / β j ^ k := fun k ↦ div_pow _ _ _
    rcases lt_or_gt_of_ne hmn with h | h
    · refine ⟨i, j, hij, n - m, by omega, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero m hr) ?_
      rw [← pow_add, mul_one, show m + (n - m) = n by omega, hdiv, hdiv, hall i, hall j]
    · refine ⟨i, j, hij, m - n, by omega, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero n hr) ?_
      rw [← pow_add, mul_one, show n + (m - n) = m by omega, hdiv, hdiv, hall i, hall j]

end CZ

/-- `corvajaZannier_dichotomy` (CZ Main Theorem, Dubickas's Lemma 3), from Stephan's Subspace
Theorem and Ridout.  Same conclusion as the phase-9 statement. -/
theorem corvajaZannier_dichotomy_of_stephan (hSub : Stephan2026Subspace)
    (hR : Stephan2026Ridout) {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ}
    (hq : 0 < q) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 0 < s 0)
    (hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * s n)) < |(q : ℝ) * α ^ s n - round ((q : ℝ) * α ^ s n)| := by
  sorry

/-- `corvajaZannier_lemma4` (CZ Lemma 4), from Stephan's Subspace Theorem.  Same statement as the
phase-9 one. -/
theorem corvajaZannier_lemma4_of_stephan (hSub : Stephan2026Subspace) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q)
    (hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α)
    {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α ∨ ∃ (l : ℕ) (r : ℚ), 0 < l ∧ α ^ l = (r : ℝ) := by
  sorry

/-- **Dubickas (2022), Lemma 6, from Stephan's machine-checked Subspace Theorem and Ridout.**
Discharges the last literature input under Dubickas's Theorem 1 (`Dubickas.lean`) down to
Stephan's two theorems. -/
theorem dubickas2022_of_stephan (hSub : Stephan2026Subspace) (hR : Stephan2026Ridout) :
    Dubickas2022 := by
  sorry

end LeanFormalizations.Transcendence.Dubickas
