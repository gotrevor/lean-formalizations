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
