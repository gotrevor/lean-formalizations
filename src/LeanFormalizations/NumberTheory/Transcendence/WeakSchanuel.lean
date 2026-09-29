/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Weakest hypotheses: what already follows from Conjecture 1 (phase 24)

Conjecture 1 (`AlgIndepLogsConjecture`, "weak Schanuel": logarithms of algebraic numbers are
algebraically independent) is the special case of Schanuel where every `e^{zᵢ}` is algebraic.
The fact graph (`FACT-GRAPH.md`) shows several results derived from full Schanuel that should
need only Conjecture 1, and theorems (Gelfond–Schneider, Baker) that Conjecture 1 should imply.
Re-deriving from the weaker node sharpens the graph: it records the *least* hypothesis each fact
needs.

* Conj 1 ⇒ Gelfond–Schneider: if `a^b = c` is algebraic, then `λ₁ = log a` and `λ₂ = b·log a` are
  logarithms of algebraic numbers, `ℚ`-independent since `b` is irrational, yet `λ₂ − bλ₁ = 0` is
  an algebraic relation over `ℚ̄`.  Take the norm to get a relation over `ℚ`.
* Conj 1 ⇒ Baker (inhomogeneous, `Baker1966`): a `ℚ̄`-linear relation with nonzero constant term
  among logarithms, after passing to a `ℚ`-basis, is an algebraic relation.
* Conj 1 ⇒ logarithms of distinct primes are algebraically independent (phase 15 used Schanuel).
* Conj 1 ⇒ `π` together with the logarithms of distinct primes is algebraically independent
  (`iπ` is a logarithm of `−1`; phase 16 used Schanuel).
* Conj 1 ⇒ strong four exponentials.  ⚠️ was flagged "Ren, about 70% confident, not checked
  against a source".  **The reading is CORRECT and the implication is now proved.**

**Result (2026-09-29, one lap): all five are proved and `#print axioms`-clean; this file is
sorry-free.**  Nothing turned out false or underivable.  The three real design points:

1. *Strong four exponentials.*  `StrongSix.strongSix`'s `Fin 2 × Fin 3` argument transfers to
   `Fin 2 × Fin 2` verbatim — the plumbing (`exists_logBasis`, `exists_aff_of_mem`) is reused
   unchanged, and Schanuel is never needed because `strongSix` touches `hS` only through
   `algebraicIndependent_of_exp_isAlgebraic`, i.e. through Conjecture 1 exactly.  What does NOT
   transfer is `AffineRankOne.const_ratio`: Roy's derivation argument genuinely needs three
   columns (it forces the three `Pⱼ` into a 2-dimensional space).  The replacement is the
   `AffTwo` section: from `A·D = B·C` for affine forms, `pderiv` + `eval 0` reads off the
   symmetric coefficient identity `AᵢD_j + A_jDᵢ = BᵢC_j + B_jCᵢ` (`sym_coeff`); then a
   `K`-functional `f` supported on a nonvanishing `2×2` minor of `(A,B)` with `f A = 0`,
   `f B = 1` gives `2·f C = 0` and hence `C = (f D)·A` (`eq_smul_of_sym`).  Characteristic `0`
   is used exactly once, to divide by `2`.
2. *Baker inhomogeneous.*  `Baker1966` has no independence hypothesis on the `ℓᵢ`, so the
   homogeneous form does not apply directly; pass to a `ℚ`-basis of `span ℚ (range ℓ)`.  That
   this basis again consists of logarithms of algebraic numbers is `logSubmodule` — the key
   closure being `exp (q·z)` algebraic, via `IsAlgebraic.of_pow` on `(exp z)^{q.num}`.
3. *`π` and prime logarithms.*  Conjecture 1 gives `iπ, log p₁, …` directly; trading `iπ` for
   `π` is the phase-15 master step `algebraicIndependent_of_le_trdeg_of_isAlgebraic`.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Transcendence.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.Exponentials
import LeanFormalizations.NumberTheory.Transcendence.StrongSix

namespace LeanFormalizations.Waldschmidt2023

open LeanFormalizations.Literature
open LeanFormalizations.Schanuel LeanFormalizations.Exponentials
open LeanFormalizations.AffineRankOne

open Complex IntermediateField Algebra Cardinal Set

/-! ## Conjecture 1 ⇒ Gelfond–Schneider -/

/-- `log a` and `b · log a` are `ℚ`-linearly independent for `a > 0`, `a ≠ 1` and `b` irrational. -/
theorem linearIndependent_log_mul {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≠ 1) (hbirr : Irrational b) :
    LinearIndependent ℚ ![((Real.log a : ℝ) : ℂ), (b : ℂ) * ((Real.log a : ℝ) : ℂ)] := by
  have hlog : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha0 ha1
  set ℓ : ℂ := ((Real.log a : ℝ) : ℂ) with hℓ
  have hℓ0 : ℓ ≠ 0 := by simpa [hℓ] using hlog
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Rat.smul_def] at hst
  have : ((s : ℂ) + (t : ℂ) * (b : ℂ)) * ℓ = 0 := by
    ring_nf; ring_nf at hst; linear_combination hst
  rcases mul_eq_zero.1 this with h | h
  · have hre : (s : ℝ) + (t : ℝ) * b = 0 := by
      have := congrArg Complex.re h; simpa using this
    by_cases ht : t = 0
    · subst ht; simp at hre ⊢; exact_mod_cast hre
    · exact absurd (hbirr.ne_rat (-s / t) (by push_cast; field_simp at hre ⊢; linarith))
        (by simp)
  · exact absurd h hℓ0

/-- **Conjecture 1 ⇒ Gelfond–Schneider.**  With `a^b` algebraic, `λ₁ = log a` and
`λ₂ = b·log a` are `ℚ`-linearly independent logarithms of algebraic numbers, so Conjecture 1
makes them algebraically independent — yet `λ₂` lies in `ℚ̄(λ₁)`, which is the contradiction. -/
theorem gelfondSchneider_of_algIndepLogs (h : AlgIndepLogsConjecture) : GelfondSchneider1934 := by
  intro a b ha0 ha1 haalg hbalg hbirr hab
  set ℓ : ℂ := ((Real.log a : ℝ) : ℂ) with hℓ
  have hexp1 : Complex.exp ℓ = ((a : ℝ) : ℂ) := by
    rw [hℓ, ← Complex.ofReal_exp, Real.exp_log ha0]
  have hexp2 : Complex.exp ((b : ℂ) * ℓ) = (((a ^ b : ℝ)) : ℂ) := by
    rw [hℓ, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos ha0]
    norm_num [mul_comm]
  have hind : AlgebraicIndependent ℚ ![ℓ, (b : ℂ) * ℓ] := by
    refine h 2 _ (linearIndependent_log_mul ha0 ha1 hbirr) ?_
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (Complex.exp ℓ)
      rw [hexp1]; exact isAlgebraic_complex_of_real haalg
    · show IsAlgebraic ℚ (Complex.exp ((b : ℂ) * ℓ))
      rw [hexp2]; exact isAlgebraic_complex_of_real hab
  refine not_isAlgebraic_of_algebraicIndependent_pair hind ?_
  exact isAlgebraic_mul_rat (isAlgebraic_complex_of_real hbalg)
    (isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ ({ℓ} : Set ℂ)) (A := ℂ)
      ⟨_, subset_adjoin _ _ rfl⟩)

/-! ## Conjecture 1 ⇒ algebraic independence of prime logarithms -/

theorem algebraicIndependent_log_primes_of_algIndepLogs (h : AlgIndepLogsConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ fun i ↦ Real.log (p i : ℕ) := by
  refine algebraicIndependent_real_of_complex ?_
  have hzli : LinearIndependent ℚ (fun i => ((Real.log ((p i : ℕ) : ℝ) : ℝ) : ℂ)) :=
    (linearIndependent_log_primes p hp).map'
      ((IsScalarTower.toAlgHom ℚ ℝ ℂ).toLinearMap)
      (by rw [LinearMap.ker_eq_bot]; exact (IsScalarTower.toAlgHom ℚ ℝ ℂ).injective)
  refine h n _ hzli ?_
  intro i
  show IsAlgebraic ℚ (Complex.exp (((Real.log ((p i : ℕ) : ℝ) : ℝ) : ℂ)))
  have hpos : (0 : ℝ) < ((p i : ℕ) : ℝ) := by exact_mod_cast (p i).2.pos
  rw [← Complex.ofReal_exp, Real.exp_log hpos]
  exact isAlgebraic_complex_of_real (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) ((p i : ℕ) : ℚ))

/-- **Conjecture 1 ⇒ `π` and prime logarithms are algebraically independent.**  `iπ` is a
logarithm of `−1`, and trading `iπ` for `π` costs nothing because `i` is algebraic. -/
theorem algebraicIndependent_pi_log_primes_of_algIndepLogs (h : AlgIndepLogsConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ
      (Fin.cons Real.pi fun i ↦ Real.log (p i : ℕ) : Fin (n + 1) → ℝ) := by
  have hz : AlgebraicIndependent ℚ (zPiLog p) := by
    refine h (n + 1) _ (linearIndependent_zPiLog p hp) ?_
    refine Fin.cases ?_ (fun j => ?_)
    · show IsAlgebraic ℚ (Complex.exp (Complex.I * (Real.pi : ℂ)))
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_mul_I]
      simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-1))
    · show IsAlgebraic ℚ (Complex.exp (((Real.log ((p j : ℕ) : ℝ) : ℝ) : ℂ)))
      have hpos : (0 : ℝ) < ((p j : ℕ) : ℝ) := by exact_mod_cast (p j).2.pos
      rw [← Complex.ofReal_exp, Real.exp_log hpos]
      exact isAlgebraic_complex_of_real (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) ((p j : ℕ) : ℚ))
  refine algebraicIndependent_real_of_complex ?_
  have hcomp : (fun i => (((Fin.cons Real.pi fun i ↦ Real.log ((p i : ℕ) : ℝ) :
      Fin (n + 1) → ℝ) i : ℝ) : ℂ)) = yPiLog p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hcomp]
  -- trade `iπ` for `π`
  refine algebraicIndependent_of_le_trdeg_of_isAlgebraic (F := ℚ) (E := ℂ)
    (yPiLog p)
    (IntermediateField.adjoin ℚ (Set.range (zPiLog p)))
    (by simpa using hz.le_trdeg_adjoin) (forall_isAlgebraic_adjoin ?_)
  set K := IntermediateField.adjoin ℚ (Set.range (yPiLog p))
    with hK
  have mpi : ((Real.pi : ℝ) : ℂ) ∈ K := subset_adjoin _ _ ⟨0, rfl⟩
  have mlog : ∀ i : Fin n, ((Real.log ((p i : ℕ) : ℝ) : ℝ) : ℂ) ∈ K :=
    fun i => subset_adjoin _ _ ⟨i.succ, rfl⟩
  rintro w ⟨i, rfl⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · show IsAlgebraic K (Complex.I * (Real.pi : ℂ))
    exact isAlgebraic_mul_rat isAlgebraic_I
      (isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, mpi⟩)
  · show IsAlgebraic K ((Real.log ((p j : ℕ) : ℝ) : ℂ))
    exact isAlgebraic_algebraMap (R := K) (A := ℂ) ⟨_, mlog j⟩

/-! ## Conjecture 1 ⇒ Baker's inhomogeneous theorem

`Baker1966` has no linear-independence hypothesis on the `ℓᵢ`, so the homogeneous form
(`bakerHomogeneous_of_algIndepLogs`) does not apply directly.  Pass to a `ℚ`-basis `μ` of the
`ℚ`-span of the `ℓᵢ`: each `μ_s` is again a logarithm of an algebraic number, because that span
is a `ℚ`-submodule of `{z | exp z algebraic}` (`logSubmodule`), and the relation becomes a
`ℚ̄`-affine relation among the algebraically independent `μ`. -/

/-- `exp (q·z)` is algebraic when `exp z` is: its `q.den`-th power is `(exp z)^q.num`. -/
theorem isAlgebraic_exp_rat_mul {q : ℚ} {z : ℂ} (h : IsAlgebraic ℚ (Complex.exp z)) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * z)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  rw [← Complex.exp_nat_mul]
  have hq : ((q.den : ℚ) : ℂ) * (q : ℂ) = ((q.num : ℤ) : ℂ) := by
    have : (q.den : ℚ) * q = (q.num : ℚ) := by
      rw [mul_comm]; exact_mod_cast Rat.mul_den_eq_num q
    exact_mod_cast congrArg (fun r : ℚ => (r : ℂ)) this
  have hq' : (q.den : ℂ) * ((q : ℂ) * z) = ((q.num : ℤ) : ℂ) * z := by
    rw [← mul_assoc]; push_cast at hq ⊢; rw [hq]
  rw [hq', Complex.exp_int_mul]
  refine mem_algebraicClosure_iff.1 ?_
  exact zpow_mem (mem_algebraicClosure_iff.2 h) _

/-- The logarithms of algebraic numbers form a `ℚ`-submodule of `ℂ`. -/
noncomputable def logSubmodule : Submodule ℚ ℂ where
  carrier := {z | IsAlgebraic ℚ (Complex.exp z)}
  add_mem' := by
    intro x y hx hy
    show IsAlgebraic ℚ (Complex.exp (x + y))
    rw [Complex.exp_add]
    exact mem_algebraicClosure_iff.1
      (mul_mem (mem_algebraicClosure_iff.2 hx) (mem_algebraicClosure_iff.2 hy))
  zero_mem' := by
    show IsAlgebraic ℚ (Complex.exp 0)
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 1
  smul_mem' := by
    intro c x hx
    show IsAlgebraic ℚ (Complex.exp (c • x))
    rw [Rat.smul_def]
    exact isAlgebraic_exp_rat_mul hx

theorem isAlgebraic_exp_of_mem_span {ι : Type} {ℓ : ι → ℂ}
    (hℓ : ∀ i, IsAlgebraic ℚ (Complex.exp (ℓ i))) {z : ℂ}
    (hz : z ∈ Submodule.span ℚ (Set.range ℓ)) : IsAlgebraic ℚ (Complex.exp z) := by
  have hle : Submodule.span ℚ (Set.range ℓ) ≤ logSubmodule := by
    rw [Submodule.span_le]
    rintro w ⟨i, rfl⟩
    exact hℓ i
  exact hle hz

/-- A finite family of complex numbers, written in a `ℚ`-basis of its own span. -/
theorem exists_rat_basis {ι : Type} [Fintype ι] (y : ι → ℂ) :
    ∃ (t : ℕ) (u : Fin t → ℂ) (q : ι → Fin t → ℚ), LinearIndependent ℚ u ∧
      (∀ s, u s ∈ Submodule.span ℚ (Set.range y)) ∧
      ∀ j, y j = ∑ s, (q j s : ℂ) * u s := by
  classical
  have hfin : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  set V := Submodule.span ℚ (Set.range y) with hV
  set B := Module.finBasis ℚ V with hB
  refine ⟨Module.finrank ℚ V, fun s => (B s : ℂ),
    fun j s => B.repr ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩ s, ?_, fun s => (B s).2, fun j => ?_⟩
  · exact B.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · have := congrArg (fun v : V => (v : ℂ)) (B.sum_repr ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun s _ => by rw [Rat.smul_def]

/-- **Conjecture 1 ⇒ Baker's theorem (1966), inhomogeneous form.** -/
theorem baker1966_of_algIndepLogs (h : AlgIndepLogsConjecture) : Baker1966 := by
  classical
  intro n β ℓ hβ hℓ hβ0 hrel
  obtain ⟨t, μ, q, hμli, hμmem, hcoord⟩ := exists_rat_basis ℓ
  have hμexp : ∀ s, IsAlgebraic ℚ (Complex.exp (μ s)) := fun s =>
    isAlgebraic_exp_of_mem_span hℓ (hμmem s)
  have hind : AlgebraicIndependent ℚ μ := h t μ hμli hμexp
  have halg : Algebra.IsAlgebraic ℚ (↥(algebraicClosure ℚ ℂ)) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hindK : AlgebraicIndependent (↥(algebraicClosure ℚ ℂ)) μ :=
    hind.extendScalars (↥(algebraicClosure ℚ ℂ))
  have hrat : ∀ r : ℚ, (r : ℂ) ∈ algebraicClosure ℚ ℂ := fun r =>
    mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) r)
  set b0 : (algebraicClosure ℚ ℂ) := ⟨β 0, mem_algebraicClosure_iff.2 (hβ 0)⟩ with hb0
  set c : Fin t → (algebraicClosure ℚ ℂ) := fun s =>
    ⟨∑ i : Fin n, β i.succ * (q i s : ℂ),
      sum_mem fun i _ => mul_mem (mem_algebraicClosure_iff.2 (hβ i.succ)) (hrat _)⟩ with hc
  have hrel' : algebraMap (algebraicClosure ℚ ℂ) ℂ b0
      + ∑ s, algebraMap (algebraicClosure ℚ ℂ) ℂ (c s) * μ s = 0 := by
    have hexpand : ∑ s, (∑ i : Fin n, β i.succ * (q i s : ℂ)) * μ s
        = ∑ i : Fin n, β i.succ * ℓ i := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoord i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    show (β 0 : ℂ) + ∑ s, (∑ i : Fin n, β i.succ * (q i s : ℂ)) * μ s = 0
    rw [hexpand]
    exact hrel
  obtain ⟨hz, -⟩ := eq_zero_of_algebraicIndependent_linear hindK b0 c hrel'
  exact hβ0 (congrArg Subtype.val hz)


/-! ## Conjecture 1 ⇒ the strong four exponentials conjecture

The `Fin 2 × Fin 2` analogue of `StrongSix.strongSix`.  The plumbing (basis extraction, affine
coordinates) is reused verbatim; the only new input is `constRatioTwo`, the two-column version of
`AffineRankOne.const_ratio`.  Roy's three-column derivation argument does not apply with two
columns, so `constRatioTwo` is proved instead by a *coefficient* argument: read off the symmetric
bilinear identity `Aᵢ D_j + A_j Dᵢ = Bᵢ C_j + B_j Cᵢ` from `A·D = B·C` by `pderiv`+`eval 0`, then
pick a `K`-functional `f` with `f A = 0`, `f B = 1` and conclude `f C = 0`, `C = (f D) · A`. -/

namespace AffTwo

open MvPolynomial LeanFormalizations.AffineRankOne

variable {K : Type*} [Field K] {N : ℕ}

/-- Linear independence of a pair of vectors gives a nonvanishing `2×2` minor. -/
theorem exists_minor_ne {A B : Fin N → K} (h : LinearIndependent K ![A, B]) :
    ∃ p q, A p * B q - A q * B p ≠ 0 := by
  by_contra hc
  push_neg at hc
  rcases eq_or_ne A 0 with hA | hA
  · refine h.ne_zero 0 ?_
    simpa using hA
  · obtain ⟨p, hp⟩ : ∃ p, A p ≠ 0 := Function.ne_iff.1 hA
    have hsum : ∑ i, (![B p / A p, -1] : Fin 2 → K) i •
        (![A, B] : Fin 2 → (Fin N → K)) i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      funext q
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, neg_smul, one_smul,
        neg_mul, one_mul]
      field_simp
      simp only [Pi.neg_apply]
      linear_combination -hc p q
    have hz := Fintype.linearIndependent_iff.1 h _ hsum
    have : (-1 : K) = 0 := by simpa using hz 1
    exact absurd this (by simp)

/-- **The symmetric-tensor cancellation.**  If the symmetric products agree coordinatewise,
`AᵢD_j + A_jDᵢ = BᵢC_j + B_jCᵢ`, and `A, B` are linearly independent, then `C` is a scalar
multiple of `A`.  (Char 0 is used once, to divide by `2`.) -/
theorem eq_smul_of_sym [CharZero K] {A B C D : Fin N → K} (hA : LinearIndependent K ![A, B])
    (hyp : ∀ i j, A i * D j + A j * D i = B i * C j + B j * C i) :
    ∃ c : K, ∀ j, C j = c * A j := by
  obtain ⟨p, q, hδ0⟩ := exists_minor_ne hA
  set δ : K := A p * B q - A q * B p with hδ
  set α : K := -A q / δ with hα
  set β : K := A p / δ with hβ
  set f : (Fin N → K) → K := fun v => α * v p + β * v q with hf
  have hfA : f A = 0 := by simp only [hf, hα, hβ]; field_simp; ring
  have hfB : f B = 1 := by
    simp only [hf, hα, hβ]; field_simp; linear_combination hδ
  have key : ∀ j, f A * D j + A j * f D = f B * C j + B j * f C := by
    intro j
    simp only [hf]
    linear_combination α * hyp p j + β * hyp q j
  have hfC : f C = 0 := by
    have h2 : (2 : K) * (f A * f D) = 2 * (f B * f C) := by
      simp only [hf]
      linear_combination α * key p + β * key q
    rw [hfA, hfB] at h2
    have h3 : (2 : K) * f C = 0 := by linear_combination -h2
    simpa using h3
  refine ⟨f D, fun j => ?_⟩
  have := key j
  rw [hfA, hfB, hfC] at this
  linear_combination -this

/-! ### From an affine product identity to the symmetric coefficient identity -/

@[simp] theorem eval_zero_aff {n : ℕ} (a : K) (b : Fin n → K) :
    (MvPolynomial.eval (0 : Fin n → K)) (aff a b) = a := by simp [aff]

@[simp] theorem constantCoeff_aff {n : ℕ} (a : K) (b : Fin n → K) :
    MvPolynomial.constantCoeff (aff a b) = a := by simp [aff]

/-- `C c * aff a b = aff (c*a) (c*b)`. -/
theorem C_mul_aff {n : ℕ} (c a : K) (b : Fin n → K) :
    MvPolynomial.C c * aff a b = aff (c * a) (fun k => c * b k) := by
  simp only [aff, mul_add, Finset.mul_sum, map_mul]
  ring_nf

/-- The coefficient vector of an affine form. -/
noncomputable def cv {n : ℕ} (a : K) (b : Fin n → K) : Fin (n + 1) → K := Fin.cons a b

/-- **Coefficient extraction.**  `A·D = B·C` for affine forms gives the symmetric identity on
coefficient vectors, read off by `pderiv` and `eval 0`. -/
theorem sym_coeff {n : ℕ} {a1 a2 a3 a4 : K} {b1 b2 b3 b4 : Fin n → K}
    (hrel : aff a1 b1 * aff a4 b4 = aff a2 b2 * aff a3 b3) (i j : Fin (n + 1)) :
    cv a1 b1 i * cv a4 b4 j + cv a1 b1 j * cv a4 b4 i
      = cv a2 b2 i * cv a3 b3 j + cv a2 b2 j * cv a3 b3 i := by
  have h0 : a1 * a4 = a2 * a3 := by
    have h := congrArg (MvPolynomial.eval (0 : Fin n → K)) hrel
    simpa using h
  have hp : ∀ k : Fin n, aff a1 b1 * MvPolynomial.C (b4 k) + aff a4 b4 * MvPolynomial.C (b1 k)
      = aff a2 b2 * MvPolynomial.C (b3 k) + aff a3 b3 * MvPolynomial.C (b2 k) := by
    intro k
    have h := congrArg (pderiv k) hrel
    simpa only [Derivation.leibniz, pderiv_aff, smul_eq_mul] using h
  have h1 : ∀ k : Fin n, a1 * b4 k + a4 * b1 k = a2 * b3 k + a3 * b2 k := by
    intro k
    have h := congrArg (MvPolynomial.eval (0 : Fin n → K)) (hp k)
    simpa using h
  have h2 : ∀ k l : Fin n, b1 l * b4 k + b4 l * b1 k = b2 l * b3 k + b3 l * b2 k := by
    intro k l
    have h := congrArg (pderiv l) (hp k)
    have h' := congrArg (MvPolynomial.eval (0 : Fin n → K)) h
    simp only [map_add, Derivation.leibniz, pderiv_aff, pderiv_C, smul_eq_mul, smul_zero,
      mul_zero, zero_add, add_zero, map_mul, MvPolynomial.eval_C, eval_zero_aff] at h'
    linear_combination h'
  refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
  · simp only [cv, Fin.cons_zero]; linear_combination 2 * h0
  · intro l; simp only [cv, Fin.cons_zero, Fin.cons_succ]; linear_combination h1 l
  · intro k; simp only [cv, Fin.cons_zero, Fin.cons_succ]; linear_combination h1 k
  · intro k l
    simp only [cv, Fin.cons_succ]
    linear_combination h2 l k

/-- **The two-column rank-one criterion for affine forms.**  If `P₀, P₁` are `K`-linearly
independent affine forms and `P₀ Q₁ = P₁ Q₀` with `Q₀, Q₁` affine, then `Q₀ = c·P₀` for a
constant `c ∈ K`. -/
theorem constRatioTwo [CharZero K] {n : ℕ} {pa0 pa1 qa0 qa1 : K}
    {pb0 pb1 qb0 qb1 : Fin n → K}
    (hind : LinearIndependent K ![aff pa0 pb0, aff pa1 pb1])
    (hrel : aff pa0 pb0 * aff qa1 qb1 = aff pa1 pb1 * aff qa0 qb0) :
    ∃ c : K, aff qa0 qb0 = MvPolynomial.C c * aff pa0 pb0 := by
  have hcvind : LinearIndependent K ![cv pa0 pb0, cv pa1 pb1] := by
    rw [LinearIndependent.pair_iff] at hind ⊢
    intro s t hst
    refine hind s t ?_
    have hc : ∀ k : Fin n, s * pb0 k + t * pb1 k = 0 := by
      intro k
      have := congrFun hst k.succ
      simpa [cv, Fin.cons_succ] using this
    have h0 : s * pa0 + t * pa1 = 0 := by
      have := congrFun hst 0
      simpa [cv, Fin.cons_zero] using this
    have : MvPolynomial.C s * aff pa0 pb0 + MvPolynomial.C t * aff pa1 pb1
        = aff (s * pa0 + t * pa1) (fun k => s * pb0 k + t * pb1 k) := by
      simp only [aff, map_add, map_mul, mul_add, Finset.mul_sum]
      rw [add_add_add_comm, ← Finset.sum_add_distrib]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    rw [smul_eq_C_mul, smul_eq_C_mul, this, h0]
    simp [aff, hc]
  obtain ⟨c, hc⟩ := eq_smul_of_sym hcvind (sym_coeff hrel)
  refine ⟨c, ?_⟩
  rw [C_mul_aff]
  have ha : qa0 = c * pa0 := by simpa [cv, Fin.cons_zero] using hc 0
  have hb : ∀ k, qb0 k = c * pb0 k := fun k => by simpa [cv, Fin.cons_succ] using hc k.succ
  rw [ha]
  congr 1
  funext k
  exact hb k

end AffTwo

set_option maxHeartbeats 1000000 in
/-- **Conjecture 1 ⇒ the strong four exponentials conjecture.**  Ren's reading was right: the
`Fin 2 × Fin 3` proof of `StrongSix.strongSix` goes through verbatim with `Fin 2 × Fin 2`, once
`AffineRankOne.const_ratio` (three columns, Roy's derivation argument) is replaced by
`AffTwo.constRatioTwo` (two columns, the symmetric-coefficient argument).  Note that Schanuel
is never needed: `strongSix` uses `hS` only through `algebraicIndependent_of_exp_isAlgebraic`,
i.e. through Conjecture 1 exactly. -/
theorem strongFourExponentials_of_algIndepLogs (h : AlgIndepLogsConjecture) :
    StrongFourExponentialsConjecture := by
  classical
  intro x y hx hy
  have hx' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) x := hx
  have hy' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) y := hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, μ, hμli, hμexp, hμmem⟩ :=
    StrongSix.exists_logBasis (fun p : Fin 2 × Fin 2 => x p.1 * y p.2) (fun p => hcon p.1 p.2)
  have hind : AlgebraicIndependent ℚ μ := h n μ hμli hμexp
  have halg : Algebra.IsAlgebraic ℚ (↥(algebraicClosure ℚ ℂ)) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hindK : AlgebraicIndependent (↥(algebraicClosure ℚ ℂ)) μ :=
    hind.extendScalars (↥(algebraicClosure ℚ ℂ))
  have hinj : Function.Injective
      (MvPolynomial.aeval μ : MvPolynomial (Fin n) (algebraicClosure ℚ ℂ) →ₐ[_] ℂ) := hindK
  choose a b hab using fun p : Fin 2 × Fin 2 => StrongSix.exists_aff_of_mem (hμmem p)
  have hPval : ∀ j, MvPolynomial.aeval μ (aff (a (0, j)) (b (0, j))) = x 0 * y j := fun j => by
    rw [StrongSix.aeval_aff]; exact (hab (0, j)).symm
  have hQval : ∀ j, MvPolynomial.aeval μ (aff (a (1, j)) (b (1, j))) = x 1 * y j := fun j => by
    rw [StrongSix.aeval_aff]; exact (hab (1, j)).symm
  have hcross : aff (a (0, 0)) (b (0, 0)) * aff (a (1, 1)) (b (1, 1))
      = aff (a (0, 1)) (b (0, 1)) * aff (a (1, 0)) (b (1, 0)) := by
    refine hinj ?_
    rw [map_mul, map_mul, hPval, hPval, hQval, hQval]
    ring
  have hx0 : x 0 ≠ 0 := hx'.ne_zero 0
  have hPind : LinearIndependent (↥(algebraicClosure ℚ ℂ))
      ![aff (a (0, 0)) (b (0, 0)), aff (a (0, 1)) (b (0, 1))] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hge : ∀ j : Fin 2, (![aff (a (0, 0)) (b (0, 0)), aff (a (0, 1)) (b (0, 1))] : Fin 2 → _) j
        = aff (a (0, j)) (b (0, j)) := by
      intro j; fin_cases j <;> rfl
    have h0 : ∑ j, (g j : ℂ) * (x 0 * y j) = 0 := by
      have := congrArg (MvPolynomial.aeval μ) hg
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, map_mul, hge j, hPval j]
      simp [MvPolynomial.algebraMap_eq]
    have h2 : ∑ j, (g j : ℂ) * y j = 0 := by
      have : x 0 * ∑ j, (g j : ℂ) * y j = 0 := by
        rw [Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl fun j _ => by ring
      exact (mul_eq_zero.1 this).resolve_left hx0
    exact Fintype.linearIndependent_iff.1 hy' g (by simpa [Algebra.smul_def] using h2)
  obtain ⟨c, hc⟩ := AffTwo.constRatioTwo hPind hcross
  have hxc : x 1 = (c : ℂ) * x 0 := by
    have hh := congrArg (MvPolynomial.aeval μ) hc
    rw [hQval, map_mul, hPval, MvPolynomial.aeval_C] at hh
    have h' : x 1 * y 0 = (c : ℂ) * (x 0 * y 0) := hh
    have hy0 : y 0 ≠ 0 := hy'.ne_zero 0
    have hz : (x 1 - (c : ℂ) * x 0) * y 0 = 0 := by linear_combination h'
    exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hy0)
  have hsum : ∑ i, (![c, -1] : Fin 2 → (algebraicClosure ℚ ℂ)) i • x i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def]
    have h1 : (algebraMap (↥(algebraicClosure ℚ ℂ)) ℂ) c = (c : ℂ) := rfl
    have h2 : (algebraMap (↥(algebraicClosure ℚ ℂ)) ℂ) (-1 : (algebraicClosure ℚ ℂ))
        = (-1 : ℂ) := by rw [map_neg, map_one]
    rw [h1, h2, hxc]
    ring
  have hzero := Fintype.linearIndependent_iff.1 hx' _ hsum
  have : (-1 : (algebraicClosure ℚ ℂ)) = 0 := by simpa using hzero 1
  exact absurd this (by simp)

/-! ## ⚠️ A second dropped-overbar bug: `SixExponentialsShifted` is FALSE

Found while trying to route `Conjecture 1 ⇒ FiveExponentials` through the repo's existing
`ExponentialsKnown.fiveExponentials_of_shifted`.  The degenerate-case analysis for
`SixExponentialsShifted` does not close, and the reason is that the statement is false:
nothing stops the shifts `βᵢⱼ` from being *equal* to the products `xᵢyⱼ`, provided those
products are algebraic — and `x`, `y` are only required to be `ℚ`-linearly independent, which
algebraic numbers easily are.  Then every `exp (xᵢyⱼ − βᵢⱼ) = exp 0 = 1`.

This is the same root cause as `Literature.StrongSixExponentialsOverQ` (refuted 2026-09-29 by
`ExponentialsKnown.not_strongSixExponentialsOverQ`): a `ℚ̄` whose overbar `pdftotext` dropped.
Waldschmidt 1988 Cor. 2.1 asks for `x` and `y` independent over the *algebraic* numbers, which
is precisely what rules the witness below out — over `ℚ̄` the pair `1, √2` is dependent.

`Literature/` is frozen, so repairing the `Prop` is an operator decision.  Consequences for the
fact graph: `ExponentialsKnown.sixExponentials_of_shifted` and `fiveExponentials_of_shifted`
remain valid implications but now have a hypothesis known to be unsatisfiable, exactly like
`sixExponentials_of_strongOverQ`.  In particular **there is currently no live route to
`FiveExponentials`** in the repo. -/

/-- **The frozen `Literature.SixExponentialsShifted` is FALSE as stated** (2026-09-29).
Witness: `x = (1, √2)`, `y = (1, √2, i)` — each `ℚ`-linearly independent — with the shifts
`βᵢⱼ := xᵢyⱼ`, which are algebraic because `x` and `y` are.  Every one of the six numbers
`exp (xᵢyⱼ − βᵢⱼ)` is then `exp 0 = 1`, which is not transcendental. -/
theorem not_sixExponentialsShifted : ¬ SixExponentialsShifted := by
  intro hsh
  set x : Fin 2 → ℂ := ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)] with hx
  set y : Fin 3 → ℂ := ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ), Complex.I] with hy
  have hxalg : ∀ i, IsAlgebraic ℚ (x i) := by
    intro i; fin_cases i
    · exact isAlgebraic_one
    · exact LeanFormalizations.ExponentialsKnown.isAlgebraic_sqrt_two
  have hyalg : ∀ j, IsAlgebraic ℚ (y j) := by
    intro j; fin_cases j
    · exact isAlgebraic_one
    · exact LeanFormalizations.ExponentialsKnown.isAlgebraic_sqrt_two
    · exact isAlgebraic_I
  obtain ⟨i, j, htr⟩ := hsh x y (fun i j => x i * y j)
    (linearIndependent_one_ofReal irrational_sqrt_two)
    LeanFormalizations.ExponentialsKnown.linearIndependent_one_sqrt_two_I
    (fun i j => mem_algebraicClosure_iff.1
      (mul_mem (mem_algebraicClosure_iff.2 (hxalg i)) (mem_algebraicClosure_iff.2 (hyalg j))))
  refine htr ?_
  rw [sub_self, Complex.exp_zero]
  exact isAlgebraic_one

/-! ## Repairing the edge into `SixExponentials`

`ExponentialsKnown.lean`'s header records that the only edge into `SixExponentials` from a
"strong" hypothesis is `sixExponentials_of_strongOverQ`, whose hypothesis
`StrongSixExponentialsOverQ` is *false* (`not_strongSixExponentialsOverQ` refutes it), so that
edge is vacuous.  The correct strong statements ask for `ℚ̄`-linear independence while the four-
and six-exponentials statements supply only `ℚ`-linear independence, and the gap is real: when
`x` is `ℚ`-independent but `ℚ̄`-dependent we have `x₁ = c·x₀` with `c` algebraic irrational, and
"all `exp (xᵢyⱼ)` algebraic" then says `exp ℓ` and `exp (c·ℓ)` are both algebraic for
`ℓ = x₀y₀ ≠ 0`.  That is exactly Gelfond–Schneider, and no strong-exponentials hypothesis
supplies it.  So the honest edge carries two hypotheses — and both are consequences of
Conjecture 1, which is how `sixExponentials_of_algIndepLogs` discharges them.

A second correction: the degenerate `y` case cannot be run against *strong six*, because a
`ℚ̄`-dependent triple need not contain a `ℚ̄`-independent pair to feed back in.  Strong **four**
is the right hypothesis — every pair of a `ℚ`-independent family is `ℚ`-independent, and if no
pair of the `yⱼ` is `ℚ̄`-independent then they are all `ℚ̄`-multiples of `y₀`. -/

/-- Conjecture 1 ⇒ Gelfond–Schneider in the branch-free complex form: `exp ℓ` and
`exp (c·ℓ)` are not both algebraic for `ℓ ≠ 0` and `c` algebraic irrational. -/
theorem not_isAlgebraic_exp_mul_of_algIndepLogs (h : AlgIndepLogsConjecture) {ℓ c : ℂ}
    (hℓ : ℓ ≠ 0) (hc : IsAlgebraic ℚ c) (hcq : ∀ q : ℚ, c ≠ (q : ℂ))
    (he : IsAlgebraic ℚ (Complex.exp ℓ)) : ¬ IsAlgebraic ℚ (Complex.exp (c * ℓ)) := by
  intro hce
  have hli : LinearIndependent ℚ ![ℓ, c * ℓ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Rat.smul_def] at hst
    have hz : ((s : ℂ) + (t : ℂ) * c) * ℓ = 0 := by linear_combination hst
    have hsum : (s : ℂ) + (t : ℂ) * c = 0 := (mul_eq_zero.1 hz).resolve_right hℓ
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hsum
    · refine absurd ?_ (hcq (-s / t))
      have htc : ((t : ℚ) : ℂ) ≠ 0 := by exact_mod_cast ht
      have hcv : c = -(s : ℂ) / (t : ℂ) := by field_simp; linear_combination hsum
      rw [hcv]; push_cast; ring
  have hind : AlgebraicIndependent ℚ ![ℓ, c * ℓ] := by
    refine h 2 _ hli ?_
    intro i; fin_cases i
    · exact he
    · exact hce
  refine not_isAlgebraic_of_algebraicIndependent_pair hind ?_
  exact isAlgebraic_mul_rat hc
    (isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ ({ℓ} : Set ℂ)) (A := ℂ)
      ⟨_, subset_adjoin _ _ rfl⟩)

/-- A `ℚ̄`-linearly dependent pair with nonzero first entry has an algebraic ratio. -/
theorem exists_algebraic_ratio {a b : ℂ} (ha : a ≠ 0)
    (hdep : ¬ LinearIndependent (↥(integralClosure ℚ ℂ)) ![a, b]) :
    ∃ c : ℂ, IsAlgebraic ℚ c ∧ b = c * a := by
  rw [LinearIndependent.pair_iff] at hdep
  push_neg at hdep
  obtain ⟨s, t, hst, hne⟩ := hdep
  simp only [Algebra.smul_def] at hst
  have hstC : (s : ℂ) * a + (t : ℂ) * b = 0 := hst
  have hsalg : IsAlgebraic ℚ ((s : ℂ)) := (s.2 : IsIntegral ℚ ((s : ℂ))).isAlgebraic
  have htalg : IsAlgebraic ℚ ((t : ℂ)) := (t.2 : IsIntegral ℚ ((t : ℂ))).isAlgebraic
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h0
    have ht : t = 0 := Subtype.ext h0
    have hs0 : s ≠ 0 := fun hs => (hne hs) ht
    have hsa : (s : ℂ) * a = 0 := by linear_combination hstC - b * h0
    rcases mul_eq_zero.1 hsa with hh | hh
    · exact hs0 (Subtype.ext hh)
    · exact ha hh
  refine ⟨-(s : ℂ) / (t : ℂ), ?_, ?_⟩
  · refine mem_algebraicClosure_iff.1 (div_mem (neg_mem ?_) ?_)
    · exact mem_algebraicClosure_iff.2 hsalg
    · exact mem_algebraicClosure_iff.2 htalg
  · field_simp
    linear_combination hstC

/-- A logarithm of an algebraic number lies in `𝓛̃`. -/
theorem mem_logAlgSpan_of_exp_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ (Complex.exp z)) :
    z ∈ LogAlgSpan :=
  ⟨1, ![0, 1], ![z],
    by intro k; fin_cases k; exacts [isAlgebraic_zero, isAlgebraic_one],
    by intro k; fin_cases k; simpa using h, by simp⟩

/-- **The honest edge into four exponentials.**  Strong four exponentials alone does not give
the `ℚ`-hypothesis form; the `ℚ̄`-degenerate cases need Gelfond–Schneider, as `hGS`. -/
theorem fourExponentials_of_strongFour_of_gs
    (h4 : StrongFourExponentialsConjecture)
    (hGS : ∀ ℓ c : ℂ, ℓ ≠ 0 → IsAlgebraic ℚ c → (∀ q : ℚ, c ≠ (q : ℂ)) →
      IsAlgebraic ℚ (Complex.exp ℓ) → ¬ IsAlgebraic ℚ (Complex.exp (c * ℓ))) :
    FourExponentialsConjecture := by
  classical
  intro x y hx hy
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  have hl0 : x 0 * y 0 ≠ 0 := mul_ne_zero hx0 hy0
  -- the two degenerate cases, both Gelfond–Schneider
  have hdeg : ∀ (z : Fin 2 → ℂ) (c : ℂ), LinearIndependent ℚ z → IsAlgebraic ℚ c →
      z 1 = c * z 0 → (∀ q : ℚ, c ≠ (q : ℂ)) := by
    intro z c hz _ hzc q hq
    refine absurd ?_ (by simpa using hz.ne_zero 0)
    have := (LinearIndependent.pair_iff.1 (by
      have he : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl
      rw [he]; exact hz)) (-q) 1 (by
        simp only [Rat.smul_def, hzc, hq]; push_cast; ring)
    exact absurd this.2 (by simp)
  by_cases hxK : LinearIndependent (↥(integralClosure ℚ ℂ)) x
  · by_cases hyK : LinearIndependent (↥(integralClosure ℚ ℂ)) y
    · obtain ⟨i, j, hmem⟩ := h4 x y hxK hyK
      exact hmem (mem_logAlgSpan_of_exp_isAlgebraic (hcon i j))
    · have hy' : ¬ LinearIndependent (↥(integralClosure ℚ ℂ)) ![y 0, y 1] := by
        intro hc; refine hyK ?_
        have he : ![y 0, y 1] = y := by funext i; fin_cases i <;> rfl
        rwa [he] at hc
      obtain ⟨c, hc, hce⟩ := exists_algebraic_ratio hy0 hy'
      refine hGS (x 0 * y 0) c hl0 hc (hdeg y c hy hc hce) (hcon 0 0) ?_
      have : c * (x 0 * y 0) = x 0 * y 1 := by rw [hce]; ring
      rw [this]; exact hcon 0 1
  · have hx' : ¬ LinearIndependent (↥(integralClosure ℚ ℂ)) ![x 0, x 1] := by
      intro hc; refine hxK ?_
      have he : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
      rwa [he] at hc
    obtain ⟨c, hc, hce⟩ := exists_algebraic_ratio hx0 hx'
    refine hGS (x 0 * y 0) c hl0 hc (hdeg x c hx hc hce) (hcon 0 0) ?_
    have : c * (x 0 * y 0) = x 1 * y 0 := by rw [hce]; ring
    rw [this]; exact hcon 1 0

/-- Four exponentials ⇒ six exponentials: a pair of a `ℚ`-independent triple is
`ℚ`-independent. -/
theorem sixExponentials_of_fourExponentials (h4 : FourExponentialsConjecture) :
    SixExponentials := by
  intro x y hx hy
  have hy2 : LinearIndependent ℚ ![y 0, y 1] := by
    have he : ![y 0, y 1] = y ∘ ![0, 1] := by funext i; fin_cases i <;> rfl
    rw [he]
    exact hy.comp _ (by decide)
  obtain ⟨i, j, htr⟩ := h4 x ![y 0, y 1] hx hy2
  refine ⟨i, ![0, 1] j, ?_⟩
  fin_cases j <;> simpa using htr

/-- **Conjecture 1 ⇒ the six exponentials theorem**, along the repaired edge. -/
theorem sixExponentials_of_algIndepLogs (h : AlgIndepLogsConjecture) : SixExponentials :=
  sixExponentials_of_fourExponentials
    (fourExponentials_of_strongFour_of_gs (strongFourExponentials_of_algIndepLogs h)
      fun _ _ hℓ hc hcq he => not_isAlgebraic_exp_mul_of_algIndepLogs h hℓ hc hcq he)

set_option maxHeartbeats 1000000 in
/-- **Conjecture 1 ⇒ Roy's strong six exponentials theorem.**  A by-product of phase 24: the
phase-17 proof `StrongSix.strongSix` uses `hS` in exactly one place, to make the logarithm basis
`μ` algebraically independent, and that is Conjecture 1 verbatim.  So the *whole* of Roy's
theorem — not only the four-exponentials specialisation — rests on the weaker hypothesis. -/
theorem strongSix_of_algIndepLogs (h : AlgIndepLogsConjecture) : StrongSixExponentials := by
  classical
  intro x y hx hy
  have hx' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) x := hx
  have hy' : LinearIndependent (↥(algebraicClosure ℚ ℂ)) y := hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, μ, hμli, hμexp, hμmem⟩ :=
    StrongSix.exists_logBasis (fun p : Fin 2 × Fin 3 => x p.1 * y p.2) (fun p => hcon p.1 p.2)
  have hind : AlgebraicIndependent ℚ μ := h n μ hμli hμexp
  have halg : Algebra.IsAlgebraic ℚ (↥(algebraicClosure ℚ ℂ)) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hindK : AlgebraicIndependent (↥(algebraicClosure ℚ ℂ)) μ :=
    hind.extendScalars (↥(algebraicClosure ℚ ℂ))
  have hinj : Function.Injective (MvPolynomial.aeval μ : MvPolynomial (Fin n) (algebraicClosure ℚ ℂ) →ₐ[(algebraicClosure ℚ ℂ)] ℂ) := hindK
  choose a b hab using fun p : Fin 2 × Fin 3 => StrongSix.exists_aff_of_mem (hμmem p)
  set pa : Fin 3 → (algebraicClosure ℚ ℂ) := fun j => a (0, j) with hpa
  set pb : Fin 3 → Fin n → (algebraicClosure ℚ ℂ) := fun j => b (0, j) with hpb
  set qa : Fin 3 → (algebraicClosure ℚ ℂ) := fun j => a (1, j) with hqa
  set qb : Fin 3 → Fin n → (algebraicClosure ℚ ℂ) := fun j => b (1, j) with hqb
  have hPval : ∀ j, MvPolynomial.aeval μ (aff (pa j) (pb j)) = x 0 * y j := fun j => by
    rw [StrongSix.aeval_aff]; exact (hab (0, j)).symm
  have hQval : ∀ j, MvPolynomial.aeval μ (aff (qa j) (qb j)) = x 1 * y j := fun j => by
    rw [StrongSix.aeval_aff]; exact (hab (1, j)).symm
  -- the cross relations
  have hcross : ∀ i j : Fin 3, aff (qa i) (qb i) * aff (pa j) (pb j)
      = aff (qa j) (qb j) * aff (pa i) (pb i) := by
    intro i j
    refine hinj ?_
    rw [map_mul, map_mul, hPval, hPval, hQval, hQval]
    ring
  -- `P` is `ℚ̄`-linearly independent
  have hx0 : x 0 ≠ 0 := hx'.ne_zero 0
  have hPind : LinearIndependent (algebraicClosure ℚ ℂ) (fun j => aff (pa j) (pb j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ j, (g j : ℂ) * (x 0 * y j) = 0 := by
      have := congrArg (MvPolynomial.aeval μ) hg
      rw [map_sum, map_zero] at this
      simpa [Algebra.smul_def, hPval] using this
    have h1 : ∑ j, g j • y j = 0 := by
      have hx0' : x 0 ≠ 0 := hx0
      have : x 0 * ∑ j, (g j : ℂ) * y j = 0 := by
        rw [Finset.mul_sum]; rw [← h0]; apply Finset.sum_congr rfl; intro j _; ring
      have h2 : ∑ j, (g j : ℂ) * y j = 0 := (mul_eq_zero.1 this).resolve_left hx0'
      simpa [Algebra.smul_def] using h2
    exact Fintype.linearIndependent_iff.1 hy' g h1
  obtain ⟨c, hc⟩ := const_ratio pa qa pb qb hPind hcross
  -- `x₁ = c·x₀`, contradicting the `ℚ̄`-independence of `x`
  have hxc : x 1 = (c : ℂ) * x 0 := by
    have h := congrArg (MvPolynomial.aeval μ) (hc 0)
    rw [hQval, map_mul, hPval, MvPolynomial.aeval_C] at h
    have h' : x 1 * y 0 = (c : ℂ) * (x 0 * y 0) := h
    have hy0 : y 0 ≠ 0 := hy'.ne_zero 0
    have hz : (x 1 - (c : ℂ) * x 0) * y 0 = 0 := by linear_combination h'
    exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hy0)
  have hsum : ∑ i, (![c, -1] : Fin 2 → (algebraicClosure ℚ ℂ)) i • x i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def]
    have h1 : (algebraMap (↥(algebraicClosure ℚ ℂ)) ℂ) c = (c : ℂ) := rfl
    have h2 : (algebraMap (↥(algebraicClosure ℚ ℂ)) ℂ) (-1 : (algebraicClosure ℚ ℂ)) = (-1 : ℂ) := by
      rw [map_neg, map_one]
    rw [h1, h2, hxc]
    ring
  have hzero := Fintype.linearIndependent_iff.1 hx' _ hsum
  have : (-1 : (algebraicClosure ℚ ℂ)) = 0 := by simpa using hzero 1
  exact absurd this (by simp)

end LeanFormalizations.Waldschmidt2023
