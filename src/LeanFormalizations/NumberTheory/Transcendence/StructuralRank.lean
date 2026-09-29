/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Rank of matrices of logarithms (Waldschmidt 2023 §5, phase 20)

Survey claims, each proved here from the stated input:

* `rk(M) ≤ r_str(M)`, "plain" (specialise `Xₖ ↦ eₖ`).
* Conjecture 1 ⇒ `rk(M) = r_str(M)` for matrices of logarithms (Roy 1995; survey p. 7).  Route:
  pick the basis `e` among `ℚ`-combinations of the entries, which are again logarithms of algebraic
  numbers.  Conjecture 1 makes `e` algebraically independent, so the specialisation
  `ℚ[X] → ℂ, Xₖ ↦ eₖ` is injective, and it preserves every minor's (non)vanishing.
* Six exponentials ⇒ (`r_str(M) ≥ 3` ⇒ `rk(M) ≥ 2`) for matrices of logarithms (survey p. 7,
  "From the six exponentials Theorem, one deduces").  Expected route: a rank-one log matrix is
  `xᵢyⱼ` with algebraic exponentials, and `r_str ≥ 3` supplies two `ℚ`-independent rows and three
  `ℚ`-independent columns.
* Sanity anchor: the 2×2 matrix `[[log 2, log 3], [2 log 2, 2 log 3]]` has structural rank 1.

If a frozen statement is false as written (e.g. the six-exponentials claim needs an extra
hypothesis), record the counterexample; that is an advance.  Frozen: the statements below, every
earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.StructuralRank
import LeanFormalizations.Literature.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.Waldschmidt2023

namespace LeanFormalizations.StructuralRank

open LeanFormalizations.Literature Matrix Module Set MvPolynomial

/-! ### Leaf 1: rank via minors (missing from mathlib) -/

theorem exists_indep_subfamily {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] (v : ι → V) (s : ℕ)
    (hs : s ≤ finrank K (Submodule.span K (Set.range v))) :
    ∃ g : Fin s → ι, LinearIndependent K (v ∘ g) := by
  classical
  obtain ⟨b, hbt, hspan, hind⟩ := exists_linearIndependent K (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbt
  have : Fintype b := hbfin.fintype
  have hcard : finrank K (Submodule.span K b) = b.toFinset.card := finrank_span_set_eq_card hind
  have hs' : s ≤ Fintype.card b := by
    rw [hspan] at hcard
    rw [Set.toFinset_card] at hcard
    omega
  obtain ⟨e⟩ : Nonempty (Fin s ↪ b) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hs'
  have hmem : ∀ i : Fin s, (e i : V) ∈ Set.range v := fun i => hbt (e i).2
  choose g hg using hmem
  refine ⟨g, ?_⟩
  have : v ∘ g = (fun x : b => (x : V)) ∘ e := by
    funext i; simp [Function.comp, hg i]
  rw [this]
  exact hind.comp e e.injective

theorem exists_submatrix_det_ne_zero {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) {s : ℕ} (hs : s ≤ A.rank) :
    ∃ (f : Fin s → m) (g : Fin s → n), (A.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := exists_indep_subfamily A.col s (by rwa [← A.rank_eq_finrank_span_cols])
  set A1 : Matrix m (Fin s) K := A.submatrix id g with hA1
  have hcol : A1.col = A.col ∘ g := rfl
  have hrank1 : A1.rank = s := by
    have : A1ᵀ.rank = s := by
      have h2 : LinearIndependent K A1ᵀ.row := hg
      simpa using h2.rank_matrix
    rwa [rank_transpose] at this
  obtain ⟨f, hf⟩ := exists_indep_subfamily A1.row s (by rw [← A1.rank_eq_finrank_span_row, hrank1])
  refine ⟨f, g, ?_⟩
  have hB : A.submatrix f g = A1.submatrix f id := rfl
  have : LinearIndependent K (A1.submatrix f id).row := hf
  rw [hB]
  have := Matrix.linearIndependent_rows_iff_isUnit.mp this
  exact Matrix.isUnit_iff_isUnit_det _ |>.mp this |>.ne_zero

theorem le_rank_of_det_ne_zero {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) {s : ℕ} (f : Fin s → m) (g : Fin s → n)
    (h : (A.submatrix f g).det ≠ 0) : s ≤ A.rank := by
  have h1 : (A.submatrix f g).rank = s := by
    rw [rank_of_isUnit _ (Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr h))]
    simp
  rw [← h1]; exact rank_submatrix_le A f g

theorem rank_map_le_rank_map {m n A L₁ L₂ : Type*} [Fintype m] [Fintype n]
    [CommRing A] [Field L₁] [Field L₂] (ψ₁ : A →+* L₁) (ψ₂ : A →+* L₂)
    (h : ∀ x, ψ₁ x ≠ 0 → ψ₂ x ≠ 0) (G : Matrix m n A) :
    (G.map ψ₁).rank ≤ (G.map ψ₂).rank := by
  classical
  obtain ⟨f, g, hfg⟩ := exists_submatrix_det_ne_zero (G.map ψ₁) (le_refl (G.map ψ₁).rank)
  refine le_rank_of_det_ne_zero _ f g ?_
  have e1 : (G.map ψ₁).submatrix f g = (G.submatrix f g).map ψ₁ := rfl
  have e2 : (G.map ψ₂).submatrix f g = (G.submatrix f g).map ψ₂ := rfl
  have d1 : ((G.submatrix f g).map ψ₁).det = ψ₁ (G.submatrix f g).det := by
    rw [RingHom.map_det]; rfl
  have d2 : ((G.submatrix f g).map ψ₂).det = ψ₂ (G.submatrix f g).det := by
    rw [RingHom.map_det]; rfl
  rw [e1, d1] at hfg
  rw [e2, d2]
  exact h _ hfg

/-! ### Leaf 2: the generic matrix -/

section
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]

/-- The generic matrix `∑ₖ cₖ Xₖ`, over the polynomial ring. -/
noncomputable def genericMat {t : ℕ} (c : Fin t → Matrix m n ℚ) :
    Matrix m n (MvPolynomial (Fin t) ℚ) := ∑ k, (c k).map (fun q ↦ C q * X k)

theorem genericMat_map {t : ℕ} (c : Fin t → Matrix m n ℚ) {S : Type*} [CommRing S]
    (ψ : MvPolynomial (Fin t) ℚ →+* S) :
    (∑ k, (c k).map (fun q ↦ ψ (C q * X k))) = (genericMat c).map ψ := by
  ext i j
  simp [genericMat, Matrix.sum_apply, map_sum]

theorem genericMat_aeval {t : ℕ} (c : Fin t → Matrix m n ℚ) (e : Fin t → ℂ) :
    (∑ k, (c k).map (fun q : ℚ ↦ (q : ℂ) * e k))
      = (genericMat c).map (aeval e : MvPolynomial (Fin t) ℚ →ₐ[ℚ] ℂ).toRingHom := by
  rw [← genericMat_map]
  congr 1
  funext k
  congr 1
  funext q
  simp

/-! ### Leaf 3: refinement of the basis -/

theorem entry_eq {t : ℕ} {M : Matrix m n ℂ} {e : Fin t → ℂ} {c : Fin t → Matrix m n ℚ}
    (hM : M = ∑ k, (c k).map (fun q : ℚ ↦ (q : ℂ) * e k)) (i : m) (j : n) :
    M i j = ∑ k, (c k i j : ℂ) * e k := by
  subst hM; simp [Matrix.sum_apply]

theorem coord_unique {t : ℕ} {e : Fin t → ℂ} (hind : LinearIndependent ℚ e)
    {a b : Fin t → ℚ} (h : ∑ k, (a k : ℂ) * e k = ∑ k, (b k : ℂ) * e k) : a = b := by
  have : ∑ k, (a k - b k) • e k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    simpa [Rat.smul_def] using sub_eq_zero.mpr h
  have := (Fintype.linearIndependent_iff.mp hind) (fun k => a k - b k) this
  funext k; have := this k; linarith [this]

theorem coeff_refine {t t' : ℕ} {M : Matrix m n ℂ} {e : Fin t → ℂ} {f : Fin t' → ℂ}
    (hind : LinearIndependent ℚ e) {c : Fin t → Matrix m n ℚ} {d : Fin t' → Matrix m n ℚ}
    (hc : M = ∑ k, (c k).map (fun q : ℚ ↦ (q : ℂ) * e k))
    (hd : M = ∑ j, (d j).map (fun q : ℚ ↦ (q : ℂ) * f j))
    (s : Fin t' → Fin t → ℚ) (hs : ∀ j, f j = ∑ k, (s j k : ℂ) * e k) (i : m) (j : n) :
    (fun k ↦ c k i j) = fun k ↦ ∑ j', d j' i j * s j' k := by
  refine coord_unique hind ?_
  rw [← entry_eq hc i j, entry_eq hd i j]
  simp only [hs]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j' _ => by ring

theorem genericMat_refine {t t' : ℕ} {M : Matrix m n ℂ} {e : Fin t → ℂ} {f : Fin t' → ℂ}
    (hind : LinearIndependent ℚ e) {c : Fin t → Matrix m n ℚ} {d : Fin t' → Matrix m n ℚ}
    (hc : M = ∑ k, (c k).map (fun q : ℚ ↦ (q : ℂ) * e k))
    (hd : M = ∑ j, (d j).map (fun q : ℚ ↦ (q : ℂ) * f j))
    (s : Fin t' → Fin t → ℚ) (hs : ∀ j, f j = ∑ k, (s j k : ℂ) * e k) :
    genericMat c = (genericMat d).map
      (aeval (fun j' ↦ ∑ k, C (s j' k) * X k) : MvPolynomial (Fin t') ℚ →ₐ[ℚ] _) := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (coeff_refine hind hc hd s hs i j)
  simp only [genericMat, Matrix.sum_apply, Matrix.map_apply, map_sum, map_mul, aeval_C, aeval_X,
    algebraMap_eq]
  simp only [h]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul, C_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j' _ => by ring

end

/-! ### The frozen statements -/

theorem rank_le_structRank {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    {M : Matrix m n ℂ} {r : ℕ} (h : IsStructRank M r) : M.rank ≤ r := by
  classical
  obtain ⟨t, e, c, hind, hM, hrank⟩ := h
  rw [genericMat_map c (algebraMap (MvPolynomial (Fin t) ℚ)
    (FractionRing (MvPolynomial (Fin t) ℚ)))] at hrank
  rw [hM, genericMat_aeval]
  rw [← hrank]
  refine rank_map_le_rank_map _ _ ?_ _
  intro x hx hc
  have hx0 : x = 0 := IsFractionRing.injective (MvPolynomial (Fin t) ℚ)
    (FractionRing (MvPolynomial (Fin t) ℚ)) (by rw [hc, map_zero])
  exact hx (by rw [hx0, map_zero])

theorem rank_eq_structRank_of_algIndepLogs (h1 : AlgIndepLogsConjecture) {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] {M : Matrix m n ℂ} {r : ℕ} (hM : IsLogMatrix M)
    (h : IsStructRank M r) : M.rank = r := by
  classical
  refine le_antisymm (rank_le_structRank h) ?_
  obtain ⟨t, e, c, hind, hc, hrank⟩ := h
  -- a maximal `ℚ`-independent set of entries
  obtain ⟨v, hvdef⟩ : ∃ v : m × n → ℂ, ∀ p : m × n, v p = M p.1 p.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hbt, hspan, hbind⟩ := exists_linearIndependent ℚ (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbt
  have : Fintype b := hbfin.fintype
  obtain ⟨t', ⟨g⟩⟩ : ∃ t' : ℕ, Nonempty (Fin t' ≃ b) :=
    ⟨Fintype.card b, ⟨(Fintype.equivFin b).symm⟩⟩
  obtain ⟨f, hfdef⟩ : ∃ f : Fin t' → ℂ, ∀ i, f i = (g i : ℂ) :=
    ⟨fun i => (g i : ℂ), fun _ => rfl⟩
  have hfeq : f = (fun x : b => (x : ℂ)) ∘ g := funext hfdef
  have hfind : LinearIndependent ℚ f := by rw [hfeq]; exact hbind.comp g g.injective
  have hfmem : ∀ i, f i ∈ Set.range v := fun i => by rw [hfdef]; exact hbt (g i).2
  -- each `f i` is an entry, hence a logarithm of an algebraic number
  have hfalg : ∀ i, IsAlgebraic ℚ (Complex.exp (f i)) := by
    intro i
    obtain ⟨p, hp⟩ := hfmem i
    rw [← hp, hvdef]; exact hM p.1 p.2
  have halg : AlgebraicIndependent ℚ f := h1 t' f hfind hfalg
  -- entries are `ℚ`-combinations of `f`
  have hrf : Set.range f = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; rw [hfdef]; exact (g i).2
    · intro hx; exact ⟨g.symm ⟨x, hx⟩, by rw [hfdef]; simp⟩
  have hentry : ∀ i j, M i j ∈ Submodule.span ℚ (Set.range f) := by
    intro i j
    rw [hrf, hspan]
    exact Submodule.subset_span ⟨(i, j), hvdef (i, j)⟩
  have hco : ∀ i j, ∃ q : Fin t' → ℚ, ∑ k, q k • f k = M i j := by
    intro i j
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hentry i j)
  choose q hq using hco
  obtain ⟨d, hd0⟩ : ∃ d : Fin t' → Matrix m n ℚ, ∀ k i j, d k i j = q i j k :=
    ⟨fun k => Matrix.of fun i j => q i j k, fun _ _ _ => rfl⟩
  have hd : M = ∑ k, (d k).map (fun r : ℚ ↦ (r : ℂ) * f k) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.sum_apply]
    rw [← hq i j]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.map_apply, hd0]; simp [Rat.smul_def]
  -- `f` is a `ℚ`-combination of `e` (each `f i` is an entry)
  have hs : ∀ i, ∃ s : Fin t → ℚ, f i = ∑ k, (s k : ℂ) * e k := by
    intro i
    obtain ⟨p, hp⟩ := hfmem i
    exact ⟨fun k => c k p.1 p.2, by rw [← hp, hvdef]; exact entry_eq hc p.1 p.2⟩
  choose s hsp using hs
  have href := genericMat_refine hind hc hd s hsp
  rw [genericMat_map c (algebraMap (MvPolynomial (Fin t) ℚ)
    (FractionRing (MvPolynomial (Fin t) ℚ)))] at hrank
  have hMd : M = (genericMat d).map (aeval f : MvPolynomial (Fin t') ℚ →ₐ[ℚ] ℂ).toRingHom := by
    rw [hd, genericMat_aeval]
  set ρ : MvPolynomial (Fin t') ℚ →+* MvPolynomial (Fin t) ℚ :=
    (aeval (fun j' ↦ ∑ k, C (s j' k) * X k) : MvPolynomial (Fin t') ℚ →ₐ[ℚ] _).toRingHom with hρ
  set σ : MvPolynomial (Fin t') ℚ →+* FractionRing (MvPolynomial (Fin t) ℚ) :=
    (algebraMap (MvPolynomial (Fin t) ℚ) (FractionRing (MvPolynomial (Fin t) ℚ))).comp ρ with hσ
  have hswap : (genericMat c).map
      (algebraMap (MvPolynomial (Fin t) ℚ) (FractionRing (MvPolynomial (Fin t) ℚ)))
      = (genericMat d).map σ := by
    rw [href, Matrix.map_map]; rfl
  rw [← hrank, hswap, hMd]
  refine rank_map_le_rank_map σ (aeval f : MvPolynomial (Fin t') ℚ →ₐ[ℚ] ℂ).toRingHom ?_
    (genericMat d)
  intro x hx hax
  have hx0 : x = 0 := halg (by simpa using hax)
  exact hx (by rw [hx0, map_zero])

theorem two_le_rank_of_sixExponentials (h6 : SixExponentials) {m n : Type} [Fintype m]
    [Fintype n] [DecidableEq n] {M : Matrix m n ℂ} {r : ℕ} (hM : IsLogMatrix M)
    (h : IsStructRank M r) (hr : 3 ≤ r) : 2 ≤ M.rank := by
  sorry

theorem structRank_log_example :
    IsStructRank !![(Real.log 2 : ℂ), (Real.log 3 : ℂ); 2 * (Real.log 2 : ℂ), 2 * (Real.log 3 : ℂ)] 1 := by
  classical
  refine ⟨2, ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)],
    ![!![1, 0; 2, 0], !![0, 1; 0, 2]], LeanFormalizations.Exponentials.linearIndependent_log_two_three,
    ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sum_apply, Fin.sum_univ_two]
  · have hvm : (∑ k, (![!![(1 : ℚ), 0; 2, 0], !![0, 1; 0, 2]] k).map (fun q : ℚ ↦
        algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (C q * X k)))
        = Matrix.vecMulVec ![(1 : FractionRing (MvPolynomial (Fin 2) ℚ)), 2]
            ![algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
                (X (0 : Fin 2)),
              algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
                (X (1 : Fin 2))] := by
      have hC2 : (C (2 : ℚ) : MvPolynomial (Fin 2) ℚ) = 2 := map_ofNat C 2
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        (try simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, map_mul,
          hC2, map_ofNat])
    rw [hvm]
    refine le_antisymm (Matrix.rank_vecMulVec_le _ _) ?_
    refine le_rank_of_det_ne_zero _ ![0] ![0] ?_
    rw [Matrix.det_fin_one]
    have hX : algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
        (X (0 : Fin 2)) ≠ 0 := by
      intro hcon
      exact MvPolynomial.X_ne_zero (0 : Fin 2)
        (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ)
          (FractionRing (MvPolynomial (Fin 2) ℚ)) (by rw [hcon, map_zero]))
    simp only [Matrix.submatrix_apply, Matrix.vecMulVec_apply, Matrix.cons_val_zero, one_mul]
    exact hX


end LeanFormalizations.StructuralRank
