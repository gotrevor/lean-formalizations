/-
# Curtis (1990) — proof engine

The proofs delegated to by the audit surface `Statement.lean`.

## Status of the two headline results
- `no_finite_polynomial_formula_engine` — **PROVED** (axiom-clean), as a direct
  corollary of the main theorem via Curtis's `F = ∏ (fᵢ − Y)` argument.
- `no_polynomial_relation_engine` — the main theorem, currently `sorry`. Its
  decomposition into Curtis's two lemmas + the degree-counting finish is laid
  out below (`lemma1`, `lemma2`, and the finish), each a disclosed `sorry` with
  a citing docstring. Multi-lap target.
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Defs
import LeanFormalizations.NumericalSemigroups.Curtis.Lemma2
import LeanFormalizations.NumericalSemigroups.Curtis.GridVanish

open MvPolynomial
open scoped Nat

namespace LeanFormalizations.NumericalSemigroups.Curtis

/-! ## The main theorem (engine)

The proof is decomposed into

* `substCurve_eq_zero` — Curtis's **Lemmas 1 + 2 + the limit argument**: for each
  prime `p > 2` and each `k ∈ {2,…,(p−1)/2+1}`, the substituted plane curve
  `G(X₂,X₃) = F(p, X₂, X₃, (k−2)X₂+X₃−p)` is identically zero;
* `half_le_totalDegree` — the **degree-counting finish**: those `(p−1)/2` distinct
  vanishing substitutions force `(p−1)/2 ≤ F.totalDegree`.

Given both, `no_polynomial_relation_engine` follows because a fixed natural number
`F.totalDegree` cannot dominate `(p−1)/2` for arbitrarily large primes `p`.
Both inputs are disclosed `sorry`s (multi-lap); the spine and the final
contradiction below are machine-checked. -/

/-- The Curtis substitution: `G(X₂,X₃) = F(p, X₂, X₃, (k−2)·X₂ + X₃ − p)`, the
plane curve obtained from `F` by fixing `X₁ := p` and `Y := (k−2)X₂ + X₃ − p`.
Here the two surviving variables `X₂, X₃` are `X 0, X 1 : MvPolynomial (Fin 2) ℂ`. -/
noncomputable def substCurve (F : MvPolynomial (Fin 4) ℂ) (p k : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  aeval ![C (p : ℂ), X 0, X 1, C ((k : ℂ) - 2) * X 0 + X 1 - C (p : ℂ)] F

/-- A substitution by degree-`≤ 1` terms cannot raise total degree. -/
theorem totalDegree_aeval_le {σ τ : Type*} [Fintype σ] (v : σ → MvPolynomial τ ℂ)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (f : MvPolynomial σ ℂ) :
    (aeval v f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  have hstep : ∀ n ∈ m.support, (v n ^ m n).totalDegree ≤ m n := fun n _ =>
    (totalDegree_pow _ _).trans
      (by calc m n * (v n).totalDegree ≤ m n * 1 := Nat.mul_le_mul_left _ (hv n)
            _ = m n := by ring)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [show ∑ n ∈ m.support, m n = m.sum fun _ e => e from rfl]
  exact le_totalDegree hm

/-- **Bridge.** Evaluating the substituted plane curve at an integer point `(x,y)`
equals evaluating `F` at the corresponding graph point `(p, x, y, (k−2)x+y−p)`. The
hypothesis `p ≤ (k−2)x + y` makes the natural-number subtraction faithful. -/
theorem eval_substCurve_eq (F : MvPolynomial (Fin 4) ℂ) (p k x y : ℕ)
    (hk : 2 ≤ k) (hg : p ≤ (k - 2) * x + y) :
    eval ![(x : ℂ), (y : ℂ)] (substCurve F p k)
      = eval (evalPoint p x y ((k - 2) * x + y - p)) F := by
  have hv : (fun i => (aeval ![(x : ℂ), (y : ℂ)])
        (![C (p : ℂ), X 0, X 1, C ((k : ℂ) - 2) * X 0 + X 1 - C (p : ℂ)] i))
      = evalPoint p x y ((k - 2) * x + y - p) := by
    funext i
    fin_cases i
    · simp [evalPoint]
    · simp [evalPoint]
    · simp [evalPoint]
    · show (aeval ![(x : ℂ), (y : ℂ)]) (C ((k : ℂ) - 2) * X 0 + X 1 - C (p : ℂ))
          = evalPoint p x y ((k - 2) * x + y - p) 3
      rw [aeval_eq_eval, map_sub, map_add, map_mul, eval_C, eval_X, eval_C, eval_X]
      simp only [evalPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val]
      rw [Nat.cast_sub hg, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk]
      push_cast
      ring
  rw [substCurve, ← aeval_eq_eval (f := ![(x : ℂ), (y : ℂ)]), comp_aeval_apply, hv,
    aeval_eq_eval]

/-- The specialization `F(p, X₂, X₃, Y)` at `X₁ := p`, a 3-variable polynomial in
`X₂, X₃, Y` (mapped to `X 0, X 1, X 2 : MvPolynomial (Fin 3) ℂ`). The Curtis
substitution `substCurve F p k` factors through this by then setting
`Y := (k−2)X₂ + X₃ − p`. -/
noncomputable def specCurve (F : MvPolynomial (Fin 4) ℂ) (p : ℕ) :
    MvPolynomial (Fin 3) ℂ :=
  aeval ![C (p : ℂ), X 0, X 1, X 2] F

/-- For `F ≠ 0`, the specialization `F(p, ·, ·, ·)` vanishes for only finitely
many `p`. Proof: viewing `F` through `MvPolynomial.finSuccEquiv` as a univariate
polynomial `Fp := finSuccEquiv ℂ 3 F` over the domain `S = ℂ[X₂,X₃,Y]`, one has
`specCurve F p = Fp.eval (C p)`; so `specCurve F p = 0` says `C p` is a root of
the nonzero `Fp`, and a nonzero polynomial over a domain has finitely many roots.
The map `p ↦ C (p : ℂ)` is injective, so the set of such `p` is finite. -/
theorem finite_specCurve_eq_zero (F : MvPolynomial (Fin 4) ℂ) (hF0 : F ≠ 0) :
    {p : ℕ | specCurve F p = 0}.Finite := by
  -- `Fp`, the image of `F` as a univariate polynomial over `ℂ[X₂,X₃,Y]`.
  set Fp : Polynomial (MvPolynomial (Fin 3) ℂ) := finSuccEquiv ℂ 3 F with hFp
  have hFp0 : Fp ≠ 0 := by
    simpa [hFp] using (finSuccEquiv ℂ 3).injective.ne hF0
  -- Per-generator agreement, then `specCurve F p = Fp.eval (C p)`.
  have hkey : ∀ p : ℕ, specCurve F p = Polynomial.eval (C (p : ℂ)) Fp := by
    intro p
    have hgen : ∀ i : Fin 4,
        aeval ![C (p : ℂ), X 0, X 1, X 2] (X i : MvPolynomial (Fin 4) ℂ)
          = Polynomial.eval (C (p : ℂ)) (finSuccEquiv ℂ 3 (X i)) := by
      intro i
      rw [aeval_X]
      refine Fin.cases ?_ ?_ i
      · simp [finSuccEquiv_X_zero]
      · intro j
        rw [finSuccEquiv_X_succ, Polynomial.eval_C]
        fin_cases j <;> rfl
    -- `aeval v` and `eval (C p) ∘ finSuccEquiv` agree as ring homs.
    have hev : ((aeval ![C (p : ℂ), X 0, X 1, X 2] :
          MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ).toRingHom)
        = (Polynomial.evalRingHom (C (p : ℂ))).comp
            ((finSuccEquiv ℂ 3 :
                MvPolynomial (Fin 4) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 3) ℂ)) :
              MvPolynomial (Fin 4) ℂ →+* Polynomial (MvPolynomial (Fin 3) ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        have hC : finSuccEquiv ℂ 3 (C r) = Polynomial.C ((C r : MvPolynomial (Fin 3) ℂ)) := by
          rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; simp
        simp [Polynomial.coe_evalRingHom, hC, MvPolynomial.algebraMap_eq]
      · intro i; simpa [Polynomial.coe_evalRingHom] using hgen i
    simp only [specCurve, hFp]
    simpa [Polynomial.coe_evalRingHom] using DFunLike.congr_fun hev F
  -- The root set of `Fp` over the domain `S` is finite.
  have hroots : {a : MvPolynomial (Fin 3) ℂ | Fp.IsRoot a}.Finite := by
    apply Set.Finite.subset Fp.roots.toFinset.finite_toSet
    intro a ha
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hFp0]
    exact ha
  -- `{p | specCurve F p = 0}` is the preimage of that finite set under `p ↦ C p`.
  have hCinj : Function.Injective (fun p : ℕ => (C (p : ℂ) : MvPolynomial (Fin 3) ℂ)) :=
    (MvPolynomial.C_injective (Fin 3) ℂ).comp Nat.cast_injective
  apply Set.Finite.subset (hroots.preimage (hCinj.injOn))
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hr : Polynomial.eval (C (p : ℂ)) Fp = 0 := by rw [← hkey p]; exact hp
  simpa [Set.mem_preimage, Polynomial.IsRoot] using hr

/-- **Step A — Curtis's Lemmas 1 + 2 + limit argument** (disclosed `sorry`).
If `F` vanishes on the graph of the Frobenius number over the admissible family,
then for every prime `p > 2` and every `k` with `2 ≤ k ≤ (p−1)/2 + 1` the
substituted plane curve is identically zero.

**The proof (machine-checked, axiom-clean).** This replaces Curtis's Lemma 1
(Dirichlet + Farey adjacency to produce a *converging* sequence of coprime points)
and the projective/limit argument by an elementary observation: neither
`IsAdmissible` nor Lemma 2 ever needs full coprimality `gcd(x,y)=1` — only
`p ∤ y` and `x ∤ y`. So fix one prime `x ≡ 1 (mod p)` with `x > p·(D+1)`
(`D = F.totalDegree`); for such a fixed `x` the open interval `((p−k)x, (p−k+1)x)`
has length `x` and therefore contains **no** multiple of `x` (so `x ∤ y` is
automatic), while it contains `≥ D+1` integers `y ≡ p−k+1 (mod p)`. Each such
`(p, x, y)` is admissible with Frobenius number `(k−2)x + y − p` (Lemma 2), so the
substituted curve `G = substCurve F p k` vanishes at `(x,y)`. Running `x` over
`D+1` such primes (Dirichlet, `Nat.exists_prime_gt_modEq_one`) gives a
`(D+1)×(D+1)` "staircase" of zeros, and `grid_vanish` (double root-counting +
`MvPolynomial.funext`) forces `G = 0`. -/
theorem substCurve_eq_zero (F : MvPolynomial (Fin 4) ℂ)
    (hF : ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} → eval (evalPoint s₁ s₂ s₃ g) F = 0)
    (p k : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hk : 2 ≤ k) (hk' : 2 * k ≤ p + 1) :
    substCurve F p k = 0 := by
  set n := F.totalDegree with hn
  -- The substituted plane curve has total degree at most `n = F.totalDegree`.
  have hGdeg : (substCurve F p k).totalDegree ≤ n := by
    rw [substCurve]
    apply totalDegree_aeval_le
    intro i
    fin_cases i
    · exact (totalDegree_C _).le.trans (Nat.zero_le _)
    · exact (totalDegree_X _).le
    · exact (totalDegree_X _).le
    · refine (totalDegree_sub _ _).trans ?_
      rw [totalDegree_C]
      simp only [Nat.max_eq_left (Nat.zero_le _)]
      refine (totalDegree_add _ _).trans ?_
      rw [max_le_iff]
      refine ⟨(totalDegree_mul _ _).trans ?_, (totalDegree_X _).le⟩
      rw [totalDegree_C, zero_add]; exact (totalDegree_X _).le
  -- Infinitely many primes `≡ 1 (mod p)` above the threshold `p·(n+1)`.
  set S : Set ℕ := {q : ℕ | q.Prime ∧ q % p = 1 ∧ p * (n + 1) < q} with hS
  have hSinf : S.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro m
    obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ :=
      Nat.exists_prime_gt_modEq_one (max m (p * (n + 1))) (k := p) (by omega)
    refine ⟨q, ⟨hq_prime, ?_, lt_of_le_of_lt (le_max_right _ _) hq_gt⟩,
      lt_of_le_of_lt (le_max_left _ _) hq_gt⟩
    have : q % p = 1 % p := hq_mod
    rwa [Nat.one_mod_eq_one.mpr (by omega)] at this
  -- Extract `n+1` distinct such primes via the natural embedding of an infinite set.
  set e := hSinf.natEmbedding with he
  set xq : Fin (n + 1) → ℕ := fun i => (e i.val).val with hxq
  have hxmem : ∀ i, xq i ∈ S := fun i => (e i.val).property
  have hxinj : Function.Injective xq := by
    intro i j hij
    simp only [hxq, Subtype.val_inj, EmbeddingLike.apply_eq_iff_eq] at hij
    exact Fin.val_injective hij
  -- Apply the grid-vanishing lemma to `G = substCurve F p k`.
  refine grid_vanish (substCurve F p k) n hGdeg
    (fun i => (xq i : ℂ)) ?_
    (fun i j => (((p - k) * xq i + 1 + j.val * p : ℕ) : ℂ)) ?_ ?_
  · -- injectivity of the first coordinates
    intro i j hij
    simp only [Nat.cast_inj] at hij
    exact hxinj hij
  · -- the `n+1` second coordinates in each row are distinct
    intro i a b hab
    have hp0 : 0 < p := by omega
    simp only [Nat.cast_inj] at hab
    have hc : (a : ℕ) * p = (b : ℕ) * p := by omega
    exact Fin.val_injective (Nat.eq_of_mul_eq_mul_right hp0 hc)
  · -- the curve vanishes at every grid point, via Lemma 2 + admissibility + `hF`
    intro i j
    obtain ⟨hxp, hxmod, hxgt⟩ := hxmem i
    set x := xq i with hxdef
    have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    have hpk1 : 1 ≤ p - k := by omega
    have hxbig : p < x := by nlinarith
    have hpkx : x ≤ (p - k) * x := by nlinarith
    have hroom : 1 + (j : ℕ) * p < x := by nlinarith
    set y := (p - k) * x + 1 + (j : ℕ) * p with hydef
    have hxy : x < y := by omega
    have hexp : (p - k + 1) * x = (p - k) * x + x := by ring
    have hub : y < (p - k + 1) * x := by omega
    have hlb : (p - k) * x < y := by omega
    have hg : p ≤ (k - 2) * x + y := by omega
    have hymodp : y % p = p - k + 1 := by
      have hmodx : x ≡ 1 [MOD p] := by
        unfold Nat.ModEq; rw [hxmod, Nat.one_mod_eq_one.mpr (by omega)]
      have e1 : (p - k) * x ≡ (p - k) * 1 [MOD p] := (Nat.ModEq.refl _).mul hmodx
      have e2 : (j : ℕ) * p ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr ⟨j, by ring⟩
      have e3 : y ≡ (p - k) * 1 + 1 + 0 [MOD p] := by
        rw [hydef]; exact (e1.add_right 1).add e2
      have hee : y % p = ((p - k) * 1 + 1 + 0) % p := e3
      rw [hee]; simp only [mul_one, add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hyxmod : y % x = 1 + (j : ℕ) * p := by
      have hregroup : y = (1 + (j : ℕ) * p) + x * (p - k) := by rw [hydef]; ring
      rw [hregroup, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hroom]
    have hxndvd : ¬ x ∣ y := by
      intro hxd; rw [Nat.dvd_iff_mod_eq_zero] at hxd; omega
    have hpndvd : ¬ p ∣ y := by
      intro hpd; rw [Nat.dvd_iff_mod_eq_zero] at hpd; omega
    have hadm : IsAdmissible p x y := ⟨hxbig, hxy, hp, hxp, hpndvd, hxndvd⟩
    have hfrob : FrobeniusNumber ((k - 2) * x + y - p) {p, x, y} :=
      Lemma2.lemma2 p x y k hp2 hxbig hxy hk hk' hlb hub hxmod hymodp
    have hzero := hF p x y ((k - 2) * x + y - p) hadm hfrob
    have key : eval ![(x : ℂ), (y : ℂ)] (substCurve F p k) = 0 := by
      rw [eval_substCurve_eq F p k x y hk hg]; exact hzero
    exact key

/-- `substCurve F p k` is the `Y := (k−2)X₂ + X₃ − p` substitution applied to the
specialization `specCurve F p`. This factoring is the bridge for Step B: each
`substCurve F p k = 0` says `(k−2)X₂+X₃−p` is a root of `specCurve F p` viewed as
a polynomial in `Y`. -/
theorem substCurve_eq_aeval_specCurve (F : MvPolynomial (Fin 4) ℂ) (p k : ℕ) :
    substCurve F p k
      = aeval ![X 0, X 1, C ((k : ℂ) - 2) * X 0 + X 1 - C (p : ℂ)] (specCurve F p) := by
  rw [substCurve, specCurve, comp_aeval_apply]
  refine congrArg (fun v => aeval v F) ?_
  funext i
  fin_cases i <;> simp

/-- Evaluating `finSuccEquiv` at `q` is the substitution `X 0 := q` keeping the
tail variables: `eval q (finSuccEquiv G) = aeval (Fin.cons q X) G`. -/
theorem eval_finSuccEquiv_eq_aeval_cons (G : MvPolynomial (Fin 3) ℂ)
    (q : MvPolynomial (Fin 2) ℂ) :
    Polynomial.eval q (finSuccEquiv ℂ 2 G) = aeval (Fin.cons q (fun i : Fin 2 => X i)) G := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hf]
      congr 1
      refine Fin.cases ?_ ?_ i
      · simp [finSuccEquiv_X_zero]
      · intro j; simp [finSuccEquiv_X_succ, Fin.cons_succ]

/-- Curtis's linear form `(k−2)X₂ + X₃ − p ∈ ℂ[X₂,X₃]`, the value substituted for
`Y` to produce `substCurve F p k`. -/
noncomputable def linForm (p k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  C ((k : ℂ) - 2) * X 0 + X 1 - C (p : ℂ)

/-- The specialization `F(p,·,·,·)` has total degree at most that of `F`. -/
theorem totalDegree_specCurve_le (F : MvPolynomial (Fin 4) ℂ) (p : ℕ) :
    (specCurve F p).totalDegree ≤ F.totalDegree := by
  rw [specCurve]
  apply totalDegree_aeval_le
  intro i
  fin_cases i
  · exact (totalDegree_C (p : ℂ)).le.trans (by norm_num)
  · exact (totalDegree_X (R := ℂ) 0).le
  · exact (totalDegree_X (R := ℂ) 1).le
  · exact (totalDegree_X (R := ℂ) 2).le

/-- **Step B — the degree-counting finish** (PROVED).
If the specialization `H := F(p,·,·,·)` is nonzero and every substituted curve
`substCurve F p k` (for `k = 2,…,(p−1)/2+1`) vanishes, then `(p−1)/2 ≤ F.totalDegree`.

Proof: view `H` as a polynomial in `Y` over `ℂ[X₂,X₃]` —
`Hy := finSuccEquiv ℂ 2 (rename (finRotate 3) H)`, which rotates `Y` into the
distinguished variable. Each `substCurve F p k = 0` says `linForm p k` is a root of
`Hy`; the `(p−1)/2` forms `linForm p k` are distinct (their `X₂`-coefficient is
`(k:ℂ)−2`), so `Hy` has at least `(p−1)/2` roots, whence
`(p−1)/2 ≤ Hy.natDegree = H.degreeOf 2 ≤ H.totalDegree ≤ F.totalDegree`.

The nonvanishing hypothesis `hH` is essential: without it `F = X₁ − p` would be a
counterexample (its specialization at `p` is `0`, so every substitution vanishes,
yet its total degree is `1`). The main theorem supplies a prime avoiding the
finitely many `p` with `specCurve F p = 0` via `finite_specCurve_eq_zero`. -/
theorem half_le_totalDegree (F : MvPolynomial (Fin 4) ℂ)
    (p : ℕ) (_hp : p.Prime) (hp2 : 2 < p) (hH : specCurve F p ≠ 0)
    (hsub : ∀ k, 2 ≤ k → 2 * k ≤ p + 1 → substCurve F p k = 0) :
    (p - 1) / 2 ≤ F.totalDegree := by
  set H := specCurve F p with hHdef
  set Hy := finSuccEquiv ℂ 2 (rename (finRotate 3) H) with hHy
  have hHyne : Hy ≠ 0 := by
    rw [hHy]
    simp only [ne_eq, AddEquivClass.map_eq_zero_iff]
    rw [rename_eq_zero_iff_of_injective _ (Equiv.injective _)]
    exact hH
  -- each `linForm p k` is a root of `Hy`
  have hroot : ∀ k, substCurve F p k = Polynomial.eval (linForm p k) Hy := by
    intro k
    rw [hHy, eval_finSuccEquiv_eq_aeval_cons, substCurve_eq_aeval_specCurve, ← hHdef,
      aeval_rename]
    refine congrArg (fun v => aeval v H) ?_
    funext i
    fin_cases i <;> rfl
  -- the forms `linForm p k` are distinct in `k`
  have hinj : Function.Injective (linForm p) := by
    intro a b hab
    have h1 : (eval ![(1 : ℂ), 0]) (linForm p a) = (eval ![(1 : ℂ), 0]) (linForm p b) := by
      rw [hab]
    simp only [linForm, map_add, map_sub, map_mul, eval_C, eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h1
    have hc : (a : ℂ) = b := by linear_combination h1
    exact_mod_cast hc
  -- `Hy.natDegree = H.degreeOf 2`
  have hdeg : Hy.natDegree = H.degreeOf 2 := by
    rw [hHy, natDegree_finSuccEquiv]
    have h := degreeOf_rename_of_injective (p := H) (Equiv.injective (finRotate 3)) 2
    have h2 : (finRotate 3) 2 = 0 := by decide
    rwa [h2] at h
  -- the `(p−1)/2` distinct roots and the degree chain
  set rng := Finset.Icc 2 ((p - 1) / 2 + 1) with hrng
  have hcard : rng.card = (p - 1) / 2 := by rw [hrng, Nat.card_Icc]; omega
  have hsubset : rng.image (linForm p) ⊆ Hy.roots.toFinset := by
    intro c hc
    simp only [Finset.mem_image, hrng, Finset.mem_Icc] at hc
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hc
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hHyne, Polynomial.IsRoot.def, ← hroot]
    exact hsub k hk1 (by omega)
  calc (p - 1) / 2 = rng.card := hcard.symm
    _ = (rng.image (linForm p)).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Hy.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ Multiset.card Hy.roots := Multiset.toFinset_card_le _
    _ ≤ Hy.natDegree := Polynomial.card_roots' _
    _ = H.degreeOf 2 := hdeg
    _ ≤ H.totalDegree := degreeOf_le_totalDegree H 2
    _ ≤ F.totalDegree := totalDegree_specCurve_le F p

/-- **Curtis's theorem (1990), engine form.** No nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]`
vanishes on the graph of the Frobenius number over the admissible family `A`.

The spine: a hypothetical `F` would, by `half_le_totalDegree` (fed by
`substCurve_eq_zero`), satisfy `(p−1)/2 ≤ F.totalDegree` for every prime `p > 2`.
But `F.totalDegree` is a fixed natural number, and `(p−1)/2 → ∞` along the primes
(Euclid), so choosing `p ≥ 2·F.totalDegree + 3` gives a contradiction. -/
theorem no_polynomial_relation_engine :
    ¬ ∃ F : MvPolynomial (Fin 4) ℂ, F ≠ 0 ∧
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        eval (evalPoint s₁ s₂ s₃ g) F = 0 := by
  rintro ⟨F, hF0, hF⟩
  set D := F.totalDegree with hD
  -- The good primes — prime, `> 2`, and with nonvanishing specialization — form
  -- an infinite set (primes are infinite; only finitely many `p` are bad).
  have hgood : {p : ℕ | p.Prime ∧ specCurve F p ≠ 0}.Infinite := by
    have hset : {p : ℕ | p.Prime ∧ specCurve F p ≠ 0}
        = {p : ℕ | p.Prime} \ {p : ℕ | specCurve F p = 0} := by
      ext p; simp [Set.mem_diff]
    rw [hset]
    exact Nat.infinite_setOf_prime.diff (finite_specCurve_eq_zero F hF0)
  -- Pick such a good prime `p ≥ 2·D + 3`.
  obtain ⟨p, ⟨hp, hpH⟩, hple⟩ := hgood.exists_gt (2 * D + 2)
  have hp2 : 2 < p := by
    have := hp.two_le; omega
  -- Curtis's degree bound at this prime.
  have hbound : (p - 1) / 2 ≤ D :=
    half_le_totalDegree F p hp hp2 hpH
      (fun k hk hk' => substCurve_eq_zero F hF p k hp hp2 hk hk')
  -- But `p ≥ 2·D + 3` forces `(p-1)/2 ≥ D+1`, a contradiction.
  have : D + 1 ≤ (p - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  omega

/-! ## The corollary (fully proved) -/

/-- **Corollary, engine form.** No finite list of polynomials
`f₀,…,f_{k-1} ∈ ℂ[X₁,X₂,X₃]` computes the Frobenius number piecewise.

Curtis's proof: if some `fᵢ` equals `g` on every admissible triple, then
`F = ∏ᵢ (fᵢ − Y)` is a nonzero polynomial vanishing on the whole graph,
contradicting the main theorem. We realize `fᵢ` inside `ℂ[X₁,X₂,X₃,Y]` by
renaming along `Fin.castSucc : Fin 3 → Fin 4` (which uses `X₁,X₂,X₃` and avoids
`Y = X₃`), and take `Y := X 3`. -/
theorem no_finite_polynomial_formula_engine :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℂ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] (f i) = (g : ℂ) := by
  rintro ⟨k, f, hf⟩
  apply no_polynomial_relation_engine
  -- The Curtis polynomial `F = ∏ᵢ (rename castSucc (fᵢ) − X₃)`.
  refine ⟨∏ i : Fin k, (rename Fin.castSucc (f i) - X 3), ?_, ?_⟩
  · -- `F ≠ 0`: each factor is nonzero (its `X₃`-coefficient is `−1`).
    rw [Finset.prod_ne_zero_iff]
    intro i _ hzero
    have hrange : (3 : Fin 4) ∉ Set.range (Fin.castSucc : Fin 3 → Fin 4) := by decide
    have hcoeff :
        coeff (Finsupp.single 3 1) (rename Fin.castSucc (f i) - X (3 : Fin 4)) = -1 := by
      rw [coeff_sub, coeff_X']
      have h0 : coeff (Finsupp.single 3 1) (rename Fin.castSucc (f i)) = 0 := by
        apply coeff_rename_eq_zero
        intro u hu
        exact absurd (hu ▸ (Finsupp.mapDomain_notin_range u 3 hrange)) (by simp)
      rw [h0]
      simp
    rw [hzero] at hcoeff
    simp at hcoeff
  · -- `F` vanishes on the graph: pick the `fᵢ` computing `g`; that factor is `0`.
    intro s₁ s₂ s₃ g hadm hfrob
    obtain ⟨i, hi⟩ := hf s₁ s₂ s₃ g hadm hfrob
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [map_sub, eval_rename, eval_X]
    have hcomp : (evalPoint s₁ s₂ s₃ g) ∘ Fin.castSucc = ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] := by
      funext j
      fin_cases j <;> rfl
    rw [hcomp, hi]
    show (g : ℂ) - evalPoint s₁ s₂ s₃ g 3 = 0
    simp [evalPoint]

end LeanFormalizations.NumericalSemigroups.Curtis
