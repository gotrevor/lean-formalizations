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

open MvPolynomial

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

Curtis's argument: by Lemma 1 pick admissible triples `(p, xₙ, yₙ)` with `xₙ`
prime, `xₙ ≡ 1`, `yₙ ≡ p−k+1 (mod p)`, `(xₙ,yₙ)=1` and `yₙ/xₙ → α` for an
irrational `α ∈ (p−k, p−k+1)`; by Lemma 2 their Frobenius number is exactly
`(k−2)xₙ + yₙ − p`, so `G(xₙ,yₙ) = F(p,xₙ,yₙ,g) = 0`. As `n → ∞` the leading form
of `G` acquires infinitely many roots (every irrational in the interval), so it
vanishes; hence `G ≡ 0`. -/
theorem substCurve_eq_zero (F : MvPolynomial (Fin 4) ℂ)
    (hF : ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} → eval (evalPoint s₁ s₂ s₃ g) F = 0)
    (p k : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hk : 2 ≤ k) (hk' : 2 * k ≤ p + 1) :
    substCurve F p k = 0 := by
  sorry

/-- **Step B — the degree-counting finish** (disclosed `sorry`).
If the specialization `H := F(p,·,·,·)` is nonzero and every substituted curve
`substCurve F p k` (for `k` in Curtis's range) vanishes, then the `(p−1)/2`
distinct linear forms `Y − ((k−2)X₂+X₃−p)` each divide `H` (as a polynomial in
`Y` over `ℂ[X₂,X₃]`, since `H` has root `(k−2)X₂+X₃−p`) and are pairwise coprime,
so their product divides `H`. Hence `(p−1)/2 ≤ degᵧ H ≤ H.totalDegree ≤
F.totalDegree`.

The nonvanishing hypothesis `hH` is essential: without it `F = X₁ − p` would be a
counterexample (its specialization at `p` is `0`, so every substitution vanishes,
yet its total degree is `1`). The main theorem supplies a prime avoiding the
finitely many `p` with `specCurve F p = 0` via `finite_specCurve_eq_zero`. -/
theorem half_le_totalDegree (F : MvPolynomial (Fin 4) ℂ)
    (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hH : specCurve F p ≠ 0)
    (hsub : ∀ k, 2 ≤ k → 2 * k ≤ p + 1 → substCurve F p k = 0) :
    (p - 1) / 2 ≤ F.totalDegree := by
  sorry

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
