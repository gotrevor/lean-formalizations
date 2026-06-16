/-
# Toward `hermite_lindemann` for `π`: the conjugate-product reduction (scaffold)

This file develops the **algebraic part** of Lindemann's π-transcendence proof — the
piece that `ETranscendental.lean` did *not* need (because the Hermite polynomial there
has integer roots `1,…,m`). For `π` the exponents are the Galois conjugates of `iπ`, so
the integer-`N`/mod-`p` assembly must run over a *symmetric* family of algebraic roots.

## The classical reduction (Lindemann 1882)

Suppose `π` is algebraic. Then `α := iπ` is algebraic and nonzero, with minimal
polynomial (scaled to `ℤ`) having complex roots `θ₁ = iπ, θ₂, …, θ_n` (the conjugate
set). Euler's identity gives `e^{θ₁} = e^{iπ} = -1`, so the product

  `∏_{k=1}^n (1 + e^{θ_k}) = 0`   (its `k = 1` factor vanishes).

Expanding the product over subsets `t ⊆ {1,…,n}` (`prod_one_add_exp_eq_sum_subsetSum`):

  `∑_{t ⊆ [n]} e^{σ_t} = 0,    σ_t := ∑_{k ∈ t} θ_k.`

Separating the subsets with `σ_t = 0` (there are `K ≥ 1` of them — at least the empty
set) from those with `σ_t ≠ 0` (`sum_subsetSum_split`) yields

  `K + ∑_{t : σ_t ≠ 0} e^{σ_t} = 0,    K = #{t : σ_t = 0} ≥ 1.`               (★)

The **two remaining ingredients** (the genuine algebraic part, still open here):

* **(Integrality of the conjugate polynomial).** The multiset `{σ_t : σ_t ≠ 0}` is
  invariant under the Galois action permuting the `θ_k`, so `F(X) = ∏_t (X − σ_t)` has
  *rational* coefficients; scaling by a power of the leading coefficient makes
  `F ∈ ℤ[X]` with `F(0) ≠ 0`. (Provable via `MvPolynomial`'s fundamental theorem of
  symmetric polynomials + Vieta, with no explicit Galois theory.)
* **(Analytic assembly over `F`'s roots).** Feed `F` to
  `LindemannWeierstrass.exp_polynomial_approx`, and re-run the integer-`N`/mod-`p`
  contradiction of `ETranscendental.no_intPoly_aeval_eq_zero` — but now the per-root
  contributions are summed *symmetrically* over the roots of `F`. The new analytic input
  is that `∑_{r ∈ F.aroots ℂ} aeval r gp ∈ ℤ` for `gp ∈ ℤ[X]` (power sums of the roots
  of a monic integer polynomial are integers); this `sum_aeval_roots_int` lemma is the
  one piece handed to Aristotle.

This file proves **(★)** — the combinatorial reduction — fully and axiom-clean. The two
ingredients above are the isolated remaining crux toward discharging `hermite_lindemann`
at `π` (equivalently, adopting mathlib PR #28013 on the next bump; see
`HermiteLindemann.lean`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open scoped Nat

namespace LeanFormalizations.Transcendence

/-- **Subset-sum expansion.** Over a finite index set `s`, the product `∏ (1 + e^{θ k})`
expands as the sum of `e^{σ_t}` (with `σ_t = ∑_{k ∈ t} θ k`) over all subsets `t ⊆ s`.

This is `Finset.prod_add` with `f = e^{θ·}`, `g = 1`, using `Complex.exp_sum` to turn
each subset-product `∏_{k ∈ t} e^{θ k}` into `e^{∑_{k ∈ t} θ k}`. -/
theorem prod_one_add_exp_eq_sum_subsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (θ : ι → ℂ) :
    ∏ k ∈ s, (1 + Complex.exp (θ k))
      = ∑ t ∈ s.powerset, Complex.exp (∑ k ∈ t, θ k) := by
  have h := Finset.prod_add (fun k => Complex.exp (θ k)) (fun _ => (1 : ℂ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [show (∏ k ∈ s, (1 + Complex.exp (θ k))) = ∏ k ∈ s, (Complex.exp (θ k) + 1) from
    Finset.prod_congr rfl (fun k _ => by ring)]
  rw [h]
  exact Finset.sum_congr rfl (fun t _ => (Complex.exp_sum t θ).symm)

/-- **Vanishing from one zero factor.** If some `θ k₀` (with `k₀ ∈ s`) satisfies
`e^{θ k₀} = -1` — as `θ k₀ = iπ` does, by Euler — then the whole subset-sum expansion
is `0`. This is the entry point of Lindemann's π argument. -/
theorem sum_subsetSum_exp_eq_zero_of_factor {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (θ : ι → ℂ) (k₀ : ι) (hk₀ : k₀ ∈ s) (hval : Complex.exp (θ k₀) = -1) :
    ∑ t ∈ s.powerset, Complex.exp (∑ k ∈ t, θ k) = 0 := by
  rw [← prod_one_add_exp_eq_sum_subsetSum]
  refine Finset.prod_eq_zero hk₀ ?_
  rw [hval]; ring

/-- **Zero/nonzero split.** The subset-sum expansion equals the integer count of subsets
with zero sum (each contributing `e^0 = 1`) plus the sum of `e^{σ_t}` over subsets with
nonzero sum. The count `#{t : σ_t = 0}` is `≥ 1` (the empty subset has sum `0`). -/
theorem sum_subsetSum_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℂ) :
    ∑ t ∈ s.powerset, Complex.exp (∑ k ∈ t, θ k)
      = ((s.powerset.filter (fun t => ∑ k ∈ t, θ k = 0)).card : ℂ)
        + ∑ t ∈ s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0),
            Complex.exp (∑ k ∈ t, θ k) := by
  rw [← Finset.sum_filter_add_sum_filter_not s.powerset (fun t => ∑ k ∈ t, θ k = 0)]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) (fun t ht => by
        simp only [Finset.mem_filter] at ht; rw [ht.2, Complex.exp_zero])]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The empty subset always lies in the zero-sum family, so its cardinality is positive:
the constant `K` in `(★)` is a genuine positive integer. -/
theorem zeroSubsetSum_card_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℂ) :
    0 < (s.powerset.filter (fun t => ∑ k ∈ t, θ k = 0)).card := by
  refine Finset.card_pos.mpr ⟨∅, ?_⟩
  simp

/-- **(★) — the combinatorial reduction of π-transcendence.** If `e^{θ k₀} = -1` for some
`k₀ ∈ s`, then writing `K := #{t ⊆ s : σ_t = 0}` (a positive integer), the nonzero
subset-sums satisfy

  `(K : ℂ) + ∑_{t : σ_t ≠ 0} e^{σ_t} = 0`.

This is exactly the integer exp-relation that the analytic assembly (over the integer
polynomial whose roots are the nonzero `σ_t`) turns into a contradiction. Proved
axiom-clean; the remaining gap is the *integrality* of that conjugate polynomial. -/
theorem pi_exp_relation {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℂ)
    (k₀ : ι) (hk₀ : k₀ ∈ s) (hval : Complex.exp (θ k₀) = -1) :
    ((s.powerset.filter (fun t => ∑ k ∈ t, θ k = 0)).card : ℂ)
      + ∑ t ∈ s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0),
          Complex.exp (∑ k ∈ t, θ k) = 0 := by
  rw [← sum_subsetSum_split]
  exact sum_subsetSum_exp_eq_zero_of_factor s θ k₀ hk₀ hval

end LeanFormalizations.Transcendence
