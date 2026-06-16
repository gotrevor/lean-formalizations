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
import LeanFormalizations.NumberTheory.Transcendence.ETranscendental

open Polynomial Filter Finset
open scoped Nat Topology

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

/-- **General analytic assembly** (the reusable analytic heart of Hermite–Lindemann for
*arbitrary* algebraic exponents — not just `e`'s integer ones). Writing `ℓ := F.leadingCoeff`,
no integer exp-relation

  `K + ∑_{r ∈ F.aroots ℂ} e^r = 0`   (`K` a positive integer)

can hold for `F : ℤ[X]` with nonzero constant term, **provided** the `ℓ`-scaled root-sums of
every integer polynomial `gp` are integers (`hsum` : `ℓ^m · ∑_r aeval r gp ∈ ℤ` whenever
`deg gp ≤ m`). This hypothesis is the *only* remaining algebraic input: it holds for **every**
`F : ℤ[X]` because `ℓ·r` is an algebraic integer for each root `r`, so symmetric functions of
the `ℓ·r` are integers (for monic `F`, `ℓ = 1` and it is `sum_aeval_roots_int`, handed to
Aristotle).

Proof: feed `F` to `LindemannWeierstrass.exp_polynomial_approx` (`gp.natDegree ≤ p·deg F − 1`,
so take `m = p·deg F`). Form the integer `N := ℓ^{p·deg F}·K·n + p·S` with
`S = ℓ^{p·deg F}·∑_r aeval r gp ∈ ℤ`. Then `(N:ℂ) = −∑_r ℓ^{p·deg F}(n·e^r − p·aeval r gp)`,
so `‖(N:ℂ)‖ ≤ (card roots)·(|ℓ|^{deg F}·c)^p/(p−1)! < 1` (pick the prime `p` large), giving
`N = 0`; while `N ≡ ℓ^{p·deg F}·K·n (mod p)` with `p ∤ ℓ·K·n` (`p` prime `> |ℓ|, K`), giving
`N ≠ 0` — contradiction. Generalizes `ETranscendental.no_intPoly_aeval_eq_zero` from the
integer roots `{1,…,m}` to an arbitrary `F.aroots ℂ`.

For the `π` reduction (★): `F` is the (in general non-monic) integer polynomial whose roots
are the nonzero subset-sums `σ_t` of the conjugates of `iπ`, and `K = #{t : σ_t = 0}`. The
only remaining gap is the *symmetric-function construction* of that conjugate polynomial
together with its `hsum`. -/
theorem no_intPoly_exp_relation
    (F : ℤ[X]) (hF0 : F.eval 0 ≠ 0)
    (hsum : ∀ (gp : ℤ[X]) (m : ℕ), gp.natDegree ≤ m → ∃ S : ℤ,
        (F.leadingCoeff : ℂ) ^ m * (((F.aroots ℂ).map (fun r => aeval r gp)).sum) = (S : ℂ))
    (K : ℤ) (hK : 0 < K)
    (hrel : (K : ℂ) + ((F.aroots ℂ).map (fun r => Complex.exp r)).sum = 0) :
    False := by
  classical
  set ℓ : ℤ := F.leadingCoeff with hℓ
  have hFne : F ≠ 0 := fun h => hF0 (by rw [h]; simp)
  have hℓne : ℓ ≠ 0 := by rw [hℓ]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  set d : ℕ := F.natDegree with hd
  set rs := F.aroots ℂ with hrs
  set B : ℝ := (Multiset.card rs : ℝ) with hB
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx F hF0
  set cc : ℝ := (|ℓ| : ℝ) ^ d * c with hcc
  obtain ⟨p, hp_prime, hp_gt, hp_small⟩ :=
    exists_prime_smallness cc B (max (F.eval 0).natAbs (max K.natAbs ℓ.natAbs))
  have hp_F : (F.eval 0).natAbs < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_Kℓ : max K.natAbs ℓ.natAbs < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hp_K : K.natAbs < p := lt_of_le_of_lt (le_max_left _ _) hp_Kℓ
  have hp_ℓ : ℓ.natAbs < p := lt_of_le_of_lt (le_max_right _ _) hp_Kℓ
  obtain ⟨n, hpn, gp, hgp_deg, hgp_bound⟩ := hc p hp_F hp_prime
  have hgp_m : gp.natDegree ≤ p * d := le_trans hgp_deg (Nat.sub_le _ _)
  obtain ⟨S, hS⟩ := hsum gp (p * d) hgp_m
  set N : ℤ := ℓ ^ (p * d) * K * n + (p : ℤ) * S with hNdef
  have gsub : ∀ (u : Multiset ℂ) (f g : ℂ → ℂ),
      (u.map (fun r => f r - g r)).sum = (u.map f).sum - (u.map g).sum := by
    intro u f g
    induction u using Multiset.induction with
    | empty => simp
    | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring
  have hexp_sum : ((rs.map (fun r => Complex.exp r)).sum) = (-K : ℂ) := by
    linear_combination hrel
  set ε : ℂ → ℂ := fun r => (ℓ:ℂ)^(p*d) * ((n : ℂ) * Complex.exp r - (p : ℂ) * aeval r gp)
    with hε
  have key : (N : ℂ) = - (rs.map ε).sum := by
    have e2 : (rs.map ε).sum
        = ((ℓ:ℂ)^(p*d)*(n:ℂ)) * (rs.map (fun r => Complex.exp r)).sum
          - (p:ℂ) * ((ℓ:ℂ)^(p*d) * ((rs.map (fun r => aeval r gp)).sum)) := by
      rw [hε, show (fun r => (ℓ:ℂ)^(p*d) * ((n:ℂ)*Complex.exp r - (p:ℂ)*aeval r gp))
            = (fun r => ((ℓ:ℂ)^(p*d)*(n:ℂ))*Complex.exp r - ((ℓ:ℂ)^(p*d)*(p:ℂ))*aeval r gp)
            from by funext r; ring,
          gsub rs (fun r => ((ℓ:ℂ)^(p*d)*(n:ℂ))*Complex.exp r)
            (fun r => ((ℓ:ℂ)^(p*d)*(p:ℂ))*aeval r gp),
          Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
      ring
    rw [e2, hexp_sum, hS]
    push_cast [hNdef]; ring
  have hεbound : ∀ r ∈ rs, ‖ε r‖ ≤ cc ^ p / (p - 1)! := by
    intro r hr
    have hb := hgp_bound hr
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    have hnorm_eq : ‖ε r‖
        = (|ℓ|:ℝ)^(p*d) * ‖(n:ℂ)*Complex.exp r - (p:ℂ)*aeval r gp‖ := by
      rw [hε, norm_mul, norm_pow, Complex.norm_intCast]
    rw [hnorm_eq, show cc ^ p / (p-1)! = (|ℓ|:ℝ)^(p*d) * (c^p/(p-1)!) from by
          rw [hcc]; ring]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hNzero : N = 0 := by
    have hnorm : ‖(N : ℂ)‖ < 1 := by
      rw [key, norm_neg]
      have h1 : ‖(rs.map ε).sum‖ ≤ (rs.map (fun r => ‖ε r‖)).sum := by
        have := norm_multiset_sum_le (rs.map ε); rwa [Multiset.map_map] at this
      have h2 : (rs.map (fun r => ‖ε r‖)).sum ≤ Multiset.card rs • (cc^p/(p-1)!) := by
        have := Multiset.sum_le_card_nsmul (rs.map (fun r => ‖ε r‖)) (cc^p/(p-1)!) (by
          intro x hx; rw [Multiset.mem_map] at hx
          obtain ⟨r, hr, rfl⟩ := hx; exact hεbound r hr)
        rwa [Multiset.card_map] at this
      calc ‖(rs.map ε).sum‖ ≤ (rs.map (fun r => ‖ε r‖)).sum := h1
        _ ≤ Multiset.card rs • (cc^p/(p-1)!) := h2
        _ = B * (cc^p/(p-1)!) := by rw [hB, nsmul_eq_mul]
        _ < 1 := hp_small
    rw [Complex.norm_intCast] at hnorm
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hnorm)
  have hNne : N ≠ 0 := by
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
    have hpdvd : ∀ a : ℤ, a.natAbs < p → 0 < |a| → ¬ (p : ℤ) ∣ a := by
      intro a ha hpos hd
      have hle : (p:ℤ) ≤ |a| := Int.le_of_dvd hpos ((dvd_abs _ _).mpr hd)
      rw [Int.abs_eq_natAbs] at hle
      have : p ≤ a.natAbs := by exact_mod_cast hle
      omega
    have hpK : ¬ (p:ℤ) ∣ K := hpdvd K hp_K (abs_pos.mpr (by positivity))
    have hpℓ : ¬ (p:ℤ) ∣ ℓ := hpdvd ℓ hp_ℓ (abs_pos.mpr hℓne)
    have hpℓpow : ¬ (p:ℤ) ∣ ℓ^(p*d) := fun h => hpℓ (hpi.dvd_of_dvd_pow h)
    intro hN0
    have hdvd : (p:ℤ) ∣ ℓ^(p*d) * K * n := by
      have he : ℓ^(p*d) * K * n = -((p:ℤ) * S) := by rw [hNdef] at hN0; linarith [hN0]
      rw [he]; exact (Dvd.intro _ rfl).neg_right
    rcases hpi.dvd_mul.mp hdvd with h | h
    · rcases hpi.dvd_mul.mp h with h' | h'
      · exact hpℓpow h'
      · exact hpK h'
    · exact hpn h
  exact hNne hNzero

end LeanFormalizations.Transcendence
