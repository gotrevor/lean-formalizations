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
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
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

/-- The complex roots of `integralNormalization F` are exactly `ℓ·(roots of F)`,
`ℓ = F.leadingCoeff` (a unit over `ℂ`). The standard "integralize" correspondence:
`integralNormalization F * C ℓ = scaleRoots F ℓ`, mapped to `ℂ`. -/
theorem aroots_integralNormalization (F : ℤ[X]) (hF : F ≠ 0) :
    (integralNormalization F).aroots ℂ
      = (F.aroots ℂ).map (fun r => (F.leadingCoeff : ℂ) * r) := by
  have hℓ : (F.leadingCoeff : ℤ) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hF
  have hℓc : ((F.leadingCoeff : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hmain := integralNormalization_mul_C_leadingCoeff F
  have h1 : (integralNormalization F * C F.leadingCoeff).aroots ℂ
      = (integralNormalization F).aroots ℂ := by
    rw [mul_comm, aroots_C_mul _ hℓ]
  have h2 : (scaleRoots F F.leadingCoeff).aroots ℂ
      = (F.aroots ℂ).map (fun r => (F.leadingCoeff : ℂ) * r) := by
    rw [aroots_def, map_scaleRoots F F.leadingCoeff (algebraMap ℤ ℂ) (by simpa using hℓc),
        roots_scaleRoots _ (isUnit_iff_ne_zero.mpr (by simpa using hℓc)), ← aroots_def]
    rfl
  rw [← h1, hmain, h2]

/-- **`hsum` for any integer `F`, reduced to the monic case.** If for every monic `G : ℤ[X]`
and every `q : ℤ[X]` the root-sum `∑_{s∈G.aroots} aeval s q` is an integer (`monic_rootsum`
— exactly `sum_aeval_roots_int`, Aristotle job `9a19f72e`), then the `ℓ`-scaled root-sums of
`no_intPoly_exp_relation`'s `hsum` hold for **every** `F : ℤ[X]` with nonzero constant term
(`ℓ = F.leadingCoeff`, `deg gp ≤ m`). Via `integralNormalization F` (monic; roots `= ℓ·F.aroots`)
and `aeval (ℓ·r) (scaleRoots gp ℓ) = ℓ^{deg gp}·aeval r gp`. So once the monic lemma lands,
`hsum` is NOT a π-specific obstruction — the *only* remaining gap is the symmetric-function
construction of the conjugate polynomial. -/
theorem hsum_of_monic_rootsum
    (monic_rootsum : ∀ (G : ℤ[X]), G.Monic → ∀ q : ℤ[X], ∃ T : ℤ,
        ((G.aroots ℂ).map (fun s => aeval s q)).sum = (T : ℂ))
    (F : ℤ[X]) (hF0 : F.eval 0 ≠ 0) :
    ∀ (gp : ℤ[X]) (m : ℕ), gp.natDegree ≤ m → ∃ S : ℤ,
        (F.leadingCoeff : ℂ) ^ m * (((F.aroots ℂ).map (fun r => aeval r gp)).sum)
          = (S : ℂ) := by
  intro gp m hm
  have hF : F ≠ 0 := fun h => hF0 (by rw [h]; simp)
  set ℓ := F.leadingCoeff with hℓ
  have hGmonic : (integralNormalization F).Monic := monic_integralNormalization hF
  have haroots := aroots_integralNormalization F hF
  obtain ⟨T, hT⟩ := monic_rootsum (integralNormalization F) hGmonic (scaleRoots gp ℓ)
  have perroot : ∀ r : ℂ, aeval ((ℓ:ℂ) * r) (scaleRoots gp ℓ)
      = (ℓ:ℂ)^(gp.natDegree) * aeval r gp := by
    intro r
    have h := scaleRoots_eval₂_mul (p := gp) (algebraMap ℤ ℂ) r ℓ
    have hcast : (algebraMap ℤ ℂ) ℓ = (ℓ:ℂ) := by simp
    rw [hcast] at h
    simpa [aeval_def] using h
  have hkey : (ℓ:ℂ)^(gp.natDegree) * (((F.aroots ℂ).map (fun r => aeval r gp)).sum)
      = (T : ℂ) := by
    rw [← hT, haroots, Multiset.map_map]
    rw [show (fun s => aeval s (scaleRoots gp ℓ)) ∘ (fun r => (ℓ:ℂ)*r)
          = (fun r => (ℓ:ℂ)^(gp.natDegree) * aeval r gp) from by funext r; exact perroot r]
    rw [Multiset.sum_map_mul_left]
  refine ⟨ℓ^(m - gp.natDegree) * T, ?_⟩
  have hpow : (ℓ:ℂ)^m = (ℓ:ℂ)^(m - gp.natDegree) * (ℓ:ℂ)^(gp.natDegree) := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [hpow, mul_assoc, hkey]; push_cast; ring

/-- **Capstone reduction.** The Lindemann subset-sum relation is impossible, modulo exactly
two named facts. Given a finite family of "conjugates" `θ : ι → ℂ` over `s` with one value
`θ k₀` satisfying `e^{θ k₀} = -1` (Euler, for `θ k₀ = iπ`), it is contradictory to have

* **(monic_rootsum)** the monic root-sum integrality (`sum_aeval_roots_int`, Aristotle
  job `9a19f72e`); and
* **(conjugate polynomial)** an integer polynomial `F` with `F.eval 0 ≠ 0` whose complex
  roots (with multiplicity) are exactly the **nonzero subset-sums** `σ_t = ∑_{k∈t} θ k`.

It assembles `pi_exp_relation` (★), `hsum_of_monic_rootsum`, and `no_intPoly_exp_relation`:
the relation `(K:ℂ) + ∑_{r∈F.aroots} e^r = 0` with `K = #{t : σ_t = 0} > 0` is exactly the
forbidden integer exp-relation. **This is the precise remaining frontier for `π`**: only the
*existence* of the conjugate polynomial `F` (the symmetric-function / Galois construction
over the conjugates of `iπ`) and `monic_rootsum` are still open; everything else is
machine-checked here. Discharging both, with `θ` the conjugate set of `iπ`, kills
`hermite_lindemann` at `π` and makes squaring-the-circle unconditional. -/
theorem subsetSum_relation_impossible
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℂ)
    (k₀ : ι) (hk₀ : k₀ ∈ s) (hval : Complex.exp (θ k₀) = -1)
    (monic_rootsum : ∀ G : ℤ[X], G.Monic → ∀ q : ℤ[X], ∃ T : ℤ,
        ((G.aroots ℂ).map (fun r => aeval r q)).sum = (T : ℂ))
    (F : ℤ[X]) (hF0 : F.eval 0 ≠ 0)
    (hFroots : F.aroots ℂ
        = (s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0)).val.map
            (fun t => ∑ k ∈ t, θ k)) :
    False := by
  set K : ℤ := ((s.powerset.filter (fun t => ∑ k ∈ t, θ k = 0)).card : ℤ) with hKdef
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast zeroSubsetSum_card_pos s θ
  refine no_intPoly_exp_relation F hF0
    (hsum_of_monic_rootsum monic_rootsum F hF0) K hK ?_
  have hrel := pi_exp_relation s θ k₀ hk₀ hval
  rw [hFroots, Multiset.map_map]
  have hsumeq : ((s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0)).val.map
      ((fun r => Complex.exp r) ∘ (fun t => ∑ k ∈ t, θ k))).sum
      = ∑ t ∈ s.powerset.filter (fun t => ∑ k ∈ t, θ k ≠ 0),
          Complex.exp (∑ k ∈ t, θ k) := by
    rw [Finset.sum]; rfl
  rw [hsumeq, show (K : ℂ)
      = ((s.powerset.filter (fun t => ∑ k ∈ t, θ k = 0)).card : ℂ) from by
        rw [hKdef]; push_cast; ring]
  exact hrel

/-- **Clearing denominators preserving complex roots** (the easy tail of the conjugate
polynomial construction). Any `Q : ℚ[X]` with nonzero constant term has an *integer*
polynomial `F` with the **same complex roots** (with multiplicity) and `F.eval 0 ≠ 0`. Via
`IsLocalization.integerNormalization` (`F.map (ℤ→ℚ) = b·Q`, `b ≠ 0`); a nonzero scalar
leaves the complex roots unchanged, and `0` is a root of neither (since `Q.eval 0 ≠ 0`).
So once the symmetric-function part yields the monic *rational* polynomial with the `σ_t`
as roots, this produces the integer `F` that `subsetSum_relation_impossible` needs. -/
theorem exists_intPoly_aroots_eq (Q : ℚ[X]) (hQ0 : Q.eval 0 ≠ 0) :
    ∃ F : ℤ[X], F.eval 0 ≠ 0 ∧ F.aroots ℂ = Q.aroots ℂ := by
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  obtain ⟨b, hb, hbeq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
  set F : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q with hF
  have hbne : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinjℚℂ : Function.Injective (algebraMap ℚ ℂ) := FaithfulSMul.algebraMap_injective ℚ ℂ
  have hFne : F ≠ 0 := by
    intro h; rw [h, Polynomial.map_zero] at hbeq
    exact (smul_ne_zero hbne hQne) hbeq.symm
  have hmapℂ : F.map (algebraMap ℤ ℂ) = (b : ℤ) • Q.map (algebraMap ℚ ℂ) := by
    have htower : (algebraMap ℤ ℂ) = (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) := by
      rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ]
    rw [htower, ← Polynomial.map_map, hbeq]
    simp only [← Polynomial.coe_mapRingHom]
    exact map_zsmul (Polynomial.mapRingHom (algebraMap ℚ ℂ)) b Q
  have haroots : F.aroots ℂ = Q.aroots ℂ := by
    rw [aroots_def, aroots_def, hmapℂ, zsmul_eq_mul, ← Polynomial.C_eq_intCast, roots_C_mul]
    exact_mod_cast hbne
  have hQroot : (0 : ℂ) ∉ Q.aroots ℂ := by
    rw [mem_aroots]
    rintro ⟨-, h⟩
    rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero] at h
    exact hQ0 (hinjℚℂ (by simpa using h))
  refine ⟨F, ?_, haroots⟩
  intro hFeval
  apply hQroot
  rw [← haroots, mem_aroots]
  exact ⟨hFne, by rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero, hFeval]; simp⟩

/-- **Elementary symmetric functions of the conjugates are rational** (the arithmetic core
of the symmetric-function descent). For a monic `G : ℚ[X]`, every `esymm j` of its complex
roots `G.aroots ℂ` lies in the range of `algebraMap ℚ ℂ`. Vieta (`coeff_eq_esymm_roots_of_card`):
`esymm j = ±G.coeff (deg − j)`, which is rational. Building block toward the conjugate
polynomial's coefficients (which are `ℤ`-polynomials in these `esymm` values, hence rational
by the fundamental theorem of symmetric polynomials — the remaining `subsetSum_poly_descends`
step, Aristotle leaf `tools/aristotle/pi-conjugate-poly-symmetric-prompt.txt`). -/
theorem esymm_aroots_mem_range (G : ℚ[X]) (hG : G.Monic) (j : ℕ) :
    (G.aroots ℂ).esymm j ∈ Set.range (algebraMap ℚ ℂ) := by
  set p : ℂ[X] := G.map (algebraMap ℚ ℂ) with hp
  have hpmonic : p.Monic := hG.map _
  have hcard : Multiset.card p.roots = p.natDegree :=
    (splits_iff_card_roots.1 (IsAlgClosed.splits p))
  have hroots_eq : G.aroots ℂ = p.roots := by rw [aroots_def]
  rw [hroots_eq]
  rcases Nat.lt_or_ge p.natDegree j with hj | hj
  · have hz : p.roots.esymm j = 0 := by
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty j (by omega),
          Multiset.map_zero, Multiset.sum_zero]
    rw [hz]; exact ⟨0, by simp⟩
  · set k : ℕ := p.natDegree - j with hk
    have hkle : k ≤ p.natDegree := Nat.sub_le _ _
    have hvieta := Polynomial.coeff_eq_esymm_roots_of_card hcard hkle
    rw [hpmonic.leadingCoeff, one_mul] at hvieta
    have hjk : p.natDegree - k = j := by omega
    rw [hjk] at hvieta
    have hcoeff : p.coeff k = algebraMap ℚ ℂ (G.coeff k) := by rw [hp, coeff_map]
    refine ⟨(-1)^j * G.coeff k, ?_⟩
    rw [map_mul, map_pow, map_neg, map_one]
    have hsq : ((-1:ℂ))^j * ((-1:ℂ))^j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hesymm : p.roots.esymm j = (-1)^j * p.coeff k := by
      rw [hvieta, ← mul_assoc, hsq, one_mul]
    rw [hesymm, hcoeff]

/-- **The conjugate polynomial descends to `ℚ[X]` — modulo the single fact that the
subset-sum `esymm` is rational.** If every elementary symmetric function `esymm j` of a
multiset `σs : Multiset ℂ` is rational, then `∏_{a ∈ σs} (X − a)` lies in `lifts (ℚ → ℂ)`,
i.e. it is the image of a polynomial in `ℚ[X]`. Via Vieta (`Multiset.prod_X_sub_C_coeff`:
each coefficient is `±esymm`) + `Polynomial.lifts_iff_coeff_lifts`.

For the `π` conjugate polynomial, `σs` is the multiset of subset-sums `{σ_t}`; combined with
the FUNDAMENTAL remaining fact `subsetSum_esymm_rational` (`esymm` of the subset-sums is
rational — symmetric in the conjugates; see
`tools/aristotle/pi-conjugate-poly-symmetric-prompt.txt`) this descends the conjugate
polynomial to `ℚ[X]`, after which `exists_intPoly_aroots_eq` produces the integer `F` and
`subsetSum_relation_impossible` finishes. So the ENTIRE remaining gap is
`subsetSum_esymm_rational`. -/
theorem subsetSum_poly_lifts (σs : Multiset ℂ)
    (hesymm : ∀ j, σs.esymm j ∈ Set.range (algebraMap ℚ ℂ)) :
    (σs.map (fun a => X - C a)).prod ∈ Polynomial.lifts (algebraMap ℚ ℂ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro k
  rcases le_or_gt k (Multiset.card σs) with hk | hk
  · rw [Multiset.prod_X_sub_C_coeff σs hk]
    obtain ⟨q, hq⟩ := hesymm (Multiset.card σs - k)
    exact ⟨(-1)^(Multiset.card σs - k) * q, by rw [map_mul, map_pow, map_neg, map_one, hq]⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [natDegree_multiset_prod_X_sub_C_eq_card]; exact hk)]
    exact ⟨0, by simp⟩

/-- **Removing the zero roots** (the `X^K`-factoring glue). Any `Q : ℚ[X]` (`Q ≠ 0`) has a
factor `Q' : ℚ[X]` with `Q'.eval 0 ≠ 0` whose complex roots are exactly the **nonzero** roots
of `Q`. Via `Q = X^{mult} · Q'` (`exists_eq_pow_rootMultiplicity_mul_and_not_dvd`): the
`X^{mult}` contributes only zero roots, `Q'` contributes the rest (none zero). Lets the
descended conjugate polynomial (whose roots are ALL subset-sums `σ_t`, including `K` zeros)
be replaced by one whose roots are just the nonzero `σ_t`, as `subsetSum_relation_impossible`
requires. -/
theorem exists_ratPoly_removeZeroRoots (Q : ℚ[X]) (hQ : Q ≠ 0) :
    ∃ Q' : ℚ[X], Q'.eval 0 ≠ 0 ∧ (Q.aroots ℂ).filter (fun r => r ≠ 0) = Q'.aroots ℂ := by
  classical
  obtain ⟨Q', hQeq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ (0 : ℚ)
  rw [map_zero, sub_zero] at hQeq hndvd
  have hcoeff : Q'.coeff 0 ≠ 0 := fun hc => hndvd (X_dvd_iff.mpr hc)
  have hQ'eval : Q'.eval 0 ≠ 0 := by rw [← coeff_zero_eq_eval_zero]; exact hcoeff
  have hQ'ne : Q' ≠ 0 := fun h => hcoeff (by rw [h]; simp)
  refine ⟨Q', hQ'eval, ?_⟩
  set m := Q.rootMultiplicity 0 with hm
  have hXmne : (X ^ m : ℚ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have haroots : Q.aroots ℂ = (X ^ m : ℚ[X]).aroots ℂ + Q'.aroots ℂ := by
    conv_lhs => rw [hQeq]
    rw [aroots_mul (mul_ne_zero hXmne hQ'ne)]
  have hXm : (X ^ m : ℚ[X]).aroots ℂ = Multiset.replicate m 0 := by
    rw [aroots_def, Polynomial.map_pow, map_X, roots_pow, roots_X, Multiset.nsmul_singleton]
  have hzero_notmem : (0 : ℂ) ∉ Q'.aroots ℂ := by
    rw [mem_aroots]
    rintro ⟨-, h⟩
    rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero] at h
    exact hQ'eval (by exact_mod_cast (FaithfulSMul.algebraMap_injective ℚ ℂ) (by simpa using h))
  rw [haroots, hXm, Multiset.filter_add]
  rw [Multiset.filter_eq_nil.mpr (fun x hx => by
        rw [Multiset.eq_of_mem_replicate hx]; simp)]
  rw [zero_add,
    Multiset.filter_eq_self.mpr (by intro x hx hx0; subst hx0; exact hzero_notmem hx)]

end LeanFormalizations.Transcendence
