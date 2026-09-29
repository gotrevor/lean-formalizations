/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Edges out of Stephan's machine-checked Ridout theorem

`Literature.Stephan2026Ridout` is `Rat.finite_setOf_ridout` from R. Stephan's
`rwst/Subspace-Theorems` (Lean 4, sorry-free there, 2026), stated verbatim.  Deriving this repo's
paper-sourced Diophantine `Prop`s from it moves their foundation from "cited paper" to "proved in
Lean elsewhere, waiting on a toolchain match" (`PROBE-ROTH.md`).

Notation: `‖β‖_S₁ := ∏_{l ∈ S₁} |β.num|_l`, `‖β‖_S₂ := ∏_{l ∈ S₂} |β.den|_l`,
`H(β) := max(|β.num|, β.den)`.  Stephan: `{β | |ξ − β| ‖β‖_S₁ ‖β‖_S₂ ≤ H(β)^(−2−ε)}` is finite.

## `roth1955_of_stephan`
`S₁ = S₂ = ∅`, `ε = δ/2`.  If `|α − r| < r.den^(−2−δ)` then `|r| ≤ |α| + 1`, so
`H(r) ≤ (|α| + 1) r.den`, and `r.den^(−2−δ) ≤ H(r)^(−2−δ/2)` once `r.den` is large
(`(|α|+1)^(2+δ/2) ≤ r.den^(δ/2)`).  Rationals with bounded denominator near `α` are finitely many.

## `ridoutSUnitDen_of_stephan`
`S₁ = ∅`, `S₂ = S` (as `Nat.Primes`).  A denominator with all prime factors in `S` has
`∏_{l∈S} |q|_l = 1/q`.  So `|α − r| < q^(−1−δ)` gives `|α − r| · (1/q) < q^(−2−δ)`, then the same
`H ≤ (|α|+1) q` comparison with `ε = δ/2`.

## `mahler_mul_of_stephan` (hence `mahler1957_of_stephan`, `q = 1`)
Same statement as `Diophantine.mahler_mul_of_ridout1957`.  `α = u/v` lowest terms, `v ≥ 2`,
`p* = round(q αⁿ)`, `β = p* vⁿ / uⁿ` (reduce by `g = gcd(p* vⁿ, uⁿ) = gcd(p*, uⁿ)`), target
`ξ = q`, `S₁` = primes of `v`, `S₂` = primes of `u`.  Then `vⁿ ∣ β.num` so `‖β‖_S₁ ≤ v^(−n)`;
`β.den = uⁿ/g` is an `S₂`-unit so `‖β‖_S₂ = g/uⁿ`; `H(β) ≤ C uⁿ / g` (as `p* ≤ 2q αⁿ`).
If `|q αⁿ − p*| ≤ e^(−εn)` then `|q − β| = (v/u)ⁿ |q αⁿ − p*| ≤ (v/u)ⁿ e^(−εn)`, so the product is
`≤ g u^(−2n) e^(−εn) ≤ H(β)^(−2−ε')` with `ε' = ε / (2 log u)` for large `n` (`g ≥ 1`).  Distinct
large `n` give distinct `β` (`β.den · g = uⁿ`, and `β ≠ q` exactly as in the Ridout-1957 proof),
so finiteness of Stephan's set bounds `n`.  Check the `C` bookkeeping; `ε'` may need shrinking.

## `Mills.irrational_of_stephan`
`Mills.irrational hB hM (mahler1957_of_stephan hS)`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.Diophantine.Edges
import LeanFormalizations.NumberTheory.Mills.Irrational

namespace LeanFormalizations.Diophantine

open LeanFormalizations.Literature

/-! ### Bookkeeping for Stephan's `S`-adic factors -/

open Finset in
/-- A finite set of primes, as a `Finset Nat.Primes`. -/
private def toPrimes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Finset Nat.Primes :=
  S.attach.image (fun x => ⟨x.1, hS x.1 x.2⟩)

private lemma prod_toPrimes {M : Type*} [CommMonoid M] (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ℕ → M) : ∏ l ∈ toPrimes S hS, f (l : ℕ) = ∏ p ∈ S, f p := by
  rw [toPrimes, Finset.prod_image, Finset.prod_attach]
  intro a _ b _ hab
  have h2 : (a : ℕ) = (b : ℕ) := by
    have h3 := congrArg (fun x : Nat.Primes => (x : ℕ)) hab
    simpa using h3
  exact Subtype.ext h2

/-- `∏_{p ∈ primeFactors d} p ^ v_p(d) = d`, over `ℚ`. -/
private lemma prod_pow_factorization (d : ℕ) (hd : d ≠ 0) :
    ∏ p ∈ d.primeFactors, (p : ℚ) ^ (d.factorization p) = (d : ℚ) := by
  have := Nat.prod_factorization_pow_eq_self hd
  rw [Finsupp.prod] at this
  calc ∏ p ∈ d.primeFactors, (p : ℚ) ^ (d.factorization p)
      = ((∏ p ∈ d.primeFactors, p ^ (d.factorization p) : ℕ) : ℚ) := by push_cast; ring
    _ = (d : ℚ) := by rw [show (∏ p ∈ d.primeFactors, p ^ (d.factorization p)) = d from this]

/-- `∏_{p ∈ S} p ^ (−v_p(d)) = 1/d` whenever every prime factor of `d` lies in `S`. -/
private lemma prod_zpow_of_subset (d : ℕ) (hd : d ≠ 0) (S : Finset ℕ)
    (hsub : d.primeFactors ⊆ S) :
    ∏ p ∈ S, (p : ℚ) ^ (-(d.factorization p : ℤ)) = 1 / d := by
  have key : ∏ p ∈ S, (p : ℚ) ^ (d.factorization p) = (d : ℚ) := by
    rw [← prod_pow_factorization d hd]
    refine (Finset.prod_subset hsub ?_).symm
    intro x _ hx
    have : d.factorization x = 0 := by
      simpa using (Nat.factorization d).notMem_support_iff.mp (by simpa using hx)
    rw [this, pow_zero]
  have hz : ∀ p ∈ S, (p : ℚ) ^ (-(d.factorization p : ℤ))
      = ((p : ℚ) ^ (d.factorization p))⁻¹ := by
    intro p _
    rw [zpow_neg, zpow_natCast]
  rw [Finset.prod_congr rfl hz, Finset.prod_inv_distrib, key, one_div]

/-- The `S`-unit factor of Stephan's product: a natural number all of whose prime factors lie in
`S` has `∏_{p ∈ S} |d|_p = 1/d`. -/
private lemma prod_padicNorm_nat (d : ℕ) (hd : d ≠ 0) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hsub : d.primeFactors ⊆ S) : ∏ p ∈ S, padicNorm p (d : ℚ) = 1 / d := by
  rw [← prod_zpow_of_subset d hd S hsub]
  refine Finset.prod_congr rfl fun p hp => ?_
  haveI : Fact p.Prime := ⟨hSp p hp⟩
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hd : ((d : ℚ) ≠ 0)),
    padicValRat.of_nat, Nat.factorization_def d (hSp p hp)]

/-- Divisibility bound on the other factor: if `d ∣ m` and all prime factors of `d` lie in `S`,
then `∏_{p ∈ S} |m|_p ≤ 1/d`. -/
private lemma prod_padicNorm_int_le (m : ℤ) (d : ℕ) (hd : d ≠ 0) (S : Finset ℕ)
    (hSp : ∀ p ∈ S, p.Prime) (hsub : d.primeFactors ⊆ S) (hdvd : (d : ℤ) ∣ m) :
    ∏ p ∈ S, padicNorm p (m : ℚ) ≤ 1 / d := by
  rw [← prod_zpow_of_subset d hd S hsub]
  refine Finset.prod_le_prod (fun p _ => padicNorm.nonneg _) (fun p hp => ?_)
  haveI : Fact p.Prime := ⟨hSp p hp⟩
  refine padicNorm.dvd_iff_norm_le.mp ?_
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd d p)) hdvd

/-! ### Bounded-denominator finiteness (a copy of `Edges.lean`'s private bookkeeping) -/

private lemma rat_inj' : Function.Injective (fun r : ℚ => (r.num, r.den)) := by
  intro a b hab
  exact Rat.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

private lemma abs_num_eq' (r : ℚ) : |(r : ℝ)| * (r.den : ℝ) = |(r.num : ℝ)| := by
  have hd : (0:ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  rw [Rat.cast_def, abs_div, abs_of_pos hd]
  field_simp

private lemma finite_den_le' (D : ℕ) (B : ℝ) :
    {r : ℚ | r.den ≤ D ∧ |(r : ℝ)| ≤ B}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.preimage (f := fun r : ℚ => (r.num, r.den)) rat_inj'.injOn
      ((Set.finite_Icc (-⌈B * D⌉) ⌈B * D⌉).prod (Set.finite_Iic D))) ?_
  intro r hr
  obtain ⟨hd, hb⟩ := hr
  have hd0 : (0:ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hdD : (r.den : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb
  have h1 : |(r.num : ℝ)| ≤ B * D := by
    rw [← abs_num_eq' r]
    exact mul_le_mul hb hdD hd0.le hB0
  have h2 : |r.num| ≤ ⌈B * D⌉ := by
    have : (|r.num| : ℝ) ≤ B * D := by exact_mod_cast h1
    exact_mod_cast le_trans this (Int.le_ceil _)
  exact ⟨⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩, hd⟩

/-- The height comparison shared by the Roth and Ridout edges: once the denominator exceeds a
threshold depending only on `α` and `δ`, `q^(−2−δ)` is below `H(r)^(−2−δ/2)`. -/
private lemma exists_height_threshold (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℕ, ∀ r : ℚ, D < r.den → |(r : ℝ)| ≤ |α| + 1 →
      (1:ℝ) / (r.den : ℝ) ^ (2 + δ) ≤ (max r.num.natAbs r.den : ℝ) ^ (-2 - δ / 2) := by
  have hα1 : (0:ℝ) < |α| + 1 := by positivity
  obtain ⟨κ, hκ_def⟩ : ∃ x : ℝ, x = 2 + δ / 2 := ⟨_, rfl⟩
  have hκ0 : (0:ℝ) < κ := by rw [hκ_def]; linarith
  obtain ⟨C, hC_def⟩ : ∃ x : ℝ, x = (|α| + 1) ^ κ := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC_def]; positivity
  refine ⟨⌈C ^ (2 / δ)⌉₊, fun r hbig hrB => ?_⟩
  have hd1 : (1:ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hd0 : (0:ℝ) < (r.den : ℝ) := by linarith
  have hCq : C ≤ (r.den : ℝ) ^ (δ / 2) := by
    have hDle : (C : ℝ) ^ (2 / δ) ≤ ((⌈C ^ (2 / δ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hdD : ((⌈C ^ (2 / δ)⌉₊ : ℕ) : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast hbig.le
    have h1 : (C ^ (2 / δ)) ^ (δ / 2) ≤ ((r.den : ℝ)) ^ (δ / 2) :=
      Real.rpow_le_rpow (by positivity) (le_trans hDle hdD) (by positivity)
    have hexp : (2 / δ) * (δ / 2) = 1 := by field_simp
    rwa [← Real.rpow_mul hC0.le, hexp, Real.rpow_one] at h1
  set M : ℝ := (max r.num.natAbs r.den : ℝ) with hM_def
  have hM0 : (0:ℝ) < M := by
    have : (r.den : ℝ) ≤ M := by rw [hM_def]; exact le_max_right _ _
    linarith
  have hM : M ≤ (|α| + 1) * (r.den : ℝ) := by
    have h1 : ((r.num.natAbs : ℕ) : ℝ) ≤ (|α| + 1) * (r.den : ℝ) := by
      have hna : ((r.num.natAbs : ℕ) : ℝ) = |(r.num : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [hna, ← abs_num_eq' r]
      exact mul_le_mul_of_nonneg_right hrB hd0.le
    have h2 : (r.den : ℝ) ≤ (|α| + 1) * (r.den : ℝ) := by nlinarith [abs_nonneg α]
    rw [hM_def]
    exact max_le h1 h2
  have hkey : ((|α| + 1) * (r.den : ℝ)) ^ κ ≤ (r.den : ℝ) ^ (2 + δ) := by
    rw [Real.mul_rpow hα1.le hd0.le, ← hC_def]
    have hsp : (r.den : ℝ) ^ (2 + δ) = (r.den : ℝ) ^ (δ / 2) * (r.den : ℝ) ^ κ := by
      rw [← Real.rpow_add hd0, hκ_def]; ring_nf
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hCq (by positivity)
  have hMκ : M ^ κ ≤ (r.den : ℝ) ^ (2 + δ) :=
    le_trans (Real.rpow_le_rpow hM0.le hM hκ0.le) hkey
  have hneg : (-2 - δ / 2 : ℝ) = -κ := by rw [hκ_def]; ring
  rw [hneg, Real.rpow_neg hM0.le, one_div]
  exact inv_anti₀ (Real.rpow_pos_of_pos hM0 κ) hMκ

/-! ### The edges -/

/-- Stephan's Ridout ⇒ Thue–Siegel–Roth.  Take `S₁ = S₂ = ∅`, so both `S`-adic factors are the
empty product `1`, and `ε = δ/2`; `exists_height_threshold` converts `q^(−2−δ)` into
`H(r)^(−2−δ/2)` for all large denominators, and `finite_den_le'` absorbs the rest. -/
theorem roth1955_of_stephan (h : Stephan2026Ridout) : Roth1955 := by
  intro α halg hirr δ hδ
  have hfin := h halg ∅ ∅ (show (0:ℝ) < δ / 2 by linarith)
  obtain ⟨D, hD⟩ := exists_height_threshold α hδ
  refine Set.Finite.subset ((finite_den_le' D (|α| + 1)).union hfin) ?_
  intro r hr
  have hlt : |α - (r:ℝ)| < 1 / (r.den : ℝ) ^ (2 + δ) := hr
  have hd1 : (1:ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hpow1 : (1:ℝ) ≤ (r.den : ℝ) ^ (2 + δ) := Real.one_le_rpow hd1 (by linarith)
  have hlt1 : |α - (r:ℝ)| < 1 := by
    refine lt_of_lt_of_le hlt ?_
    rw [div_le_one (by linarith)]; exact hpow1
  have hrB : |(r:ℝ)| ≤ |α| + 1 := by
    have := abs_sub_abs_le_abs_sub (r:ℝ) α
    rw [abs_sub_comm (r:ℝ) α] at this
    linarith [abs_nonneg ((r:ℝ) - α)]
  rcases le_or_gt r.den D with hsmall | hbig
  · exact Or.inl ⟨hsmall, hrB⟩
  · refine Or.inr ?_
    simp only [Set.mem_setOf_eq, Finset.prod_empty, mul_one]
    exact le_trans hlt.le (hD r hbig hrB)

/-- Stephan's Ridout ⇒ Ridout's `S`-unit-denominator corollary.  `S₁ = ∅`, `S₂ = S`; a
denominator whose prime factors all lie in `S` contributes exactly `1/q`, upgrading
`|α − r| < q^(−1−δ)` to `|α − r| · q^(−1) < q^(−2−δ)`. -/
theorem ridoutSUnitDen_of_stephan (h : Stephan2026Ridout) : Ridout1957SUnitDen := by
  intro α halg hirr S hS δ hδ
  have hfin := h halg ∅ (toPrimes S hS) (show (0:ℝ) < δ / 2 by linarith)
  obtain ⟨D, hD⟩ := exists_height_threshold α hδ
  refine Set.Finite.subset ((finite_den_le' D (|α| + 1)).union hfin) ?_
  intro r hr
  obtain ⟨hSr, hlt⟩ := hr
  have hd1 : (1:ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hd0 : (0:ℝ) < (r.den : ℝ) := by linarith
  have hpow1 : (1:ℝ) ≤ (r.den : ℝ) ^ (1 + δ) := Real.one_le_rpow hd1 (by linarith)
  have hlt1 : |α - (r:ℝ)| < 1 := by
    refine lt_of_lt_of_le hlt ?_
    rw [div_le_one (by linarith)]; exact hpow1
  have hrB : |(r:ℝ)| ≤ |α| + 1 := by
    have := abs_sub_abs_le_abs_sub (r:ℝ) α
    rw [abs_sub_comm (r:ℝ) α] at this
    linarith [abs_nonneg ((r:ℝ) - α)]
  rcases le_or_gt r.den D with hsmall | hbig
  · exact Or.inl ⟨hsmall, hrB⟩
  · refine Or.inr ?_
    have hsunit : (∏ l ∈ toPrimes S hS, ((padicNorm (l : ℕ) r.den : ℚ) : ℝ))
        = 1 / (r.den : ℝ) := by
      have hp1 := prod_toPrimes S hS (fun p : ℕ => ((padicNorm p (r.den : ℚ) : ℚ) : ℝ))
      rw [hp1, ← Rat.cast_prod, prod_padicNorm_nat r.den r.den_nz S hS hSr]
      push_cast
      ring
    simp only [Set.mem_setOf_eq, Finset.prod_empty, mul_one]
    rw [hsunit]
    refine le_trans (le_of_lt ?_) (hD r hbig hrB)
    have hstep : |α - (r:ℝ)| * (1 / (r.den : ℝ)) < 1 / (r.den : ℝ) ^ (1 + δ) * (1 / (r.den : ℝ)) :=
      by exact mul_lt_mul_of_pos_right hlt (by positivity)
    refine lt_of_lt_of_le hstep (le_of_eq ?_)
    have hsplit : (r.den : ℝ) ^ (2 + δ) = (r.den : ℝ) ^ (1 + δ) * (r.den : ℝ) := by
      have hh := Real.rpow_add hd0 (1 + δ) 1
      rw [Real.rpow_one] at hh
      rw [show (2 + δ : ℝ) = 1 + δ + 1 by ring, hh]
    rw [hsplit]
    field_simp

set_option maxHeartbeats 1000000 in
/-- Stephan's Ridout ⇒ Mahler (1957) with a factor `q`, the form Dubickas uses.  Same statement
as `mahler_mul_of_ridout1957`.

With `α = u/v` in lowest terms (`2 ≤ v < u`), `P = round(q αⁿ)` and `β = P vⁿ / uⁿ ∈ ℚ`, the
lowest-terms data of `β` satisfies `vⁿ ∣ β.num`, `β.den ∣ uⁿ` and `β.num ≤ 2q β.den`.  Hence, with
`ξ = q`, `S₁` the primes of `v` and `S₂` the primes of `u`,
`‖β‖_{S₁} ≤ v^(−n)`, `‖β‖_{S₂} = 1/β.den`, `H(β) ≤ 2q β.den`,
and `|q − β| = (v/u)ⁿ |q αⁿ − P|`.  A bad `n` therefore puts `β` into Stephan's finite set with
`ε' = ε/(2 log u)`, the only extra input being `β.den ≤ uⁿ`.  Every such `β` is `≠ q` (else
`vⁿ ∣ q`) while `|q − β| ≤ (v/u)ⁿ → 0`; a finite set of rationals `≠ q` stays a fixed distance
from `q`, so only finitely many `n` are bad. -/
theorem mahler_mul_of_stephan (h : Stephan2026Ridout) (q : ℕ) (hq : 0 < q) (α : ℚ)
    (hα1 : 1 < α) (hden : α.den ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * n)) < |(q : ℝ) * (α : ℝ) ^ n - round ((q : ℝ) * (α : ℝ) ^ n)| := by
  classical
  have hden0 : 0 < α.den := α.pos
  have hv2 : 2 ≤ α.den := by omega
  have hαR : (1:ℝ) < (α:ℝ) := by exact_mod_cast hα1
  have hnumpos : 0 < α.num := Rat.num_pos.mpr (lt_trans zero_lt_one hα1)
  set v : ℕ := α.den with hv_def
  set u : ℕ := α.num.natAbs with hu_def
  have hu : (u : ℤ) = α.num := Int.natAbs_of_nonneg hnumpos.le
  have hV0 : (0:ℝ) < (v:ℝ) := by exact_mod_cast hden0
  have hαuv : (α:ℝ) = (u:ℝ) / (v:ℝ) := by
    rw [Rat.cast_def]; congr 1; exact_mod_cast hu.symm
  have hUV : (v:ℝ) < (u:ℝ) := by rw [hαuv] at hαR; exact (one_lt_div hV0).mp hαR
  have hu2 : 2 ≤ u := by
    have h1 : (2:ℝ) ≤ (v:ℝ) := by exact_mod_cast hv2
    have h3 : (2:ℕ) < u := by exact_mod_cast lt_of_le_of_lt h1 hUV
    omega
  have hcop : Nat.Coprime u v := α.reduced
  have hU0 : (0:ℝ) < (u:ℝ) := by positivity
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  obtain ⟨lu, hlu_def⟩ : ∃ x : ℝ, x = Real.log u := ⟨_, rfl⟩
  have hlu : 0 < lu := by rw [hlu_def]; exact Real.log_pos (by exact_mod_cast hu2)
  obtain ⟨e', he'_def⟩ : ∃ x : ℝ, x = ε / (2 * lu) := ⟨_, rfl⟩
  have he'0 : 0 < e' := by rw [he'_def]; positivity
  obtain ⟨C, hC_def⟩ : ∃ x : ℝ, x = 2 * (q:ℝ) := ⟨_, rfl⟩
  have hC1 : (1:ℝ) < C := by rw [hC_def]; linarith
  have hC0 : (0:ℝ) < C := by linarith
  have hvS : ∀ p ∈ v.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have huS : ∀ p ∈ u.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfin := h (ξ := (q:ℝ)) (isAlgebraic_nat q)
    (toPrimes v.primeFactors hvS) (toPrimes u.primeFactors huS) he'0
  -- a positive gap between `q` and the members of that finite set other than `q`
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ hfin.toFinset, x ≠ (q:ℚ) →
      m ≤ |(q:ℝ) - (x:ℝ)| := by
    set G := (hfin.toFinset.erase (q:ℚ)).image (fun x : ℚ => |(q:ℝ) - (x:ℝ)|) with hG_def
    rcases G.eq_empty_or_nonempty with hG | hG
    · refine ⟨1, one_pos, fun x hx hxq => absurd hG ?_⟩
      refine Finset.nonempty_iff_ne_empty.mp ⟨|(q:ℝ) - (x:ℝ)|, ?_⟩
      exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hxq, hx⟩)
    · refine ⟨G.min' hG, ?_, fun x hx hxq => ?_⟩
      · obtain ⟨y, hy, hy2⟩ := Finset.mem_image.mp (G.min'_mem hG)
        obtain ⟨hyq, -⟩ := Finset.mem_erase.mp hy
        rw [← hy2, abs_pos, sub_ne_zero]
        exact fun hc => hyq (by exact_mod_cast hc.symm)
      · exact G.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hxq, hx⟩))
  -- `(v/u)ⁿ < m` for large `n`
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ n ≥ n₁, ((v:ℝ) / (u:ℝ)) ^ n < m := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hm0 ((div_lt_one hU0).mpr hUV)
    refine ⟨k, fun n hn => lt_of_le_of_lt ?_ hk⟩
    exact pow_le_pow_of_le_one (by positivity) ((div_le_one hU0).mpr hUV.le) hn
  -- `C ^ (2 + ε') ≤ exp (n ε / 2)` for large `n`
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, ∀ n ≥ n₂, C ^ (2 + e') ≤ Real.exp ((n:ℝ) * ε / 2) := by
    refine ⟨⌈(2 / ε) * Real.log (C ^ (2 + e'))⌉₊, fun n hn => ?_⟩
    have hK0 : (0:ℝ) < C ^ (2 + e') := Real.rpow_pos_of_pos hC0 _
    have h1 : (2 / ε) * Real.log (C ^ (2 + e')) ≤ (n:ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : Real.log (C ^ (2 + e')) ≤ (n:ℝ) * ε / 2 := by
      have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt (half_pos hε))
      calc Real.log (C ^ (2 + e'))
          = ((2 / ε) * Real.log (C ^ (2 + e'))) * (ε / 2) := by field_simp
        _ ≤ (n:ℝ) * (ε / 2) := h3
        _ = (n:ℝ) * ε / 2 := by ring
    calc C ^ (2 + e') = Real.exp (Real.log (C ^ (2 + e'))) := (Real.exp_log hK0).symm
      _ ≤ _ := Real.exp_le_exp.mpr h2
  refine ⟨max (max n₁ n₂) (q + 1), fun n hn => ?_⟩
  have hnn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnq : q + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n ≠ 0 := by omega
  by_contra hcon
  push_neg at hcon
  -- ### the rational `β = P vⁿ / uⁿ`
  obtain ⟨A, hA_def⟩ : ∃ x : ℝ, x = (q:ℝ) * (α:ℝ) ^ n := ⟨_, rfl⟩
  have hpow1 : 1 < (α:ℝ) ^ n := one_lt_pow₀ hαR hn0
  have hA1 : 1 < A := by rw [hA_def]; nlinarith
  have hA0 : 0 < A := by linarith
  have hAeq : A = (q:ℝ) * ((u:ℝ) ^ n / (v:ℝ) ^ n) := by rw [hA_def, hαuv, div_pow]
  have habs' := abs_le.mp (abs_sub_round A)
  have hrge : (1:ℤ) ≤ round A := by
    by_contra hc
    push_neg at hc
    have h0 : ((round A : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : round A ≤ 0)
    linarith [habs'.2]
  obtain ⟨P, hP_def⟩ : ∃ x : ℕ, x = (round A).toNat := ⟨_, rfl⟩
  have hPz : ((P : ℤ)) = round A := by rw [hP_def]; exact Int.toNat_of_nonneg (by omega)
  have hPR : (P : ℝ) = ((round A : ℤ) : ℝ) := by exact_mod_cast hPz
  have hP1 : (1:ℝ) ≤ (P:ℝ) := by rw [hPR]; exact_mod_cast hrge
  have hP0 : 0 < P := by exact_mod_cast lt_of_lt_of_le zero_lt_one hP1
  have hP2A : (P:ℝ) ≤ 2 * A := by rw [hPR]; linarith [habs'.2]
  have hnd : |A - (P:ℝ)| ≤ Real.exp (-(ε * n)) := by rw [hPR, hA_def]; exact hcon
  obtain ⟨N, hN_def⟩ : ∃ x : ℕ, x = P * v ^ n := ⟨_, rfl⟩
  obtain ⟨U, hU_def⟩ : ∃ x : ℕ, x = u ^ n := ⟨_, rfl⟩
  have hUpos : 0 < U := by rw [hU_def]; exact pow_pos (by omega) n
  have hNpos : 0 < N := by rw [hN_def]; exact Nat.mul_pos hP0 (pow_pos hden0 n)
  obtain ⟨β, hβ_def⟩ : ∃ x : ℚ, x = (N : ℚ) / (U : ℚ) := ⟨_, rfl⟩
  have hNQ : (0:ℚ) < (N:ℚ) := by exact_mod_cast hNpos
  have hUQ : (0:ℚ) < (U:ℚ) := by exact_mod_cast hUpos
  have hβpos : 0 < β := by rw [hβ_def]; positivity
  have hcross : β.num * (U : ℤ) = (N : ℤ) * (β.den : ℤ) := by
    have h1 : (β.num : ℚ) / (β.den : ℚ) = (N : ℚ) / (U : ℚ) := by rw [Rat.num_div_den, hβ_def]
    have hd0 : ((β.den : ℚ)) ≠ 0 := by exact_mod_cast β.den_nz
    rw [div_eq_div_iff hd0 hUQ.ne'] at h1
    exact_mod_cast h1
  have hβnum0 : 0 < β.num := Rat.num_pos.mpr hβpos
  -- `β.den ∣ uⁿ`
  have hdenU : (β.den : ℤ) ∣ (U : ℤ) := by
    have h1 : (β.den : ℤ) ∣ β.num * (U : ℤ) := by rw [hcross]; exact ⟨(N:ℤ), by ring⟩
    refine IsCoprime.dvd_of_dvd_mul_left ?_ h1
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using β.reduced
  have hdenUnat : β.den ∣ U := by exact_mod_cast hdenU
  -- `vⁿ ∣ β.num`
  have hvnum : ((v:ℤ) ^ n) ∣ β.num := by
    have hNv : ((N:ℤ)) = (P:ℤ) * (v:ℤ) ^ n := by rw [hN_def]; push_cast; ring
    have hdvd : ((v:ℤ) ^ n) ∣ β.num * (U : ℤ) := by
      rw [hcross, hNv]; exact ⟨(P:ℤ) * (β.den : ℤ), by ring⟩
    refine IsCoprime.dvd_of_dvd_mul_right ?_ hdvd
    have hcopz : IsCoprime ((v:ℤ)) ((u:ℤ)) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd, Nat.Coprime] using hcop.symm
    rw [hU_def]
    push_cast
    exact IsCoprime.pow hcopz
  -- `β.num ≤ 2q β.den`
  have hUR' : ((U:ℝ)) = (u:ℝ) ^ n := by rw [hU_def]; push_cast; ring
  have hPvn : (P : ℝ) * (v:ℝ) ^ n ≤ C * (u:ℝ) ^ n := by
    have h0 := mul_le_mul_of_nonneg_right hP2A (show (0:ℝ) ≤ (v:ℝ) ^ n by positivity)
    rw [hAeq] at h0
    rw [hC_def]
    calc (P : ℝ) * (v:ℝ) ^ n ≤ 2 * ((q:ℝ) * ((u:ℝ) ^ n / (v:ℝ) ^ n)) * (v:ℝ) ^ n := h0
      _ = 2 * (q:ℝ) * (u:ℝ) ^ n := by field_simp
  have hnumC : (β.num : ℝ) ≤ C * (β.den : ℝ) := by
    have h1 : (β.num : ℝ) * (U : ℝ) = (N : ℝ) * (β.den : ℝ) := by exact_mod_cast hcross
    have hURpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast hUpos
    have hNR : (N : ℝ) = (P:ℝ) * (v:ℝ) ^ n := by rw [hN_def]; push_cast; ring
    rw [hNR] at h1
    refine le_of_mul_le_mul_right ?_ hURpos
    calc (β.num : ℝ) * (U:ℝ) = (P:ℝ) * (v:ℝ) ^ n * (β.den:ℝ) := h1
      _ ≤ C * (u:ℝ) ^ n * (β.den : ℝ) :=
          mul_le_mul_of_nonneg_right hPvn (by positivity)
      _ = C * (β.den : ℝ) * (U:ℝ) := by rw [hUR']; ring
  -- ### `β ≠ q`
  have hqv : q < v ^ n := by
    calc q < 2 ^ q := Nat.lt_two_pow_self
      _ ≤ v ^ q := Nat.pow_le_pow_left hv2 q
      _ ≤ v ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hβq : β ≠ (q:ℚ) := by
    intro hc
    rw [hβ_def, div_eq_iff hUQ.ne'] at hc
    have h2 : N = q * U := by exact_mod_cast hc
    have hdvd : v ^ n ∣ q * U := ⟨P, by rw [← h2, hN_def]; ring⟩
    rw [hU_def] at hdvd
    have hfin2 := Nat.le_of_dvd hq
      (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow n n hcop.symm) hdvd)
    omega
  -- ### the three factors of Stephan's product
  have hS₁ : (∏ l ∈ toPrimes v.primeFactors hvS, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
      ≤ 1 / (v:ℝ) ^ n := by
    rw [prod_toPrimes v.primeFactors hvS (fun p : ℕ => ((padicNorm p (β.num : ℚ) : ℚ) : ℝ)),
      ← Rat.cast_prod]
    have hle := prod_padicNorm_int_le β.num (v ^ n) (by positivity) v.primeFactors hvS
      (by rw [Nat.primeFactors_pow _ hn0]) (by exact_mod_cast hvnum)
    have hle' : ((∏ p ∈ v.primeFactors, padicNorm p (β.num : ℚ) : ℚ) : ℝ)
        ≤ ((1 / (v ^ n : ℕ) : ℚ) : ℝ) := by exact_mod_cast hle
    refine le_trans hle' (le_of_eq ?_)
    push_cast
    ring
  have hS₂ : (∏ l ∈ toPrimes u.primeFactors huS, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ))
      = 1 / (β.den : ℝ) := by
    rw [prod_toPrimes u.primeFactors huS (fun p : ℕ => ((padicNorm p (β.den : ℚ) : ℚ) : ℝ)),
      ← Rat.cast_prod,
      prod_padicNorm_nat β.den β.den_nz u.primeFactors huS
        (by
          refine subset_trans (Nat.primeFactors_mono hdenUnat hUpos.ne') ?_
          rw [hU_def, Nat.primeFactors_pow _ hn0])]
    push_cast
    ring
  have hβR : (β:ℝ) = (P:ℝ) * (v:ℝ) ^ n / (u:ℝ) ^ n := by
    rw [hβ_def]
    push_cast [hN_def, hU_def]
    ring
  have hdist : |(q:ℝ) - (β:ℝ)| ≤ ((v:ℝ) / (u:ℝ)) ^ n * Real.exp (-(ε * n)) := by
    have hsplit : (q:ℝ) - (β:ℝ) = ((v:ℝ) ^ n / (u:ℝ) ^ n) * (A - (P:ℝ)) := by
      rw [hβR, hAeq]; field_simp; try ring
    rw [hsplit, abs_mul, abs_of_pos (by positivity), div_pow]
    exact mul_le_mul_of_nonneg_left hnd (by positivity)
  -- ### `β` lies in Stephan's set
  have hdR1 : (1:ℝ) ≤ (β.den : ℝ) := by exact_mod_cast β.pos
  have hdR0 : (0:ℝ) < (β.den : ℝ) := by linarith
  have hdU : (β.den : ℝ) ≤ (u:ℝ) ^ n := by
    have h1 : (β.den : ℝ) ≤ (U : ℝ) := by exact_mod_cast Nat.le_of_dvd hUpos hdenUnat
    rwa [hUR'] at h1
  have hnumabs : ((β.num.natAbs : ℕ) : ℝ) = (β.num : ℝ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    exact abs_of_pos (by exact_mod_cast hβnum0)
  have hH1 : (1:ℝ) ≤ max ((β.num.natAbs : ℕ) : ℝ) ((β.den : ℕ) : ℝ) :=
    le_trans hdR1 (le_max_right _ _)
  have hH0 : (0:ℝ) < max ((β.num.natAbs : ℕ) : ℝ) ((β.den : ℕ) : ℝ) := by linarith
  have hHC : max ((β.num.natAbs : ℕ) : ℝ) ((β.den : ℕ) : ℝ) ≤ C * (β.den : ℝ) := by
    refine max_le ?_ ?_
    · rw [hnumabs]; exact hnumC
    · nlinarith
  have hmem : β ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    rw [hS₂]
    have hQ1nn : (0:ℝ) ≤ ∏ l ∈ toPrimes v.primeFactors hvS,
        ((padicNorm (l : ℕ) β.num : ℚ) : ℝ) :=
      Finset.prod_nonneg (fun l _ => by
        exact_mod_cast (padicNorm.nonneg (p := (l:ℕ)) ((β.num : ℚ))))
    have h1 := mul_le_mul hdist hS₁ hQ1nn (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 1 / (β.den:ℝ) by positivity)
    refine le_trans h2 ?_
    have hEq : ((v:ℝ) / (u:ℝ)) ^ n * Real.exp (-(ε * n)) * (1 / (v:ℝ) ^ n) * (1/(β.den:ℝ))
        = Real.exp (-(ε * n)) / ((u:ℝ) ^ n * (β.den : ℝ)) := by
      rw [div_pow]; field_simp; try ring
    rw [hEq]
    -- compare with `H(β) ^ (−2 − ε')`
    have hneg : (-2 - e' : ℝ) = -(2 + e') := by ring
    have hstep1 : (C * (β.den:ℝ)) ^ (-(2 + e'))
        ≤ (max ((β.num.natAbs : ℕ) : ℝ) ((β.den : ℕ) : ℝ)) ^ (-(2 + e')) :=
      Real.rpow_le_rpow_of_nonpos hH0 hHC (by linarith)
    rw [hneg]
    refine le_trans ?_ hstep1
    rw [Real.rpow_neg (by positivity), ← one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hexp : (C * (β.den:ℝ)) ^ (2 + e')
        = C ^ (2 + e') * ((β.den:ℝ) * (β.den:ℝ)) * (β.den:ℝ) ^ e' := by
      rw [Real.mul_rpow hC0.le hdR0.le, Real.rpow_add hdR0]
      have h2 : (β.den:ℝ) ^ (2:ℝ) = (β.den:ℝ) * (β.den:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [h2]; ring
    have hde' : (β.den:ℝ) ^ e' ≤ Real.exp ((n:ℝ) * ε / 2) := by
      refine le_trans (Real.rpow_le_rpow hdR0.le hdU he'0.le) (le_of_eq ?_)
      rw [← Real.rpow_natCast (u:ℝ) n, ← Real.rpow_mul hU0.le, Real.rpow_def_of_pos hU0,
        ← hlu_def]
      congr 1
      rw [he'_def]
      field_simp
      try ring
    have hK := hn₂ n hnn₂
    have hEpos : (0:ℝ) < Real.exp (-(ε * n)) := Real.exp_pos _
    have hkey : Real.exp (-(ε * n)) * (C ^ (2 + e') * Real.exp ((n:ℝ) * ε / 2)) ≤ 1 := by
      have h1 : Real.exp (-(ε * n)) * Real.exp ((n:ℝ) * ε / 2)
          = Real.exp (-((n:ℝ) * ε / 2)) := by rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-(ε * n)) * (C ^ (2 + e') * Real.exp ((n:ℝ) * ε / 2))
          = (Real.exp (-(ε * n)) * Real.exp ((n:ℝ) * ε / 2)) * C ^ (2 + e') := by ring
        _ = Real.exp (-((n:ℝ) * ε / 2)) * C ^ (2 + e') := by rw [h1]
        _ ≤ Real.exp (-((n:ℝ) * ε / 2)) * Real.exp ((n:ℝ) * ε / 2) :=
            mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [hexp]
    calc Real.exp (-(ε * n)) * (C ^ (2 + e') * ((β.den:ℝ) * (β.den:ℝ)) * (β.den:ℝ) ^ e')
        ≤ Real.exp (-(ε * n)) * (C ^ (2 + e') * ((β.den:ℝ) * (β.den:ℝ))
            * Real.exp ((n:ℝ) * ε / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hde' (by positivity)) hEpos.le
      _ = (Real.exp (-(ε * n)) * (C ^ (2 + e') * Real.exp ((n:ℝ) * ε / 2)))
            * ((β.den:ℝ) * (β.den:ℝ)) := by ring
      _ ≤ 1 * ((β.den:ℝ) * (β.den:ℝ)) := mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (β.den:ℝ) * (β.den:ℝ) := by ring
      _ ≤ (u:ℝ) ^ n * (β.den:ℝ) := mul_le_mul_of_nonneg_right hdU (by positivity)
  -- ### the contradiction
  have hgap := hm β hmem hβq
  have hE1 : Real.exp (-(ε * n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have hsmall : |(q:ℝ) - (β:ℝ)| < m := by
    refine lt_of_le_of_lt hdist (lt_of_le_of_lt ?_ (hn₁ n hnn₁))
    calc ((v:ℝ) / (u:ℝ)) ^ n * Real.exp (-(ε * n))
        ≤ ((v:ℝ) / (u:ℝ)) ^ n * 1 := mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = ((v:ℝ) / (u:ℝ)) ^ n := by ring
  linarith

/-- Stephan's Ridout ⇒ Mahler (1957): the `q = 1` case of `mahler_mul_of_stephan`. -/
theorem mahler1957_of_stephan (h : Stephan2026Ridout) : Mahler1957 := by
  intro α hα1 hden ε hε
  obtain ⟨n₀, hn₀⟩ := mahler_mul_of_stephan h 1 one_pos α hα1 hden ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  have := hn₀ n hn
  simpa using this

end LeanFormalizations.Diophantine

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **Mills' constant is irrational, on Baker–Harman–Pintz, Matomäki and a machine-checked
Ridout.**  Same statement as `irrational`, with `Mahler1957` replaced by `Stephan2026Ridout`. -/
theorem irrational_of_stephan (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hS : Stephan2026Ridout) {A : ℝ} (hA : IsMinMills A) : Irrational A :=
  irrational hB hM (Diophantine.mahler1957_of_stephan hS) hA

end LeanFormalizations.Mills
