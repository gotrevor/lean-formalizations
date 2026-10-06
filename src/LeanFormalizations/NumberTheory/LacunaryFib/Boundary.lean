/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.LacunaryFib.Basic

/-!
# Lacunary Fibonacci sums at the ratio-two boundary (phase LF1)

The map, from what is known to what is open:

* ratio `≥ c > 2`: transcendental (`Nguyen2022`, cited);
* eventually exact doubling: algebraic (`algebraic_of_eventually_doubling`, from Millin);
* `n_k = 2^(e_k)` with gaps `e_(k+1) ≥ e_k + 2`: ratio `≥ 4`, transcendental
  (`restricted_transcendental_of_sparse`, wiring from Nguyen);
* `K` eventually periodic, infinite and coinfinite: believed known by Mahler's method
  (`MahlerPeriodicRestricted`, frozen).  Node D shows the support series is not rational;
* **open: the ratio-two crux** `RatioTwoRigidity`, and its restricted shadow `RestrictedRigidity`
  (any infinite coinfinite `K`, e.g. Sturmian);
* below `c = 2`: `LacunaryFibAlgebraicIffDoubling` (my conjecture, ~55%).
-/

namespace LeanFormalizations.LacunaryFib

open Filter Real

/-- **Nguyen 2022, Theorem 1.2 (Fibonacci case, so weaker than the source).**  If `c > 2` and
`n (k + 1) ≥ c · n k` for positive `n`, then `∑ 1/F_(n_k)` is transcendental.  The source allows each
term to be `F_(n_k)` or `L_(n_k)`; this is the all-Fibonacci choice.  `c > 2` is sharp (`millin`).

K. D. Nguyen, *Transcendental series of reciprocals of Fibonacci and Lucas numbers*, Algebra &
Number Theory 16 (2022), DOI 10.2140/ant.2022.16.1627; arXiv:2009.02446, Theorem 1.2. -/
def Nguyen2022 : Prop :=
  ∀ c : ℝ, 2 < c → ∀ n : ℕ → ℕ, (∀ k, 0 < n k) → StrictMono n →
    (∀ k, c * (n k : ℝ) ≤ n (k + 1)) → Transcendental ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹)

/-- A finite sum of reciprocals of naturals is algebraic. -/
theorem isAlgebraic_finset_sum_inv (s : Finset ℕ) (f : ℕ → ℕ) :
    IsAlgebraic ℚ (∑ i ∈ s, ((f i : ℝ))⁻¹) := by
  have : (∑ i ∈ s, ((f i : ℝ))⁻¹) = algebraMap ℚ ℝ (∑ i ∈ s, ((f i : ℚ))⁻¹) := by
    simp
  rw [this]; exact isAlgebraic_algebraMap _

/-- Transcendence of a tail transfers to the whole series (the head is rational). -/
theorem transcendental_of_tail (n : ℕ → ℕ) (N : ℕ)
    (ht : Transcendental ℚ (∑' k, ((Nat.fib (n (k + N)) : ℝ))⁻¹)) :
    Transcendental ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) := by
  have hs : Summable (fun k => ((Nat.fib (n (k + N)) : ℝ))⁻¹) := by
    by_contra h; rw [tsum_eq_zero_of_not_summable h] at ht; exact ht isAlgebraic_zero
  rw [← ((summable_nat_add_iff (f := fun k => ((Nat.fib (n k) : ℝ))⁻¹) N).1 hs).sum_add_tsum_nat_add N]
  intro hx
  apply ht
  have := hx.sub (isAlgebraic_finset_sum_inv (Finset.range N) (fun i => Nat.fib (n i)))
  rwa [add_sub_cancel_left] at this

/-- **Wiring (~95%): eventual doubling is algebraic.**  The tail from some `K₀` is `a·2^k` with
`a = n K₀`: one term `1/F_a` plus `doubling_tail_algebraic a`, and the finite head is rational. -/
theorem algebraic_of_eventually_doubling (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (hdbl : ∀ᶠ k in atTop, n (k + 1) = 2 * n k) :
    IsAlgebraic ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) := by
  obtain ⟨K₀, hK⟩ := eventually_atTop.1 hdbl
  by_cases hs : Summable (fun k => ((Nat.fib (n k) : ℝ))⁻¹)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]; exact isAlgebraic_zero
  have htail : ∀ k, n (k + (K₀ + 1)) = n K₀ * 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero => rw [zero_add, hK K₀ le_rfl]; ring
    | succ k ih =>
      rw [show k + 1 + (K₀ + 1) = (k + (K₀ + 1)) + 1 by ring, hK _ (by omega), ih]; ring
  rw [← hs.sum_add_tsum_nat_add (K₀ + 1)]
  simp_rw [htail]
  exact (isAlgebraic_finset_sum_inv _ (fun i => Nat.fib (n i))).add
    (doubling_tail_algebraic _ (hpos K₀))

/-- **Wiring (~95%): Nguyen holds eventually.**  Dropping finitely many terms changes the sum by
a rational, and transcendence survives a rational shift. -/
theorem transcendental_of_eventually_ratio (hN : Nguyen2022) {c : ℝ} (hc : 2 < c) (n : ℕ → ℕ)
    (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hrat : ∀ᶠ k in atTop, c * (n k : ℝ) ≤ n (k + 1)) :
    Transcendental ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) := by
  obtain ⟨N, hN'⟩ := eventually_atTop.1 hrat
  apply transcendental_of_tail n N
  refine hN c hc (fun k => n (k + N)) (fun k => hpos _) (hmono.comp (add_left_strictMono)) ?_
  intro k
  have := hN' (k + N) (by omega)
  simpa [show k + 1 + N = k + N + 1 by ring] using this

/-- **Wiring (~98%): sparse powers of two.**  Gaps `≥ 2` in the exponents give ratio `≥ 4`, so
`Nguyen2022` with `c = 3` applies. -/
theorem restricted_transcendental_of_sparse (hN : Nguyen2022) (e : ℕ → ℕ)
    (hgap : ∀ k, e k + 2 ≤ e (k + 1)) :
    Transcendental ℚ (∑' k, ((Nat.fib (2 ^ e k) : ℝ))⁻¹) := by
  have hmono : StrictMono e := strictMono_nat_of_lt_succ fun k => by have := hgap k; omega
  refine hN 3 (by norm_num) (fun k => 2 ^ e k) (fun k => by positivity)
    (fun a b h => Nat.pow_lt_pow_right (by norm_num) (hmono h)) ?_
  · intro k
    have h4 : (2 : ℕ) ^ e k * 4 ≤ 2 ^ e (k + 1) := by
      calc 2 ^ e k * 4 = 2 ^ (e k + 2) := by ring
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (hgap k)
    have : ((2 ^ e k * 4 : ℕ) : ℝ) ≤ ((2 ^ e (k + 1) : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at this ⊢
    nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (e k)]

/-- **Frozen (believed known, ~85%): periodic restrictions by Mahler's method.**  For eventually
periodic `K`, the support series `G_K(z) = ∑_(v₂ m ∈ K) z^m` satisfies a Mahler equation in
`z ↦ z^(2^p)`.  It is not a rational function (`vTwo_eventuallyPeriodic_iff`), so Mahler-method
transcendence at the algebraic point `φ⁻¹` is expected.  Nguyen 2022's introduction credits
Mahler's method for `n_k = d^k + r` (Becker–Töpfer 1994, Duverney–Kanoko–Tanaka 2002,
Kanoko–Kurosawa–Shiokawa 2009).  The exact cited statement for restricted `K` is **not yet
verified**, hence frozen, not `Literature`. -/
def MahlerPeriodicRestricted : Prop :=
  ∀ K : Set ℕ, K.Infinite → Kᶜ.Infinite →
    (∃ p > 0, ∀ᶠ k in atTop, (k + p ∈ K ↔ k ∈ K)) →
    Transcendental ℚ (∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)

/-- **Open crux: ratio-two rigidity.**  At the sharp boundary `n (k + 1) ≥ 2 · n k`, the sum is
algebraic exactly when doubling is eventually exact.  The `←` direction is
`algebraic_of_eventually_doubling`, and `n_k = 2^k` is the built-in known-false sibling for "always
transcendental".

Mechanism idea (unverified): split `n` into maximal doubling blocks `s, 2s, …, 2^L s`.  By
`fib_two_mul_inv` each block collapses (d'Ocagne) to one term of size `≍ φ^(−2s)` with
denominator `F_s F_(2^(L+1) s)`.  The collapsed series has block starts with ratio `> 2` but not
bounded away from `2` (e.g. `n_(k+1) = 2 n_k + 1`).  That is exactly the gap Nguyen's
Subspace-Theorem argument leaves. -/
def RatioTwoRigidity : Prop :=
  ∀ n : ℕ → ℕ, (∀ k, 0 < n k) → (∀ k, 2 * n k ≤ n (k + 1)) →
    (IsAlgebraic ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) ↔ ∀ᶠ k in atTop, n (k + 1) = 2 * n k)

/-- **Open: restricted rigidity**, the powers-of-two shadow of the crux.  Every infinite coinfinite
`K` gives a transcendental sum.  The sparse case is `restricted_transcendental_of_sparse` and the
periodic case is `MahlerPeriodicRestricted`.  Mixed non-periodic `K`, e.g. Sturmian with density
above `1/2`, is covered by neither. -/
def RestrictedRigidity : Prop :=
  ∀ K : Set ℕ, K.Infinite → Kᶜ.Infinite →
    Transcendental ℚ (∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)

/-- **Wiring (~90%): the crux implies its shadow.**  Enumerate `K` increasingly as `e`; then
`n_j = 2^(e j)` has ratio `≥ 2`, and coinfinite `K` means doubling is never eventually exact. -/
theorem restrictedRigidity_of_ratioTwoRigidity (h : RatioTwoRigidity) : RestrictedRigidity := by
  intro K hK hKc
  classical
  haveI : Infinite K := hK.to_subtype
  let ι := Nat.Subtype.orderIsoOfNat K
  let e : ℕ → ℕ := fun j => (ι j : ℕ)
  have hmono : StrictMono e := fun a b h => by
    simpa [e] using (ι.strictMono h)
  have hmem : ∀ j, e j ∈ K := fun j => (ι j).2
  have hsum : (∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)
      = ∑' j, ((Nat.fib (2 ^ e j) : ℝ))⁻¹ :=
    (ι.toEquiv.tsum_eq (fun k : K => ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹)).symm
  rw [hsum]
  have hr := h (fun j => 2 ^ e j) (fun j => by positivity) (fun j => by
    have : e j + 1 ≤ e (j + 1) := hmono (Nat.lt_succ_self j)
    calc 2 * 2 ^ e j = 2 ^ (e j + 1) := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this)
  intro halg
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hr.1 halg)
  have hstep : ∀ j ≥ J, e (j + 1) = e j + 1 := fun j hj => by
    have := hJ j hj
    rw [show 2 * 2 ^ e j = 2 ^ (e j + 1) by ring] at this
    exact Nat.pow_right_injective le_rfl this
  have hlin : ∀ i, e (J + i) = e J + i := by
    intro i; induction i with
    | zero => rfl
    | succ i ih => rw [← add_assoc, hstep _ (by omega), ih]; ring
  apply hKc
  refine (Set.finite_lt_nat (e J)).subset fun m hm => ?_
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_lt] at hlt
  apply hm
  have := hmem (J + (m - e J))
  rwa [hlin, Nat.add_sub_cancel' hlt] at this

/-- **Open (my conjecture, ~55%): algebraic only by tiling, all `c > 1`.**  Under Erdős #267's
hypotheses, `∑ 1/F_(n_k)` is algebraic iff eventually `n (k + 1) = 2 · n k`.  The signs
`(−1)^(nj)` in odd-index expansions could allow cancellations outside the tilings, hence the low
confidence. -/
def LacunaryFibAlgebraicIffDoubling : Prop :=
  ∀ n : ℕ → ℕ, (∀ k, 0 < n k) → StrictMono n →
    (∃ c : ℝ, 1 < c ∧ ∀ k, c * (n k : ℝ) ≤ n (k + 1)) →
    (IsAlgebraic ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) ↔ ∀ᶠ k in atTop, n (k + 1) = 2 * n k)

end LeanFormalizations.LacunaryFib
