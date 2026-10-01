/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Crux

/-!
# The linear-sieve lower bound on an interval (phase E5)

One frozen statement, `linearSieveIntervalLower_holds : LinearSieveIntervalLower`: for `ε > 0`, an
interval `(Y/2, Y]` with one excluded class per prime `q ≤ Y^{1/2−ε}` keeps `≥ c Y/log Y` points.
With E4d this makes the exceptional-set bound `#{bad n ≤ X} ≪ X exp(−(log X)^{1/2−ε})`
unconditional.

The content is the Jurkat–Richert theorem in the one case we need: sieve dimension 1, remainders
`|r_d| ≤ 1` (an interval, one class per prime), sieving level `s = log D / log z > 2` where
`f(s) = 2e^γ log(s−1)/s > 0`.  The slack is `s − 2 ≍ ε`, so every constant must be asymptotically
sharp: a crude bound that loses a constant factor in `F` makes the lower bound negative.

## Route (35% within budget; a NAMED partial result is progress)

Sources: Halberstam–Richert, *Sieve Methods*, the linear-sieve chapter (Jurkat–Richert's method);
Friedlander–Iwaniec, *Opera de Cribro*, the linear-sieve chapters (β-sieve with `β = 2`).
⚠️ Chapter/theorem numbers not re-opened; read the method, not a citation.

1. **Selberg's upper bound, sharp for `s ≤ 2`.**  `S(A_d, w) ≤ X ω(d)/d / G_w(√(D/d)) + Σ_{e ≤ D/d}
   |r|` with `G_w(x) = Σ_{e ≤ x, e ∣ P(w)} μ²(e)/φ(e)` (one class per prime: `g(p) = 1/p`).  When
   `x ≤ w`, `G_w(x) = Σ_{e ≤ x} μ²(e)/φ(e) ≥ log x` (classical, elementary).  Mathlib:
   `Mathlib/NumberTheory/SelbergSieve.lean` (`siftedSum_le_mainSum_errSum_of_upperMoebius`,
   `upperMoebius_lambdaSquared`); our `Erdos385/Brun/` did the dimension-2 analogue and is a
   template.
2. **Buchstab identity**: `S(A, z) = S(A, z₀) − Σ_{z₀ ≤ p < z} S(A_p, p)`.
3. **Fundamental lemma at `z₀ = Y^{η}`** (`η → 0` slowly): `S(A, z₀) ≥ X V(z₀)(1 − o(1)) − D₀`, e.g.
   by Brun's pure sieve / Bonferroni with `D₀ = z₀^{O(1/η)}` small.
4. **Assemble**: subtract step 1's upper bounds for `S(A_p, p)` at level `D/p` (sharp when
   `√(D/p) ≤ p`, i.e. `p ≥ D^{1/3}`; for smaller `p` use monotonicity in the sifting limit to stay
   in the sharp range).  Mertens with an explicit error (`V(z) ≍ e^{−γ}/log z`; mathlib or PNT+ has
   `∏(1 − 1/p)` asymptotics, else prove the version you need) turns the prime sum into the integral
   giving `f(s) = 2e^γ log(s − 1)/s` on `2 < s ≤ 3`.  Then `X = Y/2`, `D = Y^{1−ε/4}`,
   `z = Y^{1/2−ε}`: `s ≥ 2 + ε` and the count is `≥ (Y/2) V(z) f(s)/2 ≫_ε Y/log Y`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

## Decomposition (lap 1, 2026-10-01)

Done: the frozen statement is proved from the crux `LinearSieve.siftMin_lower`
(`LinearSieve/Crux.lean`): `S⁻(N, z) ≥ c N / log N` for `z ≤ N^{1/2−ε}`, where `S⁻ = siftMin`
is the least survivor count over *all* problems (interval of length `N`, one class per prime
`< z`).  `LinearSieve/Buchstab.lean` proves the class is self-similar and the exact Buchstab
inequalities `siftMin_buchstab`, `siftMax_buchstab` (sub-problems have length `N/p ± 1`).

Refuted shortcut (`Maze.lean`, `scripts/linear-sieve-onestep.py`): one Buchstab step on
Selberg's bound only reaches `s ≳ 2.05`.  Exact Jurkat–Richert constants are forced.

Route for the crux, normalised `a(s) = liminf S⁻(N, N^{1/s}) log N / N`, `b(s) = limsup S⁺ …`,
`C = e^{−γ}` (`mertens_third_classical_eGamma`):
1. Selberg (copy `Brun/PairSieve.lean` with `ν(p) = 1/p`): `S⁺(N, z) ≤ N/G_z(ξ) + ξ²`, and
   `G_z(ξ) ≥ log ξ` for `ξ ≤ z` ⇒ `b ≤ 2` on `[1, 2]`.
2. Limit Buchstab: `a(s) ≥ a(s') − ∫_s^{s'} b(t−1)/(t−1)`, `b(s) ≤ b(s') − ∫_s^{s'} a(t−1)/(t−1)`
   (Mertens' second theorem; `a`, `b` are monotone, so Riemann sums converge).
3. Fundamental lemma: `|a(s) − Cs|, |b(s) − Cs| ≤ η(s)`, `η` super-exponentially small (Buchstab
   from `w = 2` + Selberg + Rankin on the random-prime-product tail `1 − V(p) G_p(ξ)`).
4. Comparison functions `α = λ(sω − m/2)`, `β = λ(sω + m/2)`: `ω` Buchstab's function,
   `m' = −m(s−1)/(s−1)`, `m = 2` on `[1,2]`; these solve the JR system with equality, `α = 0`,
   `β = 2λ` on `[1, 2]`, and `λ = C/ω_∞`.  Need `λ ≥ 1`, i.e. `ω_∞ ≤ C`: the rough-number count
   obeys the *forward* Buchstab `Φ(N, z) ≥ Σ_{z ≤ p ≤ N} Φ(N/p, p)` (positive terms only, no
   coupling), which with PNT gives `Φ ≳ sω(s) N/log N`, while `Φ ≤ S⁺ ≤ (Cs + η) N/log N`.
5. **Comparison principle (new, derivative-free).**  `K = max(α − a, b − β, 0)` vanishes on
   `[1, 2]`, is tiny at `∞`, and satisfies `K(s) ≤ ∫_{s−1}^∞ K(u)/u du`.  Integrate against
   `w(u) = u − 1` and swap (Tonelli): `∫_2^∞ K(u)(u−1) ≤ ∫_2^∞ K(v)(v²−1)/(2v)`, and
   `(v−1) − (v²−1)/(2v) = (v−1)²/(2v) > 0`, so `K = 0`.  Hence `a ≥ α ≥ α_{λ=1} = 2 log(s−1) > 0`
   on `(2, 3]`.

Frozen: this statement and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **The linear-sieve lower bound** (Jurkat–Richert, interval case), proved. -/
theorem linearSieveIntervalLower_holds : LinearSieveIntervalLower := by
  classical
  intro ε hε
  set ε0 := min ε (1 / 4) with hε0
  have hε0pos : 0 < ε0 := lt_min hε (by norm_num)
  have hε0le : ε0 ≤ ε := min_le_left _ _
  have hε0q : ε0 ≤ 1 / 4 := min_le_right _ _
  obtain ⟨c, hc, N0, hN⟩ := LinearSieve.siftMin_lower (ε0 / 2) (by positivity)
  have hev : ∀ᶠ Y : ℕ in Filter.atTop, (4 : ℝ) ≤ (Y : ℝ) ^ (ε0 / 2) :=
    ((tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨Y1, hY1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨c / 2, by positivity, max (max Y1 (2 * N0 + 4)) 4, fun Y hY r => ?_⟩
  have hYY1 : Y1 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYN0 : 2 * N0 + 4 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  set N : ℕ := Y - Y / 2 with hNdef
  set lo : ℤ := (Y / 2 : ℕ) + 1 with hlo
  set η : ℝ := 1 / 2 - ε0 with hη
  set z : ℕ := ⌊(Y : ℝ) ^ η⌋₊ + 1 with hz
  set r' : ℕ → ℤ := fun q => (r q : ℤ) with hr'
  have hYpos : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have hN2 : 2 * N ≥ Y := by omega
  have hNN0 : N0 ≤ N := by omega
  have hN2' : 2 ≤ N := by omega
  -- Step 1: the sifted problem injects into the target set.
  have step1 : (LinearSieve.sift lo N r' z : ℝ) ≤
      ({a : ℕ | Y / 2 < a ∧ a ≤ Y ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - ε) → a % q ≠ r q % q}.ncard : ℝ) := by
    set S := (Finset.Ico lo (lo + N)).filter (LinearSieve.Survives r' z)
    have hpos : ∀ k ∈ S, 0 < k := by
      intro k hk
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).1
      omega
    have hinj : Set.InjOn Int.toNat (S : Set ℤ) := by
      intro x hx y hy hxy
      have h1 := Int.toNat_of_nonneg (hpos x hx).le
      have h2 := Int.toNat_of_nonneg (hpos y hy).le
      rw [← h1, ← h2, hxy]
    have hcard : (S.image Int.toNat).card = LinearSieve.sift lo N r' z :=
      Finset.card_image_of_injOn hinj
    have hsub : ((S.image Int.toNat : Finset ℕ) : Set ℕ) ⊆ {a : ℕ | Y / 2 < a ∧ a ≤ Y ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - ε) → a % q ≠ r q % q} := by
      intro a ha
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      have hk' := Finset.mem_filter.mp hk
      have hk1 := Finset.mem_Ico.mp hk'.1
      have hkk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (hpos k hk).le
      refine ⟨by omega, by omega, fun q hq hqY => ?_⟩
      have hqz : q < z := by
        have : (q : ℝ) ≤ (Y : ℝ) ^ η :=
          hqY.trans (Real.rpow_le_rpow_of_exponent_le hYpos (by rw [hη]; linarith))
        exact Nat.lt_succ_of_le (Nat.le_floor this)
      intro heq
      apply hk'.2 q hq hqz
      have h1 : ((k.toNat % q : ℕ) : ℤ) = ((r q % q : ℕ) : ℤ) := by rw [heq]
      push_cast at h1
      rw [hkk] at h1
      exact Int.ModEq.dvd h1.symm
    have hfin : {a : ℕ | Y / 2 < a ∧ a ≤ Y ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - ε) → a % q ≠ r q % q}.Finite :=
      (Set.finite_Iic Y).subset (fun a ha => ha.2.1)
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, hcard] at this
    exact_mod_cast this
  -- Step 2: the crux.
  have hzle : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε0 / 2) := by
    have hzY : (z : ℝ) ≤ (Y : ℝ) ^ η + 1 := by
      rw [hz]; push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (Y : ℝ) ^ η by positivity)
      linarith
    have hη0 : 0 ≤ η := by rw [hη]; linarith
    have h1 : (1 : ℝ) ≤ (Y : ℝ) ^ η := Real.one_le_rpow hYpos hη0
    have h4 := hY1 Y hYY1
    have he : (1 : ℝ) / 2 - ε0 / 2 = η + ε0 / 2 := by rw [hη]; ring
    have hYe : (Y : ℝ) ^ ((1 : ℝ) / 2 - ε0 / 2) = (Y : ℝ) ^ η * (Y : ℝ) ^ (ε0 / 2) := by
      rw [he, Real.rpow_add (by linarith)]
    have hNY : (Y : ℝ) / 2 ≤ N := by
      have : ((Y : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hN2
      push_cast at this; linarith
    have hepos : 0 ≤ (1 : ℝ) / 2 - ε0 / 2 := by linarith
    have hmono : ((Y : ℝ) / 2) ^ ((1 : ℝ) / 2 - ε0 / 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε0 / 2) :=
      Real.rpow_le_rpow (by positivity) hNY hepos
    have hdiv : ((Y : ℝ) / 2) ^ ((1 : ℝ) / 2 - ε0 / 2) =
        (Y : ℝ) ^ ((1 : ℝ) / 2 - ε0 / 2) / 2 ^ ((1 : ℝ) / 2 - ε0 / 2) :=
      Real.div_rpow (by positivity) (by norm_num) _
    have h2e : (2 : ℝ) ^ ((1 : ℝ) / 2 - ε0 / 2) ≤ 2 :=
      by simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
          (show (1 : ℝ) / 2 - ε0 / 2 ≤ 1 by linarith)
    have h2pos : (0 : ℝ) < 2 ^ ((1 : ℝ) / 2 - ε0 / 2) := by positivity
    have : (Y : ℝ) ^ η + 1 ≤ ((Y : ℝ) / 2) ^ ((1 : ℝ) / 2 - ε0 / 2) := by
      rw [hdiv, hYe, le_div_iff₀ h2pos]
      nlinarith
    linarith
  have step2 := (hN N hNN0 z hzle).trans
    (show ((LinearSieve.siftMin N z : ℕ) : ℝ) ≤ (LinearSieve.sift lo N r' z : ℕ) by
      exact_mod_cast LinearSieve.siftMin_le lo N r' z)
  -- Step 3: compare the normalisations.
  have hNpos : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
  have hNY : (N : ℝ) ≤ Y := by exact_mod_cast (show N ≤ Y by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogNY : Real.log N ≤ Real.log Y := Real.log_le_log (by linarith) hNY
  have hY2 : (Y : ℝ) ≤ 2 * N := by exact_mod_cast hN2
  have : c / 2 * Y / Real.log Y ≤ c * N / Real.log N := by
    calc c / 2 * Y / Real.log Y ≤ c * N / Real.log Y := by
          apply div_le_div_of_nonneg_right _ (by linarith); nlinarith
      _ ≤ c * N / Real.log N := div_le_div_of_nonneg_left (by positivity) hlogN hlogNY
  linarith

end LeanFormalizations.Erdos385
