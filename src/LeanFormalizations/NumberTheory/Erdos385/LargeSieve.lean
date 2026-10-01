/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385LargeSieveWeak
import LeanFormalizations.NumberTheory.Erdos385.LargeSieve.Gallagher

/-!
# The arithmetic large sieve, proved (phase E4c)

One frozen statement, `arithLargeSieveWeak_holds : ArithLargeSieveWeak`.

## Route (65%): Gallagher's analytic large sieve, then Montgomery's lemma

1. **Gallagher's inequality.**  For `f` continuously differentiable on `[x − δ/2, x + δ/2]`:
   `|f(x)| ≤ δ⁻¹ ∫ |f| + ½ ∫ |f'|` over that interval (fundamental theorem of calculus, averaged).
2. **Analytic large sieve.**  `S(α) = Σ_{M<n≤M+N} a_n e(nα)`.  For points `α_r` in `ℝ/ℤ` that are
   `δ`-spaced, apply step 1 to `|S|²` around each `α_r` (disjoint arcs), sum, and use Parseval on
   the circle (mathlib `tsum_sq_fourierCoeff`/`hasSum_sq_fourierCoeff`, or expand the finite sum
   directly: `∫_0^1 |S|² = Σ|a_n|²`) and Cauchy–Schwarz with `|S'| ≤ 2π·(N/2)|…|` after centring
   the `n`-range at its midpoint: `Σ_r |S(α_r)|² ≤ (δ⁻¹ + π N) Σ |a_n|²`.  The Farey points
   `a/q`, `q ≤ Q`, `(a, q) = 1` are `Q⁻²`-spaced, so `Σ_{q≤Q} Σ*_{a} |S(a/q)|² ≤ (Q² + πN) Σ|a_n|²`.
3. **Montgomery's lemma.**  If `S` (the sifted set, `a_n = 1_{n ∈ S}`) avoids `ω(p)` classes mod
   each `p ∣ q`, `q` squarefree, then `Σ*_{a mod q} |S(a/q)|² ≥ |S|² ∏_{p∣q} ω(p)/(p − ω(p))`.
   Prove for `q = p` prime (Cauchy–Schwarz over the `p − ω(p)` allowed classes plus
   `Σ_{a mod p} |S(a/p)|² = p Σ_{h mod p} |S ∩ (h mod p)|²`), then multiplicativity over CRT
   (`ZMod.chineseRemainder`).
4. **Combine**: `|S|² L ≤ (Q² + πN)|S|`, so `|S| L ≤ π(N + Q²)`; take `C = 4`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement and everything in `Literature/`.

**DONE (2026-10-01)**: proved with `C = 3 + 24π`; helpers `LargeSieve/{Montgomery,Gallagher}.lean`.
Gallagher's step 2 uses `2|S||S'| ≤ λ|S|² + λ⁻¹|S'|²` instead of Cauchy–Schwarz, and integrates
over `[-1, 2]` so no periodicity is needed.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature LargeSieve Finset

lemma farey_sep {q a q' a' : ℕ} (hq : 0 < q) (hq' : 0 < q') (Q : ℕ) (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (hne : (a : ℝ) / q ≠ a' / q') : 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - a' / q'| := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hq0' : (0:ℝ) < q' := by exact_mod_cast hq'
  have hint : ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) ≠ 0 := by
    intro h; apply hne
    have : ((a * q' : ℕ) : ℝ) = ((a' * q : ℕ) : ℝ) := by exact_mod_cast (sub_eq_zero.1 h)
    push_cast at this; field_simp; linarith
  have h1 : (1:ℝ) ≤ |((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)| := by
    have := Int.one_le_abs hint
    exact_mod_cast this
  have e : (a : ℝ) / q - a' / q' = (((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)) / (q * q') := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * q')]
  have hQ : (q : ℝ) * q' ≤ (Q:ℝ) ^ 2 := by
    rw [sq]; gcongr <;> exact_mod_cast ‹_›
  have hQ0 : (0:ℝ) < Q := by
    have : 0 < Q := lt_of_lt_of_le hq hqQ
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma norm_expSum_shift (M N : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, M < n ∧ n ≤ M + N) (x : ℝ) :
    ‖expSum S (fun _ => 1) x‖
      = ‖expSum (range (N + 1)) (fun k => if M + k ∈ S then 1 else 0) x‖ := by
  have hSimg : S = ((range (N + 1)).filter (fun k => M + k ∈ S)).image (fun k => M + k) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hn; have := hS n hn
      exact ⟨n - M, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩; exact hk
  have e : expSum S (fun _ => 1) x
      = ee (M * x) * expSum (range (N + 1)) (fun k => if M + k ∈ S then 1 else 0) x := by
    unfold expSum
    conv_lhs => rw [hSimg]
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · beta_reduce; rw [if_pos h, one_mul, one_mul, ← ee_add]; congr 1; push_cast; ring
    · simp [h]
  rw [e, norm_mul, norm_ee, one_mul]

/-- **The arithmetic large sieve** (Gallagher + Montgomery), proved. -/
theorem arithLargeSieveWeak_holds : ArithLargeSieveWeak := by
  refine ⟨3 + 24 * Real.pi, ?_⟩
  intro M N Q Ω S hΩ hS
  set L := ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
    ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)
  have hC : 0 ≤ (3 + 24 * Real.pi) * (N + (Q : ℝ) ^ 2) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hC
  have hN : 1 ≤ N := by
    obtain ⟨n, hn⟩ := hne; have := hS n hn; omega
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQ
  · subst hQ0
    have hL : L = 0 := by simp [L]
    rw [hL, mul_zero]; exact hC
  -- the Farey points
  set P := ((Finset.Icc 1 Q).filter Squarefree).sigma
    (fun q => (range q).filter (fun a => Nat.Coprime a q))
  set φ : (Σ _ : ℕ, ℕ) → ℝ := fun x => (x.2 : ℝ) / x.1
  set c : ℕ → ℂ := fun k => if M + k ∈ S then 1 else 0
  have hmemP : ∀ x ∈ P, 1 ≤ x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
    intro x hx
    simp only [P, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hx
    exact ⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2⟩
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, a⟩ hx ⟨q', a'⟩ hy hxy
    obtain ⟨h1, -, -, h4⟩ := hmemP _ hx
    obtain ⟨h1', -, -, h4'⟩ := hmemP _ hy
    simp only [φ] at hxy h1 h1' h4 h4'
    have hq0 : (0:ℝ) < q := by exact_mod_cast h1
    have hq0' : (0:ℝ) < q' := by exact_mod_cast h1'
    have hc : a * q' = a' * q := by
      rw [div_eq_div_iff hq0.ne' hq0'.ne'] at hxy; exact_mod_cast hxy
    -- reduced fractions
    have hqq : q = q' := by
      have d1 : q ∣ q' := by
        have : q ∣ a * q' := ⟨a', by rw [hc]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left h4.symm this)
      have d2 : q' ∣ q := by
        have : q' ∣ a' * q := ⟨a, by rw [← hc]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left h4'.symm this)
      exact Nat.dvd_antisymm d1 d2
    subst hqq
    have : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) hc
    subst this; rfl
  have hδ : (0:ℝ) < 1 / (Q:ℝ) ^ 2 := by
    have : (0:ℝ) < Q := by exact_mod_cast hQ
    positivity
  have hδ1 : 1 / (Q:ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1:ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have hpts : ∀ x ∈ P.image φ, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨⟨q, a⟩, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, -, h3, -⟩ := hmemP _ hy
    simp only [φ]
    have hq0 : (0:ℝ) < q := by exact_mod_cast h1
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hq0]; exact_mod_cast h3.le
  have hsep : ∀ x ∈ P.image φ, ∀ y ∈ P.image φ, x ≠ y → 1 / (Q:ℝ) ^ 2 ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨⟨q, a⟩, hx', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨⟨q', a'⟩, hy', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨h1, h2, -, -⟩ := hmemP _ hx'
    obtain ⟨h1', h2', -, -⟩ := hmemP _ hy'
    exact farey_sep h1 h1' Q h2 h2' hxy
  have hLS := analytic_large_sieve N c (P.image φ) hδ hδ1 hpts hsep
  have hc2 : ∑ k ∈ range (N + 1), ‖c k‖ ^ 2 ≤ S.card := by
    have : ∀ k, ‖c k‖ ^ 2 = if M + k ∈ S then 1 else 0 := by
      intro k; simp only [c]; split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card_of_injOn (fun k => M + k)
      (fun k hk => (Finset.mem_filter.1 hk).2) (fun a _ b _ h => by simpa using h)
  -- Montgomery for each q
  have hmont : ∀ q ∈ (Finset.Icc 1 Q).filter Squarefree,
      (S.card : ℝ) ^ 2 * sieveH Ω q
        ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ‖expSum S (fun _ => 1) (a / q)‖ ^ 2 := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    have := montgomery S Ω Q hΩ (fun n hn => (hS n hn).2.2) q hq.2
      (fun p hp => (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hq.1.2)
      (fun _ => 1)
    simpa using this
  have hmain : (S.card : ℝ) ^ 2 * L
      ≤ (3 / (1 / (Q:ℝ) ^ 2) + 12 * Real.pi * (N + 1)) * S.card := by
    calc (S.card : ℝ) ^ 2 * L = ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, (S.card : ℝ) ^ 2 * sieveH Ω q := by
          rw [Finset.mul_sum]; rfl
      _ ≤ ∑ x ∈ P, ‖expSum S (fun _ => 1) (φ x)‖ ^ 2 := by
          rw [Finset.sum_sigma]; exact Finset.sum_le_sum hmont
      _ = ∑ y ∈ P.image φ, ‖expSum S (fun _ => 1) y‖ ^ 2 := (Finset.sum_image (f := fun y => ‖expSum S (fun _ => 1) y‖ ^ 2) hinj).symm
      _ = ∑ y ∈ P.image φ, ‖expSum (range (N + 1)) c y‖ ^ 2 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [norm_expSum_shift M N S (fun n hn => ⟨(hS n hn).1, (hS n hn).2.1⟩) y]
      _ ≤ _ := hLS.trans (by gcongr)
  have hSpos : (0:ℝ) < S.card := by exact_mod_cast hne.card_pos
  have h3 : (3 / (1 / (Q:ℝ) ^ 2)) = 3 * (Q:ℝ) ^ 2 := by field_simp
  rw [h3] at hmain
  have hmain' : (S.card : ℝ) * L ≤ 3 * (Q:ℝ) ^ 2 + 12 * Real.pi * (N + 1) := by
    have := hmain
    rw [sq, mul_assoc, mul_comm _ (S.card : ℝ)] at this
    exact le_of_mul_le_mul_left this hSpos
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  calc (S.card : ℝ) * L ≤ 3 * (Q:ℝ) ^ 2 + 12 * Real.pi * (N + 1) := hmain'
    _ ≤ (3 + 24 * Real.pi) * (N + (Q : ℝ) ^ 2) := by nlinarith

end LeanFormalizations.Erdos385
