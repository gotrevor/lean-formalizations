/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Literature inputs for the Erdős #385 exceptional-set bound (phase E4)

Statements only, never `axiom`s; each faithful-or-weaker to its source.

* `ArithLargeSieve`: Montgomery's arithmetic large sieve with the Montgomery–Vaughan constant.  If
  `S ⊂ (M, M+N]` avoids, for each prime `p ≤ Q`, a set `Ω_p` of `ω(p) < p` residues mod `p`, then
  `|S| · L ≤ N + Q²`, `L = Σ_{q ≤ Q squarefree} ∏_{p ∣ q} ω(p)/(p − ω(p))`.  Source: Montgomery,
  *The analytic principle of the large sieve*, Bull. AMS 84 (1978), Thm 5 (with the
  Montgomery–Vaughan 1973 constant `N − 1 + Q²`); also Iwaniec–Kowalski Thm 7.14.  ⚠️ Theorem
  numbers recalled, not re-opened (80%); the statement is textbook.  Weaker: `N + Q²`.
* `LinearSieveIntervalLower`: the Jurkat–Richert linear-sieve lower bound, specialised to an interval
  with one excluded class per prime below `Y^{1/2−ε}` (sieving level `s > 2`, where `f(s) > 0`).
  Source: Jurkat–Richert 1965; Halberstam–Richert, *Sieve Methods*, Ch. 8 (Thm 8.4); Friedlander–
  Iwaniec, *Opera de Cribro*, Thm 12.14.  ⚠️ Theorem numbers recalled (75%).  Weaker: unspecified
  `c`, `Y₀`.
* `McDiarmidFinite`: McDiarmid's bounded-differences inequality (lower tail) for a function on a
  finite product of finite sets with the uniform measure.  Source: McDiarmid 1989, *On the method
  of bounded differences*, Lemma 1.2.  Dischargeable from mathlib's Azuma–Hoeffding
  (`measure_sum_ge_le_of_HasCondSubgaussianMGF`, `Mathlib/Probability/Moments/SubGaussian.lean`)
  via the Doob martingale.

No known-false controls yet (a later phase should add one per Prop, e.g. the large sieve with
`N` in place of `N + Q²`, false for `S` a single residue class and large `Q`).
-/

namespace LeanFormalizations.Literature

/-- **The arithmetic large sieve** (Montgomery; Montgomery–Vaughan constant, weakened). -/
def ArithLargeSieve : Prop :=
  ∀ (M N Q : ℕ) (Ω : ℕ → Finset ℕ) (S : Finset ℕ),
    (∀ p, p.Prime → p ≤ Q → Ω p ⊆ Finset.range p ∧ (Ω p).card < p) →
    (∀ n ∈ S, M < n ∧ n ≤ M + N ∧ ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) →
    (S.card : ℝ) * (∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
        ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) ≤ N + (Q : ℝ) ^ 2

/-- **Linear sieve lower bound on an interval, one class per prime below `Y^{1/2−ε}`.** -/
def LinearSieveIntervalLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y → ∀ r : ℕ → ℕ,
    c * Y / Real.log Y ≤
      ({a : ℕ | Y / 2 < a ∧ a ≤ Y ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - ε) → a % q ≠ r q % q}.ncard : ℝ)

/-- **McDiarmid's inequality** (lower tail, uniform measure on a finite product). -/
def McDiarmidFinite : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (α : ι → Type) [∀ i, Fintype (α i)]
    [∀ i, DecidableEq (α i)] [∀ i, Nonempty (α i)] (f : (∀ i, α i) → ℝ) (c : ι → ℝ),
    (∀ x y : (∀ i, α i), ∀ i, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) →
    ∀ t : ℝ, 0 < t →
      ((Finset.univ.filter fun x =>
          f x ≤ (∑ z, f z) / Fintype.card (∀ i, α i) - t).card : ℝ) ≤
        Fintype.card (∀ i, α i) * Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)

end LeanFormalizations.Literature
