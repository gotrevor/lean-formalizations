/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDGround
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence
import LeanFormalizations.NumberTheory.Mills.QuadraticPisotFloor

/-!
# Phase 55 (multi-phase): Theorem D, quadratic case — Saito's Problem 1.7 for `R(n) = c^n + s`

**Target.**  Let `α > 1 > |β|` be the roots of `X² − aX + b` (`a, b ∈ ℤ`, `a² − 4b` not a square), `c`
a prime with `c ∤ b` and `c ∤ a² − 4b`, and `s ≥ 4`.  Then `⌊α^(c^n + s)⌋` is **not prime for
infinitely many `n`**.  (`PROOF-THEOREM-D.md`, draft 2, specialized to `d = 2`; `s₀(2) = 4` since
`κ^4 > 3`.  The hypotheses `c ∤ b` (both roots are `c`-units) and `c ∤ disc` (unramified) are
simplifications for this first Lean version.)

## Proof on paper (draft 2), and the Lean route WITHOUT `c`-adic completions
Notation: `C` = companion matrix, `p_n = ⌊α^(c^n+s)⌋ = tr C^(c^n+s) + ε_n`, `ε_n ∈ {0, −1}`
(`ε_n = −1` iff `β^(c^n+s) > 0`).
1. **Filter / stuck / window** (`TheoremDGround`, phase 44): if every `p_n` (`n ≥ n₀`) is prime, then
   infinitely many `n` are good, and for good `n`, `p_n ≡ ±1 (mod c^(e_n))`, `e_n → ∞`.  So along a
   residue class `r (mod 2)` and a fixed pair `(ω, ε)`: `tr C^(c^n+s) ≡ t := ω − ε (mod c^(e_n))`,
   `t ∈ {−1, 0, 1, 2}`.
2. **Number field, no completion.**  Let `q = c²` (the residue field of `ℚ(α)` at `c` is `𝔽_c` or
   `𝔽_(c²)`), `K = ℚ(α, ζ)` with `ζ` a primitive `(q−1)`-th root of unity, `𝔓` a prime of `𝒪_K` over
   `c`.  Since `c ∤ q − 1`, the `(q−1)`-th roots of unity reduce **injectively** mod `𝔓`, and the
   residue field contains `𝔽_q`, so each unit `x ∈ 𝒪_K` has a unique **Teichmüller** `ζ_x ∈ μ_(q−1)`
   with `x ≡ ζ_x (mod 𝔓)`.  Then `x^(c^n) ≡ ζ_x^(c^n) (mod 𝔓^(n+1))` (`TeichmullerCongruence`-style
   lifting, in `𝒪_K` instead of matrices).
3. **Spectral form.**  `C^N = α^N E₁ + β^N E₂`, `E₁ = (C − β)/(α − β)`.  `α − β` is a `𝔓`-unit
   (`c ∤ disc`).  So `tr(C^(c^n) C^s) ≡ Λ_r := ζ₁^(c^r) α^s + ζ₂^(c^r) β^s (mod 𝔓^(n+1))` for
   `n ≡ r (mod 2)` (`ζ^(c^n)` depends on `n mod 2`, as `c² ≡ 1 (mod q − 1)`).
4. **Separation:** `Λ_r − t ∈ 𝔓^m` for all `m` ⇒ `Λ_r = t` (`Ideal.iInf_pow_eq_bot_of_isDomain`
   / Krull, or `Algebra.norm` of a nonzero element has bounded `c`-valuation).
5. **Size (draft 2), no rigidity.**  `c ∤ b` makes `α` a unit at `𝔓`, so `ζ₁ ≠ 0` and no automorphism is
   needed.  In the real embedding: `α^s = |ζ₁^(c^r) α^s| ≤ |t| + |β|^s < 2 + 1 = 3`.  But the least
   quadratic Pisot number is the golden ratio `φ`, and `α^s ≥ α^4 ≥ φ^4 ≈ 6.85 > 3`.  (Enough: `α^4 > 3`
   from the integrality of `a, b`: `α + β = a ≥ 2` when `α > 1 > |β|`, unless `a = 1`, where `α ≥ φ`.)

## How to proceed (treadmill)
This is a MULTI-PHASE target.  A lap succeeds by advancing the crux.  **Decomposing the frozen
theorem into named, stated sub-lemmas (each `sorry`) is progress**; so is proving any of them.
Suggested nodes: `teichmuller_exists` (step 2), `pow_c_pow_congr_teich` (step 2), `spectral_trace`
(step 3), `eq_of_mem_pow_all` (step 4), `alpha_pow_four_gt_three` (step 5), and the assembly.  If
mathlib's number-field API makes step 2 painful, an alternative is to work in the explicit ring
`ℤ[X]/(X² − aX + b) ⊗ ℤ[ζ]` modulo powers of `c`, or in `ZMod (c^m)` Galois rings as in phase 51.

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.TheoremDQuadratic

open Filter LeanFormalizations.Mills.LucasPrimePow

/-! ### Step 1a (Lemma 1): the floor is the trace plus an offset

`tr C^N = α^N + β^N = V_N(a, b)`, the Lucas `V`-sequence of `X^2 - aX + b`, and
`⌊α^N⌋ = V_N + ε_N` with `ε_N ∈ {0, -1}` (`ε_N = -1` exactly when `β^N > 0`).
-/

/-- **Binet for a general real quadratic.**  `α^N + β^N = V_N(a, b)`. -/
theorem pow_add_pow_eq_lucasV (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (N : ℕ) : α ^ N + β ^ N = ((lucasV a b N : ℤ) : ℝ) := by
  have hαq : α ^ 2 = (a : ℝ) * α - (b : ℝ) := by
    rw [← hsum, ← hprod]; ring
  have hβq : β ^ 2 = (a : ℝ) * β - (b : ℝ) := by
    rw [← hsum, ← hprod]; ring
  induction N using Nat.twoStepInduction with
  | zero => norm_num [lucasV_zero]
  | one => simp only [pow_one, lucasV_one]; rw [hsum]
  | more N ih1 ih2 =>
      have ea : α ^ (N + 2) = (a : ℝ) * α ^ (N + 1) - (b : ℝ) * α ^ N := by
        have e : α ^ (N + 2) = α ^ N * α ^ 2 := by ring
        rw [e, hαq]; ring
      have eb : β ^ (N + 2) = (a : ℝ) * β ^ (N + 1) - (b : ℝ) * β ^ N := by
        have e : β ^ (N + 2) = β ^ N * β ^ 2 := by ring
        rw [e, hβq]; ring
      rw [ea, eb, lucasV_succ_succ]
      push_cast
      linear_combination (a : ℝ) * ih2 - (b : ℝ) * ih1

/-- **Lemma 1 (floor = trace + offset).**  For `|β| < 1`, `β ≠ 0` and `N ≥ 1`,
`⌊α^N⌋ = V_N(a, b) + ε` with `ε = -1` if `β^N > 0` and `ε = 0` otherwise. -/
theorem floor_pow_eq_lucasV_add (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hβ : |β| < 1) (hβ0 : β ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    ⌊α ^ N⌋ = lucasV a b N + (if 0 < β ^ N then -1 else 0) := by
  have hsumN := pow_add_pow_eq_lucasV a b hsum hprod N
  have habs : |β ^ N| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg _) hβ (by omega)
  have hne : β ^ N ≠ 0 := pow_ne_zero _ hβ0
  obtain ⟨hlo, hhi⟩ := abs_lt.1 habs
  rcases lt_or_gt_of_ne (Ne.symm hne) with hpos | hneg
  · rw [if_pos hpos, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  · rw [if_neg (by linarith), Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith

/-! ### Step 5 (size): the archimedean obstruction

These two lemmas are the endgame of the proof and are **fully proved**: once the number-theoretic
machinery (steps 2–4) delivers the identity `u·α^s + v·β^s = t` with `u, v` roots of unity and
`|t| ≤ 2`, a contradiction is immediate, because `α^s ≥ α^4 > 3`.
-/

/-- **Step 5a.**  A quadratic integer `α > 1` whose conjugate `β` satisfies `|β| < 1` has
`α ^ 4 > 3`.

This is sharp in spirit: the smallest such `α` is the golden ratio `φ`, and `φ ^ 4 ≈ 6.854`.
The proof needs no square roots and no discriminant hypothesis: if `α ^ 4 ≤ 3` then `α < 1.32`,
so `a = α + β ∈ (0, 2.32)` forces `a ∈ {1, 2}`, and then `b = α * (a - α)` is pinned strictly
between two consecutive integers (`-1 < b < 0` when `a = 1`; `0 < b < 1` when `a = 2`). -/
theorem alpha_pow_four_gt_three (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) : 3 < α ^ 4 := by
  by_contra hcon
  push_neg at hcon
  rw [abs_lt] at hβ
  obtain ⟨hβ1, hβ2⟩ := hβ
  -- `α < 1.32`, since `1.32 ^ 4 > 3`
  have hαlt : α < 1.32 := by nlinarith [sq_nonneg (α - 1), sq_nonneg (α * α - 1)]
  -- `0 < a < 3`, hence `a = 1` or `a = 2`
  have ha0 : (0 : ℝ) < a := by rw [← hsum]; linarith
  have ha3 : (a : ℝ) < 3 := by rw [← hsum]; linarith
  have ha0' : 0 < a := by exact_mod_cast ha0
  have ha3' : a < 3 := by exact_mod_cast ha3
  interval_cases a
  · -- `a = 1`: `b = α - α ^ 2 ∈ (-1, 0)`
    have hβeq : β = 1 - α := by push_cast at hsum; linarith
    have hb1 : (b : ℝ) < 0 := by rw [← hprod, hβeq]; nlinarith
    have hb2 : (-1 : ℝ) < b := by rw [← hprod, hβeq]; nlinarith
    have : b < 0 := by exact_mod_cast hb1
    have : (-1 : ℤ) < b := by exact_mod_cast hb2
    omega
  · -- `a = 2`: `b = 1 - (α - 1) ^ 2 ∈ (0, 1)`
    have hβeq : β = 2 - α := by push_cast at hsum; linarith
    have hb1 : (0 : ℝ) < b := by rw [← hprod, hβeq]; nlinarith
    have hb2 : (b : ℝ) < 1 := by rw [← hprod, hβeq]; nlinarith
    have : 0 < b := by exact_mod_cast hb1
    have : b < 1 := by exact_mod_cast hb2
    omega

/-- **Step 5b (the contradiction).**  With `α, β` as above, `s ≥ 4`, and `u, v` of complex
modulus `1` (they will be roots of unity, the Teichmüller lifts of step 2), the spectral value
`u·α^s + v·β^s` cannot be an integer `t` with `|t| ≤ 2`.

Indeed `‖u·α^s + v·β^s‖ ≥ α^s - |β|^s > 3 - 1 = 2`. -/
theorem spectral_ne_small_int (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) {s : ℕ} (hs : 4 ≤ s) {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {t : ℤ} (ht : |t| ≤ 2) :
    u * (α : ℂ) ^ s + v * (β : ℂ) ^ s ≠ (t : ℂ) := by
  intro heq
  have h4 : 3 < α ^ 4 := alpha_pow_four_gt_three a b hsum hprod hα hβ
  -- `α ^ s ≥ α ^ 4 > 3`
  have hαs : 3 < α ^ s := lt_of_lt_of_le h4 (pow_le_pow_right₀ hα.le hs)
  -- `|β| ^ s < 1`
  have hβs : |β| ^ s < 1 := pow_lt_one₀ (abs_nonneg _) hβ (by omega)
  have hnu : ‖u * (α : ℂ) ^ s‖ = α ^ s := by
    rw [norm_mul, hu, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hnv : ‖v * (β : ℂ) ^ s‖ = |β| ^ s := by
    rw [norm_mul, hv, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hlow : α ^ s - |β| ^ s ≤ ‖u * (α : ℂ) ^ s + v * (β : ℂ) ^ s‖ := by
    have := norm_sub_norm_le (u * (α : ℂ) ^ s) (-(v * (β : ℂ) ^ s))
    rw [hnu, norm_neg, hnv, sub_neg_eq_add] at this
    exact this
  rw [heq] at hlow
  have hnt : ‖(t : ℂ)‖ = |(t : ℝ)| := by
    rw [show ((t : ℂ)) = ((t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have ht' : |(t : ℝ)| ≤ 2 := by
    rw [← Int.cast_abs]
    exact_mod_cast ht
  rw [hnt] at hlow
  linarith

/-! ### Steps 2–4: the number-field machinery (the crux, open)

The nodes below are the remaining obligations.  They are stated over a number field `K` containing
`α` and the `(q-1)`-th roots of unity, with `𝔓` a prime of `𝒪_K` above `c`; see the header.
-/

/-- **Step 4 (separation).**  In a Noetherian integral domain, an element lying in every power of
a proper ideal is zero.  This turns "`Λ - t ∈ 𝔓^m` for all `m`" into "`Λ = t`".  (Krull
intersection.) -/
theorem eq_of_mem_pow_all {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≠ ⊤) (x : R) (hx : ∀ m : ℕ, x ∈ I ^ m) : x = 0 := by
  have h := Ideal.iInf_pow_eq_bot_of_isDomain I hI
  have hxm : x ∈ ⨅ m : ℕ, I ^ m := Ideal.mem_iInf.2 hx
  rw [h] at hxm
  simpa using hxm

/-! ### Steps 2–3: the Teichmüller / spectral crux

`spectral_identity` is the single remaining mathematical obligation: it packages steps 2 and 3
(Teichmüller representatives in `𝒪_K` and the spectral form of the trace) together with step 4
(separation), and hands step 5 exactly what it needs.

**Why the conclusion has this shape.**  Let `q` be the size of the residue field of `ℚ(α)` at `c`
(so `q = c` or `c²`), `K = ℚ(α, ζ_(q-1))`, and `𝔓` a prime of `𝒪_K` over `c`.  Because `c ∤ q - 1`,
reduction mod `𝔓` is injective on `μ_(q-1)`, so `α` and `β` (both `𝔓`-units, as `c ∤ b`) have
Teichmüller representatives `ζ₁, ζ₂ ∈ μ_(q-1)`, and
`α^(c^n) ≡ ζ₁^(c^n) (mod 𝔓^(n+1))`, likewise for `β`.  As `c^2 ≡ 1 (mod q-1)`, the residues
`ζ_i^(c^n)` depend only on `n mod 2`; enlarging the modulus `f` of the residue class `r` is
harmless.  Hence `V (c^n + s) ≡ ζ₁^(c^r) α^s + ζ₂^(c^r) β^s (mod 𝔓^(n+1))`, and the hypothesis
`hcong` forces `ζ₁^(c^r) α^s + ζ₂^(c^r) β^s - t ∈ 𝔓^m` for every `m`, so by `eq_of_mem_pow_all`
the two sides are equal in `K`.  Finally `u := ζ₁^(c^r)` and `v := ζ₂^(c^r)` are roots of unity,
hence of complex modulus `1` under the embedding `K → ℂ` sending `α, β` to the given reals. -/
theorem spectral_identity (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    (V : ℕ → ℤ) (hV : ∀ N, (V N : ℝ) = α ^ N + β ^ N)
    {s f r : ℕ} (hf : 1 ≤ f) (t : ℤ)
    (hcong : ∀ m : ℕ, ∃ n, m ≤ n ∧ n % f = r ∧ (c : ℤ) ^ m ∣ V (c ^ n + s) - t) :
    ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ u * (α : ℂ) ^ s + v * (β : ℂ) ^ s = (t : ℂ) := by
  sorry

/-- **Steps 2–5 combined.**  Along a residue class, the traces `V (c^n + s)` cannot be congruent
to a fixed small integer `t` modulo arbitrarily large powers of `c`.

This is fully proved from `spectral_identity` (the crux) and `spectral_ne_small_int` (step 5). -/
theorem not_congr_small_int (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    (V : ℕ → ℤ) (hV : ∀ N, (V N : ℝ) = α ^ N + β ^ N)
    {s f r : ℕ} (hs : 4 ≤ s) (hf : 1 ≤ f) {t : ℤ} (ht : |t| ≤ 2) :
    ¬ ∀ m : ℕ, ∃ n, m ≤ n ∧ n % f = r ∧ (c : ℤ) ^ m ∣ V (c ^ n + s) - t := by
  intro hcong
  obtain ⟨u, v, hu, hv, huv⟩ :=
    spectral_identity a b hsum hprod hα hβ hdisc hc hcb hcd V hV hf t hcong
  exact spectral_ne_small_int a b hsum hprod hα hβ hs hu hv ht huv

/-- **Theorem D, quadratic case.** -/
theorem floor_pow_prime_pow_add_not_prime (a b : ℤ) {α β : ℝ} (hsum : α + β = a)
    (hprod : α * β = b) (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    {s : ℕ} (hs : 4 ≤ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDQuadratic
