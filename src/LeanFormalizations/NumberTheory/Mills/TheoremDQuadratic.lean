/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDGround
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence
import LeanFormalizations.NumberTheory.Mills.QuadraticPisotFloor
import LeanFormalizations.NumberTheory.Mills.FibonacciPrimePow

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

open Filter LeanFormalizations.Mills.LucasPrimePow LeanFormalizations.Mills.ThreeAdic

/-! ### The companion matrix

The filter of steps 1–2 runs on the companion matrix `C` of `X^2 - aX + b`.  Its traces are the
Lucas `V`-sequence, so it is the bridge between the arithmetic of `GL_2(𝔽_p)` and the real
quantity `⌊α^N⌋`.
-/

/-- The companion matrix of `X ^ 2 - a X + b`. -/
def compMat (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -b; 1, a]

@[simp] theorem compMat_det (a b : ℤ) : (compMat a b).det = b := by
  simp [compMat, Matrix.det_fin_two]

@[simp] theorem compMat_trace (a b : ℤ) : (compMat a b).trace = a := by
  simp [compMat, Matrix.trace_fin_two]

/-- Cayley–Hamilton for the companion matrix, by hand. -/
theorem compMat_sq (a b : ℤ) :
    compMat a b ^ 2 = a • compMat a b - b • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [compMat, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_val'] <;> norm_num <;> ring

/-- The traces of the companion matrix are the Lucas `V`-sequence. -/
theorem trace_compMat_pow (a b : ℤ) (N : ℕ) : (compMat a b ^ N).trace = lucasV a b N := by
  induction N using Nat.twoStepInduction with
  | zero => simp [lucasV_zero, Matrix.trace_fin_two, Matrix.one_apply]
  | one => simp [lucasV_one, compMat, Matrix.trace_fin_two]
  | more N ih1 ih2 =>
      have e : compMat a b ^ (N + 2) = compMat a b ^ N * (compMat a b ^ 2) := pow_add _ N 2
      rw [e, compMat_sq, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
        Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, lucasV_succ_succ]
      rw [← pow_succ, ih2, ih1]
      simp [smul_eq_mul]

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

/-! ### Growth: the values `⌊α^(c^n+s)⌋` are strictly increasing

Needed for the good/stuck dichotomy: a stuck `n` would make the prime `p_n` divide the strictly
larger prime `p_(n+kj)`.  The key point is that `α ≥ φ`, i.e. `α + 1 ≤ α ^ 2`, which forces
`α ^ N + 1 ≤ α ^ (N+1)` for every `N ≥ 1`.
-/

/-- **`α` is at least the golden ratio**: `α + 1 ≤ α ^ 2`.

Cases on `a = α + β ∈ ℤ` (which is `≥ 1`): for `a = 1` integrality gives `b ≤ -1`; for `a = 2` it
gives `b ≤ 0`; for `a ≥ 3` one has `α > 2` and `|b| < α`. -/
theorem golden_le_sq (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) : α + 1 ≤ α ^ 2 := by
  rw [abs_lt] at hβ
  obtain ⟨hβ1, hβ2⟩ := hβ
  have ha0 : (0 : ℝ) < a := by rw [← hsum]; linarith
  have ha0'' : (0 : ℤ) < a := by exact_mod_cast ha0
  have ha0' : 1 ≤ a := ha0''
  have hβeq : β = (a : ℝ) - α := by linarith [hsum]
  have hsq : α ^ 2 = (a : ℝ) * α - (b : ℝ) := by rw [← hsum, ← hprod]; ring
  rcases lt_trichotomy a 1 with h | h | h
  · omega
  · -- `a = 1`: `b = α - α ^ 2 < 0`, so `b ≤ -1`
    subst h
    have hbneg : (b : ℝ) < 0 := by rw [← hprod, hβeq]; push_cast; nlinarith
    have : b < 0 := by exact_mod_cast hbneg
    have hb1 : (b : ℝ) ≤ -1 := by exact_mod_cast (by omega : b ≤ -1)
    rw [hsq]; push_cast; linarith
  · rcases eq_or_lt_of_le (by omega : (2 : ℤ) ≤ a) with h2 | h3
    · -- `a = 2`: `b = 1 - (α - 1) ^ 2 < 1`, so `b ≤ 0`
      have hblt : (b : ℝ) < 1 := by rw [← hprod, hβeq, ← h2]; push_cast; nlinarith
      have : b < 1 := by exact_mod_cast hblt
      have hb0 : (b : ℝ) ≤ 0 := by exact_mod_cast (by omega : b ≤ 0)
      rw [hsq, ← h2]; push_cast; nlinarith
    · -- `a ≥ 3`: `α > a - 1 ≥ 2` and `|b| < α`
      have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h3
      have hαbig : 2 < α := by rw [hβeq] at hβ2; linarith
      have hblt : (b : ℝ) < α := by rw [← hprod]; nlinarith
      rw [hsq]; nlinarith

/-- `α ^ N + 1 ≤ α ^ (N + 1)` for `N ≥ 1`. -/
theorem pow_succ_ge (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) {N : ℕ} (hN : 1 ≤ N) : α ^ N + 1 ≤ α ^ (N + 1) := by
  have hg := golden_le_sq a b hsum hprod hα hβ
  have hone : (1 : ℝ) ≤ α ^ (N - 1) := one_le_pow₀ hα.le
  have hNe : N - 1 + 2 = N + 1 := by omega
  have key : α ^ (N - 1) * (α + 1) ≤ α ^ (N - 1) * α ^ 2 := by
    exact mul_le_mul_of_nonneg_left hg (by positivity)
  have e1 : α ^ (N - 1) * α ^ 2 = α ^ (N + 1) := by rw [← pow_add, hNe]
  have e2 : α ^ (N - 1) * α = α ^ N := by
    rw [← pow_succ]; congr 1; omega
  nlinarith [key, e1, e2]

/-- The floors `⌊α ^ N⌋` are strictly increasing in `N ≥ 1`. -/
theorem floor_pow_strictMono (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) {N N' : ℕ} (hN : 1 ≤ N) (hlt : N < N') :
    ⌊α ^ N⌋ < ⌊α ^ N'⌋ := by
  have hstep : α ^ N + 1 ≤ α ^ N' := by
    have h1 : α ^ (N + 1) ≤ α ^ N' := pow_le_pow_right₀ hα.le (by omega)
    linarith [pow_succ_ge a b hsum hprod hα hβ hN]
  have h2 : ⌊α ^ N⌋ + 1 ≤ ⌊α ^ N'⌋ := by
    have : (⌊α ^ N⌋ : ℝ) + 1 ≤ α ^ N' := by linarith [Int.floor_le (α ^ N)]
    exact_mod_cast Int.le_floor.2 (by push_cast; linarith)
  omega

/-! ### Step 1b (Lemma 2): the prime-as-modulus filter

If `p` is a prime not dividing `b = det C` and `M` annihilates the order of `C` mod `p`, then
`M ∣ N' - N` forces `p ∣ V_(N') - V_(N)`.  Splitting `M = c^A · o` and taking `j` with
`c^j ≡ 1 (mod o)` gives the periodicity along `R(n) = c^n + s` once `A ≤ n`.
-/

/-- Trace congruence from an order bound: `M ∣ N' - N` gives `p ∣ V_(N')(a,b) - V_N(a,b)`. -/
theorem lucasV_congr_of_order (a b : ℤ) {p : ℕ} (hp : p.Prime) (hpb : ¬ (p : ℤ) ∣ b)
    {M : ℕ} (hord : ∀ D : GL (Fin 2) (ZMod p),
      (D : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (Int.castRingHom (ZMod p)).mapMatrix (compMat a b) → orderOf D ∣ M)
    {N N' : ℕ} (hle : N ≤ N') (hdvd : M ∣ N' - N) :
    (p : ℤ) ∣ lucasV a b N' - lucasV a b N := by
  have := TheoremDGround.dvd_trace_sub_of_orderOf_dvd (compMat a b) hp
    (by simpa using hpb) hle (fun D hD => (hord D hD).trans hdvd)
  rwa [trace_compMat_pow, trace_compMat_pow] at this

/-- **Lemma 2 (the filter).**  With `A = v_c(M) ≤ n`, the values `V(c^(n+kj) + s)` are all
congruent to `V(c^n + s)` mod `p`, for a fixed period `j ≥ 1`. -/
theorem lucasV_stuck_period (a b : ℤ) {p : ℕ} (hp : p.Prime) (hpb : ¬ (p : ℤ) ∣ b)
    {c : ℕ} (hc : c.Prime) {M : ℕ} (hM0 : 0 < M)
    (hord : ∀ D : GL (Fin 2) (ZMod p),
      (D : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (Int.castRingHom (ZMod p)).mapMatrix (compMat a b) → orderOf D ∣ M)
    {n : ℕ} (hA : M.factorization c ≤ n) (s : ℕ) :
    ∃ j, 1 ≤ j ∧ ∀ k, 1 ≤ k →
      (p : ℤ) ∣ lucasV a b (c ^ (n + k * j) + s) - lucasV a b (c ^ n + s) := by
  set A := M.factorization c with hAdef
  set o := M / c ^ A with hodef
  have hsplit : c ^ A * o = M := by
    rw [hAdef, hodef]; exact Nat.ordProj_mul_ordCompl_eq_self M c
  have hcno : ¬ c ∣ o := by rw [hodef, hAdef]; exact Nat.not_dvd_ordCompl hc hM0.ne'
  have hopos : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h | h
    · rw [h, mul_zero] at hsplit; omega
    · exact h
  have hcop : Nat.Coprime c o := (Nat.Prime.coprime_iff_not_dvd hc).2 hcno
  refine ⟨o.totient, Nat.totient_pos.2 hopos, fun k hk => ?_⟩
  -- `o ∣ c ^ (k * totient o) - 1`
  have hpow : c ^ (k * o.totient) % o = 1 % o := by
    have h1 : c ^ o.totient ≡ 1 [MOD o] := Nat.ModEq.pow_totient hcop
    have := h1.pow k
    rw [← pow_mul, one_pow] at this
    rw [mul_comm k o.totient]
    exact this
  obtain ⟨Y, hY⟩ : ∃ Y, c ^ (k * o.totient) = Y + 1 := by
    have : 1 ≤ c ^ (k * o.totient) := Nat.one_le_pow _ _ hc.pos
    exact ⟨c ^ (k * o.totient) - 1, by omega⟩
  have hoY : o ∣ Y := by
    have h2 : Nat.ModEq o 1 (c ^ (k * o.totient)) := hpow.symm
    have h3 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ c ^ (k * o.totient))).1 h2
    rw [hY] at h3
    simpa using h3
  -- the exponent difference
  have hNN : c ^ (n + k * o.totient) + s - (c ^ n + s) = c ^ n * Y := by
    rw [pow_add, hY]; ring_nf; omega
  have hle : c ^ n + s ≤ c ^ (n + k * o.totient) + s := by
    have : c ^ n ≤ c ^ (n + k * o.totient) :=
      Nat.pow_le_pow_right hc.one_le (by omega)
    omega
  refine lucasV_congr_of_order a b hp hpb hord hle ?_
  rw [hNN, ← hsplit]
  exact Nat.mul_dvd_mul (pow_dvd_pow c hA) hoY

/-! ### `glCard` as a universal annihilator

Rather than track the exact order of `C` mod `p`, use `M = |GL_2(𝔽_p)| = glCard 2 p`: it
annihilates every element, and `Stuck n := v_c(glCard 2 p_n) ≤ n` is exactly the negation of the
hypothesis of the window lemma `TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard`.
So the good/stuck dichotomy needs no finer information. -/
theorem orderOf_dvd_glCard {p : ℕ} (hp : p.Prime) (D : GL (Fin 2) (ZMod p)) :
    orderOf D ∣ glCard 2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GL (Fin 2) (ZMod p)) = glCard 2 p := by
    rw [Matrix.card_GL_field]; simp [glCard, ZMod.card]
  rw [← hcard]
  exact orderOf_dvd_natCard D

theorem glCard_two_pos {p : ℕ} (hp : p.Prime) : 0 < glCard 2 p := by
  have h2 : 2 ≤ p := hp.two_le
  rw [glCard]
  refine Finset.prod_pos fun i _ => ?_
  have : p ^ (i : ℕ) < p ^ 2 := Nat.pow_lt_pow_right (by omega) i.isLt
  omega

/-! ### Step 1d: the stuck alternation

If `n` is stuck and the offset `ε` fails to change at `n + k j`, then the prime `p_n` divides the
strictly larger prime `p_(n+kj)` — impossible.  So `ε` alternates, which is exactly the hypothesis
`good_unbounded` needs. -/
theorem stuck_alternation (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hβ0 : β ≠ 0) (hb0 : b ≠ 0) {c : ℕ} (hc : c.Prime) {s : ℕ}
    {n₀ : ℕ} (hprime : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊).Prime)
    (hbig : ∀ m, n₀ ≤ m → |b| < (⌊α ^ (c ^ m + s)⌋₊ : ℤ))
    {n : ℕ} (hn : n₀ ≤ n)
    (hstuck : padicValNat c (glCard 2 (⌊α ^ (c ^ n + s)⌋₊)) ≤ n) :
    ∃ j, 1 ≤ j ∧ ∀ k, 1 ≤ k →
      (decide (0 < β ^ (c ^ (n + k * j) + s)) ≠ decide (0 < β ^ (c ^ n + s))) := by
  classical
  -- the floor, as an integer
  have hfl : ∀ m : ℕ, ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) = ⌊α ^ (c ^ m + s)⌋ := by
    intro m
    exact Int.natCast_floor_eq_floor (by positivity)
  have hcpos : ∀ x : ℕ, 1 ≤ c ^ x + s := fun x => by
    have := Nat.one_le_pow x c hc.pos; omega
  have hPp : (⌊α ^ (c ^ n + s)⌋₊).Prime := hprime n hn
  have hPb : ¬ ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ∣ b := by
    intro hd
    have := Int.le_of_dvd (abs_pos.2 hb0) ((dvd_abs _ _).2 hd)
    exact absurd (hbig n hn) (by omega)
  have hord : ∀ D : GL (Fin 2) (ZMod (⌊α ^ (c ^ n + s)⌋₊)),
      (D : Matrix (Fin 2) (Fin 2) (ZMod (⌊α ^ (c ^ n + s)⌋₊))) =
        (Int.castRingHom (ZMod (⌊α ^ (c ^ n + s)⌋₊))).mapMatrix (compMat a b) →
        orderOf D ∣ glCard 2 (⌊α ^ (c ^ n + s)⌋₊) :=
    fun D _ => orderOf_dvd_glCard hPp D
  have hA : (glCard 2 (⌊α ^ (c ^ n + s)⌋₊)).factorization c ≤ n := by
    rwa [Nat.factorization_def _ hc]
  obtain ⟨j, hj1, hjd⟩ :=
    lucasV_stuck_period a b hPp hPb hc (glCard_two_pos hPp) hord hA s
  refine ⟨j, hj1, fun k hk => ?_⟩
  intro heq
  have hmn : n < n + k * j := by
    have : 1 ≤ k * j := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hm0 : n₀ ≤ n + k * j := by omega
  have hiff : (0 < β ^ (c ^ (n + k * j) + s)) ↔ (0 < β ^ (c ^ n + s)) := decide_eq_decide.mp heq
  have hoff : (if 0 < β ^ (c ^ (n + k * j) + s) then (-1 : ℤ) else 0)
      = (if 0 < β ^ (c ^ n + s) then (-1 : ℤ) else 0) := by
    by_cases h : 0 < β ^ (c ^ n + s)
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hx => h (hiff.mp hx)), if_neg h]
  have he1 := floor_pow_eq_lucasV_add a b hsum hprod hβ hβ0
    (N := c ^ (n + k * j) + s) (hcpos _)
  have he2 := floor_pow_eq_lucasV_add a b hsum hprod hβ hβ0
    (N := c ^ n + s) (hcpos n)
  have hdvd : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ∣
      ⌊α ^ (c ^ (n + k * j) + s)⌋ - ⌊α ^ (c ^ n + s)⌋ := by
    rw [he1, he2, hoff]
    simpa using hjd k hk
  rw [← hfl (n + k * j), ← hfl n] at hdvd
  have hQp : (⌊α ^ (c ^ (n + k * j) + s)⌋₊).Prime := hprime _ hm0
  have hPQ : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ∣ ((⌊α ^ (c ^ (n + k * j) + s)⌋₊ : ℕ) : ℤ) := by
    have := dvd_add hdvd (dvd_refl ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ))
    simpa using this
  have hnat : (⌊α ^ (c ^ n + s)⌋₊) ∣ (⌊α ^ (c ^ (n + k * j) + s)⌋₊) := by exact_mod_cast hPQ
  have heqPQ := (Nat.prime_dvd_prime_iff_eq hPp hQp).1 hnat
  have hcm : c ^ n + s < c ^ (n + k * j) + s := by
    have : c ^ n < c ^ (n + k * j) := Nat.pow_lt_pow_right hc.one_lt hmn
    omega
  have hlt : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) < ((⌊α ^ (c ^ (n + k * j) + s)⌋₊ : ℕ) : ℤ) := by
    rw [hfl n, hfl (n + k * j)]
    exact floor_pow_strictMono a b hsum hprod hα hβ (hcpos n) hcm
  rw [heqPQ] at hlt
  exact lt_irrefl _ hlt

/-! ### Step 1c (Lemma 3): good indices are unbounded

Purely combinatorial.  `Stuck n` is any predicate such that a stuck `n` forces the offset `ε` to
*alternate* along an arithmetic progression starting at `n`; `TheoremDGround.not_stuck_twice`
then says two consecutive stuck indices `n`, `n + j n` are impossible, so non-stuck ("good")
indices occur arbitrarily late. -/
theorem good_unbounded {ε : ℕ → Bool} {Stuck : ℕ → Prop} {n₀ : ℕ}
    (halt : ∀ n, n₀ ≤ n → Stuck n → ∃ j, 1 ≤ j ∧ ∀ k, 1 ≤ k → ε (n + k * j) ≠ ε n) :
    ∀ m, ∃ n, n₀ ≤ n ∧ m ≤ n ∧ ¬ Stuck n := by
  classical
  intro m
  by_contra hcon
  push_neg at hcon
  set N := max n₀ m with hN
  have hstuck : ∀ x, N ≤ x → Stuck x := fun x hx =>
    hcon x (le_trans (le_max_left _ _) hx) (le_trans (le_max_right _ _) hx)
  -- a global choice of periods
  set j : ℕ → ℕ := fun x =>
    if h : ∃ i, 1 ≤ i ∧ ∀ k, 1 ≤ k → ε (x + k * i) ≠ ε x then h.choose else 1 with hjdef
  have hj1 : ∀ x, 1 ≤ j x := by
    intro x
    by_cases h : ∃ i, 1 ≤ i ∧ ∀ k, 1 ≤ k → ε (x + k * i) ≠ ε x
    · simp only [hjdef, dif_pos h]; exact h.choose_spec.1
    · simp only [hjdef, dif_neg h]
      exact le_rfl
  have hjspec : ∀ x, N ≤ x → ∀ k, 1 ≤ k → ε (x + k * j x) ≠ ε x := by
    intro x hx
    have h := halt x (le_trans (le_max_left _ _) hx) (hstuck x hx)
    simp only [hjdef, dif_pos h]
    exact h.choose_spec.2
  refine TheoremDGround.not_stuck_twice ε j hj1 N (hjspec N le_rfl) ?_
  exact hjspec (N + j N) (by omega)

/-! ### The window for `c = 2`

Phase 37's `pow_dvd_sub_or_add_of_lt_padicValNat` assumes `c` odd, because it uses that `c`
divides at most one of `p ∓ 1`.  At `c = 2` both are even, but `4` still divides at most one of
them (their difference is `2`), so `min(v_2(p-1), v_2(p+1)) = 1` and the same conclusion holds:
`k < 2a + b` with `min(a,b) = 1` gives `k/2 ≤ max(a,b)`. -/
theorem pow_dvd_sub_or_add_of_lt_padicValNat_all {c p k : ℕ} (hc : c.Prime)
    (hp : p.Prime) (hpc : p ≠ c) (hk : k < padicValNat c (glCard 2 p)) :
    (c : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (c : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  by_cases hc2 : c ≠ 2
  · exact FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 hp hpc hk
  push_neg at hc2
  subst hc2
  -- `p` is an odd prime
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : p ≠ 2 := hpc
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  set a := (p - 1).factorization 2 with ha
  set b := (p + 1).factorization 2 with hb
  rw [FibonacciPrimePow.padicValNat_glCard_two hc hp hpc] at hk
  -- `4` divides at most one of `p ∓ 1`
  have hmin : a ≤ 1 ∨ b ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    have hd1 : 4 ∣ p - 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2 (show 2 ≤ a by omega)
      simpa [show (2:ℕ)^2 = 4 from rfl] using this
    have hd2 : 4 ∣ p + 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2 (show 2 ≤ b by omega)
      simpa [show (2:ℕ)^2 = 4 from rfl] using this
    have hd : (4 : ℕ) ∣ 2 := by
      have hsub := Nat.dvd_sub hd2 hd1
      rwa [show p + 1 - (p - 1) = 2 from by omega] at hsub
    omega
  have hcast1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [this]; ring
  have hcast2 : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  rcases hmin with h | h
  · right
    have hkb : k / 2 ≤ b := by omega
    have hd : (2 : ℕ) ^ (k / 2) ∣ p + 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2 (by rw [← hb]; exact hkb)
    rw [← hcast2]
    exact_mod_cast Int.natCast_dvd_natCast.2 hd
  · left
    have hka : k / 2 ≤ a := by omega
    have hd : (2 : ℕ) ^ (k / 2) ∣ p - 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2 (by rw [← ha]; exact hka)
    rw [← hcast1]
    exact_mod_cast Int.natCast_dvd_natCast.2 hd

/-! ### Step 1e (Lemma 4): the window at a good index

At a good `n` the phase-37 lemma `pow_dvd_sub_or_add_of_lt_padicValNat` (odd `c`) gives
`p_n ≡ ±1 (mod c^(n/2))`, so `V(c^n + s) ≡ t (mod c^(n/2))` with `t = ω - ε ∈ {-1, 0, 1, 2}`. -/
theorem good_window (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hβ0 : β ≠ 0) {c : ℕ} (hc : c.Prime) {s n : ℕ}
    (hprime : (⌊α ^ (c ^ n + s)⌋₊).Prime) (hpc : (⌊α ^ (c ^ n + s)⌋₊) ≠ c)
    (hgood : n < padicValNat c (glCard 2 (⌊α ^ (c ^ n + s)⌋₊))) :
    ∃ t : ℤ, |t| ≤ 2 ∧ (c : ℤ) ^ (n / 2) ∣ lucasV a b (c ^ n + s) - t := by
  have hcpos : 1 ≤ c ^ n + s := by have := Nat.one_le_pow n c hc.pos; omega
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hfl : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) = ⌊α ^ (c ^ n + s)⌋ :=
    Int.natCast_floor_eq_floor (by positivity)
  have hoff := floor_pow_eq_lucasV_add a b hsum hprod hβ hβ0 hcpos
  set e : ℤ := (if 0 < β ^ (c ^ n + s) then (-1 : ℤ) else 0) with he
  have heb : |e| ≤ 1 := by rw [he]; split <;> simp
  have hV : lucasV a b (c ^ n + s) = ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) - e := by
    rw [hfl, hoff]; ring
  rcases pow_dvd_sub_or_add_of_lt_padicValNat_all hc hprime hpc hgood with h | h
  · refine ⟨1 - e, ?_, ?_⟩
    · rw [abs_le] at heb ⊢; omega
    · rw [hV]; simpa using h
  · refine ⟨-1 - e, ?_, ?_⟩
    · rw [abs_le] at heb ⊢; omega
    · rw [hV]
      have : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) - e - (-1 - e)
          = ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) + 1 := by ring
      rw [this]; exact h

/-! ### Step 1f: pigeonhole and growth -/

/-- **Pigeonhole.**  If arbitrarily late `n` carry *some* value `t` from a finite set `T`, then one
residue class `r (mod f)` and one value `t` carry arbitrarily late `n`. -/
theorem exists_class_frequently {T : Finset ℤ} {Q : ℕ → ℤ → Prop} {f : ℕ} (hf : 1 ≤ f)
    (h : ∀ m : ℕ, ∃ n, m ≤ n ∧ ∃ t ∈ T, Q n t) :
    ∃ r t, t ∈ T ∧ ∀ m : ℕ, ∃ n, m ≤ n ∧ n % f = r ∧ Q n t := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ r, ∀ t ∈ T, ∃ m, ∀ n, m ≤ n → n % f = r → ¬ Q n t`
  set bd : ℕ → ℤ → ℕ := fun r t =>
    if hh : ∃ m, ∀ n, m ≤ n → n % f = r → ¬ Q n t then hh.choose else 0 with hbdef
  have hbd : ∀ r, ∀ t ∈ T, ∀ n, bd r t ≤ n → n % f = r → ¬ Q n t := by
    intro r t htT n hn hr
    have hex : ∃ m, ∀ n, m ≤ n → n % f = r → ¬ Q n t := hcon r t htT
    simp only [hbdef, dif_pos hex] at hn
    exact hex.choose_spec n hn hr
  obtain ⟨n, hn, t, htT, hQ⟩ := h ((Finset.range f ×ˢ T).sup fun p => bd p.1 p.2)
  have hr : n % f ∈ Finset.range f := Finset.mem_range.2 (Nat.mod_lt _ hf)
  have hle : bd (n % f) t ≤ (Finset.range f ×ˢ T).sup fun p => bd p.1 p.2 :=
    Finset.le_sup (f := fun p : ℕ × ℤ => bd p.1 p.2)
      (Finset.mem_product.2 ⟨hr, htT⟩ : ((n % f, t) : ℕ × ℤ) ∈ Finset.range f ×ˢ T)
  exact hbd (n % f) t htT n (le_trans hle hn) rfl hQ

/-- The floors grow at least linearly in the index. -/
theorem index_le_floor (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) {c : ℕ} (hc : c.Prime) (s m : ℕ) :
    (m : ℤ) ≤ ⌊α ^ (c ^ m + s)⌋ := by
  have hcpos : ∀ x : ℕ, 1 ≤ c ^ x + s := fun x => by
    have := Nat.one_le_pow x c hc.pos; omega
  induction m with
  | zero =>
      have : (0 : ℝ) ≤ α ^ (c ^ 0 + s) := by positivity
      simpa using Int.floor_nonneg.2 this
  | succ m ih =>
      have hlt : c ^ m + s < c ^ (m + 1) + s := by
        have : c ^ m < c ^ (m + 1) := Nat.pow_lt_pow_right hc.one_lt (by omega)
        omega
      have := floor_pow_strictMono a b hsum hprod hα hβ (hcpos m) hlt
      push_cast
      omega

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

**The route taken here avoids number fields, completions and Teichmüller theory entirely.**
Write `T = x·I + y·C` for the (`c`-adic) Teichmüller limit of `C^(c^n)`; everything about `T`
that the proof uses is captured by three *integer polynomial equations* in `(x, y)`:

* `(x·I + y·C)^Q = I`, i.e. `A_Q(x,y) = 1` and `B_Q(x,y) = 0` where `(x·I+y·C)^N = A_N·I + B_N·C`;
* the linear relation `x·V_s + y·V_(s+1) = t`, which is `tr(T·C^s) = t`.

Step 2 (`torsion_congr_levels`) produces *integer* solutions of this system modulo `c^k` for every
`k`, with no `p`-adic numbers: take `X = C^(c^n)` for a large good `n`, and let `Q` be the
prime-to-`c` part of `|GL_2(𝔽_c)|`.

Step 3 (`exists_complex_of_all_levels`) transfers to `ℂ`.  This is where the `c`-adic and
archimedean worlds meet, and the mechanism replacing Teichmüller theory is the **Nullstellensatz
plus integrality**: if the system had no complex solution then `1` lies in the ideal it generates
over `ℚ`, so clearing denominators gives a *nonzero integer* `N` in the ideal over `ℤ`; evaluating
at a level-`k` solution forces `c^k ∣ N` for every `k`, which is absurd.

Then `u = x + yα` and `v = x + yβ` satisfy `u^Q = v^Q = 1` (so `‖u‖ = ‖v‖ = 1`) and
`u·α^s + v·β^s = x·V_s + y·V_(s+1) = t`. -/

/-- `(x·I + y·C)^N = A·I + B·C` for the companion matrix `C` of `X^2 - aX + b`; this computes the
pair `(A, B)` in any commutative ring. -/
def torsionPair {R : Type*} [CommRing R] (a b x y : R) : ℕ → R × R
  | 0 => (1, 0)
  | N + 1 =>
      let p := torsionPair a b x y N
      (p.1 * x - b * (p.2 * y), p.1 * y + p.2 * x + a * (p.2 * y))

/-- Evaluation at a root `z` of `X^2 - aX + b`: `A + B·z = (x + y·z)^N`. -/
theorem torsionPair_eval {R : Type*} [CommRing R] (a b x y z : R) (hz : z ^ 2 = a * z - b)
    (N : ℕ) :
    (torsionPair a b x y N).1 + (torsionPair a b x y N).2 * z = (x + y * z) ^ N := by
  induction N with
  | zero => simp [torsionPair]
  | succ N ih =>
      rw [pow_succ, ← ih, torsionPair]
      have : z * z = a * z - b := by rw [← hz]; ring
      simp only
      linear_combination (-((torsionPair a b x y N).2 * y)) * hz

/-- **Step 2 (levels).**  For every `k` there is an integer point of the torsion system modulo
`c^k`: take `X = C^(c^n)` for a large `n` in the residue class, and `Q` the prime-to-`c` part of
`|GL_2(𝔽_c)|`. -/
theorem torsion_congr_levels (a b : ℤ) {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b)
    (V : ℕ → ℤ) (hV : ∀ N, V N = lucasV a b N) {s r : ℕ} (t : ℤ)
    (hcong : ∀ m : ℕ, ∃ n, m ≤ n ∧ n % 2 = r ∧ (c : ℤ) ^ m ∣ V (c ^ n + s) - t) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ k : ℕ, ∃ x y : ℤ,
      (c : ℤ) ^ k ∣ (torsionPair a b x y Q).1 - 1 ∧
      (c : ℤ) ^ k ∣ (torsionPair a b x y Q).2 ∧
      (c : ℤ) ^ k ∣ x * V s + y * V (s + 1) - t := by
  sorry

/-- **Step 3 (transfer).**  A system of integer polynomial equations solvable modulo `c^k` for
every `k` has a complex solution — by the Nullstellensatz: otherwise `1` is in the ideal over `ℚ`,
hence a nonzero integer `N` is in the ideal over `ℤ`, and `c^k ∣ N` for all `k`. -/
theorem exists_complex_of_all_levels (a b : ℤ) {c : ℕ} (hc : c.Prime) {Q : ℕ}
    (w₁ w₂ t : ℤ)
    (hlev : ∀ k : ℕ, ∃ x y : ℤ,
      (c : ℤ) ^ k ∣ (torsionPair a b x y Q).1 - 1 ∧
      (c : ℤ) ^ k ∣ (torsionPair a b x y Q).2 ∧
      (c : ℤ) ^ k ∣ x * w₁ + y * w₂ - t) :
    ∃ x y : ℂ, (torsionPair (a : ℂ) (b : ℂ) x y Q).1 = 1 ∧
      (torsionPair (a : ℂ) (b : ℂ) x y Q).2 = 0 ∧
      x * (w₁ : ℂ) + y * (w₂ : ℂ) = (t : ℂ) := by
  sorry

/-- **The crux, assembled.**  Steps 2 and 3 together give the spectral identity: along the
residue class, the trace congruences force a pair of roots of unity `u, v` with
`u·α^s + v·β^s = t`. -/
theorem spectral_identity (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    (V : ℕ → ℤ) (hV : ∀ N, (V N : ℝ) = α ^ N + β ^ N)
    {s r : ℕ} (t : ℤ)
    (hcong : ∀ m : ℕ, ∃ n, m ≤ n ∧ n % 2 = r ∧ (c : ℤ) ^ m ∣ V (c ^ n + s) - t) :
    ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ u * (α : ℂ) ^ s + v * (β : ℂ) ^ s = (t : ℂ) := by
  -- identify `V` with the Lucas sequence
  have hVl : ∀ N, V N = lucasV a b N := by
    intro N
    have h1 := hV N
    have h2 := pow_add_pow_eq_lucasV a b hsum hprod N
    exact_mod_cast h1.trans h2
  obtain ⟨Q, hQ1, hlev⟩ := torsion_congr_levels a b hc hcb V hVl (r := r) t hcong
  obtain ⟨x, y, hx1, hx2, hx3⟩ :=
    exists_complex_of_all_levels a b hc (Q := Q) (V s) (V (s + 1)) t hlev
  -- the two roots, as complex numbers
  have hαq : ((α : ℂ)) ^ 2 = (a : ℂ) * (α : ℂ) - (b : ℂ) := by
    have : α ^ 2 = (a : ℝ) * α - (b : ℝ) := by rw [← hsum, ← hprod]; ring
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) this
  have hβq : ((β : ℂ)) ^ 2 = (a : ℂ) * (β : ℂ) - (b : ℂ) := by
    have : β ^ 2 = (a : ℝ) * β - (b : ℝ) := by rw [← hsum, ← hprod]; ring
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) this
  have hu : (x + y * (α : ℂ)) ^ Q = 1 := by
    rw [← torsionPair_eval (a : ℂ) (b : ℂ) x y _ hαq Q, hx1, hx2]; ring
  have hv : (x + y * (β : ℂ)) ^ Q = 1 := by
    rw [← torsionPair_eval (a : ℂ) (b : ℂ) x y _ hβq Q, hx1, hx2]; ring
  have hnorm : ∀ z : ℂ, z ^ Q = 1 → ‖z‖ = 1 := by
    intro z hz
    have h1 : ‖z‖ ^ Q = 1 := by rw [← norm_pow, hz, norm_one]
    have hQ0 : Q ≠ 0 := by omega
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg z) h hQ0))
    · exact h
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hQ0))
  refine ⟨x + y * (α : ℂ), x + y * (β : ℂ), hnorm _ hu, hnorm _ hv, ?_⟩
  -- the linear identity
  have hVs : ((V s : ℤ) : ℂ) = (α : ℂ) ^ s + (β : ℂ) ^ s := by
    have := hV s; exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) this
  have hVs1 : ((V (s + 1) : ℤ) : ℂ) = (α : ℂ) ^ (s + 1) + (β : ℂ) ^ (s + 1) := by
    have := hV (s + 1); exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) this
  rw [← hx3, hVs, hVs1]
  ring

/-- **Steps 2–5 combined.**  Along a residue class, the traces `V (c^n + s)` cannot be congruent
to a fixed small integer `t` modulo arbitrarily large powers of `c`.

This is fully proved from `spectral_identity` (the crux) and `spectral_ne_small_int` (step 5). -/
theorem not_congr_small_int (a b : ℤ) {α β : ℝ} (hsum : α + β = a) (hprod : α * β = b)
    (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    (V : ℕ → ℤ) (hV : ∀ N, (V N : ℝ) = α ^ N + β ^ N)
    {s r : ℕ} (hs : 4 ≤ s) {t : ℤ} (ht : |t| ≤ 2) :
    ¬ ∀ m : ℕ, ∃ n, m ≤ n ∧ n % 2 = r ∧ (c : ℤ) ^ m ∣ V (c ^ n + s) - t := by
  intro hcong
  obtain ⟨u, v, hu, hv, huv⟩ :=
    spectral_identity a b hsum hprod hα hβ hdisc hc hcb hcd V hV t hcong
  exact spectral_ne_small_int a b hsum hprod hα hβ hs hu hv ht huv

/-- **Theorem D, quadratic case.** -/
theorem floor_pow_prime_pow_add_not_prime (a b : ℤ) {α β : ℝ} (hsum : α + β = a)
    (hprod : α * β = b) (hα : 1 < α) (hβ : |β| < 1) (hdisc : ¬ IsSquare (a ^ 2 - 4 * b))
    {c : ℕ} (hc : c.Prime) (hcb : ¬ (c : ℤ) ∣ b) (hcd : ¬ (c : ℤ) ∣ a ^ 2 - 4 * b)
    {s : ℕ} (hs : 4 ≤ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  classical
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 hcon
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hcb (dvd_zero _)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hprod
    exact hb0 (by exact_mod_cast hprod.symm)
  -- all indices past `n₀` are prime, big, and different from `c`
  set n₀ := max n₁ (max (|b|.toNat + 1) (c + 1)) with hn₀def
  have hidx : ∀ m : ℕ, (m : ℤ) ≤ ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) := by
    intro m
    rw [Int.natCast_floor_eq_floor (by positivity)]
    exact index_le_floor a b hsum hprod hα hβ hc s m
  have hprime : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊).Prime := by
    intro m hm
    have := hn₁ m (le_trans (le_max_left _ _) hm)
    simpa using this
  have hbig : ∀ m, n₀ ≤ m → |b| < ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) := by
    intro m hm
    have h1 : |b|.toNat + 1 ≤ m :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
    have h2 := hidx m
    have h3 : |b| = (|b|.toNat : ℤ) := (Int.toNat_of_nonneg (abs_nonneg b)).symm
    have h4 : ((|b|.toNat + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast h1
    push_cast at h4
    omega
  have hnec : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊) ≠ c := by
    intro m hm heq
    have h1 : c + 1 ≤ m :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
    have h2 := hidx m
    rw [heq] at h2
    have : ((c + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast h1
    push_cast at this
    omega
  -- good indices are unbounded
  have hgood := good_unbounded (ε := fun m => decide (0 < β ^ (c ^ m + s)))
    (Stuck := fun n => padicValNat c (glCard 2 (⌊α ^ (c ^ n + s)⌋₊)) ≤ n) (n₀ := n₀)
    (fun n hn hstuck =>
      stuck_alternation a b hsum hprod hα hβ hβ0 hb0 hc hprime hbig hn hstuck)
  -- the window at each good index, with values in a fixed finite set
  have hwin : ∀ m : ℕ, ∃ n, m ≤ n ∧ ∃ t ∈ Finset.Icc (-2 : ℤ) 2,
      (c : ℤ) ^ (n / 2) ∣ lucasV a b (c ^ n + s) - t := by
    intro m
    obtain ⟨n, hn0, hnm, hns⟩ := hgood m
    obtain ⟨t, ht, htd⟩ := good_window a b hsum hprod hα hβ hβ0 hc (hprime n hn0)
      (hnec n hn0) (not_le.1 hns)
    exact ⟨n, hnm, t, Finset.mem_Icc.2 (abs_le.1 ht), htd⟩
  obtain ⟨r, t, htT, hfreq⟩ := exists_class_frequently (f := 2) (by norm_num) hwin
  refine not_congr_small_int a b hsum hprod hα hβ hdisc hc hcb hcd (lucasV a b)
    (fun N => (pow_add_pow_eq_lucasV a b hsum hprod N).symm) (r := r) hs
    (abs_le.2 (Finset.mem_Icc.1 htT)) ?_
  intro m
  obtain ⟨n, hn, hr, hd⟩ := hfreq (2 * m)
  refine ⟨n, by omega, hr, dvd_trans (pow_dvd_pow (c : ℤ) (by omega)) hd⟩

end LeanFormalizations.Mills.TheoremDQuadratic
