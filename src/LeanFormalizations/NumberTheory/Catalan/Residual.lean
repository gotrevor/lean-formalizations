/-
# The weighted residual matrix has full column rank (Sun, Theorem 2.1) — algebraic core

Field-generic core of §2 of arXiv:2609.04176v1.  The theorem is stated for an **abstract tail
sequence** `T : ℕ → F` satisfying only Sun's recurrence `T m + T (m+1) = 1/(2m+1)^2`
(`IsTailSeq`): that recurrence is the *only* property of the Catalan tails the proof uses, so
the same theorem serves the real tails (`Statement.lean`, over `ℝ`) and the fake rational tails
built from a hypothetical `G = a/q` (`TwoAdic.lean`, over `ℚ`).

## Statement

`resid T B S` is the `(S+3) × S` matrix
`R_{a,j} = Σ_{i=0}^{a+2B} (-1)^i C(a+2B, i) Π_i · T_{i+j}/(2(i+j)+1)`   (paper (2.1)),
rows `a ∈ {0,…,S+2}`, columns `j ∈ {1,…,S}` (here `j = j'.val + 1` for `j' : Fin S`), with
`Π_i = ∏_{h=1}^{B} (2(h+i)+1)^2` (`normaliser B i`).  **`resid_rank`: `rank = S` for `B > S > 0`.**

## Proof plan (the paper's argument, with its two index slips repaired)

⚠️ The paper's write-up (pp. 4–6) expands `T_{i+j}` around `T_i` in (2.4)–(2.8) but its
polynomial `K` in (2.12) uses `(2X+3)^2`, which only annihilates the integers if the expansion is
around **`T_{i+1}`** (the recurrence gives `T_i + T_{i+1} = 1/(2i+1)^2`, not `1/(2i+3)^2`); and
its `P_λ` sums from `k = 0`, where `(2i+1)^2 ∤ Π_i`, so it is not a polynomial.  Both are fixed
by ONE change — expand around `T_{i+1}` with `k ≥ 1` (`IsTailSeq.shift`) — which is what the
paper's own page-4 display already does.  With that repair the argument is:

1. `IsTailSeq.shift`: `T_{i+j+1} = (-1)^j T_{i+1} + Σ_{1≤k≤j} (-1)^{j-k}/(2(i+k)+1)^2`.
2. Hence `f_i := Π_i Σ_j λ_j u_{i+j} = -T_{i+1}·D_λ(i) + P_λ(i)` with
   `D_λ(X) = Σ_j (-1)^j λ_j Π(X)/(2X+2j+1)` (degree ≤ 2B−1, `= L_S·E²·P*_λ` in the paper's
   notation, nonzero when `λ ≠ 0`) and `P_λ` a polynomial of degree ≤ 2B−3 (needs `j ≤ S < B`).
3. `λ` in the right kernel ⟹ the alternating binomial sums of `f` of orders `2B..2B+S+2`
   vanish (`alt_choose_sum_eval_eq_zero` kills the polynomial part) ⟹ `f` agrees on
   `{0,…,2B+S+2}` with a polynomial of degree ≤ 2B−1 (`exists_poly_of_alt_sums_eq_zero`).
4. `A(X) := f(X) − P_λ(X)` has degree ≤ 2B−1 and `A(i) = -T_{i+1} D_λ(i)` for `i ≤ 2B+S+2`, so
   `K(X) := (2X+3)^2 [A(X) D_λ(X+1) + A(X+1) D_λ(X)] + D_λ(X) D_λ(X+1)` vanishes at
   `i = 0,…,2B+S+1` (by the recurrence at `m = i+1`), at `X = −3/2` (a root of `D_λ`), and is
   divisible by `G₀ := gcd(D_λ(X), D_λ(X+1))` of degree `2B−S−2` (roots at negative
   half-integers `≠ −3/2`): `4B+1` zeros against `deg K ≤ 4B`, so `K = 0`.
5. `K = 0` with `D_λ ≠ 0` gives a rational function `R = A/D_λ` with
   `R(X) + R(X+1) = −1/(2X+3)^2` — impossible (`no_rational_solution`).  Hence `λ = 0`.
-/
import Mathlib

namespace LeanFormalizations.Catalan

open Finset Polynomial

variable {F : Type*} [Field F] [CharZero F]

/-- The normaliser `Π_i = ∏_{h=1}^{B} (2(h+i)+1)^2` of Theorem 2.1.  A product of **odd**
squares — the fact `TwoAdic.lean` turns against §9. -/
def normaliser (B i : ℕ) : ℕ := ∏ h ∈ Icc 1 B, (2 * (h + i) + 1) ^ 2

/-- Sun's recurrence (1.4) for an abstract tail sequence: `T m + T (m+1) = 1/(2m+1)^2`.  This is
the *whole* interface between analysis and the algebraic core. -/
def IsTailSeq (T : ℕ → F) : Prop := ∀ m, T m + T (m + 1) = 1 / (2 * (m : F) + 1) ^ 2

/-- The **weighted residual matrix** (paper (2.1)):
`R_{a,j} = Σ_{i=0}^{a+2B} (-1)^i C(a+2B,i) Π_i · T_{i+j}/(2(i+j)+1)`, `(S+3) × S`.
Column index `j' : Fin S` stands for the paper's `j = j'+1 ∈ {1,…,S}`. -/
noncomputable def resid (T : ℕ → F) (B S : ℕ) : Matrix (Fin (S + 3)) (Fin S) F :=
  fun a j => ∑ i ∈ range (a.val + 2 * B + 1),
    (-1 : F) ^ i * ((a.val + 2 * B).choose i : F) * (normaliser B i : F) *
      (T (i + j.val + 1) / (2 * ((i + j.val + 1 : ℕ) : F) + 1))

/-! ### Leaves of the proof plan (see the module docstring) -/

/-- **Finite-difference annihilation** (van Lint–Wilson (13.13)): the `n`-th alternating
binomial sum of a polynomial of degree `< n` vanishes.  Mathlib carries this as
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` + `fwdDiff_iter_eq_sum_shift`. -/
theorem alt_choose_sum_eval_eq_zero (P : F[X]) {n : ℕ} (hP : P.natDegree < n) :
    ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) * P.eval (i : F) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : F)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h
  rw [← mul_zero ((-1 : F) ^ n), ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  push_cast
  have hpow : (-1 : F) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  have hsq : ((-1 : F) ^ (n - k)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-((-1 : F) ^ k * (n.choose k : F) * P.eval (k : F))) * hsq
    - ((-1 : F) ^ (n - k) * (n.choose k : F) * P.eval (k : F)) * hpow

/-- **Corrected (2.3)**, expanded around `T_{i+1}`:
`T_{i+j+1} = (-1)^j T_{i+1} + Σ_{k=1}^{j} (-1)^{j-k} / (2(i+k)+1)^2`.  Induction on `j` from
the recurrence at `m = i + j`. -/
theorem IsTailSeq.shift {T : ℕ → F} (hT : IsTailSeq T) (i j : ℕ) :
    T (i + j + 1) = (-1 : F) ^ j * T (i + 1) +
      ∑ k ∈ Icc 1 j, (-1 : F) ^ (j - k) / (2 * ((i + k : ℕ) : F) + 1) ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hrec := hT (i + j + 1)
    have hsum' : ∑ k ∈ Icc 1 (j + 1), (-1 : F) ^ (j + 1 - k) / (2 * ((i + k : ℕ) : F) + 1) ^ 2
        = - ∑ k ∈ Icc 1 j, (-1 : F) ^ (j - k) / (2 * ((i + k : ℕ) : F) + 1) ^ 2
          + 1 / (2 * ((i + j + 1 : ℕ) : F) + 1) ^ 2 := by
      rw [Finset.sum_Icc_succ_top (by omega), ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk : k ≤ j := (Finset.mem_Icc.1 hk).2
        rw [show j + 1 - k = (j - k) + 1 by omega, pow_succ]
        ring
      · rw [show i + (j + 1) = i + j + 1 by ring]; simp
    rw [hsum', show i + (j + 1) + 1 = (i + j + 1) + 1 by ring, pow_succ]
    linear_combination hrec - ih

/-- **Newton-interpolation degree bound.**  A sequence on `{0,…,N}` whose alternating binomial
sums of every order `n ∈ [m, N]` vanish is the restriction of a polynomial of degree `< m`.
(Interpolate with `Lagrange.interpolate`, then read the vanishing sums as
`Δ^n P (0) = 0` via `fwdDiff_iter_eq_sum_shift`; Newton's formula
`shift_eq_sum_fwdDiff_iter` rebuilds `P` from `Δ^n P (0)`, `n < m`, on all of `ℕ`, and two
polynomials agreeing on `ℕ` are equal.) -/
theorem exists_poly_of_alt_sums_eq_zero (f : ℕ → F) (m N : ℕ)
    (h : ∀ n, m ≤ n → n ≤ N →
      ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) * f i = 0) :
    ∃ P : F[X], P.degree < m ∧ ∀ i ≤ N, P.eval (i : F) = f i := by
  -- the vanishing alternating sums are exactly `Δ^n f 0 = 0`
  have hΔ : ∀ n, m ≤ n → n ≤ N → (fwdDiff (1 : ℕ))^[n] f 0 = 0 := by
    intro n hmn hnN
    rw [fwdDiff_iter_eq_sum_shift]
    have h0 := h n hmn hnN
    rw [← mul_zero ((-1 : F) ^ n), ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    simp only [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul]
    push_cast
    have hpow : (-1 : F) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    have hsq : ((-1 : F) ^ (n - k)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    have hsqk : ((-1 : F) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-((-1 : F) ^ (n - k) * (n.choose k : F) * f k)) * hsqk
      - ((-1 : F) ^ k * (n.choose k : F) * f k) * hpow
  -- Newton's forward-difference polynomial, truncated at order `m`
  refine ⟨∑ k ∈ range m, C ((fwdDiff (1 : ℕ))^[k] f 0 / (k.factorial : F)) * descPochhammer F k, ?_, ?_⟩
  · refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (by simp)]
    intro k hk
    have hk : k < m := Finset.mem_range.1 hk
    calc (C ((fwdDiff (1 : ℕ))^[k] f 0 / (k.factorial : F)) * descPochhammer F k).degree
        ≤ ((C ((fwdDiff (1 : ℕ))^[k] f 0 / (k.factorial : F)) * descPochhammer F k).natDegree : ℕ) :=
          degree_le_natDegree
      _ ≤ ((descPochhammer F k).natDegree : WithBot ℕ) := by
          exact_mod_cast natDegree_C_mul_le _ _
      _ = k := by rw [descPochhammer_natDegree]
      _ < m := by exact_mod_cast hk
  · intro i hi
    have hN := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f i 0
    simp only [zero_add, smul_eq_mul, mul_one] at hN
    rw [hN, eval_finset_sum]
    have key : ∀ k, (C ((fwdDiff (1 : ℕ))^[k] f 0 / (k.factorial : F)) * descPochhammer F k).eval (i : F)
        = (i.choose k : F) * (fwdDiff (1 : ℕ))^[k] f 0 := by
      intro k
      rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      have hk : (k.factorial : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
      rw [div_mul_eq_mul_div, div_eq_iff hk]
      ring
    simp_rw [key]
    simp only [nsmul_eq_mul]
    -- both sides equal the sum over `range (m + i + 1)`
    have hL : ∑ k ∈ range m, (i.choose k : F) * (fwdDiff (1 : ℕ))^[k] f 0
        = ∑ k ∈ range (m + i + 1), (i.choose k : F) * (fwdDiff (1 : ℕ))^[k] f 0 := by
      refine Finset.sum_subset (Finset.range_mono (by omega : m ≤ m + i + 1))
        fun k hk hk' => ?_
      have hk' : m ≤ k := by simpa using hk'
      by_cases hki : k ≤ i
      · rw [hΔ k hk' (hki.trans hi), mul_zero]
      · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hR : ∑ k ∈ range (i + 1), (i.choose k : F) * (fwdDiff (1 : ℕ))^[k] f 0
        = ∑ k ∈ range (m + i + 1), (i.choose k : F) * (fwdDiff (1 : ℕ))^[k] f 0 := by
      refine Finset.sum_subset (Finset.range_mono (by omega : i + 1 ≤ m + i + 1))
        fun k hk hk' => ?_
      have hk' : i + 1 ≤ k := by simpa using hk'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [hL, hR]

/-- **The Gosper-style obstruction** (paper p. 6, sharpened and sign-agnostic): no rational
function `R = A/D` satisfies `R(X) + R(X+1) = c/(2X+3)^2` with `c ≠ 0`.
Proof: WLOG `gcd(A, D) = 1` (the identity is homogeneous of degree 2 in `(A, D)`).  Then
`D(X) ∣ (2X+3)^2 D(X+1)` and `D(X+1) ∣ (2X+3)^2 D(X)`.  In an algebraic closure pick a root
`α` of `D` with `α+1` not a root: it must be `−3/2`; pick a root `β` with `β−1` not a root: it
must be `−1/2`.  Every root class `α + ℤ` therefore has maximum `−3/2` and minimum `−1/2`,
absurd; so `D` is constant, and then `(2X+3)^2 (A(X)+A(X+1)) = c` fails at `X = −3/2`. -/
theorem no_rational_solution (A D : F[X]) (hD : D ≠ 0) (c : F) (hc : c ≠ 0)
    (h : (2 * X + 3) ^ 2 * (A * D.comp (X + 1) + A.comp (X + 1) * D) =
      C c * (D * D.comp (X + 1))) : False := by
  classical
  -- reduce to the coprime case
  suffices core : ∀ A D : F[X], D ≠ 0 → IsCoprime A D →
      (2 * X + 3) ^ 2 * (A * D.comp (X + 1) + A.comp (X + 1) * D) =
        C c * (D * D.comp (X + 1)) → False by
    set g := GCDMonoid.gcd A D with hg
    have hgA : g ∣ A := gcd_dvd_left A D
    have hgD : g ∣ D := gcd_dvd_right A D
    have hg0 : g ≠ 0 := fun h0 => hD (by simpa [h0] using hgD)
    have hgc0 : g.comp (X + 1) ≠ 0 := by
      intro h0
      rw [show (X + 1 : F[X]) = X + C 1 by simp, comp_X_add_C_eq_zero_iff] at h0
      exact hg0 h0
    obtain ⟨A', hA'⟩ := hgA
    obtain ⟨D', hD'⟩ := hgD
    have hD'0 : D' ≠ 0 := fun h0 => hD (by simp [hD', h0])
    have hcop : IsCoprime A' D' := by
      have := isCoprime_div_gcd_div_gcd (p := A) hD
      rwa [← hg, hA', hD', mul_div_cancel_left₀ _ hg0, mul_div_cancel_left₀ _ hg0] at this
    refine core A' D' hD'0 hcop ?_
    rw [hA', hD', mul_comp, mul_comp] at h
    have hne : g * g.comp (X + 1) ≠ 0 := mul_ne_zero hg0 hgc0
    apply mul_left_cancel₀ hne
    linear_combination h
  intro A D hD hcop h
  -- the two divisibilities
  have hD1 : D ∣ (2 * X + 3) ^ 2 * D.comp (X + 1) := by
    have : D ∣ (2 * X + 3) ^ 2 * D.comp (X + 1) * A := by
      refine ⟨C c * D.comp (X + 1) - (2 * X + 3) ^ 2 * A.comp (X + 1), ?_⟩
      linear_combination h
    exact hcop.symm.dvd_of_dvd_mul_right this
  have hcopc : IsCoprime (A.comp (X + 1)) (D.comp (X + 1)) := hcop.map (compRingHom (X + 1))
  have hD2 : D.comp (X + 1) ∣ (2 * X + 3) ^ 2 * D := by
    have : D.comp (X + 1) ∣ (2 * X + 3) ^ 2 * D * A.comp (X + 1) := by
      refine ⟨C c * D - (2 * X + 3) ^ 2 * A, ?_⟩
      linear_combination h
    exact hcopc.symm.dvd_of_dvd_mul_right this
  -- `D(-3/2) D(-1/2) = 0`
  have hroot : D.eval (-3 / 2 : F) = 0 ∨ D.eval (-1 / 2 : F) = 0 := by
    have := congrArg (eval (-3 / 2 : F)) h
    simp only [eval_mul, eval_pow, eval_add, eval_C, eval_X, eval_comp, eval_ofNat] at this
    norm_num at this
    rcases this with h1 | h2 | h3
    · exact absurd h1 hc
    · left; rw [show (-3 / 2 : F) = -(3 / 2) by norm_num]; exact h2
    · right; rw [show (-1 / 2 : F) = -(1 / 2) by norm_num]; exact h3
  have hinf : ∀ (g : ℕ → F), Function.Injective g → (∀ k : ℕ, D.eval (g k) = 0) → False := by
    intro g hg hb
    apply hD
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hg)
    rintro _ ⟨k, rfl⟩; exact hb k
  rcases hroot with h32 | h12
  · -- roots march down: `D(-3/2 - k) = 0`
    refine hinf (fun k : ℕ => -3 / 2 - (k : F)) (fun a b hab => by simpa using hab) fun k => ?_
    induction k with
    | zero => simpa using h32
    | succ k ih =>
      have hr : IsRoot (D.comp (X + 1)) (-3 / 2 - (k : F) - 1) := by
        simp only [IsRoot, eval_comp, eval_add, eval_X, eval_one]
        rw [show -3 / 2 - (k : F) - 1 + 1 = -3 / 2 - (k : F) by ring]; exact ih
      have := (dvd_iff_isRoot.2 hr).trans hD2
      rw [dvd_iff_isRoot, IsRoot, eval_mul, eval_pow, eval_add, eval_mul, eval_X, eval_ofNat,
        eval_ofNat] at this
      have hne : (2 * (-3 / 2 - (k : F) - 1) + 3) ^ 2 ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have : ((k : F) + 1) = 0 := by linear_combination -h0 / 2
        exact Nat.cast_add_one_ne_zero k this
      have := (mul_eq_zero.1 this).resolve_left hne
      rw [show (-3 / 2 - ((k + 1 : ℕ) : F)) = -3 / 2 - (k : F) - 1 by push_cast; ring]
      exact this
  · refine hinf (fun k : ℕ => -1 / 2 + (k : F)) (fun a b hab => by simpa using hab) fun k => ?_
    induction k with
    | zero => simpa using h12
    | succ k ih =>
      have hr : IsRoot D (-1 / 2 + (k : F)) := ih
      have := (dvd_iff_isRoot.2 hr).trans hD1
      rw [dvd_iff_isRoot, IsRoot, eval_mul, eval_pow, eval_add, eval_mul, eval_X, eval_ofNat,
        eval_ofNat, eval_comp, eval_add, eval_X, eval_one] at this
      have hne : (2 * (-1 / 2 + (k : F)) + 3) ^ 2 ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have : ((k : F) + 1) = 0 := by linear_combination h0 / 2
        exact Nat.cast_add_one_ne_zero k this
      have := (mul_eq_zero.1 this).resolve_left hne
      rw [show (-1 / 2 + ((k + 1 : ℕ) : F)) = -1 / 2 + (k : F) + 1 by push_cast; ring]
      exact this

/-! ### The crux, decomposed: explicit polynomials

Notation (all polynomials over `F`, `lin h := 2X + (2h+1)`):
* `bigPi B = ∏_{h=1}^{B} lin h ^ 2`, so `bigPi B` at `i` is `Π_i = normaliser B i`;
* `Lpoly S = ∏_{h=1}^{S} lin h`, `Epoly S B = ∏_{h=S+1}^{B} lin h`, `Wpoly = Lpoly * Epoly^2`,
  so `bigPi B = Wpoly * Lpoly` (`S ≤ B`) — `Wpoly` is the λ-independent part of `D_λ`;
* `Gpoly S B = ∏_{h=2}^{S+1} lin h * ∏_{h=S+2}^{B} lin h ^ 2` = `gcd(Wpoly(X), Wpoly(X+1))`:
  `Wpoly = lin 1 * lin (S+1) * Gpoly` and `Wpoly(X+1) = Gpoly * lin (B+1) ^ 2`;
* `Lsub S j = Lpoly S / lin (j+1)`, `Qpoly S λ = Σ_j (-1)^j λ_j Lsub S j` (degree `≤ S-1`,
  nonzero iff `λ ≠ 0`), `Dpoly = Wpoly * Qpoly` = the paper's `D_λ` (up to sign convention);
* `Psub B j k = bigPi B / (lin (j+1) * lin k ^ 2)` for `1 ≤ k ≤ j < S`, and
  `Ppoly = Σ_j Σ_{k=1}^{j} λ_j (-1)^{j-k} Psub B j k` = the polynomial part `P_λ`;
* `rowFun T B S λ i = Π_i Σ_j λ_j T_{i+j+1}/(2(i+j+1)+1)` = the paper's `f_i`, and
  `rowFun i = T_{i+1} · Dpoly(i) + Ppoly(i)` (`rowFun_eq`);
* `Kpoly S B A Q` = the paper's `K` divided by its forced factor `lin 1 * Gpoly`: it has degree
  `≤ 2B+S+1` and vanishes at `0, …, 2B+S+1`, hence is `0`. -/

/-- `lin h = 2X + (2h+1)`; `lin 1 = 2X + 3`, and `(lin h)(X+1) = lin (h+1)`. -/
noncomputable def lin (h : ℕ) : F[X] := C 2 * X + C (2 * (h : F) + 1)

@[simp] lemma lin_eval (h : ℕ) (x : F) : (lin h).eval x = 2 * x + (2 * h + 1) := by
  simp [lin]

lemma lin_one : (lin 1 : F[X]) = 2 * X + 3 := by
  simp only [lin, Nat.cast_one]
  rw [show (2 * (1 : F) + 1) = 3 by norm_num, show (C 2 : F[X]) = 2 from C_ofNat 2,
    show (C 3 : F[X]) = 3 from C_ofNat 3]

lemma lin_comp_X_add_one (h : ℕ) : (lin h : F[X]).comp (X + 1) = lin (h + 1) := by
  simp only [lin, add_comp, mul_comp, C_comp, X_comp]
  rw [mul_add, mul_one, add_assoc, ← C_add]
  congr 2
  push_cast
  ring

omit [CharZero F] in
lemma natDegree_lin_le (h : ℕ) : (lin h : F[X]).natDegree ≤ 1 := by
  unfold lin
  refine (natDegree_add_le _ _).trans ?_
  simp only [natDegree_C, max_le_iff, zero_le, and_true]
  exact (natDegree_C_mul_le _ _).trans (by simp)

lemma lin_ne_zero (h : ℕ) : (lin h : F[X]) ≠ 0 := by
  intro h0
  have := congrArg (eval (0 : F)) h0
  simp at this
  have : ((2 * h : ℕ) : F) + 1 = 0 := by push_cast; linear_combination this
  exact Nat.cast_add_one_ne_zero _ this

lemma lin_eval_nat_ne_zero (h i : ℕ) : (lin h : F[X]).eval (i : F) ≠ 0 := by
  rw [lin_eval]
  have : (2 * (i : F) + (2 * h + 1)) = ((2 * i + 2 * h : ℕ) : F) + 1 := by push_cast; ring
  rw [this]
  exact Nat.cast_add_one_ne_zero _

/-- `bigPi B = ∏_{h=1}^{B} lin h ^ 2`; at `i` this is `Π_i`. -/
noncomputable def bigPi (B : ℕ) : F[X] := ∏ h ∈ Ico 1 (B + 1), lin h ^ 2

lemma bigPi_eval (B i : ℕ) : (bigPi B : F[X]).eval (i : F) = (normaliser B i : F) := by
  sorry

noncomputable def Lpoly (S : ℕ) : F[X] := ∏ h ∈ Ico 1 (S + 1), lin h
noncomputable def Epoly (S B : ℕ) : F[X] := ∏ h ∈ Ico (S + 1) (B + 1), lin h
noncomputable def Wpoly (S B : ℕ) : F[X] := Lpoly S * Epoly S B ^ 2
noncomputable def Gpoly (S B : ℕ) : F[X] :=
  (∏ h ∈ Ico 2 (S + 2), lin h) * ∏ h ∈ Ico (S + 2) (B + 1), lin h ^ 2

lemma bigPi_eq_Wpoly_mul_Lpoly {S B : ℕ} (hSB : S ≤ B) :
    (bigPi B : F[X]) = Wpoly S B * Lpoly S := by
  sorry

lemma Wpoly_eq {S B : ℕ} (hS : 0 < S) (hSB : S < B) :
    (Wpoly S B : F[X]) = lin 1 * lin (S + 1) * Gpoly S B := by
  sorry

lemma Wpoly_comp {S B : ℕ} (hS : 0 < S) (hSB : S < B) :
    (Wpoly S B : F[X]).comp (X + 1) = Gpoly S B * lin (B + 1) ^ 2 := by
  sorry

lemma Wpoly_ne_zero (S B : ℕ) : (Wpoly S B : F[X]) ≠ 0 := by
  sorry

lemma natDegree_Gpoly_le {S B : ℕ} (hSB : S + 1 ≤ B) :
    (Gpoly S B : F[X]).natDegree ≤ 2 * B - S - 2 := by
  sorry

/-- `Lsub S j = Lpoly S / lin (j+1)` (for `j < S`). -/
noncomputable def Lsub (S j : ℕ) : F[X] := ∏ h ∈ (Ico 1 (S + 1)).erase (j + 1), lin h

lemma Lpoly_eq_lin_mul_Lsub {S j : ℕ} (hj : j < S) :
    (Lpoly S : F[X]) = lin (j + 1) * Lsub S j := by
  sorry

lemma natDegree_Lsub_le {S j : ℕ} (hj : j < S) : (Lsub S j : F[X]).natDegree ≤ S - 1 := by
  sorry

/-- `Qpoly S λ = Σ_j (-1)^j λ_j Lsub S j`: the λ-dependent factor of `D_λ`. -/
noncomputable def Qpoly (S : ℕ) (lam : Fin S → F) : F[X] :=
  ∑ j : Fin S, C ((-1) ^ j.val * lam j) * Lsub S j.val

lemma natDegree_Qpoly_le (S : ℕ) (lam : Fin S → F) : (Qpoly S lam).natDegree ≤ S - 1 := by
  sorry

/-- `Qpoly` at `X = -(2j+3)/2` is `(-1)^j λ_j ∏_{h ≠ j+1} (2h - 2j - 3) ≠ 0` for `λ_j ≠ 0`. -/
lemma Qpoly_ne_zero {S : ℕ} {lam : Fin S → F} (hlam : lam ≠ 0) : Qpoly S lam ≠ 0 := by
  sorry

/-- `Dpoly = Wpoly * Qpoly`: the paper's `D_λ`. -/
noncomputable def Dpoly (S B : ℕ) (lam : Fin S → F) : F[X] := Wpoly S B * Qpoly S lam

/-- `Psub B j k = bigPi B / (lin (j+1) * lin k ^ 2)`. -/
noncomputable def Psub (B j k : ℕ) : F[X] :=
  lin (j + 1) * ∏ h ∈ ((Ico 1 (B + 1)).erase (j + 1)).erase k, lin h ^ 2

lemma bigPi_eq_Psub {B j k : ℕ} (hj : j + 1 ≤ B) (hk : 1 ≤ k) (hkj : k ≤ j) :
    (bigPi B : F[X]) = lin (j + 1) * lin k ^ 2 * Psub B j k := by
  sorry

lemma natDegree_Psub_lt {B j k : ℕ} (hj : j + 1 ≤ B) : (Psub B j k : F[X]).natDegree < 2 * B := by
  sorry

/-- The polynomial part `P_λ`. -/
noncomputable def Ppoly (B S : ℕ) (lam : Fin S → F) : F[X] :=
  ∑ j : Fin S, ∑ k ∈ Icc 1 j.val, C (lam j * (-1) ^ (j.val - k)) * Psub B j.val k

lemma natDegree_Ppoly_lt {B S : ℕ} (hSB : S < B) (lam : Fin S → F) :
    (Ppoly B S lam).natDegree < 2 * B := by
  sorry

/-- The paper's `f_i = Π_i Σ_j λ_j u_{i+j}`. -/
noncomputable def rowFun (T : ℕ → F) (B S : ℕ) (lam : Fin S → F) (i : ℕ) : F :=
  (normaliser B i : F) *
    ∑ j : Fin S, lam j * (T (i + j.val + 1) / (2 * ((i + j.val + 1 : ℕ) : F) + 1))

/-- Row `a` of `resid ⬝ λ` is the alternating binomial sum of order `a + 2B` of `rowFun`. -/
lemma mulVec_resid_eq (T : ℕ → F) (B S : ℕ) (lam : Fin S → F) (a : Fin (S + 3)) :
    (resid T B S).mulVec lam a =
      ∑ i ∈ range (a.val + 2 * B + 1),
        (-1 : F) ^ i * ((a.val + 2 * B).choose i : F) * rowFun T B S lam i := by
  sorry

/-- **Step 2 of the plan**: `f_i = T_{i+1} D_λ(i) + P_λ(i)`. -/
lemma rowFun_eq {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hSB : S < B) (lam : Fin S → F)
    (i : ℕ) :
    rowFun T B S lam i = T (i + 1) * (Dpoly S B lam).eval (i : F) + (Ppoly B S lam).eval (i : F) := by
  sorry

/-- **Step 3**: in the kernel, the alternating sums of `g_i := T_{i+1} D_λ(i)` of orders
`2B, …, 2B+S+2` vanish, so `g` is a polynomial of degree `< 2B` on `{0, …, 2B+S+2}`. -/
lemma exists_interp {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hSB : S < B) (lam : Fin S → F)
    (h : (resid T B S).mulVec lam = 0) :
    ∃ A : F[X], A.natDegree < 2 * B ∧
      ∀ i ≤ 2 * B + S + 2, A.eval (i : F) = T (i + 1) * (Dpoly S B lam).eval (i : F) := by
  sorry

/-- The paper's `K` with its forced factor `lin 1 * Gpoly` removed. -/
noncomputable def Kpoly (S B : ℕ) (A Q : F[X]) : F[X] :=
  lin 1 * (A * lin (B + 1) ^ 2 * Q.comp (X + 1) + A.comp (X + 1) * lin 1 * lin (S + 1) * Q)
    - lin (S + 1) * lin (B + 1) ^ 2 * Gpoly S B * Q * Q.comp (X + 1)

lemma natDegree_Kpoly_le {S B : ℕ} (hS : 0 < S) (hSB : S < B) {A Q : F[X]}
    (hA : A.natDegree < 2 * B) (hQ : Q.natDegree ≤ S - 1) :
    (Kpoly S B A Q).natDegree ≤ 2 * B + S + 1 := by
  sorry

/-- **Step 4**: `K` vanishes at `0, …, 2B+S+1` by the recurrence at `m = i+1`. -/
lemma Kpoly_eval_eq_zero {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S) (hSB : S < B)
    (lam : Fin S → F) {A : F[X]}
    (hA : ∀ i ≤ 2 * B + S + 2, A.eval (i : F) = T (i + 1) * (Dpoly S B lam).eval (i : F))
    (i : ℕ) (hi : i ≤ 2 * B + S + 1) :
    (Kpoly S B A (Qpoly S lam)).eval (i : F) = 0 := by
  sorry

lemma Kpoly_eq_zero {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S) (hSB : S < B)
    (lam : Fin S → F) {A : F[X]} (hAdeg : A.natDegree < 2 * B)
    (hA : ∀ i ≤ 2 * B + S + 2, A.eval (i : F) = T (i + 1) * (Dpoly S B lam).eval (i : F)) :
    Kpoly S B A (Qpoly S lam) = 0 := by
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (f := fun i : Fin (2 * B + S + 2) => (i.val : F)) ?_ ?_ ?_
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro i
    exact Kpoly_eval_eq_zero hT hS hSB lam hA i.val (by omega)
  · rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le (natDegree_Kpoly_le hS hSB hAdeg (natDegree_Qpoly_le S lam))

/-- **Step 5**: `K = 0` is the rational-function identity `R(X) + R(X+1) = 1/(2X+3)^2` for
`R = A / D_λ`, in the polynomial form `no_rational_solution` consumes. -/
lemma key_identity {S B : ℕ} (hS : 0 < S) (hSB : S < B) {A Q : F[X]}
    (hK : Kpoly S B A Q = 0) :
    (2 * X + 3) ^ 2 * (A * (Wpoly S B * Q).comp (X + 1) + A.comp (X + 1) * (Wpoly S B * Q)) =
      C 1 * ((Wpoly S B * Q) * (Wpoly S B * Q).comp (X + 1)) := by
  rw [mul_comp, Wpoly_comp hS hSB, Wpoly_eq hS hSB, C_1, one_mul, ← lin_one]
  unfold Kpoly at hK
  linear_combination (lin 1 * Gpoly S B) * hK

/-- **The crux** (steps 2–5 of the plan): the right kernel of `resid T B S` is trivial. -/
theorem resid_mulVec_eq_zero {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S)
    (hBS : S < B) (lam : Fin S → F) (h : (resid T B S).mulVec lam = 0) : lam = 0 := by
  by_contra hlam
  obtain ⟨A, hAdeg, hA⟩ := exists_interp hT hBS lam h
  have hK := Kpoly_eq_zero hT hS hBS lam hAdeg hA
  have hD : Wpoly S B * Qpoly S lam ≠ 0 := mul_ne_zero (Wpoly_ne_zero S B) (Qpoly_ne_zero hlam)
  exact no_rational_solution A _ hD 1 one_ne_zero (key_identity hS hBS hK)

/-- **Theorem 2.1** for an abstract tail sequence: `rank (resid T B S) = S` when `B > S > 0`.
Wiring: trivial right kernel ⟹ `mulVecLin` injective ⟹ `rank = finrank (Fin S → F) = S`. -/
theorem resid_rank (T : ℕ → F) (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    (resid T B S).rank = S := by
  have hinj : Function.Injective (resid T B S).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro lam hlam
    exact resid_mulVec_eq_zero hT hS hBS lam hlam
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

end LeanFormalizations.Catalan
