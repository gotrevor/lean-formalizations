/-
# The generic frame: what ANY Apéry/Nesterenko-style attack on `G` must supply (Phase 3)

Phase 1 (`Residual`, `TwoAdic`, `Statement`) settled what survives of arXiv:2609.04176v1 and
kernel-checked why its §3–§9 cannot work.  This file plants the **frame** those sections were
trying to fill, stated so that a corrected construction (a v2, or anyone else's) drops into
slots instead of restarting:

* **W — wiring** (`irrational_of_forms`): the sink edge, once.  A family of integers
  `N_B(a,q)`, nonzero under `x = a/q` and tending to `0`, forces `Irrational x`.
* **E — integrality** (`resid_fakeTail_den`, `det_resid_fakeTail_den`, `abs_det_ge_of_rational`):
  the exact, `F_B`-free integerizer of the residual matrix under a hypothetical `G = a/q`, and
  the resulting lower bound `|det R[A,J]| ≥ 1/(q·L)^S` — the no-go of `TwoAdic.lean` with the
  factorial removed.  This is the arithmetic half of any ledger.
* **D — the real place** (`alt_choose_sum_inv_eq`, `alt_choose_sum_inv_sq_eq`,
  `alt_choose_sum_div_sq`, `resid_tail_eq`): the Beta identity and its square, the `n`-th
  finite difference of a rational function `p(i)/(i+c)^2` in closed form, and from it an exact
  closed form for the entries of the residual matrix at the TRUE tails.  This is the analytic
  half of any ledger; every asymptotic estimate starts from `resid_tail_eq`.
* **The frontier, stated honestly** (`SmallForms`, `catalan_irrational_of_smallForms`): *if* the
  true-tail minors were smaller than the integrality floor, `G` would be irrational.  The host
  probe (`papers/sun-2026-catalan-twoadic-check.py ledger`) says the minors of THIS construction
  are not — `log|N_B| ≈ +3.4·S·B` and growing — so `SmallForms` is (numerically) false for Sun's
  weights.  **Nothing in this file proves, or should ever claim, `Irrational catalanConst`.**
  `SmallForms` is a `def … : Prop`, never a theorem.

## Proof plans

* `irrational_of_forms`: by contradiction; `x = a/q` gives `N a q B ≠ 0` for all `B`, so
  `1 ≤ |N a q B|` (`Int.one_le_abs`), contradicting `Tendsto … (nhds 0)`
  (`Filter.Tendsto.eventually_lt_const` / `eventually_atTop`).
* `alt_choose_sum_inv_eq`: induction on `n` with the Pascal rule, or the partial-fraction
  identity `1/((x+i)) − 1/(x+i+1)` telescoping; mathlib may have it near
  `Finset.sum_range_choose` / `Nat.choose_mul_succ_eq`.  Field `F` of characteristic zero.
* `alt_choose_sum_inv_sq_eq`: formally differentiate the previous identity in `x`
  (`Polynomial`/`derivative` route), or prove directly by the same induction.
* `alt_choose_sum_div_sq`: write `p = poly·(X+c)^2 + α(X+c) + β` (`Polynomial.modByMonic` /
  `divByMonic` twice, `α = p'(−c)`, `β = p(−c)`); the `poly` part dies by
  `alt_choose_sum_eval_eq_zero` (`Residual.lean`) since `natDegree poly < n`; the two pole terms
  are the previous two lemmas.
* `resid_tail_eq`: unfold `resid`, `tail`; `normaliser B i / (2(i+j+1)+1) = (redPi B (j+1)).eval i`
  (`bigPi_eval`, exact division since `lin (j+1) ∣ bigPi B` for `j+1 ≤ B`);
  `1/(2(m+r)+1)^2 = (1/4)/(i + (j + r + 3/2))^2`; swap the finite sum over `i` with the `tsum`
  over `r` (`tsum_finset_sum` needs `summable_tailTerm`-style summability of each column, i.e.
  `Summable (fun r => 1/(r + c)^2)`), then `alt_choose_sum_div_sq` termwise with `c = j+r+3/2`
  and `natDegree (redPi B (j+1)) = 2B − 1 ≤ a + 2B + 1`.
* `resid_fakeTail_den`: each entry is `Σ_i (−1)^i C(n,i) Π_i · (±(a/q − S_{i+j}))/(2(i+j+1)+1)`;
  `q·(a/q) = a`; the partial sum `S_{i+j}` has denominators `(2k+1)^2`, `k ≤ i+j ≤ a+2B+S`, all
  dividing `oddLcm (a+2B+S)^2`; `2(i+j+1)+1 ∣ normaliser B i` (`h = j+1 ≤ B`).  Work in `ℚ` with
  `Rat.den` or with an `IsInt`-style predicate like `OddDen` in `TwoAdic.lean`.
* `det_resid_fakeTail_den`: `Matrix.det_apply` (Leibniz) — each product has `S` factors, each a
  multiple of `1/(q·L)` with `L = oddLcm (2B+2S+2)` (which dominates every row's index).
* `abs_det_ge_of_rational`: `exists_row_set_det_ne_zero` (`Statement.lean`) over `ℚ` gives `A`
  with `det ≠ 0`; `det_resid_fakeTail_den` gives `det = z/(qL)^S` with `z ∈ ℤ`, `z ≠ 0`, so
  `|det| ≥ 1/(qL)^S` (`Int.one_le_abs`).
* `catalan_irrational_of_smallForms`: assume `G = a/q`; `fakeTail_eq_tail_of_catalan_eq` turns the
  true-tail minor into the fake-tail minor (cast `ℚ → ℝ` through `resid`, entrywise, then
  `RingHom.map_det`); `abs_det_ge_of_rational` contradicts the hypothesis.
-/
import Mathlib
import LeanFormalizations.NumberTheory.Catalan.Tails
import LeanFormalizations.NumberTheory.Catalan.Residual
import LeanFormalizations.NumberTheory.Catalan.TwoAdic
import LeanFormalizations.NumberTheory.Catalan.Statement

namespace LeanFormalizations.Catalan

open Finset Polynomial Filter Topology

/-! ### W — wiring: the sink edge -/

/-- **W.**  If a family of integers `N a q B` is nonzero whenever `x = a/q` (`q > 0`) and
tends to `0` in `B`, then `x` is irrational.  This is the whole of §9's logic, once. -/
theorem irrational_of_forms (x : ℝ) (N : ℤ → ℤ → ℕ → ℤ)
    (hne : ∀ a q : ℤ, 0 < q → x = (a : ℝ) / q → ∀ B, N a q B ≠ 0)
    (hsmall : ∀ a q : ℤ, 0 < q → x = (a : ℝ) / q →
      Tendsto (fun B => ((|N a q B| : ℤ) : ℝ)) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, hr⟩
  have hq : (0 : ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  have hx : x = (r.num : ℝ) / ((r.den : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def]; push_cast; rfl
  have h1 := hne _ _ hq hx
  have h2 := hsmall _ _ hq hx
  obtain ⟨B, hB⟩ := (h2.eventually (gt_mem_nhds zero_lt_one)).exists
  have h3 : (1 : ℤ) ≤ |N r.num r.den B| := Int.one_le_abs (h1 B)
  have h4 : (1 : ℝ) ≤ ((|N r.num r.den B| : ℤ) : ℝ) := by exact_mod_cast h3
  linarith


/-! ### D — the real place: Beta identities and the closed form of the true entries -/

variable {F : Type*} [Field F] [CharZero F]

/-- **D1 (Beta identity).**  `Σ_{i≤n} (−1)^i C(n,i)/(x+i) = n!/∏_{i≤n}(x+i)`. -/
theorem alt_choose_sum_inv_eq (x : F) (n : ℕ) (hx : ∀ i ∈ range (n + 1), x + i ≠ 0) :
    ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) / (x + i) =
      (n.factorial : F) / ∏ i ∈ range (n + 1), (x + i) := by
  sorry

/-- **D2 (squared Beta identity).**
`Σ_{i≤n} (−1)^i C(n,i)/(x+i)^2 = n!/∏_{i≤n}(x+i) · Σ_{i≤n} 1/(x+i)`  (minus the `x`-derivative
of D1). -/
theorem alt_choose_sum_inv_sq_eq (x : F) (n : ℕ) (hx : ∀ i ∈ range (n + 1), x + i ≠ 0) :
    ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) / (x + i) ^ 2 =
      (n.factorial : F) / (∏ i ∈ range (n + 1), (x + i)) *
        ∑ i ∈ range (n + 1), 1 / (x + i) := by
  sorry

/-- **D4 (finite difference of a rational function).**  For a polynomial `p` with
`natDegree p ≤ n + 1` and `c` avoiding `−0, …, −n`,
`Σ_{i≤n} (−1)^i C(n,i) p(i)/(i+c)^2 = n!/∏(i+c) · (p'(−c) + p(−c) Σ 1/(i+c))`.
The polynomial part of `p/(X+c)^2` has degree `< n` and is annihilated
(`alt_choose_sum_eval_eq_zero`); the two pole terms are D1 and D2. -/
theorem alt_choose_sum_div_sq (p : F[X]) (n : ℕ) (hp : p.natDegree ≤ n + 1) (c : F)
    (hc : ∀ i ∈ range (n + 1), (i : F) + c ≠ 0) :
    ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) * p.eval (i : F) / ((i : F) + c) ^ 2 =
      (n.factorial : F) / (∏ i ∈ range (n + 1), ((i : F) + c)) *
        (p.derivative.eval (-c) + p.eval (-c) * ∑ i ∈ range (n + 1), 1 / ((i : F) + c)) := by
  sorry

/-- `Π / (2X + 2j + 1)`: the normaliser polynomial with one copy of the `h = j` factor removed
(exact division in `F[X]` for `1 ≤ j ≤ B`, since `lin j ^ 2 ∣ bigPi B`). -/
noncomputable def redPi (B j : ℕ) : F[X] := bigPi B / lin j

lemma lin_dvd_bigPi {B j : ℕ} (hj : 1 ≤ j) (hjB : j ≤ B) : (lin j : F[X]) ∣ bigPi B := by
  sorry

lemma redPi_mul_lin {B j : ℕ} (hj : 1 ≤ j) (hjB : j ≤ B) :
    (redPi B j : F[X]) * lin j = bigPi B := by
  sorry

lemma natDegree_redPi_le (B j : ℕ) : (redPi B j : F[X]).natDegree ≤ 2 * B := by
  sorry

/-- **D5 (closed form of the true residual entries).**  With `n = a + 2B`, `c_r = j + r + 3/2`
and `P = redPi B (j+1)`:
`R_{a,j} = Σ'_r (−1)^r · (1/4) · n!/∏_{i≤n}(i + c_r) · (P'(−c_r) + P(−c_r) Σ_{i≤n} 1/(i + c_r))`.
Numerically verified to 55 digits at `(B,S,a,j) = (2,1,0,0), (3,1,2,0), (3,2,1,1), (4,2,3,0)`
before freezing (2026-09-04).  Every real-place estimate starts here. -/
theorem resid_tail_eq {B S : ℕ} (hS : 0 < S) (hBS : S < B) (a : Fin (S + 3)) (j : Fin S) :
    resid tail B S a j = ∑' r : ℕ, (-1 : ℝ) ^ r * (1 / 4) *
      (((a.val + 2 * B).factorial : ℝ) /
          (∏ i ∈ range (a.val + 2 * B + 1), ((i : ℝ) + ((j.val : ℝ) + r + 3 / 2))) *
        ((redPi B (j.val + 1) : ℝ[X]).derivative.eval (-((j.val : ℝ) + r + 3 / 2)) +
          (redPi B (j.val + 1) : ℝ[X]).eval (-((j.val : ℝ) + r + 3 / 2)) *
            ∑ i ∈ range (a.val + 2 * B + 1), 1 / ((i : ℝ) + ((j.val : ℝ) + r + 3 / 2)))) := by
  sorry

/-! ### E — integrality: the exact `F_B`-free integerizer -/

/-- `L_n = lcm {1, 3, 5, …, 2n+1}`. -/
def oddLcm (n : ℕ) : ℕ := (range (n + 1)).lcm fun k => 2 * k + 1

lemma oddLcm_pos (n : ℕ) : 0 < oddLcm n := by
  unfold oddLcm
  exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.2 fun k _ => by omega)


lemma odd_dvd_oddLcm {n k : ℕ} (hk : k ≤ n) : 2 * k + 1 ∣ oddLcm n :=
  Finset.dvd_lcm (by simp; omega)

/-- `x ∈ ℤ` inside `ℚ`. -/
def IsInt (x : ℚ) : Prop := ∃ z : ℤ, x = z

lemma isInt_intCast (z : ℤ) : IsInt (z : ℚ) := ⟨z, rfl⟩
lemma isInt_natCast (n : ℕ) : IsInt (n : ℚ) := ⟨n, by simp⟩
lemma IsInt.add {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; rfl⟩
lemma IsInt.mul {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by push_cast; rfl⟩
lemma IsInt.neg {x : ℚ} (hx : IsInt x) : IsInt (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by push_cast; rfl⟩
lemma IsInt.sub {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg
lemma IsInt.pow {x : ℚ} (hx : IsInt x) (n : ℕ) : IsInt (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨a ^ n, by push_cast; rfl⟩
lemma IsInt.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))
lemma IsInt.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
lemma isInt_natCast_div {d n : ℕ} (h : d ∣ n) : IsInt ((n : ℚ) / d) := by
  obtain ⟨c, rfl⟩ := h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; exact ⟨0, by simp⟩
  · exact ⟨c, by push_cast; field_simp⟩

lemma oddLcm_dvd_oddLcm {m n : ℕ} (h : m ≤ n) : oddLcm m ∣ oddLcm n :=
  Finset.lcm_dvd fun k hk => odd_dvd_oddLcm (by simp at hk; omega)

lemma odd_dvd_normaliser {B i h : ℕ} (h1 : 1 ≤ h) (hB : h ≤ B) :
    2 * (h + i) + 1 ∣ normaliser B i :=
  (dvd_pow_self _ two_ne_zero).trans (Finset.dvd_prod_of_mem _ (by simp [h1, hB]))

/-- The scaled partial sums are integers: `L_n^2 · S_m ∈ ℤ` for `m ≤ n + 1`. -/
lemma isInt_oddLcm_sq_mul_partial {m n : ℕ} (hm : m ≤ n + 1) :
    IsInt ((oddLcm n : ℚ) ^ 2 * ∑ k ∈ range m, (-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2) := by
  rw [mul_sum]
  refine IsInt.sum _ _ fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  have : (oddLcm n : ℚ) ^ 2 * ((-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2)
      = (-1 : ℚ) ^ k * ((((oddLcm n) ^ 2 : ℕ) : ℚ) / (((2 * k + 1) ^ 2 : ℕ) : ℚ)) := by
    push_cast; ring
  rw [this]
  exact ((isInt_intCast (-1)).pow k).mul (isInt_natCast_div (pow_dvd_pow_of_dvd (odd_dvd_oddLcm hk') 2))

lemma isInt_mul_fakeTail (a q : ℤ) (hq : q ≠ 0) {m n : ℕ} (hm : m ≤ n + 1) :
    IsInt ((q : ℚ) * (oddLcm n : ℚ) ^ 2 * fakeTail ((a : ℚ) / q) m) := by
  have hq' : (q : ℚ) ≠ 0 := Int.cast_ne_zero.2 hq
  have : (q : ℚ) * (oddLcm n : ℚ) ^ 2 * fakeTail ((a : ℚ) / q) m
      = (-1 : ℚ) ^ m * ((a : ℚ) * ((oddLcm n : ℚ) ^ 2) -
          (q : ℚ) * ((oddLcm n : ℚ) ^ 2 * ∑ k ∈ range m, (-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2)) := by
    unfold fakeTail; field_simp
  rw [this]
  exact ((isInt_intCast (-1)).pow m).mul (((isInt_intCast a).mul ((isInt_natCast _).pow 2)).sub
    ((isInt_intCast q).mul (isInt_oddLcm_sq_mul_partial hm)))

theorem isInt_resid_fakeTail (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hSB : S ≤ B) (i : Fin (S + 3))
    (j : Fin S) :
    IsInt ((q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2 * resid (fakeTail ((a : ℚ) / q)) B S i j) := by
  rw [resid, mul_sum]
  refine IsInt.sum _ _ fun i' hi' => ?_
  have hi'' : i' ≤ i.val + 2 * B := by simp at hi'; omega
  have : (q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2 *
      ((-1 : ℚ) ^ i' * ((i.val + 2 * B).choose i' : ℚ) * (normaliser B i' : ℚ) *
      (fakeTail ((a : ℚ) / q) (i' + j.val + 1) / (2 * ((i' + j.val + 1 : ℕ) : ℚ) + 1)))
      = (-1 : ℚ) ^ i' * ((i.val + 2 * B).choose i' : ℚ) *
        ((normaliser B i' : ℚ) / ((2 * (j.val + 1 + i') + 1 : ℕ) : ℚ)) *
        ((q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2 * fakeTail ((a : ℚ) / q) (i' + j.val + 1)) := by
    have : ((2 * (j.val + 1 + i') + 1 : ℕ) : ℚ) = 2 * ((i' + j.val + 1 : ℕ) : ℚ) + 1 := by
      push_cast; ring
    rw [this]; ring
  rw [this]
  refine (((isInt_intCast (-1)).pow i').mul (isInt_natCast _)).mul
    (isInt_natCast_div (odd_dvd_normaliser (by omega) (by have := j.isLt; omega))) |>.mul ?_
  exact isInt_mul_fakeTail a q hq (by have := j.isLt; omega)

/-- **E1.**  Under `G = a/q` and `S ≤ B`, every entry of the residual matrix lies in
`(1 / (q · L_{a+2B+S}^2)) ℤ`, with `L = oddLcm`.  (Paper's Lemma 5.4, at every prime.)

**Statement fixed 2026-09-04 (lap 2):** the frozen version lacked `S ≤ B`, and is FALSE without
it — exact probe: `B = 0, S = 7, a/q = 1` leaves a denominator `15` after scaling by `q·L^2`
(the pole `1/(2(i+j+1)+1)` is only absorbed by `Π_i` when `j+1 ≤ B`).  E3 already assumed
`S < B`, so nothing downstream changes. -/
theorem resid_fakeTail_den (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hSB : S ≤ B) (i : Fin (S + 3))
    (j : Fin S) :
    ∃ z : ℤ, resid (fakeTail ((a : ℚ) / q)) B S i j =
      (z : ℚ) / ((q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2) := by
  obtain ⟨z, hz⟩ := isInt_resid_fakeTail a q hq hSB i j
  refine ⟨z, ?_⟩
  have hq' : (q : ℚ) ≠ 0 := Int.cast_ne_zero.2 hq
  have hL : (oddLcm (i.val + 2 * B + S) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (oddLcm_pos _).ne'
  rw [← hz]; field_simp

/-- Common denominator for all rows. -/
theorem isInt_resid_fakeTail_common (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hSB : S ≤ B) (i : Fin (S + 3))
    (j : Fin S) :
    IsInt ((q : ℚ) * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2 * resid (fakeTail ((a : ℚ) / q)) B S i j) := by
  obtain ⟨c, hc⟩ := oddLcm_dvd_oddLcm (show i.val + 2 * B + S ≤ 2 * B + 2 * S + 2 by
    have := i.isLt; omega)
  have : (q : ℚ) * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2 * resid (fakeTail ((a : ℚ) / q)) B S i j
      = (c : ℚ) ^ 2 * ((q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2 *
          resid (fakeTail ((a : ℚ) / q)) B S i j) := by
    rw [hc]; push_cast; ring
  rw [this]
  exact ((isInt_natCast c).pow 2).mul (isInt_resid_fakeTail a q hq hSB i j)

/-- **E2.**  Every `S × S` minor of the fake-tail residual matrix lies in
`(1 / (q · L_{2B+2S+2}^2)^S) ℤ`.  (Hypothesis `S ≤ B` added with E1, 2026-09-04.) -/
theorem det_resid_fakeTail_den (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hSB : S ≤ B)
    (A : Fin S → Fin (S + 3)) :
    ∃ z : ℤ, ((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det =
      (z : ℚ) / ((q : ℚ) * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2) ^ S := by
  set d : ℚ := (q : ℚ) * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2 with hd
  have hd0 : d ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hq)
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (oddLcm_pos _).ne'))
  have key : IsInt (d ^ S * ((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det) := by
    rw [show d ^ S = d ^ Fintype.card (Fin S) by simp, ← Matrix.det_smul, Matrix.det_apply]
    refine IsInt.sum _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    refine (isInt_intCast _).mul (IsInt.prod _ _ fun k _ => ?_)
    simp only [Matrix.smul_apply, Matrix.submatrix_apply, id, smul_eq_mul]
    exact isInt_resid_fakeTail_common a q hq hSB _ _
  obtain ⟨z, hz⟩ := key
  exact ⟨z, by rw [← hz]; field_simp⟩

/-- **E3 (the `F_B`-free no-go).**  Under `G = a/q`, some row selection has a nonzero minor
bounded BELOW by the integrality floor `1/(q · L^2)^S`.  This is `sun_ledger_impossible` with the
factorial gone: the floor that any real-place bound must beat. -/
theorem abs_det_ge_of_rational (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    ∃ A : Fin S → Fin (S + 3),
      ((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det ≠ 0 ∧
      1 / (|(q : ℚ)| * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2) ^ S ≤
        |((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det| := by
  obtain ⟨A, -, hdet⟩ := exists_row_set_det_ne_zero (fakeTail_isTailSeq ((a : ℚ) / q)) hS hBS
  refine ⟨A, hdet, ?_⟩
  obtain ⟨z, hz⟩ := det_resid_fakeTail_den a q hq hBS.le A
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; exact hdet hz
  have h1 : (1 : ℚ) ≤ |(z : ℚ)| := by exact_mod_cast Int.one_le_abs hz0
  have hd0 : 0 < |(q : ℚ)| * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2 :=
    mul_pos (abs_pos.2 (Int.cast_ne_zero.2 hq)) (pow_pos (Nat.cast_pos.2 (oddLcm_pos _)) 2)
  rw [hz, abs_div, abs_pow, abs_mul, abs_pow, Nat.abs_cast]
  rw [div_le_div_iff_of_pos_right (pow_pos hd0 _)]
  exact h1

/-! ### The frontier, stated honestly -/

/-- **The open node.**  "Sun's construction produces small forms": for every hypothetical
`G = a/q` there are parameters `B > S > 0` at which EVERY `S × S` minor of the true-tail residual
matrix is below the integrality floor.  A `Prop`, never a theorem: the host probe says it is
**false** for these weights (`log|N_B| ≈ +3.4·S·B`, growing).  A corrected construction replaces
`resid`/`oddLcm` here and nowhere else. -/
def SmallForms : Prop :=
  ∀ a q : ℤ, 0 < q → catalanConst = (a : ℝ) / q →
    ∃ B S : ℕ, 0 < S ∧ S < B ∧ ∀ A : Fin S → Fin (S + 3),
      |((resid tail B S).submatrix A id).det| <
        1 / ((q : ℝ) * (oddLcm (2 * B + 2 * S + 2) : ℝ) ^ 2) ^ S

/-- `resid` commutes with a ring hom applied to the tail sequence. -/
lemma resid_map {K : Type*} [Field K] [CharZero K] (f : F →+* K) (T : ℕ → F) (B S : ℕ) :
    (resid T B S).map f = resid (fun m => f (T m)) B S := by
  ext a j
  simp only [Matrix.map_apply, resid, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_div₀, map_add, map_ofNat]

lemma resid_fakeTail_cast_eq_tail (a q : ℤ) (hG : catalanConst = (a : ℝ) / q) (B S : ℕ) :
    (resid (fakeTail ((a : ℚ) / q)) B S).map (Rat.castHom ℝ) = resid tail B S := by
  rw [resid_map]
  congr 1
  funext m
  exact fakeTail_eq_tail_of_catalan_eq a q hG m

/-- **The sink edge.**  `SmallForms → Irrational catalanConst`.  Green means: the ledger is the
ONLY thing missing, and E3 is the floor it must beat.  `SmallForms` itself is open (and, for
these weights, numerically false). -/
theorem catalan_irrational_of_smallForms (h : SmallForms) : Irrational catalanConst := by
  rintro ⟨r, hr⟩
  have hq : (0 : ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  have hG : catalanConst = (r.num : ℝ) / ((r.den : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def]; push_cast; rfl
  obtain ⟨B, S, hS, hBS, hsmall⟩ := h r.num r.den hq hG
  obtain ⟨A, -, hge⟩ := abs_det_ge_of_rational r.num r.den hq.ne' hS hBS
  have hcast : ((resid tail B S).submatrix A id).det =
      ((((resid (fakeTail ((r.num : ℚ) / (r.den : ℤ))) B S).submatrix A id).det : ℚ) : ℝ) := by
    rw [← resid_fakeTail_cast_eq_tail r.num r.den hG B S, Matrix.submatrix_map,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have h1 := hsmall A
  rw [hcast] at h1
  have habs : |((r.den : ℤ) : ℚ)| = (r.den : ℚ) := by simp
  rw [habs] at hge
  have hden : (((r.den : ℤ) : ℝ)) = ((r.den : ℚ) : ℝ) := by simp
  have hL : ((oddLcm (2 * B + 2 * S + 2) : ℕ) : ℝ) = ((oddLcm (2 * B + 2 * S + 2) : ℚ) : ℝ) := by
    simp
  rw [hden, hL, ← Rat.cast_abs, ← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_pow, ← Rat.cast_one,
    ← Rat.cast_div, Rat.cast_lt] at h1
  linarith


end LeanFormalizations.Catalan
