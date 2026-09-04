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
  sorry

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
  sorry

lemma odd_dvd_oddLcm {n k : ℕ} (hk : k ≤ n) : 2 * k + 1 ∣ oddLcm n := by
  sorry

/-- **E1.**  Under `G = a/q`, every entry of the residual matrix lies in
`(1 / (q · L_{a+2B+S}^2)) ℤ`, with `L = oddLcm`.  (Paper's Lemma 5.4, at every prime.) -/
theorem resid_fakeTail_den (a q : ℤ) (hq : q ≠ 0) (B S : ℕ) (i : Fin (S + 3)) (j : Fin S) :
    ∃ z : ℤ, resid (fakeTail ((a : ℚ) / q)) B S i j =
      (z : ℚ) / ((q : ℚ) * (oddLcm (i.val + 2 * B + S) : ℚ) ^ 2) := by
  sorry

/-- **E2.**  Every `S × S` minor of the fake-tail residual matrix lies in
`(1 / (q · L_{2B+2S+2}^2)^S) ℤ`. -/
theorem det_resid_fakeTail_den (a q : ℤ) (hq : q ≠ 0) (B S : ℕ) (A : Fin S → Fin (S + 3)) :
    ∃ z : ℤ, ((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det =
      (z : ℚ) / ((q : ℚ) * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2) ^ S := by
  sorry

/-- **E3 (the `F_B`-free no-go).**  Under `G = a/q`, some row selection has a nonzero minor
bounded BELOW by the integrality floor `1/(q · L^2)^S`.  This is `sun_ledger_impossible` with the
factorial gone: the floor that any real-place bound must beat. -/
theorem abs_det_ge_of_rational (a q : ℤ) (hq : q ≠ 0) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    ∃ A : Fin S → Fin (S + 3),
      ((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det ≠ 0 ∧
      1 / (|(q : ℚ)| * (oddLcm (2 * B + 2 * S + 2) : ℚ) ^ 2) ^ S ≤
        |((resid (fakeTail ((a : ℚ) / q)) B S).submatrix A id).det| := by
  sorry

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

/-- **The sink edge.**  `SmallForms → Irrational catalanConst`.  Green means: the ledger is the
ONLY thing missing, and E3 is the floor it must beat.  `SmallForms` itself is open (and, for
these weights, numerically false). -/
theorem catalan_irrational_of_smallForms (h : SmallForms) : Irrational catalanConst := by
  sorry

end LeanFormalizations.Catalan
