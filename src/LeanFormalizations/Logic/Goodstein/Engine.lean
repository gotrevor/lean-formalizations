/-
# Goodstein — proof engine (ordinal descent)

This file is the proof machinery behind `goodstein_terminates`. It is NOT part of
the audit surface (that is `Defs`/`Statement`/`Anchors`); it just has to be
correct, which the kernel checks.

## Strategy
Interpret `n`, read in hereditary base `b`, as an ordinal `toOrdinal b n` by
replacing the base `b` with `ω` (same peeling recursion as `bump`). Two facts:

* **Bump invariance** — `toOrdinal (b+1) (bump b n) = toOrdinal b n` (`b ≥ 2`):
  bumping the base `b ↦ b+1` does not change the ordinal, since both read the base
  as `ω`.
* **Strict monotonicity** — `m < n → toOrdinal b m < toOrdinal b n` (`b ≥ 2`):
  the natural order maps to the ordinal order.

Then `a k := toOrdinal (k+2) (G k)` is strictly decreasing while `G k ≠ 0`
(subtract-one strictly lowers the ordinal, the base-bump preserves it), and
`Ordinal` is well-founded, so some `G N = 0`.

Both monotonicity and the leading-coefficient bound are proved together by one
strong induction; `bump` gets the parallel pair over `ℕ`.
-/
import LeanFormalizations.Logic.Goodstein.Defs
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.SuccPred

namespace LeanFormalizations.Logic.Goodstein

open Ordinal

/-- **Ordinal interpretation.** Read `n` in hereditary base `b`, replacing `b` by
`ω`. Same top-power peeling as `bump`: with `e = log b n`, `c = n / b^e`,
`r = n % b^e`, `toOrdinal b n = ω^(toOrdinal b e) * c + toOrdinal b r`. -/
noncomputable def toOrdinal (b : ℕ) (n : ℕ) : Ordinal.{0} :=
  if h : n = 0 then 0
  else
    ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
      + toOrdinal b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] lemma toOrdinal_zero (b : ℕ) : toOrdinal b 0 = 0 := by
  rw [toOrdinal]; simp

@[simp] lemma bump_zero (b : ℕ) : bump b 0 = 0 := by
  rw [bump]; simp

/-- Unfolding `toOrdinal` at a nonzero argument (peel the top power). -/
lemma toOrdinal_pos (b n : ℕ) (h : n ≠ 0) :
    toOrdinal b n =
      ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
        + toOrdinal b (n % b ^ Nat.log b n) := by
  rw [toOrdinal]; simp [h]

/-- Unfolding `bump` at a nonzero argument (peel the top power). -/
lemma bump_pos (b n : ℕ) (h : n ≠ 0) :
    bump b n =
      n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n) := by
  rw [bump]; simp [h]

/-- **Crux (ordinal side).** For `b ≥ 2`, the map `n ↦ toOrdinal b n` is strictly
monotone, and each value is bounded by `ω^(toOrdinal b (log b n) + 1)`. Both halves
are proved together by strong induction, because each needs the other on smaller
arguments. -/
theorem toOrdinal_mono_and_bound (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → toOrdinal b m < toOrdinal b n) ∧
      (n ≠ 0 → toOrdinal b n < ω ^ (toOrdinal b (Nat.log b n) + 1)) := by
  have hb1 : 1 < b := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- Remainder bound: `r < b^e'`, `e' < n`, `r < n` ⇒ `toOrdinal b r < ω^(toOrdinal b e')`.
    have rb : ∀ r e', e' < n → r < b ^ e' → r < n →
        toOrdinal b r < ω ^ toOrdinal b e' := by
      intro r e' he'n hre' hrn
      rcases eq_or_ne r 0 with rfl | hr0
      · simpa using opow_pos (toOrdinal b e') omega0_pos
      · have hlogr : Nat.log b r < e' := (Nat.log_lt_iff_lt_pow hb1 hr0).2 hre'
        have h1 : toOrdinal b (Nat.log b r) < toOrdinal b e' := (ih e' he'n).1 _ hlogr
        have h2 : toOrdinal b r < ω ^ (toOrdinal b (Nat.log b r) + 1) := (ih r hrn).2 hr0
        refine h2.trans_le (opow_le_opow_right omega0_pos ?_)
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h1
    constructor
    · ----- Part A: strict monotonicity into `n`
      intro m hmn
      have hn0 : n ≠ 0 := by omega
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hn_eq := toOrdinal_pos b n hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      have hpos : (0 : Ordinal) < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) := by
        apply mul_pos (opow_pos _ omega0_pos)
        exact_mod_cast hc_pos
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [toOrdinal_zero, hn_eq]
        exact lt_of_lt_of_le hpos (le_self_add)
      · -- `m ≥ 1`; compare leading exponents
        have hem_le : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hem_le with hem_lt | hem_eq
        · -- `log b m < log b n`: `m`'s whole ordinal sits below `ω^(toOrdinal b (log b n))`
          have hmb : toOrdinal b m < ω ^ (toOrdinal b (Nat.log b m) + 1) := (ih m hmn).2 hm0
          have hexp : toOrdinal b (Nat.log b m) + 1 ≤ toOrdinal b (Nat.log b n) := by
            rw [← Order.succ_eq_add_one]
            exact Order.succ_le_of_lt ((ih _ he_lt_n).1 _ hem_lt)
          calc toOrdinal b m
              < ω ^ (toOrdinal b (Nat.log b m) + 1) := hmb
            _ ≤ ω ^ toOrdinal b (Nat.log b n) := opow_le_opow_right omega0_pos hexp
            _ = ω ^ toOrdinal b (Nat.log b n) * 1 := (mul_one _).symm
            _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                  mul_le_mul_right (by exact_mod_cast hc_pos) _
            _ ≤ toOrdinal b n := by rw [hn_eq]; exact le_self_add
        · -- equal leading exponents: compare the leading digit, then the remainder
          have hbem_pos : 0 < b ^ Nat.log b m := Nat.pow_pos (by omega)
          have hbem_le : b ^ Nat.log b m ≤ m := Nat.pow_log_le_self b hm0
          have hrm_lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ hbem_pos
          have hm_eq := toOrdinal_pos b m hm0
          -- rewrite `log b m` to `log b n` everywhere
          rw [hm_eq, hn_eq, hem_eq]
          have hcm_le : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := by
            rw [← hem_eq]; exact Nat.div_le_div_right hmn.le
          have hrm_lt' : m % b ^ Nat.log b n < b ^ Nat.log b n := by
            rw [← hem_eq]; exact hrm_lt
          have hrm_lt_n : m % b ^ Nat.log b n < n :=
            lt_of_lt_of_le hrm_lt' hbe_le
          have hrbm : toOrdinal b (m % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
            rb _ _ he_lt_n hrm_lt' hrm_lt_n
          rcases lt_or_eq_of_le hcm_le with hcm_lt | hcm_eq
          · -- leading digit strictly smaller
            calc ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + toOrdinal b (m % b ^ Nat.log b n)
                < ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrbm
              _ = ω ^ toOrdinal b (Nat.log b n) * ((m / b ^ Nat.log b n : ℕ) + 1) := by
                    rw [mul_add_one]
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                    mul_le_mul_right (by exact_mod_cast hcm_lt) _
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
                  + toOrdinal b (n % b ^ Nat.log b n) := le_self_add
          · -- equal leading digit: remainder strictly smaller
            have hrm_rn : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              have em := Nat.div_add_mod m (b ^ Nat.log b n)
              have en := Nat.div_add_mod n (b ^ Nat.log b n)
              rw [← hcm_eq] at en
              omega
            rw [hcm_eq]
            have hlt : toOrdinal b (m % b ^ Nat.log b n) < toOrdinal b (n % b ^ Nat.log b n) :=
              (ih _ hr_lt_n).1 _ hrm_rn
            exact (add_lt_add_iff_left _).2 hlt
    · ----- Part B': leading bound
      intro hn0
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      rw [toOrdinal_pos b n hn0]
      calc ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + toOrdinal b (n % b ^ Nat.log b n)
          < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrb
        _ = ω ^ toOrdinal b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) + 1) := by rw [mul_add_one]
        _ ≤ ω ^ toOrdinal b (Nat.log b n) * ω :=
              mul_le_mul_right (by rw [← Nat.cast_add_one]; exact (natCast_lt_omega0 _).le) _
        _ = ω ^ (toOrdinal b (Nat.log b n) + 1) := by rw [← opow_succ, Order.succ_eq_add_one]

end LeanFormalizations.Logic.Goodstein
