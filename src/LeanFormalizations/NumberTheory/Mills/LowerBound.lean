/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The lower half of the Mills digits, unconditionally

`lower_bound_of_RH` (Caldwell-Cheng) pins the least Mills number to
`(1.3063778838, 1.3063778839)` under RH.  RH is only needed for the **upper** end, where the
greedy chain `2, 11, 1361, 2521008887, ...` must be known to continue forever.  The **lower**
end holds for every Mills number with no hypothesis at all.

## How it goes through

The plan in the original header was a four-way case split along the greedy chain
(`p1 = 2` / `p1 >= 3`, then `p2 = 11` / `p2 >= 13`, ...).  That split is *not needed*: the
lexicographic-minimality lemma `gseq_le_digits` in `RH.lean` already performs it, uniformly and
**unconditionally** -- for any Mills `A` it gives `gseq k <= floor (A ^ 3^(k+1))` for every `k`,
using only `lpa_le` (there is always a prime above `n`, Euclid) plus the self-generated chain
bound `c^3 < floor (A ^ 3^(k+2))` coming from primality of the digits.  `PrimeBetweenCubesFrom`
enters `RH.lean` only through `gseq_hi`, i.e. only for the *upper* bound.

So the whole proof is: instantiate at `k = 3`, where `gseq 3 = 2521008887` (`gseq_three`), to get
`A ^ 81 >= 2521008887`, and compare with `(1.3063778838 : R) ^ 81 < 2521008887` by `norm_num`.
-/
import LeanFormalizations.NumberTheory.Mills.RH

namespace LeanFormalizations.Mills

/-- **Every Mills number exceeds `1.3063778838`.**  Unconditional. -/
theorem lower_bound_of_isMills {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) :
    (1.3063778838 : ℝ) < A := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have h81 : ((3:ℕ) ^ (3 + 1)) = 81 := by norm_num
  -- The greedy chain is termwise below the digits of *any* Mills number (`gseq_le_digits`
  -- needs no hypothesis), and its fourth term is `2521008887`.
  have hlow : (2521008887 : ℝ) ≤ A ^ (81:ℕ) := by
    have hd := gseq_le_digits hA1 hA 3
    rw [gseq_three, h81] at hd
    have hc : (2521008887 : ℝ) ≤ ((⌊A ^ (81:ℕ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hd
    exact hc.trans (Nat.floor_le (by positivity))
  by_contra hcon
  push Not at hcon
  have hmono : A ^ (81:ℕ) ≤ (1.3063778838 : ℝ) ^ (81:ℕ) := pow_le_pow_left₀ hA0 hcon 81
  have hnum : (1.3063778838 : ℝ) ^ (81:ℕ) < 2521008887 := by norm_num
  linarith

/-- **The least Mills number exceeds `1.3063778838`**: the lower half of formal-conjectures'
`Mills.lower_bound_of_RH`, with no hypothesis. -/
theorem lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A :=
  lower_bound_of_isMills hA.1.1 hA.1.2

end LeanFormalizations.Mills
