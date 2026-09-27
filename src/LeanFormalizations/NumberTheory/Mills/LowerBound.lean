/-
# The lower half of the Mills digits, unconditionally

`lower_bound_of_RH` (Caldwell–Cheng) pins the least Mills number to
`(1.3063778838, 1.3063778839)` under RH.  RH is only needed for the **upper** end, where the
greedy chain `2, 11, 1361, 2521008887, …` must be known to continue forever.  The **lower** end
holds for every Mills number with no hypothesis at all:

Let `p_k = ⌊A^(3^k)⌋₊` (`k ≥ 1`), so `p_k` is prime and `p_k³ ≤ p_{k+1}` (`Basic.lean`,
Saito Lemma 3.5 shape).  Walk the greedy chain:

* `p₁` is prime, so `p₁ ≥ 2`; if `p₁ ≥ 3` then `A ≥ 3^(1/3) ≈ 1.442`.
* `p₁ = 2`: `p₂ ∈ [8, 27)` prime, so `p₂ ≥ 11`; if `p₂ ≥ 13` then `A ≥ 13^(1/9) ≈ 1.330`.
* `p₂ = 11`: `p₃ ∈ [1331, 1728)` prime, so `p₃ ≥ 1361`; if `p₃ ≥ 1367` then
  `A ≥ 1367^(1/27) ≈ 1.30645`.
* `p₃ = 1361`: `p₄ ≥ 1361³ = 2521008881` prime, so `p₄ ≥ 2521008887`, and
  `A ≥ 2521008887^(1/81) ≈ 1.3063778838630`.

Each branch clears `1.3063778838`.  Reuse the chain lemmas and the exact rational-power
comparisons from `RH.lean` / `Chain.lean` where they fit (`c < A ↔ c^(3^k) < A^(3^k)` for
positive reals, and `A^(3^k) ≥ p_k`).  The composite gaps (`8..10`, `1331..1360`,
`2521008881..2521008886`, and `1362..1366`) are `decide`/`norm_num` checks.
-/
import LeanFormalizations.NumberTheory.Mills.RH

namespace LeanFormalizations.Mills

/-- **Every Mills number exceeds `1.3063778838`.**  Unconditional. -/
theorem lower_bound_of_isMills {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) :
    (1.3063778838 : ℝ) < A := by
  sorry

/-- **The least Mills number exceeds `1.3063778838`**: the lower half of formal-conjectures'
`Mills.lower_bound_of_RH`, with no hypothesis. -/
theorem lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A :=
  lower_bound_of_isMills hA.1.1 hA.1.2

end LeanFormalizations.Mills
