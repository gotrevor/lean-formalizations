/-
# Goodstein sequences — definitions (audit surface, part 1 of 2)

This file fixes the **faithful definition** of a Goodstein sequence. Together with
`Statement.lean` (the headline) and `Anchors.lean` (the ground-truth check) it is
the entire trust surface for the project — audit these three, ignore the engine.

## The definition (standard; Goodstein 1944)

For a base `b ≥ 2`, the *hereditary base-`b`* representation of `n` writes `n` in
base `b`, then rewrites every exponent in base `b`, recursively, until every
number appearing (other than `b` itself) is `< b`. Example in base 2:
`266 = 2^(2^2 + 1) + 2^(2 + 1) + 2`.

The **bump** operation `bump b n` reads `n` in hereditary base `b` and replaces
every occurrence of the base `b` by `b + 1` (exponents bumped recursively, digits
unchanged). We peel the top power: with `e = Nat.log b n`, leading digit
`c = n / b^e` (so `1 ≤ c < b`) and remainder `r = n % b^e` (so `r < b^e`),
`bump b n = c · (b+1)^(bump b e) + bump b r`, and `bump b 0 = 0`. Both recursive
calls are on strictly smaller numbers (`e < n` and `r < n`), so this is
well-founded.

The **Goodstein sequence** seeded at `m` is `G 0 = m`, and for `k ≥ 0`:
`G (k+1)` = take `G k`, bump base `(k+2) ↦ (k+3)`, then **subtract 1** (with `0`
a fixed point). So `G 0` is read in base 2, the first bump is `2 ↦ 3`, the next
`3 ↦ 4`, …

`goodsteinSeq m k` is `G k`. The base at step `k` is `base k = k + 2`.
-/
import Mathlib.Data.Nat.Log

namespace LeanFormalizations.Logic.Goodstein

/-- The base used to read `G k` at step `k` of a Goodstein sequence: `base k = k + 2`
(so `G 0` is read in base 2, the first bump sends `2 ↦ 3`, and so on). -/
def base (k : ℕ) : ℕ := k + 2

/-- **Hereditary-base bump.** `bump b n` reads `n` in hereditary base `b` and
replaces every occurrence of `b` by `b + 1`. Peeling the top power (`e = log b n`,
`c = n / b^e`, `r = n % b^e`):
`bump b n = c · (b+1)^(bump b e) + bump b r`, with `bump b 0 = 0`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- **Goodstein sequence** seeded at `m`: `goodsteinSeq m k = G k` (see the module
doc). `G 0 = m`; `G (k+1)` bumps the hereditary base `k+2 ↦ k+3` in `G k` and
subtracts one (`0` is a fixed point, as `bump b 0 = 0` and `0 - 1 = 0`). -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

end LeanFormalizations.Logic.Goodstein
