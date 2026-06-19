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

The **Goodstein sequence** seeded at `m` is `G 0 = m`, and for `k ≥ 0`:
`G (k+1)` = take `G k`, write it in hereditary base `(k+2)`, replace every
occurrence of the base `(k+2)` by `(k+3)`, then **subtract 1** (with `0` a fixed
point). So `G 0` is read in base 2, the first bump is `2 ↦ 3`, the next `3 ↦ 4`, …

`goodsteinSeq m k` is `G k`. The base at step `k` is `base k = k + 2`.

## ⚠️ STATUS — `goodsteinSeq` is a STUB

`goodsteinSeq` below is a placeholder that returns the seed. The treadmill must
replace it with the faithful hereditary-base definition above. Correctness is
pinned by the `Anchors.lean` `example`s (the full m = 0,1,2,3 trajectories),
which are currently `sorry` and must be discharged by `decide`/`native_decide`
once the real definition is in place. A vacuous definition CANNOT satisfy the
nonzero intermediate values (e.g. `goodsteinSeq 3 3 = 2`), so the anchors are the
anti-vacuity lock on this audit surface. No special-casing of small inputs: one
general definition must serve both the anchors and `goodstein_terminates`.

Likely substrate: `Nat.digits` for the base expansion, with well-founded
recursion on the value (exponents are strictly smaller). The ordinal interpretation
(replace the base by `ω`) and the descent argument live in the engine, not here.
-/
import Mathlib.Data.Nat.Digits.Defs

namespace LeanFormalizations.Logic.Goodstein

/-- The base used to read `G k` at step `k` of a Goodstein sequence: `base k = k + 2`
(so `G 0` is read in base 2, the first bump sends `2 ↦ 3`, and so on). -/
def base (k : ℕ) : ℕ := k + 2

/-- **Goodstein sequence** seeded at `m`: `goodsteinSeq m k = G k` (see the module
doc for the definition). `G 0 = m`; `G (k+1)` bumps the hereditary base `k+2 ↦ k+3`
in `G k` and subtracts one.

⚠️ STUB — returns the seed. Replace with the faithful definition; `Anchors.lean`
pins the required behaviour. -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ := fun _ => m

end LeanFormalizations.Logic.Goodstein
