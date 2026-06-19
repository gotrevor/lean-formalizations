/-
# Goodstein — ground-truth anchors (faithfulness gate)

Hand-computed FULL Goodstein trajectories for the seeds `m = 0,1,2,3` (bases
`2,3,4,…`; bump-then-subtract-one; `0` absorbing). Derivation in `README.md`.

These are the anti-vacuity lock on the `goodsteinSeq` definition: a placeholder
or vacuous definition cannot reproduce the nonzero intermediate values. They are
currently `sorry`; once `goodsteinSeq` is faithfully defined, discharge each by
`decide`/`native_decide`. They MUST stay in `src/` so they count toward the
`--allow-stop` sorry-gate (the run does not finish until the definition is real).

`native_decide` here is fine — these are standalone `example`s, never on
`goodstein_terminates`'s axiom path. Re-check `#print axioms goodstein_terminates`
after, not these.

Trajectories (length = steps to reach 0):
  m=0:  0
  m=1:  1, 0
  m=2:  2, 2, 1, 0
  m=3:  3, 3, 3, 2, 1, 0
-/
import LeanFormalizations.Logic.Goodstein.Defs

namespace LeanFormalizations.Logic.Goodstein

-- m = 0 : already 0
example : goodsteinSeq 0 0 = 0 := by native_decide

-- m = 1 : 1, 0
example : goodsteinSeq 1 0 = 1 := by native_decide
example : goodsteinSeq 1 1 = 0 := by native_decide

-- m = 2 : 2, 2, 1, 0
example : goodsteinSeq 2 0 = 2 := by native_decide
example : goodsteinSeq 2 1 = 2 := by native_decide
example : goodsteinSeq 2 2 = 1 := by native_decide
example : goodsteinSeq 2 3 = 0 := by native_decide

-- m = 3 : 3, 3, 3, 2, 1, 0  (the classic short-but-not-trivial trajectory)
example : goodsteinSeq 3 0 = 3 := by native_decide
example : goodsteinSeq 3 1 = 3 := by native_decide
example : goodsteinSeq 3 2 = 3 := by native_decide
example : goodsteinSeq 3 3 = 2 := by native_decide
example : goodsteinSeq 3 4 = 1 := by native_decide
example : goodsteinSeq 3 5 = 0 := by native_decide

end LeanFormalizations.Logic.Goodstein
