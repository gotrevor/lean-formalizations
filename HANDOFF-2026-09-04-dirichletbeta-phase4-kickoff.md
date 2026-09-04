# Phase 4 kickoff — one of β(2), β(4), …, β(20) is irrational

**Read `DIRECTION.md` "Phase 4 — ACTIVE" first.**  It carries the ledger, the frozen names, the
order of attack, and the numeric provenance of every constant.  This file is the lap baton.

## Where you are

`src/LeanFormalizations/NumberTheory/DirichletBeta/` is planted and **builds green** (8668 jobs)
with exactly **eight** `sorry` leaves.  `Statement.lean` is **proof-complete**: the headline

    exists_even_beta_irrational : ∃ i ∈ Icc 1 10, Irrational (dirichletBeta (2 * i))

is already derived from the four ledger nodes.  Closing the leaves closes the theorem.  There is
no design work left at the top — do not redesign the frame, fill it.

## The eight leaves

| file | name | shape |
|---|---|---|
| `Lcm.lean` | `dn_le_exp` | **N5** · `∃ N, ∀ n ≥ N, lcm(1..n) ≤ e^{1.01n}` — nearly free |
| `Beta.lean` | `summable_betaTerm` | routine |
| `Beta.lean` | `beta_two_eq_catalanConst` | `β(2) = catalanConst` (`Catalan/Tails.lean`) |
| `Rational.lean` | `Rval_pos` | `positivity` after unfolding |
| `Rational.lean` | `summable_Rval` | decay `u^{3n+1−s(n+1)} ≤ u^{−2}` |
| `LinearForm.lean` | `exists_int_combination` | **N2** · partial fractions + integrality |
| `Bound.lean` | `abs_rForm_le_exp` | **N4** · `|r_n| ≤ e^{−21.3n}` eventually |
| `Integral.lean` | `rForm_neg` | **N3, the crux** · `r_n < 0` via the `s`-fold Beta integral |

Attack them in that order (`DIRECTION.md` gives the route for each).  N5 and the `Beta.lean` pair
are a first lap's worth on their own.

## Non-negotiables

- **Do not change a frozen statement** to make it provable.  If you believe one is FALSE, say so
  loudly in the lap handoff with the counterexample and move to another leaf — a refutation is a
  result (Phase 3 found `E1` false and that was the lap's best output).
- **Do not tighten `-21.3` or `1.01`.**  The slack is deliberate; it is what makes N4/N5 elementary.
  The kernel already checks that this pair closes the ledger (`Statement.lean`).
- The sign convention `r_n = −C_n·∫` is numerically verified (`papers/catalan-beta-validate.py`
  part (c), and termwise-exact in `papers/catalan-beta-rval-check.py`).  Do not re-derive it.
- No `axiom`.  `decide +kernel` before `native_decide`.  Commit every green build; never push.
- Progress is **a closed leaf**, not a lower sorry count.  Splitting a leaf into named sub-leaves
  raises the count and is progress.

## Verify before you claim

    lake build                                            # must be green
    grep -rn "sorry" src/LeanFormalizations/NumberTheory/DirichletBeta/
    # when a headline closes:  #print axioms LeanFormalizations.DirichletBeta.exists_even_beta_irrational
