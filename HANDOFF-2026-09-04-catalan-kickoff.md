# HANDOFF — 2026-09-04 — Catalan salvage kickoff (scaffold planted, nothing proved yet)

## 👉 Read `DIRECTION.md` first.  Objective: the Catalan conjecture graph — Phase 1 grind.

**State at handoff (host, Ren, 2026-09-04 morning):**
- Branch `catalan` off `main` (`09d1805`).  New thread `src/LeanFormalizations/NumberTheory/Catalan/`
  = `Tails.lean`, `Residual.lean`, `TwoAdic.lean`, `Statement.lean`, `README.md`, wired into
  `src/LeanFormalizations.lean`.  **Every file compiles; every proof leaf is a named `sorry`**
  except the wiring already proved (`resid_rank` from `resid_mulVec_eq_zero`; `fakeTail_isTailSeq`;
  `odd_normaliser`, `odd_normaliserProd`; `two_pow_le_abs_NB`).
- The statements were hand-checked against the paper and numerically probed on the host
  (`rank R = S` at the true `G`, 400-digit precision, for `(B,S)` up to `(8,5)`; the 2-adic
  identity `v₂(N_B) ≥ v₂(F_B)` exactly over `ℚ` at `B = 4,5,6`), **not** machine-checked: a
  frozen statement that turns out wrong gets fixed loudly, per DIRECTION.

## Start here (lap 1)
1. `lake build` (warm tree; the four Catalan modules build in seconds).
2. Phase 1, step 1: `Tails.lean` — `summable_tailTerm`, `tail_add_tail_succ`,
   `tail_eq_catalan_sub_partialSum`.  Mathlib hooks: `Summable.of_norm_bounded`,
   `Real.summable_one_div_nat_pow`, `summable_nat_add_iff`, `Summable.tsum_eq_zero_add`.
3. Then step 2 (`Residual.lean`) in the listed order.  For the crux, **first** commit a skeleton
   of named sub-lemmas (`D_λ`, `P_λ`, `K`) with `sorry`, then attack them.

## Operator triage worth knowing before you read the paper
- The paper's proof of Thm 2.1 expands around `T_i` but its `K` needs `T_{i+1}`; its `P_λ` sums
  from `k = 0` where `(2i+1)^2 ∤ Π_i`.  Both fixed by expanding around `T_{i+1}` with `k ≥ 1` —
  which is what `IsTailSeq.shift` states.  The "(2.3) sign slip" mentioned in the briefing is the
  same phenomenon seen from the page-4 display.
- `no_rational_solution` is stated for a general nonzero constant `c` on the right-hand side, so
  the sign of the functional equation never matters.
- Theorem 2.1 uses NOTHING about the tails beyond the recurrence — that is why `Residual.lean`
  is field-generic over `IsTailSeq`, and why the same theorem feeds Target B over `ℚ`.
