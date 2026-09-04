# Catalan's constant — the salvage of Sun's arXiv:2609.04176v1 (and its refutation)

**Result.**  Zhi-Wei Sun's *Catalan's constant is irrational* (arXiv:2609.04176v1, 3 Sep 2026)
does **not** prove its headline: a 2-adic bookkeeping error kills §3–§9.  Full analysis, the
exact-rational check, and the community context: `papers/sun-2026-catalan-irrationality.md`.
This thread formalises exactly what survives, plus the refutation as a kernel-checked no-go.

**⚠️ Nothing here claims that Catalan's constant is irrational.  It remains open.**

## The two targets

| | Statement | Where |
|---|---|---|
| **A. Theorem 2.1** | The `(S+3) × S` weighted residual matrix `R_{a,j} = Σ_i (-1)^i C(a+2B,i) Π_i u_{i+j}` has rank `S` for `B > S > 0`. | `residual_rank` (`Statement.lean`), engine `resid_rank` (`Residual.lean`) |
| **B. The 2-adic no-go** | Under `G = a/q`, the paper's own integer `N_B` is divisible by `2^{v₂(F_B)}`, and `v₂(F_B) ≥ B(2B−1) − 2B(⌊log₂ 2B⌋+1)`; some row set makes `N_B ≠ 0`, hence `|N_B| ≥ 2^{2B² − O(B log B)}` against Theorem 9.1's `log|N_B| ≤ −δ₀B²`. | `two_pow_padicValNat_bigF_dvd_NB`, `padicValNat_two_bigF_ge` (`TwoAdic.lean`); `sun_ledger_impossible` (`Statement.lean`) |

## What to audit (`Statement.lean`)

- `tail`, `catalanConst`, `wtail` (`Tails.lean`) — the paper's `T_m`, `G`, `u_m` as `tsum`s.
- `normaliser`, `IsTailSeq`, `resid` (`Residual.lean`) — `Π_i`, the recurrence interface, `R`.
  Theorem 2.1 is proved for **any** sequence satisfying the recurrence; the real tails
  (`tail_add_tail_succ`) and the fake rational tails (`fakeTail_isTailSeq`) are two instances.
- `fakeTail`, `bigF`, `normaliserProd`, `qhat`, `NB` (`TwoAdic.lean`) — the paper's §3 objects
  read off a hypothetical `G = a/q`.  `fakeTail_eq_tail_of_catalan_eq` is the faithfulness edge:
  if `G` were `a/q`, the fake tails are the tails.

## Status

Scaffold planted 2026-09-04 with the statements frozen and the proof plan in each file's header;
the paper's two index slips in the proof of Theorem 2.1 are documented and repaired in
`Residual.lean`.  Grind in progress (see the repo `DIRECTION.md`).
