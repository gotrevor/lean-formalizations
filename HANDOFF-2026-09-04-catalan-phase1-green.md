# HANDOFF — 2026-09-04 (evening) — Catalan salvage: PHASE 1 GREEN, all headlines axiom-clean

## 👉 Read `DIRECTION.md` first.  Objective: the Catalan conjecture graph.

**State at handoff (branch `catalan`, HEAD = the "PHASE 1 GREEN" commit + this doc):**
- `src/LeanFormalizations/NumberTheory/Catalan/{Tails,Residual,TwoAdic,Statement}.lean` are
  **all sorry-free**.  `#print axioms` on `residual_rank`, `exists_row_set_det_ne_zero`,
  `fakeTail_eq_tail_of_catalan_eq`, `sun_ledger_impossible`, `two_pow_padicValNat_bigF_dvd_NB`,
  `padicValNat_two_bigF_ge`, `tail_add_tail_succ`, `tail_eq_catalan_sub_partialSum` =
  `[propext, Classical.choice, Quot.sound]`.  Build 🟢 (8660 jobs).
- **No frozen statement needed fixing.**  Every planted statement was right as frozen.
- **⚠️ Nothing proved here says Catalan's constant is irrational.  It remains open.**

## What the lap did (one lap, seven green commits)
1. `Tails.lean` — alternating-series machinery (`Summable.alternating`,
   `Antitone.alternating_series_le_tendsto` / `tendsto_le_alternating_series`); (1.4) by peeling
   the first term; (1.1) by induction; both halves of (1.3).
2. `Residual.lean` leaves — `IsTailSeq.shift` (induction), `alt_choose_sum_eval_eq_zero`
   (mathlib's `fwdDiff_iter_eq_zero_of_degree_lt` + `fwdDiff_iter_eq_sum_shift`),
   `exists_poly_of_alt_sums_eq_zero` (truncated Newton polynomial in `descPochhammer`; no
   Lagrange needed), `no_rational_solution` (coprime reduction, then `D(-3/2)D(-1/2)=0` forces an
   infinite arithmetic progression of roots — no algebraic closure needed).
3. **The crux `resid_mulVec_eq_zero`** — decomposed into explicit polynomials
   `lin/bigPi/Wpoly/Gpoly/Lsub/Qpoly/Dpoly/Psub/Ppoly/rowFun/Kpoly`.  Design change vs the
   paper's write-up: the paper's `K` (degree `≤ 4B`, `4B+1` zeros counted with multiplicity via
   `gcd(D(X),D(X+1))`) is replaced by `Kpoly := K / (lin 1 · Gpoly)`, which has degree
   `≤ 2B+S+1` and `2B+S+2` **simple integer** zeros — so `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`
   closes it with no multiplicity bookkeeping.  `key_identity` then recovers the rational-function
   identity `no_rational_solution` consumes.
4. `TwoAdic.lean` — an `OddDen` (2-integral) closure toolkit on `ℚ` (`Rat.add_den_dvd`,
   `mul_den_dvd`, `den_dvd`); Lemma 5.4 both halves; `odd_den_det` via `det_apply`;
   `2^{v₂(F_B)} ∣ N_B` via `padicValRat.mul` + `padicValInt_dvd_iff`; Legendre via
   `sub_one_mul_padicValNat_factorial` + `Nat.length_digits` + `List.sum_le_card_nsmul`.
5. `Statement.lean` — Corollary 2.1 via `rank_eq_finrank_span_row` + `exists_linearIndependent'`
   + `linearIndependent_rows_iff_isUnit`; the faithfulness edge; the no-go assembly.

## Where the graph stands (DIRECTION's node list)
- 🟢 Node A (Theorem 2.1) — GREEN.
- 🟢 Node B (2-adic no-go) — GREEN.
- 🔴 Sink `Irrational catalanConst` — NOT a target; untouched.

## Next (Phase 2 — the moonshot; DIRECTION says review laps own this)
- The frontier question: *what is the weakest open node on any path from A to the sink?*
- N1 (binomial completion, `F_B`-free `N'_B`): the probe `papers/sun-2026-catalan-twoadic-check.py`
  already prints `N'_B`; the open question is the real-place size of `N'_B`.  Extend the probe
  for N2 (an even normaliser) before stating any `Prop`.  **No Lean discharge for Phase-2 nodes;**
  the deliverable is a stated `def … : Prop` + probe result + the next story.
- Optional Phase-1 polish (off-path, low value): `Tails.lean` anchors are done; a
  `Statement.lean` `#print axioms` guard block could be added as a `#guard_msgs` test.

## Gotchas learned this lap (for the reference corpus)
- Over an abstract `Field F` with `CharZero F` there is no order: `positivity`/`linarith`
  don't apply; prove `2n+3 ≠ 0` etc. via `Nat.cast_add_one_ne_zero` after a `linear_combination`.
- `natDegree_prod_le` and `natDegree_sum_le_of_forall_le` take `s` and `f` EXPLICITLY in this
  mathlib; `natDegree_prod_le.trans` parses as an unknown constant.
- The `Δ_[h]` notation needs `open fwdDiff`; write `(fwdDiff (1:ℕ))^[n]` instead.
- `Rat` `/.` notation needs `open Rat`; write `Rat.divInt`.
- `isCoprime_div_gcd_div_gcd` is top-level (not `EuclideanDomain.`), needs `classical` for the
  `GCDMonoid F[X]` instance.
- `Matrix.submatrix_smul` produces a `Pi`-smul shape; prove `(c • M).submatrix e f = c • M.submatrix e f`
  by `ext; simp` instead.
