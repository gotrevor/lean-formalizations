# Handoff: DirichletBeta Phase 4 — COMPLETE, headline axiom-clean

**Date**: 2026-09-04 · **Branch**: `catalan` · build green (seen, 8673 jobs)

## 🎯 Result
`exists_even_beta_irrational : ∃ i ∈ Icc 1 10, Irrational (dirichletBeta (2 * i))` and
`catalan_or_higher_beta_irrational` are proved; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` for both and for every leaf. `src/LeanFormalizations/NumberTheory/DirichletBeta/` has
no `sorry`. ⚠️ This does NOT claim `G ∉ ℚ` — every disjunct is individually open.

## 🧠 How N2 (`exists_int_combination`) closed this lap
- `Symmetry.lean`: `Rfun_symm` (`R_n(-t-n) = R_n(t)`, odd `s`, even `n`), `Rep.symmetrize`
  (coefficients `ã i k = (a i k + (-1)^{i+1} a i (n-k))/2`, half-integral: `2 d^{s-1-i} ã ∈ ℤ`),
  `sum_sign_symCoef_eq_zero` (odd-`L` coefficients vanish), `Rval_eq_Rfun`, `Rfun_vanish`
  (`R_n(w + ½ - m) = 0` for `w < 3m`). No uniqueness of partial fractions needed.
- `PartialSums.lean`: `Tps q a W = Σ_{w<W} (-1)^w/(w+a)^q`; one-step recursion
  `Tps q (a+1) W = 1/a^q - Tps q a (W+1)` (holds for all real `a`, Lean's `1/0 = 0` included);
  from the base `Tps q ½ = 2^q Eps q` walk forward/backward to `a = k - m + ½`, `|k-m| ≤ m`,
  collecting corrections `2^q/(2j+1)^q` with `2j+1 ≤ n-1`, recorded as `d^q F = 2z` (the factor 2
  pays for the half-integral `ã`). `L_q` exists for `q ≥ 1` (alternating test), `= β(q)` for `q ≥ 2`.
- `LinearForm.lean`: partial sums `PS W` from Zudilin's start `ν = 1 - m`; `PS → rForm` via
  `HasSum.tendsto_sum_nat` + `tendsto_add_atTop_iff_nat (3m)`; expand through `pfSum`, take limits
  termwise, `tendsto_nhds_unique`; regroup; odd-index reindexing `sum_range_odd_eq`.

## ✅ State
All Phase 4 leaves closed. Working tree: this commit. Nothing open in scope.

## 🎬 Next
Phase 4 is done; `DIRECTION.md` updated. Nothing to resume here. (Phase 2 moonshot remains
probe-first per `DIRECTION.md`; never claim `G` irrational.)

## ⚠️ Gotchas learned
- `neg_pow` rewrites `(-1)^k` too (as `(-(1))^k`) — pass the base explicitly.
- `congr 2` over `(-1)^a * ↑(f x)` descends into the exponent; use `congr 3` after rewriting the
  sign with `neg_one_pow_eq_pow_mod_two`.
- `Rat.cast_intCast` needed after `push_cast` for `((z:ℚ):ℝ) = (z:ℝ)`.
- `tendsto_finset_sum` deprecated → `tendsto_finsetSum`.
