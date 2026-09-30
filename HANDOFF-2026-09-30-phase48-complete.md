# HANDOFF — 2026-09-30, phase 48 COMPLETE

## State
`src/LeanFormalizations/NumberTheory/Mills/UnipotentTrace.lean` is **sorry-free**.
All three frozen statements proved and axiom-clean (`propext, Classical.choice, Quot.sound`):

- `three_dvd_trace_pow`
- `adjugate_unipotent`
- `three_dvd_trace_adjugate_pow`

`lake build` green (8769 jobs). `scripts/fact-graph` regenerated: 30 edges, 31 hypotheses.
Commit: `5ae4107`.

## How it was proved
Everything after reduction mod 3 via `red = (Int.castRingHom (ZMod 3)).mapMatrix`;
`red_eq_zero_iff` converts the entrywise `3 ∣ ·` hypotheses into `= 0` over `ZMod 3`.
Transport lemmas: `red_sub`, `red_pow`, `red_trace`, `red_adjugate`, `red_smul_one`.

1. `trace_pow_eq_zero (v N) (N^3 = 0) : tr ((v•1 + N)^s) = 0`.
   `Commute.add_pow` (scalar `v•1` is central, `commute_smul_one`), then every binomial term
   dies by `trace_pow_nilpotent`, which is uniform in `m` — `m = 0` works because
   `tr 1 = 3 = 0` in `ZMod 3`, `m ≥ 1` by `Matrix.isNilpotent_trace_of_isNilpotent` plus
   `isNilpotent_iff_eq_zero` (ZMod 3 reduced).

2. `adjugate_sub_sq_cube_eq_zero` — **deviates from the header route** (which wanted
   `adjugate M = det M · M⁻¹` and charpoly/inverse machinery):
   - `det_eq_of_unipotent`: char-3 Frobenius (`add_pow_char_of_commute`) gives
     `(v•1 + N)^3 = v^3•1` EXACTLY, so `(det A)^3 = v^9`; `cube_eq_self : x^3 = x` on `ZMod 3`
     makes cube-rooting free ⟹ `det A = v`. No charpoly coefficients, no `e₂`.
   - `mul_inv_aux`: explicit right inverse `B = v•1 - N + v•N^2`, expansion closed by
     `simp only [...]` + `module` using `v^2 = 1` (`sq_eq_one_of_ne_zero`, `decide`) and `N^3 = 0`.
   - `adjugate A = (adjugate A * A) * B = det A • B = v • B`, hence
     `adjugate A - v^2•1 = N * (N - v•1)`; cube `= N^3 * (…)^3 = 0` by `Commute.mul_pow`.

3. `three_dvd_trace_adjugate_pow` = statement 1 applied to `M.adjugate` with shift `w^2`.

No statement was false; `ROADMAP-PRIME-TOWERS.md` needed no counterexample entry.
Nothing outside the target file was touched.

## Next
Phase 48 is sub-node **R4** of `ShiftedTraceRigidity` (`PROOF-THEOREM-E.md` Step 5).
Remaining sub-nodes of that node are the next planting target; `DIRECTION.md` is owned by
altitude laps and should be consulted before picking one.

## Gotchas worth reusing
- `Matrix.natCast_eq_diagonal` does NOT exist; use `Matrix.smul_one_eq_diagonal` then
  `(Matrix.diagonal_natCast _).symm`.
- `Commute.add_pow_char` is not a projection — it is `add_pow_char_of_commute (p := 3) h`.
- Do NOT `set` the nilpotent `N := A - v•1` inside the big algebra proofs: the folding makes
  `abel`/`rw` re-fold `A` and the goals become unrewritable. Take `v` and `N` as plain
  variables in standalone lemmas and only convert at the interface (via an `abel`-proved
  `hsplit : red M = v•1 + (red M - v•1)`).
- `module` closes smul-linear matrix identities once all products are expanded; `abel` alone
  chokes on `1 • N^2`.
- `simp only [..., pow_two, ...]` leaves `N * (N * N)` right-associated; `rw [← Matrix.mul_assoc]`
  before applying `N * N * N = 0`.
