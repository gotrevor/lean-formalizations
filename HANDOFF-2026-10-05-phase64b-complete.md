# HANDOFF 2026-10-05: phase 64b COMPLETE

`#print axioms LeanFormalizations.Mills.SaitoTypeB.xi_shift_transcendental_classical`
= [propext, Classical.choice, Quot.sound].  No native_decide, no ofReduceBool, no new axioms.

- `ShiftRigidity.cm3_check`: plain `decide +kernel` (27 cubics, ~15s).
- `E1Cert.cert_all` (2·27³ = 39366 cases): statement unchanged. Defs + soundness moved verbatim
  to `E1CertCore.lean`, which also adds `E1Cert.Fast`: matrix entries are monomials `0`/`±ζ^e`
  (`mono`, `mmul`, `cmul_mono`, `cmul_mono_left`), so `Cert` follows from `Fast.CertV`
  (coefficient functions, no list multiplication), via `cert_of_certV`.  Kernel tables in
  `E1CertTable{1,2}{0,1,2}.lean` (one `decide +kernel` lemma per (t,a,b), 27 cases each,
  ~0.07 s/case, ~8 min per file, ~47 min total).
- Build gotcha: building the six table files in parallel fails with "Too many open files"
  (host-wide fd pressure from 6 lean processes mmapping mathlib); build them sequentially once
  if a fresh tree hits it.  A single 39366-lemma file was killed by a signal (likely memory).
- Downstream oleans must be rebuilt for `#print axioms` to reflect it (stale ShiftRigidity olean
  showed sorryAx until `lake build ...SaitoTypeB`).
