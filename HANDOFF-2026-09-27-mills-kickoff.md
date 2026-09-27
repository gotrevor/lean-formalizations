# HANDOFF 2026-09-27 — Mills + Wright kickoff (planted by Ren, no lap yet)

Scaffold planted on branch `mills` (from `main`), both files compile with only `sorry` warnings:

- `src/LeanFormalizations/NumberTheory/Mills/Wright.lean` — `tower`, `wright` (1 sorry).
- `src/LeanFormalizations/NumberTheory/Mills/Basic.lean` — `IsMills`/`IsMinMills` (verbatim from
  formal-conjectures), `PrimeBetweenCubesFrom`, `prime_add_one_lt_cube`,
  `exists_mills_of_primeBetweenCubes`, `exists_least_of_exists` (3 sorries), plus the wired
  corollary `exists_least_of_primeBetweenCubes`.

Operator triage (host-side, before launch):
- PNT+ upstream (`55270df`, 2026-09-24) proves StrongPNT / classical zero-free region but has no
  short-interval theorem strong enough for cubes; its explicit-formula / zero-density inputs are
  `sorry`.  Hence the hypothesis.  Not this run's problem.
- Bertrand in this mathlib: `Nat.exists_prime_lt_and_le_two_mul` (verify the exact name).
- Mills' `⌊·⌋` needs the strict `A^(3^k) < p k + 1`; step 1 (`(n+1)³−1` composite) supplies it.

Next: DIRECTION.md "Order" step 1 (`wright`).
