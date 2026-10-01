# HANDOFF 2026-10-01 — Erdős #385 E4 DONE (bad set exponentially thin)

`badCountExpBound_of_lit : ArithLargeSieve → LinearSieveIntervalLower → McDiarmidFinite →
BadCountExpBound` proved; `#print axioms` = [propext, Classical.choice, Quot.sound].
`Exceptional.lean` sorry-free.  Helpers in `Erdos385/Exceptional/`:
Basic (uSet, forbidden classes), CRT (residue-vector counting), McD (McDiarmid on unblocked
count), Mertens (∏_{y^θ<p≤y}(1−1/p) ≥ δ via repo `mertens_second`; Σ1/p² ≤ 1/⌊z⌋), Tail
(`tail_bound`), Sieve (`sieve_count`: large sieve with ω(p)=p−1 for p ≤ y, moduli y#·q₁⋯q_j),
Count (`bad_count_le` three-way split), Analytic (Chebyshev π lower bound, pool weight ≥ 8^j,
L-conditions), Terms, Main (`eventually_bad_le`, parameters y=⌊L/8⌋, R=y², j=⌈L^θ⌉,
K=⌈cy/log y⌉, Q=⌊√X⌋).

Deviations from the planted outline (all simplifications): no dyadic blocks (n ≤ R+y counted
trivially); no transport through the unit mod q — the primorial class enters the large sieve
directly (cost P/φ(P) ≤ y); pool = primes in (y, y²] instead of (y, Q^{1/j}] (no Mertens needed
for L, only Chebyshev).  Outline closed without gaps.

Next: discharge the three literature Props (McDiarmid from mathlib Azuma–Hoeffding is the
most tractable), per DIRECTION.md.
