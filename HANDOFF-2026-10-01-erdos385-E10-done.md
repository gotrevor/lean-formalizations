# HANDOFF 2026-10-01 — Erdős #385 phase E10 DONE (branch erdos-385-d)

Remainder.lean is sorry-free; every frozen statement `#print axioms` = [propext, Classical.choice, Quot.sound].
- `almost_all_erdos463_powerSaving`: new `Remainder/Erdos463Power.lean` — `almost_all_of_windowPowerSaving`
  (Assembly for arbitrary E), `card_shift_le_split` (E6 shifted windows in split form),
  `erdos463_windowPowerSaving` (E6 construction on LongAveragePower/DifferenceSplit at 1/8, windows 1/16).
- GoldbachWindow edges: square parameter m (least m with m² ≥ n+m, so (m²−n)/m ∈ [1,3)); finitely many
  mesh-1/K windows (`goldbachWindow_mesh`, `eventually_mesh_windows`); integer core `strip_of_gap`.
  EES uses K ≈ 2/ε; #463 uses K = 1 with f(n) = √n/4.
- Margin edges via `minFac_mul_primes`, `composite_mul_primes`.
Open: nothing in scope.  Off-scope designated-open: `nearOneLargeValues_of_density` (OFF path).

Branch `erdos-385-d`, HEAD 5bf3fe2 (before this note).
## Next (for an altitude lap)
- Update DIRECTION.md: its top CURRENT DIRECTIVE still names E9b's (proved) `localZeroDetect_of_richert`; mark E10 ✅.
- Candidate next phases: weaken `GoldbachWindow` to the single window actually used (gap ∈ [a√N,b√N] for a
  finite family suffices — `eventually_mesh_windows`), or a power-saving EES variant reusing Erdos463Power.
