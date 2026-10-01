# HANDOFF 2026-10-01 — Erdős #385 E5 (linear sieve) lap 1

Branch `erdos-385`, HEAD `144ad24` (+ this note). Worktree clean. Target: `LinearSieve.lean` sorry-free
in substance. Its file text has no `sorry`, but it imports the crux `LinearSieve.siftMin_lower`
(`LinearSieve/Crux.lean`, disclosed `sorry`). NOT done; do not `box done`.

## Proved (sorry-free, in `src/LeanFormalizations/NumberTheory/Erdos385/LinearSieve/`)
- `Buchstab.lean`: problem class (interval, one class per prime < z), `sift`, `siftMin/siftMax`,
  exact `sift_buchstab`, self-similarity `hit_eq_sift`, `siftMin_buchstab`, `siftMax_buchstab`.
- `LinearSieve.lean`: frozen `linearSieveIntervalLower_holds` from `siftMin_lower`.
- `Comparison.lean`: `comparison_principle` (step 5; weight u−1 + Tonelli; K ≡ 0).
- `Selberg.lean`: CRT `exists_crt`, `probSieve` BoundingSieve, `siftMax_le_selberg`:
  S⁺(N,z) ≤ N/selG z ξ + selE z ξ².
- `GLower.lean`: `sum_inv_le_prod`, `log_le_selG` (G ≥ log ξ for ξ < z), `selE_le` (E ≤ ξ·Π(ξ)).

## Route (full plan in LinearSieve.lean header "Decomposition")
Normalise a(s)=liminf S⁻(N,N^{1/s})logN/N, b = limsup S⁺. Remaining:
1b. Π(ξ) = mertensP ξ ≪ log ξ (repo Mertens: `mertens_third_classical_eGamma`) ⇒ b ≤ 2 on [1,2].
2. Limit Buchstab integral inequalities (Mertens 2nd; a, b monotone ⇒ Riemann sums).
3. Fundamental lemma |a−Cs|,|b−Cs| ≤ η(s), C=e^{-γ} (Buchstab from w=2 + Selberg + Rankin).
4. Comparison functions α=λ(sω−m/2), β=λ(sω+m/2), λ=C/ω_∞ ≥ 1 (forward rough-number Buchstab + PNT).
5. Done; then apply comparison_principle to K=max(α−a, b−β, 0) ⇒ a ≥ 2log(s−1) on (2,3].
Refuted shortcut: one Buchstab step on Selberg reaches only s ≳ 2.05 (Maze row, scripts/linear-sieve-onestep.py).
Next attack: plant step 2–4 statements as named sorries in a new `LinearSieve/Limits.lean`, then 1b.
