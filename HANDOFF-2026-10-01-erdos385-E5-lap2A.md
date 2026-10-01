# HANDOFF 2026-10-01 — Erdős #385 E5 (linear sieve), session A lap 2

Branch `erdos-385`, HEAD `cd71a56`.  ⚠ Session B commits to this same worktree concurrently
(see `HANDOFF-2026-10-01-erdos385-E5-lap2.md`, its own).  Commit only your own paths
(`git commit -- <paths>`); index.lock collisions are transient, retry after ~30s.

Scoped target: `LinearSieve/Crux.lean` sorry-free *in substance*.  Its text has no `sorry`, but it
depends on `Leaves.fundamental_lemma` (the ONLY open leaf left).  NOT done; do not `box done`.

## Proved by A this lap (all sorry-free)
- `UpperAt.lean`: `upperAt_of_theta` (Selberg UpperAt at any level), `upperAt_two`.
- `Bounded.lean`: `bSeq_bdd`, `bUp_mono'`, `aSeq_cobdd`, `aLow_nonneg'`, `aLow_mono'`.
- `BuchstabLimit.lean`: Mertens window `tendsto_primeRecip_window`, `eventually_sum_window_le`.
- `BuchstabBin.lean`: `eventually_bin_le`, `aLow_ge_bins_delta`, `aLow_ge_bins`.
- `BuchstabLimitA.lean`: `riemann_delay_le`, **`buchstab_limit_a'`**.
- `BuchstabLimitB.lean`: `eventually_bin_ge`, `bUp_le_bins`, `riemann_delay_ge`, **`buchstab_limit_b'`**.
- `RoughLimit.lean`: **`phiL_buchstab`** ⇒ `RoughOmega.phi_buchstab` (omega_le / comparison_functions now sorry-free).
- `FLLower.lean`: `Vw`, `sum_Vw_div` (Σ_{p<z} V(p)/p = 1 − V(z)), `primeProd_log_bounds`.

## Claimed by A (see PENDING_WORK.md CLAIMS): fundamental_lemma LOWER half
Plan (FLLower.lean): hypothesis `UpperFLHyp c K C` := ∀ M w ξ, 2≤w, 2≤ξ →
S⁺(M,w) ≤ M V(w)(1+K e^{−c log ξ/log w}) + (Cξ log ξ)²  (B's step (b) shape).
1. L3: Σ_{p<z} V(p)/p · e^{−κ log N/log p} ≤ A' V(z) e^{−κ s} — V(p) ≤ 2A₁/log p, V(z) ≥ A₂/log z,
   dyadic u-ranges with uniform Mertens-2nd (Σ_{x<p≤x²}1/p ≤ log2+B).
2. Assembly: siftMin N z ≥ N − Σ_{p<z} siftMax(N/p+1,p) (siftMin_buchstab with w=2, sift_two);
   ξ_p = ⌊(N/p)^{1/3}⌋; errors ≤ z·N^{2/3}log²N (s ≥ 4); c ≥ 4 ⇒ rate 4/3 > 1;
   liminf with V(z)log N → e^{−γ}s (mertens_third_classical_eGamma); small s trivial (M large).
B keeps upper half (a)–(c) and wiring `fundamental_lemma`.
