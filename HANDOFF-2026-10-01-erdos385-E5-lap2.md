# HANDOFF 2026-10-01 — Erdős #385 E5 (linear sieve) lap 2 (session B)

Branch `erdos-385`, HEAD `09794e2`.  ⚠ Another session commits to this same worktree concurrently
(it owns step 2: BuchstabLimit*/BuchstabBin/Bounded/UpperAt).  Commit only your own paths (`git commit -- <paths>`).
Scoped target: `LinearSieve.lean` + `LinearSieve/` sorry-free.  NOT done.

## Proved this lap (sorry-free)
- `MertensBound.lean`: Π(ξ) ≪ log ξ, `siftMax_le_explicit`.  `UpperBoundary.lean`: `bUp_le_two`.
- `Normalized.lean`: aLow/bUp, `lower_of_aLow_pos`.  Crux `lowerAt_pos` ⇐ `aLow_pos_of_leaves` (Leaves.lean).
- `Assembly.lean`: `pos_of_delay_system` (comparison principle on K=max(α−a,b−β,0)); `aLow_pos_of_leaves` proved.
- `DelayConstruct/DelayP/DelayQ/DelaySolution.lean`: delay ODE solved; P>0, P ≤ 2e⁵e^{−s}; Q/(2s)→ω with e^{−s} rate;
  `comparison_functions` (takes `omega_le` hypothesis).
- `Rough.lean`, `RoughPNT.lean` (PNT via PNT+ `pi_alt`, axiom-clean), `RoughOmega.lean`: `omegaLe_of_bUp`
  (ω ≤ e^{−γ} from b ≤ Cs+Me^{−s}) modulo leaf `phi_buchstab`.
- `fundamental_lemma` weakened to one-sided form (a ≥ Cs−Me^{−s}, b ≤ Cs+Me^{−s}).
- `Rankin.lean`: `mertensP_sub_selG_le`: Π(z−1) − G_z(ξ) ≤ ξ^{−ε}∏_{p<z}(1+p^ε/(p−1)).

## Open sorries in scope
1. `fundamental_lemma` (Leaves.lean) — MINE.  Next: (a) ∏(1+p^ε/(p−1)) ≤ Π(z−1)·exp(Σ(p^ε−1)/p),
   Σ_{p<z}(p^ε−1)/p ≤ ε z^ε Σ log p/p ≤ c e^c(1+B/log2) with ε=c/log z (`mertens_first_prime`);
   (b) uniform upper FL S⁺(M,w) ≤ M V(w)(1+K e^{−c log ξ/log w}) + E(ξ)² via `siftMax_le_selberg`;
   (c) b-limit with Mertens 3rd; (d) lower half: Buchstab from w=2 (S⁻ ≥ N − Σ_{p<z} S⁺(N/p+1,p)),
   Σ V(p)/p telescopes to 1−V(z); error via V(p)/V(z) ≤ A log z/log p (mertensP_le_log + sum_inv_le_prod)
   and dyadic-in-log p Mertens sums, weight e^{−c s 2^{k−1}}.
2. `phi_buchstab` (RoughOmega.lean) — copy the other session's buchstab_limit_b bin machinery with
   rough in place of siftMin (hit_rough/rough_buchstab give the exact identity).
3. `buchstab_limit_b` (Leaves.lean) — other session.
