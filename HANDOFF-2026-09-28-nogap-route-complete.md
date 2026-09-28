# HANDOFF 2026-09-28 — Dubickas phase 8: the no-gap route is proved end to end

Branch `main`, HEAD `68a5082`.  Working tree clean.  `lake build` green (8707 jobs); the only
`sorry` in the repo is the one disclosed `deg β ≥ 6` case in `DubickasNoGap.lean:52`.

## What happened this lap

DIRECTION phase 8 asked for `c_eq_zero_or_two_noGap` from `Dubickas2022` alone, or a written
obstruction.  **There is no obstruction.**  A degree-uniform elementary route exists; it is
written up in `PROBE-DUBICKAS-NOGAP.md` and is now **formalized end to end, sorry-free and
axiom-clean**, in six new files:

| file | headline | what it gives |
|---|---|---|
| `MultisetNewton.lean` | `multiset_isRatInt_factorial_mul_esymm` | Newton for multisets; `k!·eₖ ∈ ℤ` from integral power sums |
| `MultisetGraeffe.lean` | `esymm_map_sq` | `(−1)^k eₖ(s²) = Σ_{i+j=2k} (−1)^i eᵢ e_j` |
| `DubickasEsymm.lean` | `eFull_succ`, `isRatInt_factorial_mul_eFull`, `norm_eSmall_le` | bridge to `otherConj β` |
| `DubickasWeight.lean` | `weight_bound` | the parity-weight induction |
| `DubickasNormalized.lean` | `eFull_eq_zero_of_odd`, `AA_odd_succ` | odd `Eₙ` vanish; `A` normalization |
| `DubickasBSeq.lean` | `bb_rec_approx` | the finite-`j` recursion, error `O(q_j²)` |
| `DubickasLimit.lean` | **`eFull_two_const_eq_zero_or_one`** | the conclusion |
| `DubickasBRec.lean` | `eq_zero_or_one_of_bRec_finite_support` | the combinatorial finish |

**The theorem now available** (`DubickasLimit.lean`):

    eFull_two_const_eq_zero_or_one (hβ : IsPisot β) {z : ℂ} {J₀ : ℕ}
      (hE2 : ∀ j ≥ J₀, eFull β 2 (2 ^ j) = z) : z = 0 ∨ z = 1

No Lemma-8-strength lower bound on `|S_N|` appears anywhere.  `#print axioms` on every headline
above = `[propext, Classical.choice, Quot.sound]`.

## NEXT (one step, then phase 8 is done)

1. In `DubickasNoGap.lean`, replace the whole `rcases … with hLc | …` case analysis (or just the
   `5 ≤ L` branch) by a single application of `eFull_two_const_eq_zero_or_one`.  The only glue
   needed is turning `hident` into the hypothesis `hE2`:

   `hident j : (c : ℂ) = 2 * βᴺ * conjPowSum β N + (conjPowSum β N)² − conjPowSum β (2N)`
   with `N = 2^j`.  And `eFull β 2 (2^j) = eSmall β 2 (2^j) + βᴺ · eSmall β 1 (2^j)`
   (`eFull_succ` with `k = 1`), where `eSmall β 1 N = conjPowSum β N` (both are the sum of the
   multiset — `Multiset.esymm 1` is `Multiset.sum` after `powersetCard_one`) and
   `eSmall β 2 N = (S_N² − S_{2N})/2` (Newton `k = 2` on the small conjugates, or
   `multiset_mul_esymm_eq_sum` at `k = 2`).  So `eFull β 2 (2^j) = c/2` and `z = c/2`, giving
   `c = 0 ∨ c = 2`.
   ⚠ The one genuinely new mini-lemma to write: `eSmall β 1 N = conjPowSum β N` and
   `2 * eSmall β 2 N = (conjPowSum β N)^2 − conjPowSum β (2*N)`.
2. Then, per DIRECTION: drop `hG : Dubickas2022PisotGap` from
   `transcendental_growth_of_monic_quadratic`, `theorem1`, `oeis_constants` in `Dubickas.lean`
   (names/paths unchanged — OEIS-linked), route through `c_eq_zero_or_two_noGap`, update
   `Comparator/Dubickas/Challenge.lean`, and check `scripts/comparator-probe Dubickas` says
   identical.
3. `#print axioms` the three `Dubickas.lean` headlines; they should stay on the trust base with
   only `Dubickas2022` as a hypothesis.

## Notes / gotchas hit this lap

* `squeeze_zero_norm'`'s bounding-function argument is named `a`, not `g`.
* `tendsto_finset_sum` is deprecated → `tendsto_finsetSum`.
* `n + 1 - 1` does *not* match `n` syntactically; `simp only [Nat.add_sub_cancel]` before `rw`.
* `Finset.not_mem_empty` → `Finset.notMem_empty`; `le_or_lt` gone → `Nat.lt_or_ge`.
* `Finset.sum_def` does not exist; use `Finset.sum`.
* Over a bare `Field`, `linarith` cannot finish `-C = 0 ⊢ C = 0` — use `linear_combination`.
