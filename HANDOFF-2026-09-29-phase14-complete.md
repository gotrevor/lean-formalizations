# HANDOFF — phase 14 COMPLETE (2026-09-29)

**Mills' constant is transcendental under RH is formalized.**
`src/LeanFormalizations/NumberTheory/Mills/TranscendentalRH.lean` is **sorry-free**, and both
frozen phase-14 theorems are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`):

- `pisot_branch_otherConj_real` — Saito 2025 Thm 1.7, first half (unconditional): in the Pisot
  branch the cubic Pisot number `β = A^(3^m)` has *no* complex pair of conjugates.
- `transcendental_of_RH` — Saito 2025 Thm 1.8: `Transcendental ℚ A` for the least Mills number,
  from `Schoenfeld1976 + RiemannHypothesis` (plus the standing BHP / Matomäki / Dubickas inputs).

## The route as actually built (differs from the file header in two places)

1. `cube_re` — `Re(w³) = 4(Re w)³ − 3‖w‖²(Re w)`: the triple-angle identity with **no trig**, so
   the `×3` map on the circle becomes a cubic recursion.
2. `eq_neg_one_of_triple_orbit` — `c_{j+1} = 4c_j³ − 3c_j`, all `c_j ∈ [−1,0)` ⟹ `c_0 = −1`.
   Mechanism: `c_{j+1}+1 = (c_j+1)(2c_j−1)²` with `(2c_j−1)² > 4` (from `4c² > 3`), so
   `c_j + 1 ≥ 4ʲ(c_0+1)` while `c_j + 1 ≤ 1`.  **Replaces** the header's `mod 1` interval
   argument: no fractional parts, no `Complex.arg`.
3. `eq_floor_of_abs_lt_half`, `newton_cube_gap`, `pair_pow_sum_re_neg` — trace = Mills prime, plus
   `p_k³ − p_{k+1} = 3s(x₁² + x₁s + x₂x₃)`, giving `s_i < 0` for all large `i`.
4. `pow_im_eq_zero_of_re_neg` + `pisot_pow_two_of_pow_eq` — the complex case.  **The header left
   the endgame open; the cheap closure is:** once `u^N = v^N = y ∈ ℝ`, the *two* trace relations
   `β^N + 2y = t` and `β^{2N} + 2y² = T` give the explicit integer quadratic
   `3x² − 2tx + (t² − 2T) = 0` killed by `x = β^N`, so `deg β^N ≤ 2`; `u^N ∈ otherConj(β^N)` pins
   `deg = 2`, and `not_pisot_two_of_cube` (Saito 2024 Lemma 4.3, already proved) finishes.  **No
   Galois / embedding machinery** (`range_eval_eq_rootSet_minpoly`, root-set transport) is needed.
5. `log_sq_le_sqrt`, `exists_prime_short_interval` — under RH there is a prime in
   `(y, y + √y (log y)²]` for `y ≥ 41000`.  The `log²` is **essential**: with `g ≍ √y log y` the
   main term `g/log(y+g)` is only `≍ √y` and loses to the `√y log y /(8π)` Schoenfeld error.
6. `digits_eq_gseq`, `gap_le_of_RH` — under RH the least Mills number's digits *are* `gseq`
   (`gseq_le_digits` up, minimality against `exists_greedy_mills` down), so `p_{k+1} = lpa(p_k³)`
   and step 5 caps the gap.
7. `equal_norm_contradiction` — `‖u‖ = ‖v‖` with both real and distinct forces `v = −u`, and then
   `s_i = 0` for the **odd** exponent `N = 3ⁱ`, contradicting `s_i < 0`.  Cheap.
8. `real_case_contradiction` — `ρ = ‖u‖/‖v‖ > 1`, `|s| ≥ ‖u‖^N/2`, so `gap ≥ (3/4)‖u‖^N X²`.
   Squaring against `gap ≤ √Y (log Y)²`, `Y ≤ X³`, `log Y ≤ 3N log β` yields
   `(9/16)(β‖u‖²)^N ≤ 81 N⁴ (log β)⁴`; with `β‖u‖² ≥ ρ` (field norm `β‖u‖‖v‖ ≥ 1`) this contradicts
   `N⁴/ρ^N → 0`.

## Lean gotchas from this lap

- Work with **squares** throughout step 8 to avoid `β^(N/2)`-style half powers.
- In a context this large, `set` (let-valued locals) blows the `isDefEq`/linarith budget; use
  `obtain ⟨X, hXdef⟩ : ∃ X, X = … := ⟨_, rfl⟩` and rewrite by hand.  `maxHeartbeats 1600000`
  is still needed for `real_case_contradiction`.
- `rw [hure]` where `hure : u = ((u.re : ℝ) : ℂ)` rewrites the `u` inside `u.re` too — use
  `conv_lhs => rw [hure]`.

## NEXT

Phase 14's stop condition is met.  Open items elsewhere in the repo are the phase-9/13 disclosed
Corvaja–Zannier `sorry`s (`DubickasNoSubspace.lean`, `CorvajaZannier.lean`) — DESIGNATED OPEN by
`DIRECTION.md`; phase 13/13b are parked.  A new direction is an altitude-lap decision.
