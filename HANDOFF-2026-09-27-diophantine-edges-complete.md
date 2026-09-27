# Handoff: DIRECTION phase 5 COMPLETE — all three Diophantine wiring edges proved

**Date**: 2026-09-27 · **Branch**: `mills` · **HEAD**: `ab2d1d0` · **Objective**:
`sorry-free:src/LeanFormalizations/NumberTheory/Diophantine` — **MET** (run self-stopped with
`box done --green`; the treadmill will not relaunch).

**Repo state at handoff**: working tree clean, nothing pushed (no egress — the host pushes).
`lake build` → `Build completed successfully (8684 jobs)`.
`grep -rn "sorry\|admit" src/LeanFormalizations/NumberTheory/Diophantine/` → no matches.

## ✅ What landed (all observed, not assumed)
`src/LeanFormalizations/NumberTheory/Diophantine/Edges.lean` is **sorry-free**; every edge is
`#print axioms` clean (`[propext, Classical.choice, Quot.sound]`); `lake build` green, 8684 jobs.

1. `mahler_of_ridout1957 : Ridout1957 → Mahler1957` (commit `2632a94`)
2. `ridoutSUnitDen_of_ridout1957 : Ridout1957 → Ridout1957SUnitDen` (commit `9993c8a`)
3. `roth_of_ridout1958 : Ridout1958 → Roth1955` (commit `1837946`)
4. `Mills.irrational_of_ridout (hB) (hM) (hR : Ridout1957)` in `Mills/Irrational.lean` — Saito's
   irrationality with the `Mahler1957` hypothesis discharged into Ridout.  The literature bedrock
   under Mills irrationality is now BHP + Matomäki + **Ridout**.

## 🧠 The three ideas worth carrying forward
* **Mahler's §3 bookkeeping collapses if you write every power as an exponential.**  With
  `lu = log u`, `lv = log v`, `λ = lv/lu`, `μ = 1−λ`, `κ = μ + ε/(2 lu)`, both Ridout side
  conditions become *linear* inequalities in `lu, lv, ε, n`: the distance condition reduces to
  `−εn < −εn/2`, and condition (4) `p* ≤ 2p^μ` reduces (after logs) to
  `λ log p* ≤ log 2 + (1−λ) n lv`, which follows from `p* ≤ 2αⁿ` and `λ·lu = lv`.
  No rpow gymnastics survives to the end.
* **A "degree ≥ 2 integer polynomial" hypothesis never needs minpoly.**  Clear denominators of any
  algebraicity witness (`IsLocalization.integerNormalization (nonZeroDivisors ℤ)`) and multiply by
  `X² + 1`: no real root, so the root set is unchanged, and the degree bound is free.  This dodged
  the whole "an irrational's minimal polynomial has degree ≥ 2" argument in `roth_of_ridout1958`.
* **Ridout's solution sets live in ℕ×ℕ or coprime ℤ×ℤ; a ℚ-indexed statement needs a cover, not a
  bijection.**  `ridoutSUnitDen` splits ℚ into positive numerator / negative numerator (negate both
  `α` and `r`; `(-r).den = r.den` is `rfl`) / zero.  `roth` needs a *finite exceptional set* of
  small denominators, hence the new reusable helper
  `finite_den_le (D : ℕ) (B : ℝ) : {r : ℚ | r.den ≤ D ∧ |(r:ℝ)| ≤ B}.Finite`.

## ⚠️ Gotchas (cost real time this lap)
* **Do NOT introduce `μ`, `κ`, `lu`, `lv` with `set`.**  A let-valued local in context makes
  `linarith`/`nlinarith` blow the `isDefEq` heartbeat budget unfolding it — two separate 200000-
  heartbeat timeouts.  Introduce them opaquely: `obtain ⟨μ, hμ_def⟩ : ∃ x : ℝ, x = … := ⟨_, rfl⟩`,
  then `rw [hμ_def]` where the definition is genuinely needed.  Also prefer `linarith only [...]`
  in a fat context.
* `λ` is a reserved token — a hypothesis may not be named `hλ0`.
* A `Set.Finite.preimage` goal needs `(f := fun r => …)` given explicitly; it cannot infer `f`.
* Membership goals under a preimage carry a beta-redex: `dsimp only` FAILS there (the Fin 0 →
  `Nat.Primes` coercion makes the goal not type-correct at `instances` transparency).  State the
  inequality as a separate `have` in fully explicit form and close with `exact`/`simpa` — defeq
  handles the beta and projection reduction for free.
* Renamed in this pin: `le_or_lt` → `le_or_gt`; `inv_le_inv_of_le` → `inv_anti₀`;
  `0 < n → 0 < n.toNat` is `Int.pos_iff_toNat_pos.mp` (omega does *not* see through the
  `Prod.fst` of a lambda-applied pair).  `push_neg` is deprecated → `push Not at h`.

## 🎬 Next actions
The phase-5 objective is complete and there is **nothing open in `Diophantine/`**.  The `mills`
branch wants a host push + merge to `main`.  A new lap needs a **fresh `DIRECTION.md` objective**;
`Ridout1957` / `Ridout1958` themselves are frozen literature `Prop`s, not axiom debt — do not
"prove" them.

## 📁 Key files
* `src/LeanFormalizations/NumberTheory/Diophantine/Edges.lean` — the three edges + `finite_den_le`.
* `src/LeanFormalizations/Literature/Diophantine.lean` — the four frozen statements.
* `src/LeanFormalizations/NumberTheory/Mills/Irrational.lean` — `irrational_of_ridout` at the end.
