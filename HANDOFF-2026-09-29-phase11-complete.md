# HANDOFF 2026-09-29 — phase 11 COMPLETE

**State**: `main` @ `6a0452b`, working tree clean, `lake build` green (8711 jobs).

**Scoped objective met**: `src/LeanFormalizations/NumberTheory/PolyIteration/` is sorry-free.
All 25 `sorry`s in `PolyIteration/Siblings.lean` are discharged and every phase-11 headline is
`#print axioms`-clean (`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no
`native_decide`/`Lean.ofReduceBool`).

Full route write-up (the `sub_dvd_sub_addMul` workhorse, the `HasSum` route via
`summable_of_sum_range_le`, the mod-4 square obstruction, `4a(n+1) = (2a n − 1)² + 3`, the
`864 ∣ 432 n(1+3n)` parity step, Mohanty via `intGcd_congr_of_dvd_sub`) is at the top of
`PENDING_WORK.md` under **PHASE 11 — CLOSED 2026-09-29**.

**Untouched, by direction**: the two disclosed Corvaja–Zannier `sorry`s in
`NumberTheory/Transcendence/DubickasNoSubspace.lean` (phase 9, designated-open).

**Gotchas worth reusing**
* `decide` on a goal reached by `subst` of a context variable can fail with *"expected type must
  not contain free variables"* even when the goal itself is closed — put the concrete fact in its
  own private lemma (`neg_three_isSquare_two`) proved before the substitution.
* `convert h using 1` on `IsCoprime` descends further than expected; rewrite the argument with an
  explicit `have e : … := by ring` and `exact` instead.
* `linear_combination` sign: check the printed residual is `2 ×` the goal difference — that means
  you want `-h`, not `h`.

**Next** (out of this run's scope): phase 12 has no objective set in `DIRECTION.md`; an altitude
lap owns picking it.
