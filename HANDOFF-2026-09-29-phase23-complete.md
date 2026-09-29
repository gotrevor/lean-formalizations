# HANDOFF 2026-09-29 — phase 23 COMPLETE: Schanuel ⇒ log π, π^e, π^π

`NumberTheory/Transcendence/SchanuelPi.lean` is **sorry-free**; all five frozen statements are
machine-checked and `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  Full
`lake build` green (8735 jobs).  Commit `e08dfd7`.

## The five

| statement | route |
|---|---|
| `algebraicIndependent_exp_one_pi_log_pi` | Schanuel at `z = (1, iπ, log π)`, exponentials `e, −1, π` |
| `transcendental_log_pi` | index 2 of the triple |
| `algebraicIndependent_pi_rpow_exp_one` | Schanuel at `z = (1, iπ, log π, e·log π)`, exponentials `e, −1, π, π^e` |
| `transcendental_pi_rpow_exp_one` | index 3 of the quadruple |
| `transcendental_pi_rpow_pi` | same bootstrap with `c₀ = π` |

## The crux was step 0, not the bootstrap

`ℚ`-linear independence of `(1, iπ, log π)` needs `log π` **irrational**, which is open
unconditionally.  `irrational_log_pi` spends Schanuel's own phase-15 `e, π` independence: if
`log π = n/d` then `π^d = e^n`, so `π` is a root of `X^d − C(e^n)` over `ℚ(e)`.
(`Polynomial.monic_X_pow_sub_C` for `≠ 0`; `map_zpow₀` to push the coefficient through
`algebraMap ℚ⟮e⟯ ℂ`.)

## The second design point: one bootstrap serves both π^e and π^π

`linearIndependent_quad` is uniform in `c₀`: a relation `a + b·iπ + c·log π + d·c₀·log π = 0`
has `b = 0` (imaginary part), and then either `c + d c₀ ≠ 0` — putting `log π ∈ ℚ(c₀)`, against
the *pair* `(c₀, log π)` restricted out of step 1 — or `c + d c₀ = 0`, which forces `d = c = 0`
by irrationality of `c₀`.  Only the membership `c₀ ∈ ℚ(e, π, log π, π^{c₀})` needs the case
split (`hc2 : c = Real.exp 1 ∨ c = Real.pi`).

## Gotchas

1. `Fintype.linearIndependent_iff` + `Fin.sum_univ_three/four` + `Rat.smul_def`, then
   `simp at him hre`: the imaginary part is **already solved** to `g 1 = 0` — no disjunction to
   `rcases` (`Real.pi_ne_zero` is discharged by `simp` itself).
2. `algebraMap_mem` is ambiguous under `open IntermediateField`; spell
   `IntermediateField.algebraMap_mem`.
3. `field_simp` on `log π = −a/(c + d c₀)` produces a doubled-up target; use
   `rw [eq_div_iff hne']` + `linear_combination` instead.
4. `isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q` gives `IsAlgebraic ℚ ((algebraMap ℚ ℂ) q)`, not
   `IsAlgebraic ℚ (↑q)` — wrap in `by simpa using`.

## Nothing false or underivable

Every statement was derivable as planted.

## Checkpoint (treadmill stop, 2026-09-29)

* **Branch:** `main`.  **HEAD at write time:** `60421f5` (this doc), proof commit `e08dfd7`.
* **Working tree:** clean.  Full `lake build` green (8735 jobs), verified by the pre-commit hook.
* **Scope status:** the phase-23 objective (`sorry-free:.../SchanuelPi.lean`) is **met**.
  `grep -c sorry` on that file = 0; all five frozen statements `#print axioms`-clean.
  `box done --green` was signalled.
* Every other `sorry` in the repo is designated-open (audit surface / heroic holes) and was not
  touched this lap.

### Exact next steps (for whoever plants phase 24)

1. **New names now available for reuse** (all in `LeanFormalizations.Schanuel`, `SchanuelPi.lean`):
   `irrational_log_pi`, `cexp_ofReal_log_pi`,
   `algebraicIndependent_exp_one_pi_log_pi_complex` / `_real`,
   `algebraicIndependent_pair_exp_one_log_pi`, `algebraicIndependent_pair_pi_log_pi`,
   `linearIndependent_quad`, `algebraicIndependent_pi_rpow`.
2. **`algebraicIndependent_pi_rpow` generalizes cheaply.**  Its only `c`-specific hypothesis is
   `hc2 : c = Real.exp 1 ∨ c = Real.pi`, used *once*, purely to place `c` inside
   `ℚ(e, π, log π, π^c)`.  Replacing `hc2` by a direct membership hypothesis would give
   `π^c` transcendental for any irrational real `c` alg.-independent from `log π` — e.g. a
   `π^{log π}` or `e^{π^…}` extension, or the `(log π)`-tower analogue of
   `algebraicIndependent_wright_tower`.
3. **Uncovered Waldschmidt 2023 survey items still open** (see `WALDSCHMIDT-2023.md`):
   Leopoldt §2 and Conjecture 7 (Roy's equivalent of Schanuel).  §5 structural rank was
   phase 20.
