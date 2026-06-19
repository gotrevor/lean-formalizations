# Planar Kakeya set conjecture (Davies 1971)

> Every Kakeya (Besicovitch) set in `ℝ²` — a set containing a unit line segment in every
> direction — has Hausdorff dimension `2`.

R. O. Davies, *Some remarks on the Kakeya problem*, Math. Proc. Cambridge Philos. Soc. **69**
(1971), 417–421. The `n = 2` case of the Kakeya set conjecture; `n = 3` is Wang–Zahl (2025).

## What to audit (the whole trusted surface)
Two items in this directory, nothing else:
1. `Defs.lean` — `IsKakeya` and `KakeyaSetConjectureDim`. These mirror
   `google-deepmind/formal-conjectures`' `FormalConjectures/Wikipedia/Kakeya.lean` **verbatim**.
2. `Statement.lean` — `davies_kakeya_2d : KakeyaSetConjectureDim 2`, i.e. exactly
   *every Kakeya set in `ℝ²` has `dimH = 2`*.

## Status
- ✅ `dimH_le_two` — upper bound `dimH S ≤ 2` for any planar set. **Proven, axiom-clean**
  (`#print axioms = [propext, Classical.choice, Quot.sound]`).
- ⏳ `two_le_dimH` — Davies' actual content `2 ≤ dimH S`. **Open crux** (disclosed `sorry`).
  Córdoba `L²`/bush strategy laid out in `PLAN.md`.
- `davies_kakeya_2d` is assembled from the two halves, so closing `two_le_dimH` completes it.

## Why this is the genuine work
The upper bound is free (any subset of the plane has dimension `≤ 2`). All the mathematics is in
the lower bound, which requires building δ-tube geometry, the two-tube overlap estimate, the
Córdoba `L²` content bound, and the Minkowski→Hausdorff bridge — none of which is in mathlib. This
is a single-paper harmonic-analysis result, expected to take many laps. See `PLAN.md`.

## Portability
Because the definitions match `formal-conjectures` verbatim, a finished proof drops directly onto
that repo's `kakeya_2d` `sorry` (the DeepMind submission is gated by the Proof-Legal/Google-CLA step).
