/-
# Faithfulness bridge to DeepMind `formal-conjectures` — the publication reference

**This is the file to cite when submitting the planar-Kakeya result to
`google-deepmind/formal-conjectures` (their `kakeya_2d`).** It *machine-checks* that our headline
`davies_kakeya_2d` proves **exactly** DeepMind's stated conjecture — not a weakened, vacuous, or
reworded cousin.

We cannot `import` their repo directly: it pins **mathlib v4.27.0** while this repo is on **v4.31.0**,
and cross-repo Lean imports require an identical mathlib revision. So we restate their definitions
**verbatim** (transcribed from the sources below) and prove the bridge against that transcription.

**DeepMind sources** — confirm this transcription against these three lines (a 3-line textual diff):
* `ℝ^n` notation        — `FormalConjecturesForMathlib/Geometry/Euclidean.lean:22`
  (`scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)`)
* `IsKakeya`            — `FormalConjectures/Wikipedia/Kakeya.lean:37`
* `KakeyaSetConjectureDim` — `FormalConjectures/Wikipedia/Kakeya.lean:54`
  (their `kakeya_2d : KakeyaSetConjectureDim 2 := by sorry` is at line 70)

**What is proved below** (all axiom-clean — `#print axioms = [propext, Classical.choice, Quot.sound]`):
1. `kakeya_pred_defeq`           — our `IsKakeya` *is* theirs, definitionally (`Iff.rfl`).
2. `kakeya_statement_defeq`      — our `KakeyaSetConjectureDim 2` *is* theirs, definitionally (`Iff.rfl`).
3. `formalConjectures_kakeya_2d` — our proven `davies_kakeya_2d`, unadapted, inhabits their statement.

**Trust chain:** (1)–(3) are kernel-checked here; the only remaining human step is confirming the
`FormalConjectures` block below matches the three cited DeepMind lines. Statement faithfulness then
rests on DeepMind's curated definition + mathlib's `dimH` — the two intended authorities.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Statement

open Set MeasureTheory

namespace LeanFormalizations.Kakeya2D

/-- DeepMind's `ℝ^n` notation, transcribed verbatim **including the exact `scoped[EuclideanGeometry]`
form** (`FormalConjecturesForMathlib/Geometry/Euclidean.lean:22`), then activated with
`open scoped EuclideanGeometry` exactly as their `Wikipedia/Kakeya.lean` does. -/
scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
open scoped EuclideanGeometry

/- Verbatim transcription of DeepMind `formal-conjectures`' Kakeya definitions
(`FormalConjectures/Wikipedia/Kakeya.lean:37,54`), to bridge our headline against. -/
namespace FormalConjectures

def IsKakeya {n : ℕ} (S : Set (ℝ^n)) : Prop :=
  ∀ v, ‖v‖ = 1 → ∃ a, affineSegment ℝ a (a + v) ⊆ S

def KakeyaSetConjectureDim (n : ℕ) : Prop :=
  ∀ S : Set (ℝ^n), IsKakeya S → dimH S = n

end FormalConjectures

/-- Our `IsKakeya` and DeepMind's are the **same predicate by definition**. -/
theorem kakeya_pred_defeq (S : Set (EuclideanSpace ℝ (Fin 2))) :
    IsKakeya S ↔ FormalConjectures.IsKakeya S := Iff.rfl

/-- Our `KakeyaSetConjectureDim 2` and DeepMind's are the **same proposition by definition**. -/
theorem kakeya_statement_defeq :
    KakeyaSetConjectureDim 2 ↔ FormalConjectures.KakeyaSetConjectureDim 2 := Iff.rfl

/-- **Our proven headline directly discharges DeepMind's `kakeya_2d`.** `davies_kakeya_2d`, with no
adaptation, inhabits DeepMind's verbatim statement — so closing their line-70 `sorry` is exactly
this theorem. -/
theorem formalConjectures_kakeya_2d : FormalConjectures.KakeyaSetConjectureDim 2 :=
  davies_kakeya_2d

end LeanFormalizations.Kakeya2D
