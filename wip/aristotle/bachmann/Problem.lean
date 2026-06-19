/-
# Bachmann inequality for ONote.fundamentalSequence (the FGH index-monotonicity prerequisite)

GOAL: replace the `sorry` with a real proof.

CONTEXT. `ONote.fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)` assigns to each ordinal
notation below ε₀ its canonical fundamental sequence (`Mathlib/SetTheory/Ordinal/Notation.lean`):
`inl none` for 0, `inl (some a)` for a successor `a+1`, `inr f` for a limit with `f i ↑ o`.
`fundamentalSequence_has_prop` gives, in the limit (`inr f`) case:
`IsSuccLimit o.repr ∧ (∀ i, f i < f (i+1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr`.

The **Bachmann inequality** below is the single number-theoretic fact that powers pointwise
monotonicity of the fast-growing hierarchy (`ONote.fastGrowing`): for a limit `o` with fundamental
sequence `f`, when the successor term `f (n+1)` is itself a limit with fundamental sequence `g`, the
previous term `f n` is dominated by `g` at level `n+1`. (When `f (n+1)` is a successor instead, the
monotonicity step is elementary.)

VERIFIED EXAMPLE (must hold): `o = ω²`, `f i = ω·(i+1)`, `f (n+1) = ω·(n+2)` is a limit with
`g i = ω·(n+1) + (i+1)`; then `f n = ω·(n+1) ≤ ω·(n+1)+(n+2) = g (n+1)` ✓ (`le_self_add`).

SUGGESTED ATTACK: induction / case analysis following the recursive definition of
`fundamentalSequence (oadd e m b)` (the six cases fixing how `f` and then `g` are built). Most cases
reduce to `le_self_add` / monotonicity of `oadd` in its tail at the `repr` level. Carry `o.NF`.
If you cannot close it fully, make maximal honest progress and leave the narrowest possible `sorry`.
-/
import Mathlib

open ONote

theorem fundSeq_bachmann {o : ONote} [o.NF] {f g : ℕ → ONote} {n : ℕ}
    (ho : fundamentalSequence o = Sum.inr f)
    (hg : fundamentalSequence (f (n + 1)) = Sum.inr g) :
    f n ≤ g (n + 1) := by
  sorry
