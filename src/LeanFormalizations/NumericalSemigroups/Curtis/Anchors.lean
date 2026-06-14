/-
# Curtis (1990) — faithfulness anchors

The headline theorems in `Statement.lean` are only meaningful if the definitions
they quantify over (`IsAdmissible`, `FrobeniusNumber`, and Lemma 2's value
formula) mean what Curtis means. A subtle mis-statement could make a headline
*vacuously* true. This file pins the definitions to concrete, hand-checked
witnesses — the `native_decide`/`omega`-style anchors that the audit relies on.

We use the admissible triple `⟨3, 7, 8⟩`. Its numerical semigroup is
`{0, 3, 6, 7, 8, 9, 10, …}`; the non-representable numbers are `1, 2, 4, 5`, so
the Frobenius number is `5`. The three anchors below independently confirm:

1. `⟨3, 7, 8⟩` really is admissible (so `IsAdmissible` is satisfiable, not empty);
2. mathlib's `FrobeniusNumber` of `{3, 7, 8}` is `5` — proved *directly* from the
   definition (`5` not representable; everything `> 5` is), confirming
   `FrobeniusNumber` carries Curtis's intended meaning;
3. **Lemma 2 yields the same value `5`** on this triple (with `k = 2`), confirming
   the value formula `(k−2)s₂ + s₃ − s₁` is faithful — not just internally
   consistent.

That anchors 1+2 agree with the proof's machinery, and that anchor 3 reproduces
anchor 2 by a completely different route, is the faithfulness signal.
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Engine

namespace LeanFormalizations.NumericalSemigroups.Curtis.Anchors

open LeanFormalizations.NumericalSemigroups.Curtis

/-- Anchor 1: `⟨3, 7, 8⟩` is admissible (`IsAdmissible` is non-vacuous). -/
theorem isAdmissible_3_7_8 : IsAdmissible 3 7 8 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Anchor 2: the Frobenius number of `{3, 7, 8}` is `5`, proved directly from
mathlib's definition (`5` is not a nonneg-integer combination of `3, 7, 8`, and
every `k > 5` is). This certifies that `FrobeniusNumber` means "largest
non-representable number", exactly Curtis's notion. -/
theorem frobeniusNumber_3_7_8 : FrobeniusNumber 5 ({3, 7, 8} : Set ℕ) := by
  rw [frobeniusNumber_iff]
  refine ⟨?_, ?_⟩
  · -- `5` is not representable as `3a + 7b + 8c`
    rw [Lemma2.mem_closure_triple]
    rintro ⟨a, b, c, h⟩
    have hc : c = 0 := by omega
    have hb : b = 0 := by omega
    omega
  · -- every `k > 5` is representable (cover the three residues mod `3`)
    intro k hk
    rw [Lemma2.mem_closure_triple]
    have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h | h | h
    · exact ⟨k / 3, 0, 0, by omega⟩
    · exact ⟨(k - 7) / 3, 1, 0, by omega⟩
    · exact ⟨(k - 8) / 3, 0, 1, by omega⟩

/-- Anchor 3: **Lemma 2 reproduces the value `5`** on the same triple (`k = 2`,
so the formula `(k−2)·s₂ + s₃ − s₁ = 0·7 + 8 − 3 = 5`). Independent confirmation
of the value formula's faithfulness. -/
theorem frobeniusNumber_3_7_8_via_lemma2 : FrobeniusNumber 5 ({3, 7, 8} : Set ℕ) :=
  Lemma2.lemma2 3 7 8 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanFormalizations.NumericalSemigroups.Curtis.Anchors
