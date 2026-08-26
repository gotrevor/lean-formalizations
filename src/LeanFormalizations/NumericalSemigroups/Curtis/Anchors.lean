/-
# Curtis (1990) — faithfulness anchors

The headline theorems in `Statement.lean` are only meaningful if the definitions
they quantify over (`IsAdmissible`, `FrobeniusNumber`, and Lemma 2's value
formula) mean what Curtis means. A subtle mis-statement could make a headline
*vacuously* true. This file pins the definitions to concrete, hand-checked
witnesses — the `decide`/`norm_num`/`omega`-style anchors that the audit relies on.

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

## Additional anchors (more `FrobeniusNumber` ↔ Lemma-2 agreements)

To widen the faithfulness evidence beyond a single triple, we add three more
admissible triples on which Curtis's Lemma-2 value formula `(k−2)·s₂ + s₃ − s₁`
agrees with mathlib's independently-defined `FrobeniusNumber`:

- `⟨3, 7, 11⟩`, `k = 2`: value `0·7 + 11 − 3 = 8` (also verified a *second* way,
  directly from the definition, in `frobeniusNumber_3_7_11`);
- `⟨3, 13, 14⟩`, `k = 2`: value `0·13 + 14 − 3 = 11`;
- `⟨5, 11, 23⟩`, `k = 3`: value `1·11 + 23 − 5 = 29` (exercises `k = 3`, so the
  `(k−2)` coefficient is non-trivial here, not just `0`).

`⟨3, 7, 11⟩` is an independent point at which two unrelated computations of "the Frobenius
number" coincide (`frobeniusNumber_3_7_11` direct, and `..._via_lemma2`), as is `⟨3, 7, 8⟩`
above. `⟨3, 13, 14⟩` and `⟨5, 11, 23⟩` widen the coverage of the value formula (including
`k = 3`) without a second, independent route.
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

/-- Anchor 4 (admissibility): `⟨3, 7, 11⟩` is in Curtis's family. -/
theorem isAdmissible_3_7_11 : IsAdmissible 3 7 11 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Anchor 4 (Lemma 2): the Frobenius number of `⟨3, 7, 11⟩` is `8`, via Lemma 2
with `k = 2` (`(2−2)·7 + 11 − 3 = 8`). -/
theorem frobeniusNumber_3_7_11_via_lemma2 : FrobeniusNumber 8 ({3, 7, 11} : Set ℕ) :=
  Lemma2.lemma2 3 7 11 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Anchor 4 (direct, second route): the Frobenius number of `⟨3, 7, 11⟩` is `8`,
proved directly from mathlib's definition (`8` not representable; every `k > 8`
is, covering the three residues mod `3`). Agrees with the Lemma-2 value `8`. -/
theorem frobeniusNumber_3_7_11 : FrobeniusNumber 8 ({3, 7, 11} : Set ℕ) := by
  rw [frobeniusNumber_iff]
  refine ⟨?_, ?_⟩
  · rw [Lemma2.mem_closure_triple]
    rintro ⟨a, b, c, h⟩
    omega
  · intro k hk
    rw [Lemma2.mem_closure_triple]
    have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h | h | h
    · exact ⟨k / 3, 0, 0, by omega⟩
    · exact ⟨(k - 7) / 3, 1, 0, by omega⟩
    · exact ⟨(k - 11) / 3, 0, 1, by omega⟩

/-- Anchor 5 (admissibility): `⟨3, 13, 14⟩` is in Curtis's family. -/
theorem isAdmissible_3_13_14 : IsAdmissible 3 13 14 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Anchor 5 (Lemma 2): the Frobenius number of `⟨3, 13, 14⟩` is `11`, via Lemma 2
with `k = 2` (`(2−2)·13 + 14 − 3 = 11`). -/
theorem frobeniusNumber_3_13_14_via_lemma2 : FrobeniusNumber 11 ({3, 13, 14} : Set ℕ) :=
  Lemma2.lemma2 3 13 14 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Anchor 6 (admissibility): `⟨5, 11, 23⟩` is in Curtis's family. -/
theorem isAdmissible_5_11_23 : IsAdmissible 5 11 23 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Anchor 6 (Lemma 2): the Frobenius number of `⟨5, 11, 23⟩` is `29`, via Lemma 2
with `k = 3` (`(3−2)·11 + 23 − 5 = 29`). Unlike the other anchors this uses
`k = 3`, so the `(k−2)·s₂` term is genuinely present. -/
theorem frobeniusNumber_5_11_23_via_lemma2 : FrobeniusNumber 29 ({5, 11, 23} : Set ℕ) :=
  Lemma2.lemma2 5 11 23 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Anchor 7 (outside Curtis's family): the classic Chicken-McNugget number,
`FrobeniusNumber 43 {6, 9, 20}`. The triple `⟨6, 9, 20⟩` is NOT admissible (`6` is
not prime), so this exercises mathlib's `FrobeniusNumber` predicate on a surface
*outside* Curtis's `IsAdmissible` family — a different faithfulness check than the
Lemma-2 anchors. Proved directly (`43` not representable as `6a + 9b + 20c`; every
`k > 43` is, covering the six residues mod `6`). No `native_decide` is used here, so these
anchors add nothing to the trust base. (Scope: this file. Elsewhere in the repo the Goodstein
growth closures do carry `native_decide` artifacts - see `STATUS.md`.) -/
theorem frobeniusNumber_6_9_20 : FrobeniusNumber 43 ({6, 9, 20} : Set ℕ) := by
  rw [frobeniusNumber_iff]
  refine ⟨?_, ?_⟩
  · rw [Lemma2.mem_closure_triple]
    rintro ⟨a, b, c, h⟩
    omega
  · intro k hk
    rw [Lemma2.mem_closure_triple]
    have h6 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
    rcases h6 with h | h | h | h | h | h
    · exact ⟨k / 6, 0, 0, by omega⟩
    · exact ⟨(k - 49) / 6, 1, 2, by omega⟩
    · exact ⟨(k - 20) / 6, 0, 1, by omega⟩
    · exact ⟨(k - 9) / 6, 1, 0, by omega⟩
    · exact ⟨(k - 40) / 6, 0, 2, by omega⟩
    · exact ⟨(k - 29) / 6, 1, 1, by omega⟩

end LeanFormalizations.NumericalSemigroups.Curtis.Anchors
