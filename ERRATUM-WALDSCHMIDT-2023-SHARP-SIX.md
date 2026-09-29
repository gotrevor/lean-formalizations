# Erratum: Waldschmidt 2023, p. 8, the "shifted" six exponentials statement is false as printed

**Finding (2026-09-29).**  M. Waldschmidt, *The four exponentials problem and Schanuel's conjecture* (Springer, 2023), p. 8, states a result attributed to [Waldschmidt (1990), Cor. 2.3], [Waldschmidt (1988), Cor. 2.1] and [Waldschmidt (2000), §11.3.3, example 2].  As printed, the statement is false.  A missing exceptional clause is the cause.  The correct statement is the *sharp six exponentials theorem*, as Waldschmidt himself states it elsewhere.

## As printed (rendered page checked, not a text dump)

> Let x₁, x₂ be two complex numbers which are linearly independent over ℚ, let y₁, y₂, y₃ be three complex numbers which are linearly independent over ℚ and let βᵢⱼ (i = 1, 2, j = 1, 2, 3) be six algebraic numbers.  Then one at least of the six numbers e^{x₁y₁−β₁₁}, …, e^{x₂y₃−β₂₃} is transcendental.

## Counterexample (checkable by hand)

- Take x = (1, √2) and y = (1, √2, i).  Both are ℚ-linearly independent.
- Let βᵢⱼ = xᵢyⱼ.  These products are algebraic because every xᵢ and yⱼ is algebraic.
- Then every e^{xᵢyⱼ−βᵢⱼ} = e⁰ = 1, which is algebraic.  So none of the six numbers is transcendental.

In Lean: `LeanFormalizations.Waldschmidt2023.not_sixExponentialsShifted : ¬ Literature.SixExponentialsShifted` (`src/LeanFormalizations/NumberTheory/Transcendence/WeakSchanuel.lean`), kernel-checked.

## The correct statement: sharp six exponentials

> If x₁, x₂ are ℚ-linearly independent, y₁, y₂, y₃ are ℚ-linearly independent, and βᵢⱼ are six algebraic numbers such that every e^{xᵢyⱼ−βᵢⱼ} is algebraic, then xᵢyⱼ = βᵢⱼ for all i, j.

The "then" clause is what the survey drops.  Sources:
- M. Waldschmidt, lectures at NCTS Hsinchu, 2003, slide 23 (`webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/NCTS-10-2003.pdf`); the sharp *four* exponentials conjecture on slide 19 has the same shape;
- Waldschmidt 2005, Theorem 1.4, as cited by Wikipedia's *Six exponentials theorem*, §Sharp six exponentials theorem.

Setting βᵢⱼ = 0 recovers the six exponentials theorem.  Setting x₃ = γ/x₁ together with Baker's theorem gives the five exponentials theorem.  The survey says its statement "includes both" of these, and that is true of the corrected form.

In Lean: `Literature.SixExponentialsSharp` (`src/LeanFormalizations/Literature/Periods.lean`).  The edges sharp ⇒ six and sharp + Baker ⇒ five are phase 25 targets in `NumberTheory/Transcendence/Periods.lean`.

## What the error is *not*

- **Not a dropped overbar.**  The rendered page says ℚ, not ℚ̄.  A treadmill lap first diagnosed it as the same `pdftotext` overbar loss that bit our transcription of Roy's *strong* six exponentials theorem.  That was a different, genuinely ours, transcription error: `StrongSixExponentialsOverQ`, refuted by `ExponentialsKnown.not_strongSixExponentialsOverQ`.
- **Not repairable by switching to ℚ̄.**  With ℚ̄-independence the counterexample above dies, but the resulting statement no longer contains the six exponentials theorem, whose hypotheses are over ℚ.  It would be a different, weaker theorem.  It is still **true**: the ℚ̄ version follows from the sharp theorem, because under ℚ̄-independence the exceptional case `xᵢyⱼ = βᵢⱼ` cannot occur.  It is recorded as `Periods.SixExponentialsShiftedAlg`, with `shiftedAlg_of_sharp` and the scope witness `witness_not_algIndep` (`NumberTheory/Transcendence/SharpSixVariants.lean`).  The fix to the survey is the exceptional clause.

## Context

The same page already carries a published erratum footnote, about Corollary 2.12 of Waldschmidt (2005a).  This is a second, independent slip on that page.

Whether to tell Prof. Waldschmidt is Trevor's call.  Nothing has been sent.
