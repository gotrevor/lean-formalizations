# ON-LINE-REQUEST

## 2026-09-28 — Corvaja–Zannier (2004): exact statements of the main theorem and Lemma 4

**Why:** phase 9 (`DIRECTION.md`) reduced the last hypothesis under the ⚓ OEIS-linked Dubickas
headlines to exactly two leaves in
`src/LeanFormalizations/NumberTheory/Transcendence/DubickasNoSubspace.lean`:
`corvajaZannier_dichotomy` (their main theorem, p. 177) and `corvajaZannier_lemma4` (their
Lemma 4).  Both are currently transcribed from **Dubickas's paraphrase** (his Lemmas 3 and 4,
p. 574), because we have only `papers/dubickas-2022-transcendency-polynomial-iterations.pdf`
locally.  Before either is stated in `Literature/` we want the primary text.

**Wanted** (any of these, in order of usefulness):

1. The verbatim statement of the **main theorem of** P. Corvaja, U. Zannier, *On the rational
   approximations to the powers of an algebraic number: solution of two problems of Mahler and
   Mendès France*, Acta Math. **193** (2004), 175–191 — the theorem on p. 177 (with its
   definitions of `δ`, `u`, `Γ`, and of *pseudo-Pisot*).
2. The verbatim statement **and proof sketch of their Lemma 4** (`trace(q_n α^(s_n))` a nonzero
   integer with `log q_n = o(n)` ⟹ `α` is an `ℓ`-th root of a rational or an algebraic integer).
   We especially want to know **which machinery the proof uses** — we reconstructed a
   Newton-polygon / valuation argument in `ℚ_p` with a root-of-unity tie case (written up in
   `PROBE-DUBICKAS-NOSUBSPACE.md`); if CZ instead reduce it to an `S`-unit equation or to their
   main theorem, the Lean route changes completely.
3. Whether their Lemma 4 is itself subspace-strength.  Dubickas's presentation implies it is not,
   and our whole phase-9 plan (close Lemma 4 first, leave the subspace step last) depends on that.

The paper is on Acta Mathematica's open archive (projecteuclid / actamathematica.org).  A plain
text or Markdown transcription of pp. 176–179 suffices; no need for the whole paper.
