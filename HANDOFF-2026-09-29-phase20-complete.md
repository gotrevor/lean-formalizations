# HANDOFF 2026-09-29 — phase 20 COMPLETE (Waldschmidt 2023 §5, rank of matrices of logarithms)

`src/LeanFormalizations/NumberTheory/Transcendence/StructuralRank.lean` is **sorry-free**, and all
four frozen statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`):

* `rank_le_structRank` — `rk(M) ≤ r_str(M)`.
* `rank_eq_structRank_of_algIndepLogs` — Conjecture 1 ⇒ `rk(M) = r_str(M)` for log matrices.
* `two_le_rank_of_sixExponentials` — six exponentials ⇒ (`r_str ≥ 3` ⇒ `rk ≥ 2`).
* `structRank_log_example` — the 2×2 sanity anchor has structural rank 1.

No statement needed an extra hypothesis, and no definition turned out unfaithful.  Full route and
the two elaboration gotchas are in the file header; the headline points:

1. **`Matrix.rank` via minors is missing from mathlib.**  `exists_submatrix_det_ne_zero` /
   `le_rank_of_det_ne_zero` are built here from `exists_linearIndependent`,
   `finrank_span_set_eq_card` and `linearIndependent_rows_iff_isUnit`.  They are genuinely
   reusable — this is the only way to compare ranks across a ring hom.  Everything else in the
   file is a corollary of the one lemma `rank_map_le_rank_map`.
2. **The `∃`-form of `IsStructRank` is weaker than the textbook definition** (the basis `e` need
   not consist of logarithms), so Conjecture 1 cannot be applied to the given `e`.  The fix is
   `genericMat_refine`: refine to a maximal independent set of *entries*; the given generic matrix
   is a polynomial substitution of the refined one, and substitution only lowers rank.  That is the
   one real mathematical idea of the lap.
3. `structRank_le_of_factor` (rational factor of width `p` ⇒ every structural rank `≤ card p`,
   proved with dual functionals from `Basis.extend`) is what makes the six-exponentials statement
   go; `structRank_transpose` halves the case analysis.

## Next

Uncovered survey items in `WALDSCHMIDT-2023.md`: Leopoldt §2, Conj 7 (Roy's equivalent of
Schanuel), and the converse half of Roy 1995 (`rk = r_str` for all log matrices ⇒ Conjecture 1),
which would upgrade `rank_eq_structRank_of_algIndepLogs` to the stated equivalence.  Also still
open: `Literature.Waldschmidt1981` (`r_str ≤ 2 rk`) is a cited Prop, never derived — that is a real
transcendence theorem and a legitimate multi-lap target.
