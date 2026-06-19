# wip/ — work-in-progress, NOT in the build target

Files here are preserved (never deleted) but excluded from `lake build` (they live
outside `srcDir = "src"`), so the `src/`-scoped `sorry`/`admit` gate does not see them.

## Logic/FastGrowing/Basic.lean (quarantined 2026-06-19)
Out-of-lane fast-growing-hierarchy development. Complete except one genuinely hard,
multi-lap core lemma `fastGrowing_fundSeq_step` (the limit-step index-monotonicity
crux of the Wainer/Cichoń–Wainer growth theory), which remains a disclosed `sorry`.
It is NOT imported by any `src/` headline (Goodstein uses mathlib's `ONote.fastGrowingε₀`
directly, not this file). Moved out of the build target so `src/` is sorry-free; to
resume, prove `fastGrowing_fundSeq_step`, move the file back under
`src/LeanFormalizations/Logic/FastGrowing/`, and restore its import in
`src/LeanFormalizations.lean`.
