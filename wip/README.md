# wip/ — work-in-progress, NOT in the build target

Files here are preserved (never deleted) and are outside `srcDir = "src"`, so the
`src/`-scoped `sorry`/`admit` gate does not see them and the default `lake build` does not
build them. A subset is built explicitly by the non-default `DaviesWip` lean_lib — see
`lakefile.toml` for exactly which.

⚠️ `Logic/FastGrowing/` is **superseded**: `src/` now proves the A3 crux outright
(`fastGrowing_bachmann_reach`, axiom-clean). These copies share the same namespace and are
kept only as the record of the route.

## Logic/FastGrowing/Basic.lean (quarantined 2026-06-19)
Out-of-lane fast-growing-hierarchy development. Complete except one genuinely hard,
multi-lap core lemma `fastGrowing_fundSeq_step` (the limit-step index-monotonicity
crux of the Wainer/Cichoń–Wainer growth theory), which remains a disclosed `sorry`.
It is NOT imported by any `src/` headline (Goodstein uses mathlib's `ONote.fastGrowingε₀`
directly, not this file). Moved out of the build target so `src/` is sorry-free; to
resume, prove `fastGrowing_fundSeq_step`, move the file back under
`src/LeanFormalizations/Logic/FastGrowing/`, and restore its import in
`src/LeanFormalizations.lean`.
