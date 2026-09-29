# HANDOFF 2026-09-29 — phase 24 checkpoint (lap end)

Branch `main`, HEAD `ce88be9`. Working tree **clean**, `lake build` green, nothing uncommitted.

Full route/gotcha detail is in `HANDOFF-2026-09-29-phase24-complete.md` (six addenda). This
file is the short state-of-play.

## Objective: MET

`src/LeanFormalizations/NumberTheory/Transcendence/WeakSchanuel.lean` is **sorry-free**. All
five frozen phase-24 statements are proved and `#print axioms`-clean (`propext,
Classical.choice, Quot.sound`), as is everything added afterwards.

The flagged item resolved in the operator's favour: **Conj 1 ⇒ strong four exponentials is
TRUE** (it was carried as "Ren, ~70% confident, unchecked"). Roy's three-column derivation
argument does not transfer, so the new `AffTwo` section replaces it with a symmetric-coefficient
argument (`sym_coeff` + `eq_smul_of_sym` + `constRatioTwo`).

## Commits this lap

| commit | content |
|---|---|
| `cb4e192` | GS, log-primes, π+log-primes, **strong four exponentials** |
| `543fcac` | Baker 1966 inhomogeneous — file sorry-free, all 5 axiom-clean |
| `35c9aac` | Conj 1 ⇒ Roy's strong **six** exponentials (Schanuel never needed) |
| `3f24003` | repaired the vacuous `SixExponentials` edge (needs strong four **+** GS) |
| `1a1e4fe` | ⚠️ **`Literature.SixExponentialsShifted` REFUTED** |
| `10bbe2e` | restored a live route: Conj 1 ⇒ `FiveExponentials` |
| `27c4cc6` | repaired shifted six from Conj 1 + overbar audit (clean) |
| `ce88be9` | hard limit: rank consequence of Conj 1 does **not** reach `𝓛̃` |

## ⚠️ Two items that need the OPERATOR (`Literature/` is frozen)

1. **`Literature.SixExponentialsShifted` is false** — kernel-refuted by
   `not_sixExponentialsShifted` (witness `x = (1,√2)`, `y = (1,√2,i)`, `βᵢⱼ := xᵢyⱼ`). Same
   dropped-overbar root cause as `StrongSixExponentialsOverQ`. Fix is
   `LinearIndependent ℚ ⟶ LinearIndependent (integralClosure ℚ ℂ)` on `x` and `y`; the repaired
   statement is **already proved** as `sixExponentialsShifted_bar_of_algIndepLogs`, so the fix
   is a one-line swap plus repointing `ExponentialsKnown.{six,five}Exponentials_of_shifted`.
2. **`Literature.IsStructRank` fixes `K = ℚ`**, which is correct for `IsLogMatrix` but makes any
   `𝓛̃`-version false (`not_rank_eq_structRank_of_mem_logAlgSpan`). A Roy-style converse
   (rank conjecture ⇒ Conj 1) needs `r_str` over `ℚ̄`; that is a new frozen definition, not
   something a lap can add.

The overbar audit of every other `LinearIndependent ℚ` in `Literature/` came back **clean**.

## Next steps (in rough priority order)

1. **Roy's converse**, `rank = r_str ⇒ Conjecture 1` — the missing half of the equivalence
   `Literature/StructuralRank.lean` advertises. Blocked as stated (see item 2 above); needs a
   `ℚ̄`-structural-rank definition first. Determinantal route would be Valiant's theorem.
2. **Uncovered Waldschmidt-2023 survey items**: Leopoldt §2, and Conj 7 (`RoyConjecture` /
   `Roy2001Equivalence`, the only known strategy toward Schanuel). Coverage map is
   `WALDSCHMIDT-2023.md`.
3. `LindemannWeierstrassAlgIndep` carries 11 theorems but has only Schanuel as an incoming
   edge. I do **not** believe Conj 1 gives it (Conj 1 constrains logarithms of algebraic
   numbers; LW constrains exponentials of algebraic numbers, the opposite configuration) —
   Conj 1 does give Hermite–Lindemann at `n = 1`, but not the algebraic independence. Worth one
   probe before anyone invests.

## Designated-open, untouched (outside scope, per the run's `--done-when`)

`DubickasNoSubspace.lean` (2), `CorvajaZannier.lean` (4), `CorvajaZannierStephan.lean` (1),
`PrimeNumberTheoremAnd/Wiener.lean` (2).
