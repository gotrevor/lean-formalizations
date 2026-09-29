# Coverage: Waldschmidt 2023, *The four exponentials problem and Schanuel's conjecture*

Trevor, 2026-09-29: formalize the survey.  Scope, as agreed:
- every **theorem** enters `Literature/` as a cited hypothesis `Prop`;
- every **conjecture** enters as a named hypothesis `Prop`;
- every **implication the survey derives** is proved.

Fields (`ℚ` vs `ℚ̄`) are checked against the rendered PDF, never a pdftotext dump.  The dump lost an overbar once, and `StrongSixExponentialsOverQ` is the refuted record of that.

| Survey item | Lean | Status |
|---|---|---|
| §2 Leopoldt's conjecture (p-adic regulator), Ax/Brumer | none | ⏭️ not covered: needs p-adic logarithms and regulators; a separate project |
| Conj 1, algebraic independence of logs ("weak Schanuel") | `Literature.AlgIndepLogsConjecture` | stated; ✅ from Schanuel (phase 19) |
| Conj 1, n = 1 (Hermite–Lindemann) | `Waldschmidt2023.transcendental_log_of_lindemann` | ✅ phase 19 |
| Baker 1966 (p. 4 conclusion, `ℚ̄`-linear independence) | `Literature.BakerHomogeneous`; inhomogeneous `Literature.Baker1966` | stated; ✅ Conj 1 ⇒ Baker (phase 19) |
| Example: `log 2`, `π` algebraically independent under Conj 1 | `Waldschmidt2023.algebraicIndependent_log_two_pi` | ✅ phase 19 |
| Conj 2, four exponentials | `Literature.FourExponentialsConjecture` | ✅ from Schanuel (phase 16); ✅ from Conj 1 (phase 19, the survey's route) |
| Consequence: `2^t` or `3^t` transcendental | `Exponentials.two_rpow_or_three_rpow_transcendental` | ✅ phase 16 |
| Thm 3, six exponentials (Lang, Ramachandra) | `Literature.SixExponentials` | stated; consequences ✅ phases 16–17 (`p^t ∈ ℤ` for 3 primes ⇒ `t ∈ ℕ`; `2^t, 3^t, 5^t`) |
| §5 rank of matrices of logarithms; Roy's structural-rank bound `rk ≥ ½ r_str`; Conj 1 ⇔ `rk = r_str` | none | ⏭️ not yet: needs a structural-rank definition |
| Thm 4, five exponentials (Waldschmidt 1988) | `Literature.FiveExponentials` | stated; ✅ from shifted six + Baker (phase 17) |
| Shifted six exponentials (Waldschmidt 1988 Cor 2.1) | `Literature.SixExponentialsShifted` | stated; ✅ ⇒ six exponentials (phase 17) |
| Thm 5, Roy's strong six exponentials | `Literature.StrongSixExponentials` | stated; ✅ from Schanuel (phase 17) |
| Strong four exponentials conjecture | `Literature.StrongFourExponentialsConjecture` | stated (phase 19) |
| Conj 6, Schanuel | `Literature.SchanuelConjecture` | stated; 10 consequences ✅ (phase 15) |
| Conj 7, Roy's conjecture, equivalent to Schanuel (Roy 2001) | none | ⏭️ not yet: a heavy statement (derivation `D`, height bounds); state it carefully from the rendered page |
