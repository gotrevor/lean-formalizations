# HANDOFF 2026-09-30 — phase 36 COMPLETE (LucasInert sorry-free, axiom-clean)

**Branch** `main` · **HEAD** `889bdcb` (this doc's own commit follows). Scoped run
(`sorry-free:src/LeanFormalizations/NumberTheory/Mills/LucasInert.lean`); objective met.

`src/LeanFormalizations/NumberTheory/Mills/LucasInert.lean` is sorry-free; all three frozen
statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):
`lucasU_frobenius_inert`, `lucasU_prime_pow_succ_add`, `lucasU_prime_pow_add_not_prime`.
`lake build` green; `scripts/fact-graph` rerun (30 edges, 29 hypotheses).

**Result.** For every odd prime `c` with `c ∤ Q` and `P² − 4Q` a non-square mod `c` (`c` inert in
`ℚ(√(P²−4Q))`), whenever `|U_(c^n)(P,Q)| → ∞`, and for **every** integer `h`, `U_(c^n)(P,Q) + h`
fails to be prime for infinitely many `n`.  Subsumes phase 34 (`P=1, Q=−1`); odd-`c` companion of
phase 33 (`c = 2`).

## The crux and how it fell
Phase 34's exponent lift *divides* by `A^(c^n)` using an explicit integer inverse `fibMinv`, which
exists only because `det(fibM) = −1` is a unit.  For general `Q`, `det(A) = Q` is not a unit — this
was the one route-decisive blocker.  Fix: the **adjugate**, `A^N · adj(A^N) = det(A^N) • 1 = Q^N • 1`.
Multiplying the frobenius congruence on the right by `adj(A^N)` and reading entry `(1,0)`
(`adj(A^N)_(1,0) = −U(c^n)`, `Matrix.adjugate_fin_two`) gives
`Q^N · (U(c^(n+1)) + U(c^n)) = c^(n+1) · W`, and `IsCoprime (c^(n+1)) (Q^N)` cancels `Q^N`.
**The adjugate needs the determinant only coprime to the modulus, never a unit** — the reusable idea.

## Reusable lemmas added
`lucasA`, `lucasA_det`, `lucasA_pow_apply_one_zero`, `lucasA_pow_succ_left`,
`lucasA_pow_apply_zero_zero`, `lucasA_pow_succ_apply_one`, `pow_eq_lucasU`,
`ne_two_of_not_isSquare`, `not_dvd_of_not_isSquare`, `ne_zero_of_not_isSquare`, `no_root_inert`,
`intCast_eq_zsmul_one`, `intCast_add_pow_expand`, `scalar_add_pow_expand`, `lucasA_pow_frobenius`,
`lucasU_dvd_lucasA_pow_apply_zero_one`, `lucasU_dvd_offdiag`, `lucasU_dvd_mul`,
`lucasU_tower_dvd`, `abs_sub_abs_le_abs_add'`, `not_prime_of_dvd_of_lt_abs`,
`lucasU_prime_pow_mod`.

`scalar_add_pow_expand` is worth remembering: in **any** ring, `c ∣ a ⟹ (q + a·B)^c ≡ q^c (mod c·a)`,
proved by transporting `(C q + X)^(k+1) = C(q^(k+1)) + C((k+1)q^k)·X + X²·D` from the commutative
ring `ℤ[X]` along `Polynomial.aeval` — the standard way to get a binomial identity in a
noncommutative ring.  `lucasU_dvd_offdiag` gives tower divisibility with no diagonalisation.

## Notes
Full mathematical notes are in `SWEEP-PRIME-MODULUS.md` § "Phase 36".  `hD` alone forces `c ≠ 2`,
`c ∤ Q` and `Q ≠ 0`, so the frozen statement 1 needs no extra hypotheses.

## Next (for a fresh session; DIRECTION.md is owned by altitude laps)
Split/ramified `c` for general `U(P,Q)` (i.e. `P² − 4Q` a square mod `c`), plus `Q = 0`.  Natural
attack = phase 37's odd-index Cayley–Hamilton composition; the obstruction is the `Q^N` in
`det(A_N) = −Q^N`, which is a sign exactly when `Q = ±1`, where the phase-37 route should transfer
verbatim.
