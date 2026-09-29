# HANDOFF — phase 33 COMPLETE (2026-09-29)

`src/LeanFormalizations/NumberTheory/Mills/LucasTwoPow.lean` is **sorry-free**; all five frozen
statements are `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only):

- `lucasU_one_neg_one`, `lucasU_add_two`, `lucasU_two_pow_odd`,
  `two_pow_dvd_lucasU_two_pow_succ_add`, `lucasU_two_pow_add_not_prime`.

**Result.** Saito's Problem 1.8 generalised: for every odd `P, Q` with `|U_{2^n}(P,Q)| → ∞` and
every integer `h`, `U(2^n) + h` is composite for infinitely many `n`.

**Method** (details in `DIRECTION.md` phase-33 block and `PROBE-SAITO-FIBONACCI.md` § Phase 33):
the entire Lucas toolkit is read off the companion matrix `A = !![P,-Q;1,0]`; the doubling
identities `U(2m)=U(m)V(m)`, `V(2m)=V(m)²−2Q^m` are the `(1,0)` entry and the trace of `(A^m)²`.
The one genuinely new ingredient over phase 32 is the **iterated return step**: without
monotonicity the mechanism only gives `|t_{n+j}| = |t_n|`, so it is applied repeatedly to
contradict `|t_n| → ∞`.

Only other change: `exists_entry_pow_congr` in `SaitoFibonacci.lean` is no longer `private`.

`lake build` green (8751 jobs); `scripts/fact-graph` rerun (30 edges, 29 hypotheses).

**Next** — pick the next DIRECTION.md target; no open obligation remains in the Mills/Saito line
opened by phase 33.
