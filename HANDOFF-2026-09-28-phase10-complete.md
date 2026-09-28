# HANDOFF 2026-09-28 — phase 10 COMPLETE: `NumberTheory/PolyIteration/` sorry-free

## State

`src/LeanFormalizations/NumberTheory/PolyIteration/` is **sorry-free and axiom-clean**.
`lake build` green (8710 jobs).  19 theorems, every one `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (Somos even drops `Classical.choice`).

* `Sylvester.lean` — `isStrongDivSeq_of_iterate`, `isStrongDivSeq_sub`, `isStrongDivSeq_add`.
* `A003095.lean` — all 16 statements of the phase-10 catalogue.

## How it went

**Sylvester** is the Fibonacci proof.  `Polynomial.sub_dvd_eval_sub` gives
`u a − u b ∣ u (a+n) − u (b+n)` by induction on `n` (`sub_dvd_sub_shift`); with `u 0 = 0` that is
`u m ∣ u (t + m*q) − u t`, and `Nat.gcd.induction` finishes.  mathlib has the `gcd`-shift lemmas
only for `Nat`, so `intGcd_congr_of_dvd_sub` (`a ∣ b − c → Int.gcd a b = Int.gcd a c`) is proved
here by two applications of `Int.dvd_gcd` — note `Int.dvd_gcd : ↑c ∣ a → ↑c ∣ b → c ∣ a.gcd b`
lands in `ℕ`, so state the helper's `key` at `ℕ` or elaboration fails.
Bala's Theorem 1 is Sylvester at `Q = P(X + u k) − u k`, resp. `Q = P(X − u k) + u k`; evenness of
`P` is exactly what makes the `n = 0` step of the second recursion land on `Q.eval 0`.

**A003095.**  Everything hangs on the one-step factorisation
`a(n+m+1) − a(m+1) = (a(n+m) − a m)(a(n+m) + a m)`.  From it: Bala's product identity by
`Nat.le_induction` + `Finset.prod_Ico_succ_top`, and the two Harden towers —
`2^(n+1) ∣ a(n+2) − a(n)` (needs `a(n) ≡ n mod 2`) and `5^⌊(n+5)/3⌋ ∣ a(n+3) − a(n)`.
The second is the only real content: `a(n) mod 5` cycles `0,1,2` with period 3, so
`5 ∣ a(n+3) + a(n)` **iff** `3 ∣ n` — that is why the exponent is `⌊(n+5)/3⌋` and not linear.
Conjectures 1–4, the `20^k` period (`2^(2k)·5^k`), the mod-10 cycle, and the three exactness
claims all reduce to the two towers plus `IsCoprime (2^i) (5^j)`.
`a(n) − a(k) ∣ a(mn) − a(mk)` telescopes `m` copies of the index shift.

## The one correction

**`a003095_sq_dvd` was FALSE as frozen.**  `a(n)² ∣ a(n+m) − a(m)` at `m = 0` reads
`a(n)² ∣ a(n)`; `n = 2` gives `4 ∤ 2`.  Added `1 ≤ m` — the same hypothesis Bala's identity
`a003095_add_sub_eq` carries.  Name and path unchanged; documented in the `A003095.lean` header
and `PENDING_WORK.md`.  Every other threshold (`k−1`, `3k−5`, `2k−1`, `⌊k/2⌋`) proved as stated.

## Not touched

`DubickasNoSubspace.lean`'s three disclosed Corvaja–Zannier leaves — designated-open per
`DIRECTION.md` phase 9.  Next phase is the operator's call.
