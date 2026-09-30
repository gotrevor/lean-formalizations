# Handoff: phase 34 complete — `F(c^n) + h` composite i.o. for inert `c` and for `c = 5`

**Date**: 2026-09-30 · **Branch**: `main` · **HEAD**: `2eb97a9`

## 🎯 What we're doing

Phase 34 of the Mills/Saito campaign (top open block of `DIRECTION.md`): generalise phase 32's
answer to Saito's Problem 1.8 from `c = 2` to the other primes `c`, following
`SWEEP-PRIME-MODULUS.md`.  Target `src/LeanFormalizations/NumberTheory/Mills/FibonacciPrimePow.lean`,
six frozen statements, route in its header.  **This is DONE** — the file is sorry-free and all six
statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`, verified this
session).  Scoped objective `sorry-free:…/FibonacciPrimePow.lean` is met.

## ✅ State

- `lake build` **green**, 8752 jobs (observed via the pre-commit hook on every commit below).
- `FibonacciPrimePow.lean`: 0 sorries.  All six frozen statements axiom-clean:
  `fib_frobenius_inert`, `fib_prime_pow_succ_add`, `pow_dvd_sub_or_add_of_lt_padicValNat`,
  `fib_prime_pow_add_not_prime`, `five_pow_dvd_fib_five_pow`, `fib_five_pow_add_not_prime`.
- No file outside the target was touched (frozen files and `Literature/` untouched); no new
  declaration is `private`, per the directive.
- `scripts/fact-graph` rerun: 30 edges, 29 hypotheses (unchanged).
- Commits this lap: `2074990` (step 1), `f5d8646` (step 2), `51c295b` (step 3), `f3f7e2e` (step 4),
  `97db78b` (step 5), `2eb97a9` (step 6 + FINDING + sweep notes).  Working tree clean; nothing
  pushed (no egress; the host pushes).

## 🧠 Context to carry forward

Full formalization notes are in `SWEEP-PRIME-MODULUS.md` § Phase 34.  The five that will save a
future lap real time:

- **A quadratic Frobenius argument does not need Cayley–Hamilton or a power basis.**  In
  `K = AdjoinRoot (X²−X−1)` over `ZMod c`, `pow_eq_fib` (`x^(N+1) = F(N+1)·x + F(N)`, one-step
  induction, valid in any commutative ring with `x² = x+1`) converts `x^(c+1) = −1` straight into
  the two coefficient equations.  Independence of `1, x` is a **degree** argument:
  `a·x + b = 0` ⟹ `f ∣ C a * X + C b` ⟹ `2 ≤ 1` when `a ≠ 0`.  The header's suggested route
  (polynomial divisibility + `aeval` of the charpoly, as in phase 31) is strictly more work.
- **LTE inside a noncommutative ring: prove the expansion in `ℤ[X]` and `aeval` it over.**
  `one_sub_pow_expand : ∃ D, (1 − ε)^k = 1 − k•ε + ε²·D` for an arbitrary `Ring`.  Doing the
  induction directly in `Matrix … ℤ` fights `smul`/`noncomm_ring`; in `ℤ[X]` `ring` closes it, and
  `Polynomial.aeval` is available for a noncommutative `ℤ`-algebra.  Reusable for any
  "lift the exponent along a tower" step.
- **Divide a matrix power down with an explicit inverse, never `Matrix.inv`.**
  `fibMinv Q := !![F Q − F(Q+1), F Q; F Q, −F(Q+1)]` and `A^Q * fibMinv Q = 1` for **odd** `Q` by
  Cassini alone.  Odd `Q = c^n` is exactly where oddness of `c` gets consumed.
- **At an odd base, `h = ±1` is elementary and the parity case vanishes.**  `F(c^n) ≡ (−1)^n
  (mod c)` (telescope the sign flip mod `c`) gives `c ∣ F(c^n)+1` for odd `n`, `c ∣ F(c^n)−1` for
  even `n` — true at `c = 2` as well.  So the main case split is `h = 0`, `h = ±1`, `|h| ≥ 2`, and
  phase 32's "odd `h` ⟹ even value" step (which has no odd-`c` analogue, since `2 ∣ F(N)` iff
  `3 ∣ N`) is simply not needed.  The `|h| ≥ 2` endgame is also cleaner than phase 32's:
  `c^(n/2) ∣ s + s' − 2h` with `s, s' ∈ {±1}` forces `2h = s + s'`, so `|h| ≤ 1`.
- **Quintuplication for `c = 5` is the `(0,1)` entry of `(A^m)^5`.**  The polynomial identity is
  `Φ(f₀,f₁) = 25f₀⁵ + 25f₀³N + 5f₀N²` with `N = f₁² − f₁f₀ − f₀²`; with Cassini and `((−1)^m)² = 1`
  that is `F(5m) = F(m)(25F(m)^4 + 25(−1)^m F(m)² + 5)`, hence `5^n ∣ F(5^n)` by induction.

Nothing was abandoned this lap; the header's route worked as written throughout, with the two
simplifications noted above.

## ⚠️ Gotchas hit (worth the corpus)

- `decide` on `¬ IsSquare ((2:ℕ) : ZMod 5)` fails **inside** a proof with `c` in context
  ("Expected type must not contain free variables"), and `decide +revert` then tries to decide the
  whole reverted telescope.  Hoist such a closed decidable fact to a **top-level** lemma.
- `set f := X^2 − X − 1` then `rw [hf] at h0` where `h0 : AdjoinRoot.mk f f = 0` is a **motive
  failure** — `AdjoinRoot g`'s type depends on `g`.  Get the statement in the shape you want
  directly: `have h0 : (AdjoinRoot.mk f) (X^2 − X − 1) = 0 := by rw [← hf]; exact AdjoinRoot.mk_self`
  (rewriting only the *argument* position is safe).
- `rw [pow_add]` on a goal that also contains `c ^ (n+1)` in an exponent rewrites **that** instead
  (it matches `?m + 1`).  Pre-package the reassociation as a `have … := by rw [← pow_add]; congr 1`.
- `smul_pow` is ambiguous when `Polynomial` is open — use `_root_.smul_pow`.
- `Nat.dvd_sub'` is gone; the current name is `Nat.dvd_sub` (no `≤` hypothesis).  `le_or_lt` /
  `Nat.le_or_lt` are also gone — reach for `omega` instead.
- `A ^ 5` will not unfold by `pow_succ` (literal vs `?n + 1`).  Use
  `rw [show (5:ℕ) = 1+1+1+1+1 from by norm_num, pow_add, pow_add, pow_add, pow_add, pow_one]`.
- `omega` sees `Int.natAbs` and `Int.toNat` natively; several `rw [Int.abs_eq_natAbs]`-style
  preparations that phase 32 needed are just `omega` here.

## 🎬 Next actions

1. Phase 34 is finished; **do not reopen it**.  A future lap should take the next open block from
   `DIRECTION.md`.
2. The natural continuation, already written up in `SWEEP-PRIME-MODULUS.md` § Phase 34 and flagged
   as Maze-row material: the **split** primes `c ≡ ±1 (mod 5)` (11, 19, 29, 31, 41, …).  There
   Frobenius fixes the root, the `c`-adic limit of `F(c^n)` is a *single* point, and the sweep's
   survivors only *look* non-integral — settling every `h` needs a proof that the limit is not an
   integer.  The Dickson-polynomial idea recorded for traces (`V(c^(n+1)) = D_c(V(c^n), Q)`, so an
   integer limit is a root of `D_c(x,Q) − x`) is the closest available handle, but it is a trace
   argument and does not transfer to an entry as written.  That gap is the real crux.
3. Also stated in the sweep as the natural general theorem after this phase: **entries at inert `c`
   for a general Lucas sequence** — every `h` is settled whenever `c ∤ Q` and `c` is inert in
   `ℚ(√(P²−4Q))`.  Phase 33's companion-matrix toolkit plus this lap's `one_sub_pow_expand` and
   `fibMinv`-style explicit inverse should make that a mostly mechanical merge of phases 33 and 34.
4. Remaining `src/` sorries are all outside the Mills/Saito line and were designated-open under
   this run's scope (untouched): `DubickasNoSubspace.lean` (1595, 1635), `CorvajaZannier.lean`
   (961, 1157, 1167, 1179), `CorvajaZannierStephan.lean` (196).

## 📁 Key files

- `src/LeanFormalizations/NumberTheory/Mills/FibonacciPrimePow.lean` — the phase-34 result.
- `SWEEP-PRIME-MODULUS.md` § Phase 34 — the sweep table, now with both proved rows, the
  formalization notes, and the split-prime gap.
- `src/LeanFormalizations/NumberTheory/Mills/SaitoFibonacci.lean` — phase 32; source of
  `exists_entry_pow_congr` (reused verbatim) and of the `c = 2` delegations.
- `src/LeanFormalizations/NumberTheory/Mills/Projective.lean` — phase 31; source of the
  fixed-points-are-scalars argument (private there, re-derived public here as
  `exists_algebraMap_eq_of_pow_eq`).
- `DIRECTION.md` — the operator's directive stack; owned by altitude laps, do not edit.

---
**→ Next session: this is your starting point.  Phase 34 is finished and the treadmill is stopped.
Read `DIRECTION.md`'s top open directive and start there; don't reopen phase 34 and don't summarize
this doc back.**
