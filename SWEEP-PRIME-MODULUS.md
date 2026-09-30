# Sweep: what the prime-as-modulus filter settles (2026-09-29)

**The filter** (phases 29, 32, 33).  Let `u(N)` be read off `A^N` for an integer matrix `A`: either an entry or the trace.  Let `c` be a prime.  If `u(c^n) + h = p_n` is prime for all large `n`, then `v_c|GL(𝔽_p)|` must be large; otherwise `p_n ∣ p_(n+j)` for some `j ≥ 1`.  For a 2×2 matrix this means `p_n ≡ ±1 (mod c^(~n/2))`.  So a shift `h` **survives** only if `u(c^n) + h → ±1` `c`-adically along every `n`.

**Instrument.**  `scripts/prime-modulus-sweep.py` computes the `c`-adic limit points of `u(c^n)` at precision `c^6` and `c^9`, and prints the surviving `h`.
- "Integer survivors" means the same small residue at both precisions.
- "Non-integral" means the survivor residues never stabilise.  That is **numerical evidence only**: to settle every `h` you still have to prove the limit is not an integer.
- Known-answer control: the Fermat-type cases come out as integer survivors, as they must.  Examples: `L(2^n)` at `h = 0`, and `a^(2^n) + 1`.

## Freshness
- The 1×1 case `a^(c^n) + h` is **folklore**.  It is olympiad material, e.g. "for every `k > 1`, `k·2^(2^n) + 1` is composite for infinitely many `n`" in the PEN problem collection.  So there is no phase for it.
- The 2×2 **entry** case at a general base is where the new content is.  Saito's Problem 1.8 (the `c = 2` Fibonacci case, now proved in phase 32) is the only instance I found posed in print.

## Results for Fibonacci `F(c^n) + h` (entry `U(1,−1)`), primes `c ≤ 47`

| `c` | how `5` behaves at `c` | limit points of `F(c^n)` | verdict |
|---|---|---|---|
| 2, 3, 7, 13, 17, 23, 37, 43, 47 | inert (`c ≡ ±2 mod 5`) | 2, a sign flip | **all `h` settled** by the filter plus the flip |
| 5 | ramified | 1, namely `0`, since `5^n ∣ F(5^n)` | survivors `h = ±1` only; these are killed by `F(4k+1) ± 1 = F(2k+1)L(2k)`, `F(2k)L(2k+1)` |
| 11, 19, 29, 31, 41 | split (`c ≡ ±1 mod 5`) | 1 | survivors look non-integral (numerics only); proving that needs an algebraic argument |

**Why the inert primes work.**
- Frobenius swaps the roots: `φ^c ≡ ψ = −φ⁻¹ (mod c)`, that is, `A^(c+1) ≡ −I (mod c)`.
- Lifting gives `A^(c^(n+1)) ≡ −A^(−c^n) (mod c^(n+1))`.  Reading off entry `(0,1)`, with `c^n` odd, gives the sign flip `F(c^(n+1)) ≡ −F(c^n) (mod c^(n+1))`.
- The contradiction then runs as in phase 32.  For odd `c` it also kills `h = ±1`, because `F(c^n) ≡ (−1)^n (mod c)` is a unit.

**Conjecture from the sweep** (numerics above): for **every** prime `c` and every integer `h`, `F(c^n) + h` is composite for infinitely many `n`.  Phase 34 proves the inert primes and `c = 5`.  The split primes are a Maze row.

## Other families (full table: run the script)
- **Traces `V(c^n)` (Lucas numbers, etc.).**  There is always a single limit point, because Frobenius fixes a trace.
  - For `c = 2`, the integer survivors are exactly the classical open cases, such as `L(2^n)` (`h = 0`).
  - For odd `c`, the survivors are usually non-integral.  `L(7^n) + h` would then be settled for every `h`, but that needs the non-integrality proof.  A route when `Q = ±1`: `V(c^(n+1)) = D_c(V(c^n), Q)` exactly, where `D_c` is the Dickson polynomial.  An integer limit is then an integer root of `D_c(x, Q) − x`, and there are finitely many to check.
- **Entries at inert `c`** always give two limit points, so every `h` is settled whenever `c ∤ Q` and `c` is inert in `ℚ(√(P² − 4Q))`.  This is the natural general theorem after phase 34.

## § Phase 34 — DONE (2026-09-30, 1 lap)

`NumberTheory/Mills/FibonacciPrimePow.lean` is sorry-free; all six frozen statements are
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  Both halves of the table above
are now theorems: **for every inert prime `c` (`c % 5 ∈ {2,3}`, including `c = 2`) and every
integer `h`, `F(c^n) + h` is composite for infinitely many `n`**, and likewise for the ramified
prime `c = 5`.  Nothing in the header's route failed; formalization notes:

- **Step 1 (`fib_frobenius_inert`) needs no Cayley–Hamilton.**  The header suggested going through
  `F ∣` polynomial divisibility plus Cayley–Hamilton as in phase 31.  That is unnecessary: in
  `K = AdjoinRoot (X²−X−1)` the identity `x^(N+1) = F(N+1)·x + F(N)` (`pow_eq_fib`, one-step
  induction, valid in *any* commutative ring with `x² = x+1`) turns `x^(c+1) = −1` directly into
  the two coefficient equations.  Linear independence of `1, x` is a **degree** argument: from
  `a·x + b = 0` one gets `f ∣ C a * X + C b`, and `2 ≤ 1` if `a ≠ 0`.  Much shorter than a power
  basis.
- **`x^c = x` is the only fork**, and it is killed by re-deriving phase 31's private
  `exists_algebraMap_eq_of_pow_eq` (fixed points of the `c`-power map on a finite field are
  scalars) — a verbatim copy, made public here.
- **Step 2's LTE works in the noncommutative matrix ring via `ℤ[X]`.**  The lifting step needs
  `(1 − ε)^k = 1 − kε + ε²D`.  Proving that by induction inside the matrix ring fights `smul`
  and non-commutativity; instead prove it in `ℤ[X]` (where `ring` closes it) and transport with
  `Polynomial.aeval ε`.  `aeval` is available for a noncommutative `ℤ`-algebra, so this is free.
  `one_sub_pow_expand` is stated for an arbitrary ring and is reusable.
- **Dividing `A^(c^n(c+1))` down to `A^(c^(n+1))` uses an explicit inverse, not `Matrix.inv`.**
  `fibMinv Q := !![F Q − F(Q+1), F Q; F Q, −F(Q+1)]` satisfies `A^Q * fibMinv Q = 1` for **odd**
  `Q` by Cassini alone (`fibM_pow_mul_fibMinv`).  Odd `Q = c^n` is exactly where oddness of `c` is
  consumed.
- **`h = ±1` at an odd inert `c` is elementary**, and does not need the filter: `F(c^n) ≡ (−1)^n
  (mod c)` (telescope step 2 modulo `c`), so `c ∣ F(c^n)+1` for odd `n` and `c ∣ F(c^n)−1` for even
  `n`.  Both hold for `c = 2` too, so the case split in the main theorem is only `h = 0`,
  `h = ±1`, `|h| ≥ 2`; the parity argument phase 32 used for odd `h` has no analogue at odd `c`
  (`2 ∣ F(N)` iff `3 ∣ N`) and is not needed.
- **`|h| ≥ 2` is cleaner than phase 32's endgame.**  The filter at `n` and `n+1` plus the sign flip
  gives `c^(n/2) ∣ s + s' − 2h` with `s, s' ∈ {±1}`; for large `n` that forces `2h = s + s'`, hence
  `|h| ≤ 1`.  No parity case split.
- **`c = 5`**: `five_pow_dvd_fib_five_pow` comes from the quintuplication formula
  `F(5m) = F(m)(25F(m)^4 + 25(−1)^m F(m)^2 + 5)`, which is the `(0,1)` entry of `(A^m)^5` — the
  polynomial identity is `Φ = 25f₀^5 + 25f₀³N + 5f₀N²` with `N = f₁² − f₁f₀ − f₀²`, so the only
  extra input is Cassini and `((−1)^m)² = 1`.  Then `5^n ∣ F(5^n)` collapses the filter to
  `h = ±1`, killed by `F(4k+1) + 1 = F(2k+1)L(2k)` and `F(4k+1) − 1 = F(2k)L(2k+1)` (both from
  `Nat.fib_two_mul_add_one` plus Cassini, one `linear_combination` each).

**Still open (Maze-row material):** the split primes `c ≡ ±1 (mod 5)` (11, 19, 29, 31, 41, …),
where the sweep's survivors look non-integral.  There the `c`-adic limit of `F(c^n)` is a single
point and proving it is not an integer needs an algebraic argument, not the Frobenius sign flip.
The Dickson-polynomial route noted above for traces is the closest available idea.

## § Phase 35 — DONE (2026-09-30, 1 lap)

`NumberTheory/Mills/LucasPrimePow.lean` is sorry-free; all frozen statements are
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  **For every odd prime `c`, every
integer `P` with `c ∤ P`, and every integer `h`, `V_(c^n)(P, −1) + h` fails to be prime for
infinitely many `n`** — in particular `L(c^n) + h` (the `P = 1` case).  The trace family at odd `c`
is therefore settled with no non-integrality proof, exactly as the header's route promised.  Nothing
in that route failed; formalization notes:

- **One trace lemma does all the algebra.**  `trace_pow_eq_lucasV : (B ^ k).trace =
  lucasV B.trace B.det k` for any 2×2 integer `B`, proved by `Nat.twoStepInduction` off the explicit
  Cayley–Hamilton `B^2 = (tr B) • B − (det B) • 1`.  Composition (`lucasV_mul_odd`), doubling
  (`lucasV_two_mul`, needed only for the `c = 2` half of `lucas_prime_pow_mod`) and the Frobenius
  congruence are all instances of it.
- **Frobenius needs no field extension.**  `V_c(x,−1) ≡ x (mod c)` comes from the binomial theorem
  for the two *commuting* matrices `B = !![x,1;1,0]` and `B' = !![0,−1;−1,x]`, whose sum is the
  scalar `diagonal (fun _ => x)` and which have the same trace `x` and determinant `−1`.
  `Commute.add_pow` plus `Matrix.trace_sum` gives `2x^c = V_c + V_c + (c-divisible middle)`, and
  `c` odd cancels the `2`.  No `AdjoinRoot`, no linear-independence/degree argument, no
  `add_pow_char` — and `trace_mul_natCast` is the only glue lemma (`tr (M * (k : Matrix)) =
  k * tr M`).  This is markedly shorter than phase 34's inert-prime Frobenius.
- **Monotonicity is recovered by a sign WLOG.**  `SharedConjecture.exists_trace_pow_congr` is used
  through the same "bigger prime divides smaller" endgame as phase 34, which needs `t n < t (n+j)`.
  For `P ≤ −1` the trace alternates, so instead of phase 33's iterated-return trick we use
  `lucasV (−x) (−1) k = (−1)^k lucasV x (−1) k`: at odd `c^n` the whole sequence just flips sign, so
  the theorem for `(P, h)` is the theorem for `(−P, −h)` composed with `Prime (−z) ↔ Prime z`.  The
  main argument then only ever runs at `P ≥ 1`, where `V_k` is strictly increasing from `k = 1`
  (`lucasV_pos_lt`) and `k ≤ V_k`.
- **The endgame has no case split on `h` at all** — cleaner than both phase 32 and phase 34.  The
  filter at `n` and `n+1` gives `V(c^n) ≡ x_n` and `V(c^(n+1)) ≡ x_(n+1) (mod c^(n/2))` with
  `x_n, x_(n+1) ∈ {1−h, −1−h}`; composition plus `dvd_lucasV_sub` (`lucasV · q k` respects
  congruences, since it is a polynomial in its first argument) turns this into
  `c^(n/2) ∣ lucasV x_n (−1) c − x_(n+1)`.  If `x_n ≠ 0` then `|lucasV x_n (−1) c| ≥ |x_n| + 3`
  while `|x_(n+1)| ≤ |x_n| + 2`, so the difference is nonzero and bounded by a constant depending
  only on `c` and `h`; choosing `n` with `c^(n/2)` beyond that bound forces `x_n = 0`.  Then
  `c ∣ V(c^n)`, contradicting `V(c^n) ≡ P (mod c)` and `c ∤ P`.
- **`c = 2` in `lucas_prime_pow_mod`** (the one statement that does not assume `c ≠ 2`) is the
  doubling identity mod 2: `L(2^(n+1)) = L(2^n)² − 2(−1)^(2^n)`, so oddness propagates from
  `L(1) = 1`.  The main theorem still genuinely excludes `c = 2` (`L(2^n)` at `h = 0` is
  Fermat-type).

**Still open:** the split Fibonacci primes `c ≡ ±1 (mod 5)` (Maze-row material, unchanged), and the
general Lucas **entry** family `U(P,Q)` at odd inert `c` (phase 36 draft).  Note the trace route of
this phase does *not* transfer to entries: `U` has no composition identity of the form
`U_(cm) = f(U_m)`.

## Progress
- Phase 35 ✅: Lucas traces `V_(c^n)(P,−1) + h` (incl. `L(c^n) + h`) composite i.o. at every odd prime `c`, for every `h` and every `c ∤ P`.
- Phase 34 ✅ (`2eb97a9`): Fibonacci at every inert prime and at `c = 5`.
- Phase 35 (DONE, see § above): Lucas traces at every odd prime, via the exact composition `L(c·m) = V_c(L(m), −1)` (`m` odd) and `|V_c(x, −1)| ≥ |x| + 3` for `x ≠ 0`.  An integer surviving `h` would force an integer point with `V_c(x) ∈ {x, x ± 2}`, hence `x = 0`, but `L(c^n) ≡ 1 (mod c)`.  This settles traces at odd `c` without any non-integrality proof.
- Phase 36 (drafted): general Lucas `U(P,Q)` at odd inert `c`.
