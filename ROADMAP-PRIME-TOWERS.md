# Roadmap: composite values along prime-power towers (weeks of 2026-09-30)

Ren's plan, written overnight 2026-09-30 at Trevor's request ("plan out what new math we'll aim for in the coming weeks - paper conjectures & proofs").  What is proved so far: `PRIME-MODULUS-MAP.md`.  Numerics are in `scripts/`.

## 0. The frame, in one paragraph

Take `A ∈ M_d(ℤ)`, a prime `c`, and an integer linear functional `u(N)` of `A^N` (an entry or the trace).
- `A^(c^n)` converges `c`-adically along residue classes of `n`, because Frobenius permutes the Teichmüller lifts of the eigenvalues.  Call the limit points `λ_0, …, λ_(k−1)`.
- **The filter** (phases 29, 32): if `u(c^n) + h` is prime for all large `n`, then each value is `≡` a root of unity `c`-adically, i.e. it lies in the window `μ_(d!)(ℤ_c)`, which is `{±1}` in the cases we care about.  Otherwise the prime divides a later term.

Two regimes follow:
- **Survivors.**  `h` survives if **every** limit point satisfies `λ_r + h ∈ μ`.  For survivors, "composite i.o." is out of reach of congruence methods.  The known survivors are exactly the classical open problems: Fermat numbers, `L(2^n)`, and the six Mills residue classes.
- **Intervals.**  If **no** limit point has `λ_r + h ∈ μ` for any `|h| ≤ H`, the window is visited only finitely often.  Every later value then has a prime factor with a small `c`-part, which gives Dubickas-type covering, i.e. **prime-free intervals** (Theorem C).

## 1. Theorems to prove (Lean via treadmill; paper math by Ren)

### Theorem A: recurrences of any order, at inert primes  ✅ numerics, ⏳ Lean
Let `χ_A` be irreducible mod `c` (degree `d`), take `u(N) = (A^N)_ij` with `i ≠ j`, and assume `μ_(≤d)(ℤ_c) = {±1}` (i.e. `c = 2`, or no `k ∈ [3,d]` divides `c − 1`).  Assume `d` is odd and `c ∤ u(c^r)` for `r < d`.  Then `u(c^n) + h` is composite i.o. **for every `h`**.
- **Key identity:** `Σ_(i<d) A^(c^(n+i)) ≡ (scalar)·I (mod c^(n+1))`.  Frobenius acts on `𝔽_c[A] ≅ 𝔽_(c^d)` as a `d`-cycle, and the orbit sum is a field trace.  So `Σ_(i<d) u(c^(n+i)) ≡ 0`.  This is the sign flip (`d = 2`) in general form.
- **Survivor count:** `s_i = u_i + h ∈ {±1}` with `Σ s_i = d·h`.  For odd `d` this forces `h = ±1` with all `s_i = h`, hence `u ≡ 0`, which is impossible.  (For even `d` the case `h = 0` needs the divisibility-sequence argument, which works for `d = 2`; open for `d ≥ 4`.)
- Checked (`scripts/order-d-inert-probe.py`, with a known-answer control): Tribonacci at `c = 3, 5, 23`; `x³ − x − 1`; the cyclic cubic `x³ − 3x + 1` at 6 primes; Tetranacci at 2 and 5; `x⁵ − x − 1` at 3, 5, 11, 13.  The orbit sum is scalar in every case and there are **no survivors**, including at `c ≡ 1 (mod 3)`, where the theory as stated needs the extra `μ₃` case analysis.
- Corollary: **`T(3^n) + h` is composite i.o. for every `h`** (Tribonacci), and likewise at `c = 5, 23, …`.
- Lean: `exists_entry_pow_congr` is already stated for general `n × n`.  New pieces: the field trace of Frobenius in `AdjoinRoot χ_A` over `ZMod c` (phase 31 did `d = 3` by hand), and the `GL_d` filter's `c`-adic output.  About 2 phases.

### Theorem B: 2×2 traces at odd `c` — the `n = 2` case of our `DoubleExpTraceComposite`  ✅ numerics, ⏳ Lean
For `C ∈ M_2(ℤ)`, an odd prime `c` with `det C ≡ ε = ±1 (mod c)`, and `c ∤ tr C · disc C`: **`tr C^(c^n) + h` is composite i.o. for every `h`**, with exactly one exception: `χ_C ≡ X² ∓ X + 1 (mod c)` with `ε = +1`.  In that case `τ = ±1` exactly (sixth or third roots of unity), the survivors are `h ∈ {0, ∓2}`, and it is a genuine Fermat-type case.
- Route: lifting the exponent gives `det^(c^n) ≡ ε (mod c^(n+1))`, so `tr C^(c^(n+1)) ≡ V_c(tr C^(c^n), ε) (mod c^(n+1))`.  The finite window then forces an integer fixed point `V_c(x, ε) = x` (or a 2-cycle inside `{x, x ± 2}`).  With `ε = −1`, `|V_c(x, −1)| ≥ |x| + 3`.  With `ε = +1`, `V_c(x, 1) = 2T_c(x/2)`: `|x| ≥ 3` grows, `x = 0, ±2` are excluded by `c ∤ tr·disc`, and `x = ±1` is exactly the `Φ_6` / `Φ_3` exception.
- The sweep's table matches: `V(4,1)` at `c = 5` has survivors `{0, 2}`, and `X² − 4X + 1 ≡ X² + X + 1 (mod 5)`.
- **Classification tested (2026-09-30 01:15):** 1276 cases (`c ∈ {3,5,7,11,13}`, `|P| ≤ 12`, `|Q| ≤ 30` with `Q ≡ ±1 (mod c)`, `c ∤ P·D`).  Survivors appear **exactly** in the 216 predicted `Φ₃`/`Φ₆` classes: 0 mismatches.  Non-unit determinants are included (e.g. `Q = 4` at `c = 3, 5`).
- Generalizes phase 35 (`Q = −1` exactly).  About 1 phase.
- **Consequence for the conjecture graph:** `DoubleExpTraceComposite` is folklore for `n = 1`.  Theorem B proves it for `n = 2`, every odd `c` with `det ≡ ±1`, except the `Φ₃`/`Φ₆` classes, which are provably survivors.  For `n = 3, c = 3` the residual classes are Mills.  That is a clean staircase for the paper.

### Theorem C: prime-free intervals for the non-reversible tower `c^n`  ✅ PROVED IN LEAN FOR EVERY PRIME (phases 40–41, 2026-09-30) — headline `fib_prime_pow_prime_free_all`
This is Saito's actual wish in arXiv:2504.14968: *"We desire to remove the reversibility."*

**Statement (Fibonacci first).**  For every prime `c ≠ 5` and every `H`, there are `m`, `L` and primes `p_h` (`|h| ≤ H`) with `p_h ∣ F(c^(Lk+m)) + h` for all `k ≥ 0`.  Hence `[F(c^n) − H, F(c^n) + H]` contains no prime for all large `n ≡ m (mod L)`.  At `c = 5` the shifts `h = ±1` are always composite, via `F(4k+1) ± 1` factorizations.
- **Mechanism:**
  1. A value outside the window has a prime factor `p` with `v_c(ord_p A) ≤ n`.  If every prime factor had a large `c`-part, their product would lie in the window.
  2. That `p` then divides `u(c^(n+kj)) + h` for all `k ≥ 0`.
  3. Pick one `m` outside every window with `|h| ≤ H`; this is possible because each window is visited only finitely often.  Then take `L = lcm j_h`.
- **Non-integrality certificates** (why each window is visited finitely often):
  - `c = 2`: `5F(2^n)² = L(2^n)² − 4` and `L(2^n) → −1`, so `5λ² = −3`, which has no rational solution.
  - Odd `c ≠ 5`: phase 37's `Φ_j` with `2j + 1 = c²` along each parity class.  `x = Φ_j(x)` forces `x = 0`, and `c ∤ F(c^n)`.  (Everything is already in Lean.)
- **Concrete check** (`scripts/fib-d1-demo.py`): `H = 6`, `m = 4`, `L = 60`, primes `{2, 3, 23, 197, 983, 991}`.  So `F(2^(4+60k)) + h` is composite for all `|h| ≤ 6` and all `k ≥ 1`.
- **Quantitative:** tracking sizes gives `m ≈ 4 log₂ H`, `p_h ≤ φ^(25H⁴)`, and `L ≤ ∏ j_h`.  Hence prime-free intervals of length `≫ (log n)^(1/5)` around `F(2^n)` for infinitely many `n`.  Saito's reversible theorem has `log n / (2d)`, so ours is weaker in the exponent, but it is the first result for a non-reversible tower as far as the searches show.
- General `A`: the statement goes through whenever every single limit point avoids `ℤ + μ`.  The certificates are per family: easy for `d = 2` via exact composition, open for `d ≥ 3` (Tribonacci numerics say yes).
- **Extended to every Lucas sequence the same day** (`NumberTheory/Mills/LucasCoveringAllPrimes.lean`, sorry-free, axiom-clean): `lucasU_prime_pow_covering` and `lucasU_prime_pow_prime_free` for every `U(P, ±1)` with `D = P² − 4Q ≥ 5`, every odd prime `c ∤ D`, given `|U(c^n)| → ∞`.  Nothing new was needed beyond phase 38's `lucasOddPoly` composition and phase 41's `exists_shift_pow_congr` — the certificate is the *same* two ingredients as Fibonacci (`c`-adic convergence + `Φ_J` fixed point).
- **Note on the `d ≥ 3` wall, reformulated.**  `exists_shift_pow_congr` says the sequence `A^(c^n)` is `c`-adically Cauchy along each residue class `n mod d'`, so the limit `Λ` exists in `Mₑ(ℤ_c)`; and since `A^(c^(n+d')) = (A^(c^n))^(c^(d'))`, the limit satisfies **`Λ^(c^(d') − 1) = I`**.  So the limit point is a *torsion* element of `GL_d(ℤ_c)` of order coprime to `c`, i.e. its eigenvalues are Teichmüller lifts.  The `d ≥ 3` certificate is therefore exactly: *no torsion element of `GL_d(ℤ_c)` in the closure of `⟨A⟩` has `(i,j)` entry equal to `s − h`*.  For `d = 2` the exact composition `Φ_J` makes this concrete and elementary; for `d ≥ 3` it still needs the lifts.  This is a sharper statement of the wall than "no exact composition in `d = 3`".
- Lean: **phase 40 DONE** (2026-09-30).  `NumberTheory/Mills/FibonacciCovering.lean` is sorry-free
  and all four statements are `#print axioms`-clean: `five_mul_fib_two_pow_sq`,
  `exists_good_prime_factor`, `fib_two_pow_covering`, `fib_two_pow_prime_free`.  No step of the
  route failed.  Three remarks on how it actually went in:
  - The certificate `2^(n+1) ∣ 5F(2^n)²+3` is cleanest as a *self-contained* induction: with
    `x_n = 5F(2^n)²` one has `x_(n+1) = x_n(x_n+4)` (from `F(2m) = F(m)L(m)` and Cassini), so
    `x_(n+1)+3 = (x_n+1)(x_n+3)`, and `x_n+1 = 2^(n+1)c − 2` is automatically even.  Phase 32's
    `two_pow_dvd_lucas_two_pow_add_one` is not needed at all.
  - Step 2 needs only that `{±1 mod 2^e}` is **multiplicatively closed** (`PmOne.mul`) plus a
    strong induction on `minFac` (`PmOne.of_prime_factors`); `2` is good because
    `|GL₂(𝔽₂)| = 6` has 2-part `2`.
  - Step 3's strengthening is one line of the old proof: `g^(c^j) = g` iterates to
    `g^(c^(kj)) = g` (`exists_entry_pow_congr_mul`).  Step 4 takes `L = ∏_h j_h` (a product, not
    an lcm — `Finset.dvd_prod_of_mem` and `Finset.one_le_prod'` are cheaper than
    `Finset.lcm_eq_zero_iff`).  Step 5 compares the values at `k = K` and `k = K+1`: a prime
    `p_h` dividing both, with `0 < A_K < A_(K+1)`, forces `p_h = A_(K+1) ≤ A_K`.
- **Phase 41 DONE the same day** (`NumberTheory/Mills/FibonacciCoveringAllPrimes.lean`,
  sorry-free, axiom-clean): `fib_prime_pow_covering` and `fib_prime_pow_prime_free` for every odd
  prime `c ≠ 5`.  Two corrections to this section's plan:
  - The `Φ_j` certificate as described here is **two-index**, and naive two-index comparison only
    shows the bad set is exponentially sparse (`|Φ_J(x)| ≍ φ^(c^d)` forces the threshold on `n` to
    grow like `c^d`).  It does not give `∀ᶠ n`, and does not give one index good for all `|h| ≤ H`.
  - What repairs it is a **`c`-adic convergence** theorem, `exists_shift_pow_congr`: for any
    integer matrix `A` with `c ∤ det A` there are `d ≥ 1` and `s ≤ v_c|GLₙ(𝔽_c)|` with
    `c^(n−s+1) ∣ (A^(c^(n+d)))ᵢⱼ − (A^(c^n))ᵢⱼ` for `n ≥ s`.  Contrary to expectation this needs
    **no Teichmüller/Witt lifting and no binomial coefficients**: `A^T ≡ 1 (mod c)` for
    `T = |GLₙ(𝔽_c)|`; then `Z^c − 1 = (∑_{i<c} Z^i)(Z − 1)` with `∑_{i<c} Z^i ≡ c·1 ≡ 0 (mod c)`,
    so the geometric sum itself supplies the extra power of `c`; then `e ∣ c^d − 1` with
    `d = φ(e)`, `e` the `c`-free part of `T`.  A general shift `d` in place of the guessed `d = 2`
    is what makes this elementary, and it costs nothing (`c^d` is still odd, so `fib_odd_mul`
    applies with `2J + 1 = c^d`, and `d` depends only on `c`).
  - The odd-`c` `GL₂` bound (`pow_dvd_sub_or_add_of_lt_padicValNat_odd`) is *easier* than `c = 2`:
    an odd `c` divides at most one of `p ∓ 1`, so one of the two valuations is `0`.
- **`c = 5` DONE the same lap, away from `h = ±1`.**  The degeneration at `5` is a *gift*, not an
  obstacle: `Φ_2 = 25x⁵ − 25x³ + 5x = 5x(5x⁴ − 5x² + 1)`, so `5 ∣ Φ_2(x)` identically, giving
  `5^n ∣ F(5^n)` (`five_pow_dvd_fib_five_pow`) in three lines.  The `5`-adic limit of `F(5^n)` is
  therefore `0`, and the window condition `F(5^n) + h ≡ ±1 (mod 5^(n/2))` reads `5^(n/2) ∣ h ∓ 1`
  directly — no `Φ_J` fixed-point analysis at all, so `c = 5` is the EASIEST prime, not the hardest.
  `exists_good_prime_factor_five`, `fib_five_pow_covering`, `fib_five_pow_prime_free`.
- **The `c = 5` survivors are exactly `h = ±1`**, and they are survivors in the strict sense of §0:
  the window condition holds identically for them, so no covering prime can come from this
  mechanism.  The elementary `F(4k+1) − 1 = F(2k)L(2k+1)` and `F(4k+1) + 1 = F(2k+1)L(2k)`
  (specialisations of `F(m+n) + (−1)^n F(m−n) = F(m)L(n)`; note `5^n ≡ 1 mod 4`) give
  compositeness for them, but NOT a covering prime — the factors depend on `n`.  So the honest
  shape of Theorem C at `c = 5` is: covering for `h ≠ ±1`, plus separate factorisation
  compositeness at `h = ±1`.
- **That factorisation is DONE too** (`fib_five_pow_pm_one_not_prime`), and it needed no new
  identity: `F(4k+1) = F(2k+1)² + F(2k)²` (`Nat.fib_two_mul_add_one`) together with Cassini
  `F(2k+1)² − F(2k+1)F(2k) − F(2k)² = 1` gives both factorisations by `linarith`.  Hence
  `fib_five_pow_prime_free_all` (no exceptional shifts at `c = 5`) and the headline
  **`fib_prime_pow_prime_free_all`: for EVERY prime `c` and every `H`, `[F(c^n) − H, F(c^n) + H]`
  contains no prime for infinitely many `n`.**  Theorem C is closed.

### Theorem C′: non-integrality of limit points for `d ≥ 3` (paper math, written 2026-09-30 01:30)
The obstacle for Theorem C at `d ≥ 3` is that no exact composition is available.  Galois theory replaces it.
- Let `K` be the splitting field of `χ_A` (irreducible over `ℚ`), with eigenvalues `α_k` and spectral projectors `E_k ∈ M_d(K)`.  The Teichmüller lifts are `ω(α_k) = ζ^(c^k)`, where `ζ` is a root of unity of order `n ∣ c^d − 1` (`c` inert).
- Then `lim A^(c^(dn + r)) = Σ_k ζ^(c^(k+r)) E_k`, and the limit point `λ_r = Σ_k (E_k)_ij ζ^(c^(k+r))` lies in `K(ζ_n) ∩ ℚ_c`.
- **Claim:** suppose `K` and `ℚ(ζ_n)` are linearly disjoint, `n` is squarefree, and `ord_n(c) = d < φ(n)`.  Then `λ_r ∉ ℚ` unless `u ≡ 0`.  This suffices whenever the window is `{±1}`: `c = 2`, or `μ_(d!) ∩ μ_(c−1) = {±1}` (e.g. `d = 3` with `3 ∤ c − 1`).
  - Proof: for squarefree `n` the primitive `n`-th roots `{ζ^m : m ∈ (ℤ/n)^×}` form a `ℚ`-basis of `ℚ(ζ_n)`, hence a `K`-basis of `K(ζ_n)` by disjointness.
  - A rational `q` equals `q·μ(n)·Σ_m ζ^m`, since the sum of the primitive roots is `μ(n) = ±1`.
  - `λ_r` is supported on the `d` exponents `{c^(k+r)}` of one Frobenius orbit.  Since `φ(n) > d`, some basis vector lies outside the orbit; its coefficient forces `q = 0`, and then all `e_k = (E_k)_ij = 0`.
  - **Larger windows** (the window contains `ω` when `3 ∣ c − 1` and `d ≥ 3`): let `g = gcd(n, c − 1)` and `K₀ = Gal(ℚ(ζ_n)/ℚ(ζ_g)) ⊂ (ℤ/n)^×`.  Elements of `ℚ(ζ_g)` have primitive-basis coefficients that are constant on `K₀`-cosets.  The Frobenius orbit `⟨c⟩·c^r` (size `d`) sits inside ONE `K₀`-coset, since `c ≡ 1 (mod g)`.  So if `|K₀| = φ(n)/φ(g) > d`, then `λ_r ∉ ℚ(ζ_g) ⊇ ℤ + (window)`, unless `u ≡ 0`.  **Condition for the general claim: `n` squarefree, `K ⊥ ℚ(ζ_n)`, and `φ(n) > d·φ(gcd(n, c − 1))`.**  Two points still to verify line by line before the paper:
    - the equation `λ_r + h = ζ′` pulls back along the fixed embedding `ι : ℚ̄ → ℚ̄_c` to the algebraic `Λ_r + h = ζ′`;
    - if `ord(ζ′) ∤ n`, the comparison has to run in `ℚ(ζ_lcm(n, ord ζ′))`, where the support bookkeeping changes by the non-primitive-root expansion.
- **Tribonacci at `c = 3`:** `n = 13`.  `K ⊃ ℚ(√−11)` (`disc = −44`), and the only quadratic subfield of `ℚ(ζ₁₃)` is `ℚ(√13)`, so the fields are linearly disjoint.  `φ(13) = 12 > 3`.  Hence **Theorem C for Tribonacci along `3^n`: prime-free intervals of any fixed length around `T(3^n)`, infinitely often.**
- The larger-window version would also re-derive Theorem A at `c ≡ 1 (mod 3)`, where the elementary orbit-sum count does not reach (the window contains `ω`).
- **Lean path.**  The full Galois argument is paper-only for now; formalizing linear disjointness is heavy.  Lean-sized substitute: for each FIXED `H`, the statement "no limit point lies in `{s − h : |h| ≤ H}`" is a finite congruence check mod `c^K`.  So "(D1) for Tribonacci with `H = 10`" is a `decide`-able certificate, plus the general mechanism from phase 40.

### Theorem B at `c = 2` (why the staircase has a Fermat step at every size)
- With `det` odd, `V(2^(n+1)) ≡ V(2^n)² − 2 (mod 2^(n+2))`.  The integer orbits of `x ↦ x² − 2` inside a window `{a, a − 2}` are the fixed points `−1` and `2`.
- `P, Q` odd: `α (mod 2) ∈ 𝔽₄ ∖ 𝔽₂`, so `τ = ζ₃ + ζ₃² = −1` and the survivors are `h ∈ {0, 2}`.  The prototype is `L(2^n)`.
- `P` even: `τ = 2`, survivors `h ∈ {−1, −3}`.
- So **every** 2×2 trace at `c = 2` has Fermat-type survivors, while at odd `c` Theorem B leaves only the `Φ₃`/`Φ₆` classes.

### Theorem C for traces at odd `c` (Lucas numbers)
A trace has a single limit point `τ`.  If `τ ∈ ℤ`, then phase 35's exact `V_c(τ, −1) = τ` forces `τ = 0`, contradicting `τ ≡ P ≢ 0 (mod c)`.  So `τ ∉ ℤ`, and **prime-free intervals of any fixed length surround `L(c^n)` (and `V_(c^n)(P, −1)`, `c ∤ P`) infinitely often.**  All pieces are in Lean already.

### Theorem D: a partial answer to Saito's Problem 1.7 (paper math, 2026-09-30 01:45; numerics ✅, proof sketch below, to verify)
Saito's Problem 1.7: *find a non-reversible ILRS `R` such that for every Pisot `α` (especially degree 3), `⌊α^(R(n))⌋` is composite for infinitely many `n`.*

**Candidate `R(n) = c^n + s`** (`R(n+1) = c R(n) − (c − 1)s`; `a₀ = c ≠ ±1`, so non-reversible).
- With `s = 0` this is the Mills situation: the floor's `c`-adic limit points are **traces** `τ = Σ ω(α_k)`, which are Frobenius-invariant and can equal `±1`.  That is where the residual classes come from.
- A shift `s ≥ 1` replaces them by **weighted** sums `Λ_r = Σ_k ω(α_k)^(c^r) α_k^s`, which are not Frobenius-invariant.

**Statement (candidate).**  Let `c` be prime, `s ≥ s₀(d)`, and `α` a Pisot number of degree `d` with minimal polynomial `f`.  Assume:
- (i) `f` is irreducible over `ℚ(ζ_M)`, where `M` is the order of the relevant Teichmüller roots of unity (`M ∣ ∏_(i≤d)(c^i − 1)`, times `d!`-window roots);
- (ii) `f ≢ X^d (mod c)`.

Then `⌊α^(c^n + s)⌋` is composite for infinitely many `n`.

**Proof sketch.**
1. `⌊α^N⌋ = tr C^N + ε_N` with `ε_N ∈ {0, −1}`, where `C` is the companion matrix.  Assume every `p_n = ⌊α^(R(n))⌋` is prime for `n ≥ n₀`.
2. **Filter with a varying `ε`.**  If `v_c(ord_(p_n) C) ≤ n`, then `C^(R(n+kj)) ≡ C^(R(n)) (mod p_n)` for all `k ≥ 1`.  So `p_n ∣ ⌊α^(R(n+kj))⌋` whenever `ε_(n+kj) = ε_n`, and this is impossible (composite).  Call `n` *stuck* if `ε` flips for every `k`.  If `n` is stuck, then `n′ = n + j` is not stuck: at `k = j`, `n′ + j·j′ = n + j(1 + j′)` gets opposite `ε`-verdicts from the two stuck conditions.  **This is purely combinatorial, so it works for any configuration of conjugates, complex pairs included.**  Hence the window `v_c(ord) > n` occurs for infinitely many `n`.
3. Along a residue class `r` hit infinitely often, `λ_r + ε ∈ μ_(window)`, i.e. `Λ_r := ι⁻¹(λ_r) = t` with `t ∈ ζ′ + {0, 1}` and `|t| ≤ 2`.  Here `λ_r = Σ_k ω(α_k)^(c^r) α_k^s` (spectral decomposition `C^N = Σ α_k^N E_k`, `tr(E_k C^s) = α_k^s`; Teichmüller limits along `n ≡ r`, non-units → 0).
4. **Galois plus Pisot dominance.**  `G = Gal(K(ζ)/ℚ(ζ))` is transitive on the roots by (i) and fixes the `ζ_k`, so `Σ_k ζ_k α_(σk)^s = t` for all `σ ∈ G`.  The constant vector `ζ° = (t / tr C^s)·𝟙` solves this.  If `η` is the difference, pick `k₀` maximizing `|η_k|` and `σ` with `σ(k₀) = 1` (the Pisot root).  Then `|η_(k₀)| α^s ≤ |η_(k₀)| Σ_(j≥2) |α_j|^s`, which is impossible once `α^s > d − 1`.  So every `ζ_k = t / tr C^s`.
5. Then either all `ζ_k` are equal roots of unity, so `|t| = |tr C^s| ≥ 3` for `s ≥ s₀`, which is impossible; or all `ζ_k = 0`, i.e. `f ≡ X^d (mod c)`, which is excluded by (ii).  (Mixed zero/non-zero is impossible by the constancy.)  ∎

**Numerics** (`scripts/saito-17-shift-probe.py`, precision `3^10` / `2^20`, all Pisot `α` of degree 2 and 3 with coefficients in `[−6, 6]` / `[−8, 8]` and `c ∤ N(α)`).
- `s = 0`: 48 survivors of 244 at `c = 3` (the Mills residual classes, the known-answer control) and 73 of 183 at `c = 2`.
- `s ≥ 2`: **0 genuine survivors** at either `c` (the only hit, `(x − 1)²`, is not Pisot).
- The predicted exception family survives: `2 + √2`, `1 + √3` at `c = 2`; `3 + √6`, `x² − 3x − 3` at `c = 3`.
- **Degree 4** (coefficients in `[−4, 4]`, 2026-09-30 02:00): `s = 0` gives 27 of 201 survivors at `c = 2` and 33 of 271 at `c = 3`; `s ≥ 2` gives **0 at both**.
- **Exception (i) looks like a proof artifact.**  The cyclic cubic Pisot numbers of conductor 7 (the exceptional field at `c = 2`: `(−6, 5, −1)`, `(−3, −4, −1)`, …) have **no survivors at any `s`, even `s = 0`**.  `2` is inert there, so traces are sums like `ζ₇ + ζ₇² + ζ₇⁴ = (−1 + √−7)/2`, which are irrational.  A decomposition-group version of step 4 should remove (i).

**The exception (ii) is a genuine obstruction for congruence methods.**
- If `f ≡ X^d (mod c)`, then `⌊α^N⌋ ≡ ε_N (mod c^(big))`.
- If `ε_N = 0` along the tower, the value is divisible by `c`, hence composite.  So negative-conjugate cases are killed by choosing the parity of `s`, e.g. `1 + √3` with `s` odd.
- If `ε_N = −1` persistently (all conjugate contributions positive, e.g. `2 + √2` at `c = 2`, `6 + √30` at `c ∈ {2, 3}`), the value is `≡ −1` forever: a **Mersenne-type survivor**.
- For **any** non-reversible ILRS `R`, `a₀` has finitely many primes, and `f = x² − Mx + N` with `M, N ≡ 0 (mod rad a₀)` and both conjugates in `(0, 1)` gives such an `α`.  **So Problem 1.7 in full ("every Pisot α") cannot be settled by prime-as-modulus arguments alone, even in degree 2.**  A precise negative, worth a remark in the paper.

**Exceptions (i).**  Abelian fields inside `ℚ(ζ_M)`: finitely many, e.g. for `c = 2`, `d ≤ 3`, `M ∣ 21`: `ℚ(√21)` and the cubic subfield of `ℚ(ζ₇)`.  These need a separate argument; the numerics suggest no survivors there either.

**Complementarity with Mills.**  At `s = 0` the unconditional wall is the totally real cubic case.  At `s ≥ s₀`, Theorem D handles totally real and complex cubics alike.  The obstruction for Mills is exactly the `s = 0` trace structure.

**Step-by-step re-check (2026-09-30 01:55):**
- Filter: `R(n+kj) − R(n) = c^n (c^(kj) − 1)` ✓.
- Window: `Σ_i v_c(p^i − 1) > n ⇒ ∃ i ≤ d`, `p ≡ ω(p) (mod c^(n/d − v_c(i)))` ✓.
- Teichmüller limits in ramified extensions: `⟨u⟩^(c^n) → 1` ✓.
- Pull-back `ι⁻¹` ✓.
- The Galois dominance step needs one complex embedding only, since the Pisot property is a property of the root set ✓.
- `s₀(d) = ⌈log(d + 1)/log 1.3247⌉` suffices (`α^s > d + 1` gives both `α^s > d − 1` and `|tr C^s| ≥ 3`).

**To verify before the paper:**
- the Teichmüller limit formula when `C` is not semisimple mod `c`;
- the size bound `s₀(d)` (need `α^s > d − 1` and `tr C^s ≥ 3`; `α ≥ 1.3247` by Siegel, so `s₀ = 3` works for `d ≤ 3`);
- the window for `c ≡ 1 (mod 3)` (`t ∈ ℚ(ζ₃)`: same argument, `|t| ≤ 2`);
- disjointness bookkeeping for (i).

**Lean path.**  The Galois step is heavy.  Lean-sized pieces:
- the combinatorial "stuck" lemma (pure `ℕ → Bool` combinatorics);
- the filter with varying `ε`;
- the quadratic case via exact identities: `d = 2` needs no Galois, since `Λ = ζ₁ α₁^s + ζ₂ α₂^s` can be handled by the norm/trace of `ℚ(√D)`.
A reasonable first Lean target: **Theorem D for quadratic Pisot `α`**.

### Theorem C_D: prime-free intervals around `⌊α^(c^n + s)⌋` (paper math, 02:25)
Combine the engine (phase 41) with Theorem D's Galois step.  For `(D1)` with half-width `H`, each window must be visited only finitely often for every `|h| ≤ H`, i.e. `Λ_r ∉ {ζ′ − h − ε}`.
- If `Λ_r ∈ ℚ(ζ)`, step 4 of Theorem D forces all `ζ_k` equal, and then `Λ_r = z·tr C^s` with `z ∈ {0, ±1}`.
- So outside the **unipotent classes** `f ≡ (X ∓ 1)^d` or `X^d (mod c)`, `Λ_r ∉ ℚ(ζ)` and every shift is eventually outside its window.
- Hence **for Pisot `α` outside the unipotent classes (and the abelian exceptions (i)), there are prime-free intervals of every fixed length around `⌊α^(c^n + s)⌋`, infinitely often.**
- Inside a unipotent class exactly one shift, `h = z·tr C^s ± 1 − ε`, is a survivor, so intervals fail by construction for that `h`.
- Lean: needs the Galois step, so it goes with Theorem D (paper first).

### Theorem E (candidate): transcendence of shifted Mills constants with SMALL first term (2026-09-30 02:10)
Saito 2025 (arXiv:2508.16068) Theorem 2.6 (Type C): under `(C1)–(C5)` and short-interval primes `(2.2)` (for `c = 3` this is unconditional by MTY24), `ξ(C_k)` is transcendental OR `ξ^g` is a cubic Pisot number `≤ (2x₀^(1/9) + 1)^(g/c₁)`, with `g ∣ agcd(C_k)`.  He kills the Pisot branch **by size only**, hence his Theorem 1.9(C) needs `r ≥ 4.003·10¹⁴` for `C_k = r·3^k − 1`.

**`C_k = 3^k − 2` satisfies `(C1)–(C5)`:**
- `c₁ = 1`; the ratios exceed 3;
- `C_m ∣ C_(m + φ(C_m))`, since `gcd(3, C_m) = 1`;
- `agcd = 1`, since `gcd(3^m − 2, 3^(m+1) − 2) ∣ 4` and every term is odd.

So `ξ := ξ(3^k − 2)` is transcendental or itself a cubic Pisot number with `⌊ξ^(3^k − 2)⌋` prime for all `k`.  (`c₁ = 1` makes the size bound useless.)  **Theorem D with the shift `s = −2` then applies:**
- The mechanism is unchanged.
- The limit points are `λ_r = Σ_(units) ω(α_k)^(3^r) α_k^(−2)`.
- For `d = 3` the Galois rank step needs no Pisot dominance: `S₃` acts through `𝟙 ⊕ std` and the vector `(α_k^(−2))` is non-constant with nonzero sum; in the `C₃` case, a circulant with nonzero eigenvalues.
- So every `ζ_k = z = t/T` with `T = tr(C^(−2)) ∈ ℚ`, hence `z = ±1` or `0`.

**Exceptional classes that remain:**
- **E1.** `ξ` in the cyclic cubic field of conductor 13 (the only abelian cubic field inside `ℚ(ζ_(lcm(26, 8)))`).  Probably an artifact, as the conductor-7 check suggests.
- **E2.** `f ≡ (X ∓ 1)³ (mod 3)` and `tr(ξ^(−2)) ∈ {0, ±1, ±2}`.  (`T = 0` forces `t = 0`, i.e. value `≡ ε`, so it behaves like E3 and dies whenever `ε = 0`.  Numerics found `(−9, −6, −2)`: `σ₂² = 2σ₁σ₃`, `T = 0`, complex, and killed by `ε`.)  **Impossible for totally real `ξ`**, where `β₂^(−2) + β₃^(−2) > 2`; only complex cubics with `2|β₂|^(−2) cos 2θ + ξ^(−2)` small remain.
- **E3.** `f ≡ X³ (mod 3)` with the floor offset `ε = −1` for all large `n` (if `ε_n = 0`, then `3 ∣ ⌊⌋`, which is composite).  For totally real `ξ` this needs a positive dominant conjugate; for complex `ξ`, an orbit of `x ↦ 3x + 4θ/2π` trapped in a half-circle.

**Candidate statement:** `ξ(3^k − 2)` is transcendental unless `ξ ∈ E1 ∪ E2 ∪ E3`.

**Numerics (02:15):** all irreducible cubic Pisot `f` with coefficients in `[−9, 9]` (867 of them), at `c = 3`, `R = 3^n − 2`, precision `3^10`, with the true floor offset `ε_n` computed from the conjugates (`n = 4..15`).
- 41 pass the window test.
- 37 of those are killed by `ε_n = 0 ⇒ 3 ∣ value`.
- **The 4 genuine-looking survivors are all E3 with a positive dominant conjugate**: `x³ − 9x² + 3`, `x³ − 9x² + 6`, `x³ − 9x² + 3x + 3`, `x³ − 6x² + 3` (coefficient tuples `(−9,0,3)`, `(−9,0,6)`, `(−9,3,3)`, `(−6,0,3)`).
- So the exception set in practice is exactly the Mersenne-type class.  The same template works for `ξ(r·3^k − 1)` at every `r ≥ 1` (`s = −1`, `T = σ₂/σ₃`), which would extend Saito's Theorem 1.9(C) from `r ≥ 4·10¹⁴` to all `r`, up to congruence-defined exceptions.

**Honest weight.**
- Saito's own Mills exceptions are a size window (`(1.3)`); ours are congruence classes mod 3 plus a trace condition.  Neither is empty, so this is a *different* partial result, not a completion.
- E3 is Mersenne-shaped and probably genuinely out of reach of congruences.
- **Checked against Saito's text (§9, 02:05):**
  - Theorem 2.6 allows real `c_k` (only `C_k ∈ ℕ`); our `(C4)` witness `k = m + φ(C_m) > m` is exactly his pattern for `r·3^k − 1`.
  - The proof routes through Type B (Theorem 2.3), which already forces degree `ℓ = 3` (quadratic excluded) and `g ∣ agcd = 1`.
  - So the branch is exactly "`ξ` is cubic Pisot with `⌊ξ^(3^k − 2)⌋` prime `∀k`".
- **Remaining:** the Theorem D (`s = −2`) write-up, and E1–E3.

## 2. Conjectures, each with its difficulty check

| Conjecture | Proved implications | Unproved premise | Mechanism for the premise |
|---|---|---|---|
| **DoubleExpTraceComposite** (ours, phase 30) | ⇒ Fermat composites i.o.; ⇒ Mills transcendental | the survivor cases (all `λ_r + h ∈ μ`) | **none known**; these are Fermat-type by construction |
| **Theorem C for `d ≥ 3`** (e.g. Tribonacci intervals) | ⇐ non-integrality of every limit point; the filter and the whole assembly are now `d`-generic in Lean (`exists_shift_pow_congr`, `covering_of_good_seq`, `prime_free_of_covering_seq`) | `λ_r ∉ ℤ + μ` for order-3 entries | **reformulated (2026-09-30):** the limit `Λ` exists and satisfies `Λ^(c^(d')−1) = I`, so it is torsion in `GL_d(ℤ_c)` with Teichmüller eigenvalues.  The certificate is "no such torsion element has entry `s − h`".  `d = 2` avoids the lifts via the exact composition `Φ_J`; `d ≥ 3` does not.  Candidate: norm or trace relations over `W(𝔽_(c^d))` |
| **Theorem A for even `d ≥ 4`, `h = 0`** | ⇐ no limit point in `{±1}` | — | **resolved on paper by Theorem C′**: `h = 0` survivors need `λ_r ∈ {±1} ⊂ ℚ`, but `λ_r ∉ ℚ` (given disjointness).  The elementary orbit-sum count remains the Lean route for odd `d`; even `d` in Lean needs C′ or a per-`H` certificate |
| **Quantitative Theorem C with `log n` intervals** | would match Saito's `δ(n)` | small good primes `p_h` (instead of `p_h ∣` a huge value) | Chebotarev-type density of primes whose Frobenius cycle hits `−h`; plausible and analytic, not Lean-sized |
| **Saito Problem 1.7** (one `R` for all Pisot `α`) | — | trace survivors in every residue class | none; Maze row stands |

## 3. What the survivors teach about Mills (write-up, not a phase)
- The six Mills residue classes are exactly the survivors of the cubic trace at `c = 3`.
- Saito's exact recurrence `(t, b) ↦ (t³ − 3bt + 3e, b³ − 3etb + 3e²)` has the integer fixed point `(x, e·x)` (`x = ±1`), i.e. `χ ≡ (X − x)(X² + ex) (mod 3)`.  That is **the same structure as Fermat**: an integer fixed point of the composition dynamics inside the `±1` window.
- Precise sentence for the paper: *the prime-as-modulus method proves compositeness exactly when the composition dynamics has no integer orbit in the window; Fermat, `L(2^n)` and the Mills residual classes are integer orbits.*
- The Mills question in those classes is therefore at least "Fermat-shaped".  No reduction is proved, and none is claimed.

## 4. Treadmill queue (Lean only; Ren steers)
1. Phase 38 (running): Lucas `U(P, ±1)`, odd `c ∤ D`.
2. Phase 39 (drafted): `⌊α^(c^n)⌋ + h` for quadratic Pisot units of norm `−1` (cheap corollary; communicative value).
3. **Phase 40: Theorem C, Fibonacci, `c = 2`**: `∀ H, ∃ m L (p : ℤ → ℕ), ∀ |h| ≤ H, ∀ k, p h ∣ F(2^(Lk+m)) + h`, plus the interval corollary.
4. **Phase 41: the Theorem C ENGINE.**  A general `d × d` statement with an abstract hypothesis: `A ∈ M_d(ℤ)` with `det` a unit mod every relevant `p`, prime `c`, entry or trace `u`, and `∀ |h| ≤ H, ∀ᶠ n, ∃ prime p ∣ u(c^n) + h` with `v_c(glCard d p) ≤ n`.  Conclusion: (D1) plus prime-free intervals.  Refactor phase 40's mechanism into it.
   - Instances, each only needing `exists_good_prime_factor`: Fibonacci at every prime (`Φ_j` with `2j + 1 = c²`; `c = 5` via factorizations); Lucas at odd `c` (phase 35 fixed point); `U(P, ±1)` (phase 38); Tribonacci for a fixed `H` by a `decide` certificate.
5. Phase 42: Theorem B (2×2 traces, odd `c`, `det ≡ ±1`), plus the `Φ₃`/`Φ₆` exception stated as a frozen survivor fact.
6. Phases 43–44: Theorem A (general `d`, inert), with the Tribonacci corollary.
7. Stretch: a quantitative Theorem C statement (`(log n)^(1/5)`), if the bookkeeping is clean.

## 4a. Week-by-week (proposal, 2026-09-30)
- **Week 1 (Lean, cheap, high certainty).**  Phase 42 (Theorem B), phase 43 (intervals: Fibonacci at every prime; `U(P, ±1)`), phase 39 (quadratic Pisot floor corollary).  In parallel Ren writes the **paper draft §1–3 and §5** (everything already in Lean): Saito 1.8, binary recurrences, Theorem B, Theorem C for binary sequences.
- **Week 2 (paper math, the new frontier).**  Rigorous write-ups of Theorem D (Saito 1.7 partial) and Theorem E (`ξ(3^k − 2)`), including the decomposition-group fix for exception (i) and the `T = 0` subcase.  Numerics to extend: degree 5–6 Pisot; `c = 5, 7`; `r·3^k − 1` for small `r`.
- **Week 3 (Lean infrastructure).**  The orbit-sum identity `Σ_(i<d) A^(c^(n+i)) ≡ tr(A^(c^n))·I (mod c^(n+1))`, via either (a) a Galois-ring Frobenius (Hensel lift of a root of `f` near `x^c` in `(ℤ/c^k)[X]/f`), or (b) the Teichmüller limit `S = lim A^(c^(dk))` in `M_d(ℤ_c)` plus the eigenvalue/Cayley–Hamilton argument that `Σ S^(c^i)` is scalar.  Then Theorem A (Tribonacci).  Multi-phase; the first phase is only the `c`-adic limit `S` and `S^(c^d) = S`.
- **Week 4+.**  Lean for Theorem D in the quadratic case (the Galois step for `d = 2` is a conjugation in `ℚ(√D)`), then cubic.  Theorem E in Lean is the long pole: it needs Saito's Type C (`Literature` Prop or our phase-6-era machinery) plus Theorem D for cubics.

**Ranking by value:** D ≈ E (new answers to Saito's open problems) > C (intervals; qualitative) > A (order `d`) > B (classification) > corollaries.  The ranking by Lean cost runs the other way, which is why weeks 1 and 3 are Lean-heavy and week 2 is paper-heavy.

## 4b. Outward notes (Trevor's call, not queued)
- formal-conjectures (checked 2026-09-30, `origin/main` + all PRs): no Saito problems stated; only `Wikipedia/Mills.lean`.  Stating Saito's 1.7/1.8 there, with 1.8 solved, is possible.

## 5. The paper (a draft for Trevor to decide on; publishing and arXiv are his call)
Working title: *Composite values of linear recurrences along prime-power towers.*
1. Saito's Problem 1.8, with the one-page proof.
2. The filter, and the limit-point framework (survivors vs. intervals).
3. Binary recurrences: the sign flip (inert), exact composition (all primes), and Theorem B's classification for traces.
4. Theorem A: order `d`, inert primes (Tribonacci).
5. Theorem C: prime-free intervals for non-reversible towers (engine; Fibonacci/Lucas at every prime; C′ Galois for `d ≥ 3`; C_D for Pisot floors).
5b. **Theorem D: Saito's Problem 1.7 for `R(n) = c^n + s`**, every Pisot `α` outside the unipotent/Mersenne class and the abelian exceptions; plus the proof that congruence methods cannot reach the Mersenne class (so 1.7 in full needs a new idea).
5c. **Theorem E: transcendence of `ξ(3^k − 2)`** outside E1–E3 (Saito Type C + Theorem D).  Also the template for `ξ(r·3^k − 1)` at every `r`.
6. Survivors: Fermat, `L(2^n)`, Mills; the fixed-point picture; open problems.

Everything is Lean-checked (link the repo), but the paper stands on its own mathematics.  Credit Saito's (C4) argument for the easy form of the filter (see `FINDING-SAITO-PROBLEM-1-8.md`).
