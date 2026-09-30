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

### Theorem C: prime-free intervals for the non-reversible tower `c^n`  ✅ numerics, ⏳ Lean
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
- Lean: phase 40 (Fibonacci, `c = 2`, the qualitative (D1) plus intervals), then all primes.

### Theorem C′: non-integrality of limit points for `d ≥ 3` (paper math, written 2026-09-30 01:30)
The obstacle for Theorem C at `d ≥ 3` is that no exact composition is available.  Galois theory replaces it.
- Let `K` be the splitting field of `χ_A` (irreducible over `ℚ`), with eigenvalues `α_k` and spectral projectors `E_k ∈ M_d(K)`.  The Teichmüller lifts are `ω(α_k) = ζ^(c^k)`, where `ζ` is a root of unity of order `n ∣ c^d − 1` (`c` inert).
- Then `lim A^(c^(dn + r)) = Σ_k ζ^(c^(k+r)) E_k`, and the limit point `λ_r = Σ_k (E_k)_ij ζ^(c^(k+r))` lies in `K(ζ_n) ∩ ℚ_c`.
- **Claim:** suppose `K` and `ℚ(ζ_n)` are linearly disjoint, `n` is squarefree, and `ord_n(c) = d < φ(n)`.  Then `λ_r ∉ ℚ` unless `u ≡ 0`.  This suffices whenever the window is `{±1}`: `c = 2`, or `μ_(d!) ∩ μ_(c−1) = {±1}` (e.g. `d = 3` with `3 ∤ c − 1`).
  - Proof: for squarefree `n` the primitive `n`-th roots `{ζ^m : m ∈ (ℤ/n)^×}` form a `ℚ`-basis of `ℚ(ζ_n)`, hence a `K`-basis of `K(ζ_n)` by disjointness.
  - A rational `q` equals `q·μ(n)·Σ_m ζ^m`, since the sum of the primitive roots is `μ(n) = ±1`.
  - `λ_r` is supported on the `d` exponents `{c^(k+r)}` of one Frobenius orbit.  Since `φ(n) > d`, some basis vector lies outside the orbit; its coefficient forces `q = 0`, and then all `e_k = (E_k)_ij = 0`.
  - Larger windows (`ω ∈` window when `3 ∣ c − 1` and `d ≥ 3`) need the same comparison against `ℚ(ζ_(c−1))`-combinations, i.e. full orbits of `Gal(ℚ(ζ_n)/ℚ(ζ_(c−1)))`.  Still to write out.
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

## 2. Conjectures, each with its difficulty check

| Conjecture | Proved implications | Unproved premise | Mechanism for the premise |
|---|---|---|---|
| **DoubleExpTraceComposite** (ours, phase 30) | ⇒ Fermat composites i.o.; ⇒ Mills transcendental | the survivor cases (all `λ_r + h ∈ μ`) | **none known**; these are Fermat-type by construction |
| **Theorem C for `d ≥ 3`** (e.g. Tribonacci intervals) | ⇐ non-integrality of every limit point | `λ_r ∉ ℤ + μ` for order-3 entries | no exact composition in `d = 3`, because the free second symmetric function is Saito's `b_k` obstacle.  Candidate: norm or trace relations over `W(𝔽_(c^d))`.  Needs an idea; worth a probe |
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

## 4b. Outward notes (Trevor's call, not queued)
- formal-conjectures (checked 2026-09-30, `origin/main` + all PRs): no Saito problems stated; only `Wikipedia/Mills.lean`.  Stating Saito's 1.7/1.8 there, with 1.8 solved, is possible.

## 5. The paper (a draft for Trevor to decide on; publishing and arXiv are his call)
Working title: *Composite values of linear recurrences along prime-power towers.*
1. Saito's Problem 1.8, with the one-page proof.
2. The filter, and the limit-point framework (survivors vs. intervals).
3. Binary recurrences: the sign flip (inert), exact composition (all primes), and Theorem B's classification for traces.
4. Theorem A: order `d`, inert primes (Tribonacci).
5. Theorem C: prime-free intervals for non-reversible towers.
6. Survivors: Fermat, `L(2^n)`, Mills; the fixed-point picture; open problems.

Everything is Lean-checked (link the repo), but the paper stands on its own mathematics.  Credit Saito's (C4) argument for the easy form of the filter (see `FINDING-SAITO-PROBLEM-1-8.md`).
