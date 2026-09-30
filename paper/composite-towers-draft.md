# Composite values of linear recurrences along prime-power towers

*Working draft 0, 2026-09-30.  Drafted by Claude (Ren) at Trevor Morris's direction.  Whether, where and how this is published is Trevor's decision.  Every statement marked **[Lean]** is machine-checked in `gotrevor/lean-formalizations` (file and theorem named).  Statements marked **[paper]** have written proofs (`PROOF-THEOREM-*.md`) that have had adversarial read-throughs but no independent refereeing.*

---

## Abstract (draft)
Saito (arXiv:2504.14968) asked whether `F(2^n) + h` is composite for infinitely many `n`, for every integer `h` (Problem 1.8).  He also asked for a non-reversible inhomogeneous linear recurrence `R` such that `⌊α^(R(n))⌋` is composite infinitely often for every Pisot number `α` (Problem 1.7).  We answer Problem 1.8 affirmatively and extend it to every prime base and to all Lucas sequences with unit parameter.  We obtain Dubickas-type covering systems, and hence prime-free intervals of every fixed length, along the non-reversible tower `c^n`.  We classify the traces of `2×2` integer matrices at odd prime towers.  For `R(n) = c^n + s` we answer Problem 1.7 for every Pisot number outside an explicit "Mersenne-type" class `f ≡ X^d (mod c)`, and we show that class cannot be handled by the method for any non-reversible `R`.  Combined with Saito's reduction theorems, this yields the transcendence of the least constant `ξ` with `⌊ξ^(3^k + s)⌋` prime for all `k`, for every `s ≠ 0`.  The unshifted case `s = 0` is Mills' constant, and the method identifies exactly why it fails there.

## 1. Introduction
- Mills' constant and Saito's programme: irrationality (Saito 2024); transcendence under RH/DH (Saito 2025); the cubic Pisot obstruction.
- Dubickas (2002, 2018) and Saito (2025): composite values and prime-free intervals near `⌊α^(R(n))⌋` when `R` is **reversible**.  The difficulty is non-reversible `R` such as `2^n` or `3^n`, which is where Mills lives.
- Our main tool: **the prime is its own modulus.**  If `p = u(c^n) + h` is prime, Lagrange's theorem in `GL_d(𝔽_p)` shows that either `p` divides a later term or `p ≡` a root of unity modulo a large power of `c`.  The observation is not new in its simplest form: Saito's (C4) argument in 2508.16068 uses the term as modulus, and the 1×1 case `a^(c^n) + h` is olympiad folklore (PEN).  **What is new is what we do with the root-of-unity escape.**

## 2. The filter  **[Lean]** `SharedConjecture.exists_trace_pow_congr`, `SaitoFibonacci.exists_entry_pow_congr`, `FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat`, `TheoremDGround.*`
**Lemma 2.1.**  Let `A ∈ M_d(ℤ)`, `ℓ` a `ℤ`-linear functional, `c` prime, and `p` prime with `p ∤ det A` and `p ∣ ℓ(A^(c^n)) + h`.  If `v_c(|GL_d(𝔽_p)|) ≤ n`, then `p ∣ ℓ(A^(c^(n+kj))) + h` for all `k ≥ 0`, for some `j ≥ 1`.  Otherwise `p^i ≡ 1 (mod c^(n/d))` for some `i ≤ d`.

## 3. Saito's Problem 1.8  **[Lean]** `SaitoFibonacci.fib_two_pow_add_not_prime`
**Theorem 3.1.**  For every `h ∈ ℤ`, `F(2^n) + h` is composite for infinitely many `n`.
*Proof.*  Odd `h`: parity.  `h = 0`: divisibility.  Even `h ≠ 0`:
- the filter gives `F(2^n) + h ≡ ±1 (mod 2^(n/2))` for all large `n`;
- the **sign flip** `F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`, from `L(2^n) ≡ −1 (mod 2^(n+1))`, turns two consecutive windows into `2h ≡ s + s′ (mod 2^(n/2))` with `s, s′ ∈ {±1}`;
- so `h = 0`.  ∎

## 4. Binary recurrences at every prime base
- **Theorem 4.1 (Fibonacci, every prime).**  For every prime `c` and every `h`, `F(c^n) + h` is composite i.o.  **[Lean]** `FibonacciAllPrimes.fib_prime_pow_add_not_prime_all`.
  - The inert primes use the sign flip (Frobenius swaps the eigenvalues).
  - The other primes use the exact composition `F((2j+1)N) = Φ_j(F(N))` for odd `N`, which turns the congruences into the integer equation `Φ_j(x) ∈ {x, x ± 2}`; it has no admissible solution.
  - `c = 5` uses `5^n ∣ F(5^n)` and `F(4k+1) ± 1` factorizations.
- **Theorem 4.2 (Lucas sequences).**  `U(P,Q)`, `P, Q` odd, at `c = 2` (**[Lean]** `LucasTwoPow`); any `(P,Q)` at odd `c` inert in `ℚ(√(P² − 4Q))` (**[Lean]** `LucasInert`); `U(P, ±1)` at every odd `c ∤ D` (**[Lean]** `LucasUnitAllPrimes`).
- **Theorem 4.3 (Lucas numbers).**  `L(c^n) + h`, and `V_(c^n)(P, −1) + h` for `c ∤ P`, are composite i.o. at every odd prime `c` (**[Lean]** `LucasPrimePow`).  At `c = 2` the method stops exactly at `L(2^n)`, a Fermat-type problem.
- **Corollary 4.4.**  `⌊φ^(c^n)⌋ + h` is composite i.o. for every odd prime `c` and every `h` (`φ` the golden ratio), and likewise for every quadratic Pisot unit of norm `−1` (**[Lean]** `QuadraticPisotFloor`).

## 5. Traces of 2×2 matrices: a classification  **[Lean]** `TraceClassification`
**Theorem 5.1.**  Let `C ∈ M_2(ℤ)`, `c` an odd prime, `det C ≡ ε = ±1 (mod c)`, `c ∤ tr C · disc C`.  Then `tr C^(c^n) + h` is composite i.o. for every `h`, unless `ε = 1` and `tr C ≡ ±1 (mod c)`.  In that exceptional case `c^(n+1) ∣ tr C^(c^n) ∓ 1`, so the shifts `h ∈ {0, ∓2}` are genuine survivors of the method.
*Remark.*  At `c = 2`, every `2×2` trace has survivors (`τ = −1` or `2`); `L(2^n)` is the prototype.  The staircase is: `1×1` folklore; `2×2` classified; `3×3` at `c = 3` is Mills (§9).

## 6. Prime-free intervals along a non-reversible tower  **[Lean]** `FibonacciCovering`, `CoveringEngine`, `CoveringInstances`
**Theorem 6.1 (engine).**  If every value `ℓ(A^(c^n)) + h`, for `|h| ≤ H` and `n` large, has a prime factor `p` with `v_c(|GL_d(𝔽_p)|) ≤ n`, then there are `m`, `L` and primes `p_h` with `p_h ∣ ℓ(A^(c^(Lk+m))) + h` for all `k`.  In particular the intervals `[ℓ(A^(c^n)) − H, ℓ(A^(c^n)) + H]` are prime-free infinitely often (given growth).
**Theorem 6.2.**  For every prime `c` and every `H`, `[F(c^n) − H, F(c^n) + H]` contains no prime for infinitely many `n`.  The same holds for `L(c^n)` (odd `c`) and `U(c^n)(P, ±1)`.
*Example.*  `F(2^(4 + 60k)) + h` is composite for all `|h| ≤ 6` and all `k ≥ 1`, divisible by one of `2, 3, 23, 197, 983, 991`.
*Remark (quantitative).*  The bookkeeping gives intervals of length `≫ (log n)^(1/5)` around `F(2^n)` [paper; not optimized].  Saito's reversible theorems give `log n/(2d)`.
*Remark (higher order).*  For order `d ≥ 3` entries (Tribonacci), the needed non-integrality of the limit points follows from linear disjointness of `ℚ(α)` and `ℚ(ζ_n)` [paper, `ROADMAP` Theorem C′].

## 7. Saito's Problem 1.7 for `R(n) = c^n + s`  **[paper]** `PROOF-THEOREM-D.md`
**Theorem 7.1.**  Let `c` be prime and `s ≥ s₀(d) = ⌈log(d+1)/log κ⌉`.  For every Pisot `α` of degree `d` with `f ≢ X^d (mod c)`, the number `⌊α^(c^n + s)⌋` is composite for infinitely many `n`.
*Key steps.*
- the floor offset `ε ∈ {0, −1}` and a combinatorial "stuck-index" lemma;
- Teichmüller limit points `Λ_r = Σ_k ζ_k α_k^s`;
- one automorphism moving a unit root onto `α`, after which the dominant term `α^s` exceeds everything else in the limit identity (`α^s < d + 1`, a contradiction).  No Galois rigidity is needed; rigidity is used only in §8, where the shift is negative.
*Numerics.*  Degrees 2–4, `c ∈ {2, 3, 5, 7}`: with `s = 0`, 27–73 survivors per box (the Mills-type residual classes); with `s ≥ 2`, **none**.
**Proposition 7.2 (the obstruction).**  If `f ≡ X^d (mod c)` and the conjugate contribution stays positive (e.g. `α = 2 + √2`, `c = 2`), the values are `≡ −1` modulo growing powers of `c`, and the filter is silent.  For **any** non-reversible ILRS `R` there is a quadratic Pisot `α` of this type, so Problem 1.7 in full needs an idea beyond this method.

## 8. Transcendence of shifted Mills constants  **[paper]** `PROOF-THEOREM-E.md`
**Theorem 8.1.**  For every even `s ≠ 0`, the least `ξ > 1` such that `⌊ξ^(3^k + s)⌋` is prime for every `k ≥ k₀(s)` is transcendental.  (`3 ∣ s` reduces to the shift `s/3^a` for `β = ξ^(3^a)`.)
**Theorem 8.2 (odd `s`).**  The same holds for every odd `s`.  So **`ξ(3^k + s)` is transcendental for every `s ≠ 0`.**  The new ingredient for `g = 2` is a trace-zero argument over `ℚ(μ₂₀₈)`, since odd powers of `±√β` cancel.  The Kummer-degenerate case `ξ = √d·γ` gives `|tr γ^s| = d^(−s/2) ∉ ℚ`.  In the conductor-13 field it is instead killed by a prime `q ∣ d` with a unique prime above it.  E.g. `ξ(3^k − 2)` (`k ≥ 1`) and `ξ(3^k + 2)` (`k ≥ 1`).
*Proof outline.*
- Saito's Theorem 2.3 reduces to `ξ` a cubic Pisot number.  His extra hypothesis `(B6)` is exactly what non-reversibility breaks.
- His Proposition 3.1(iv) gives floor = trace.
- §7's machinery with the shift `s` (for degree 3 the rigidity needs no dominance) forces `f ≡ (X ∓ 1)³ (mod 3)` and `tr(ξ^s) = ±1`, which contradicts `tr(ξ^s) ≡ 0 (mod 3)`.
- The one exceptional field (cyclic cubic of conductor 13) is closed by a finite Galois-trace computation.
*Example.*  Heuristically (greedy chain; cf. Mills' constant under RH), `ξ(3^k − 2) ≈ 2.0066301472550073895638290682681…`, with prime chain `2, 131, 36448807, …`.
*Comparison.*  Saito's Theorem 1.9(C) proves transcendence for `ξ(r·3^k − 1)` with `r ≥ 4·10¹⁴`, by size.  Ours is arithmetic and works at the smallest first term.

## 9. What the method cannot do
- **Fermat and `L(2^n)`**: integer fixed points of the composition dynamics inside the window.
- **Mills' constant (`s = 0`)**: the floor is a Frobenius-invariant trace.  With `ε = 0`, the filter forces `χ ≡ (X − x)(X² + ex) (mod 3)` (6 of 27 classes), which is the fixed point `(x, e·x)` of Saito's recurrence `(t, b) ↦ (t³ − 3bt + 3e, …)`.  Galois rigidity has no weights to act on.  We record this as the precise obstruction.
- **The Mersenne class** of Proposition 7.2.

## References (to complete)
Saito 2024 (Mills irrational), Saito 2025 (arXiv:2504.14968; arXiv:2508.16068), Dubickas 2002 and 2018, Mossinghoff–Trudgian–Yang 2024, Baker–Harman–Pintz 2001, Siegel 1944, PEN problems (olympiad folklore for `a^(2^n) + k`).
