# Mills' constant: the six residual mod-3 classes (probe, 2026-09-30)

**Verdict: no mechanism.**  The lap produced three things.
1. **One new local lemma** (the Kronecker lemma, §3).  It splits the six classes into an abelian half and a hard core.
2. **A sharper map of the wall** (§5a).  The local route is *not* Fermat-blocked.  Every explicit residual cubic we tried dies to a small certificate: all 184,513 totally real cubic Pisot β ≲ 6000 with Saito's (1.3), and all 2.4 million τ = −1 cubics in a box, die by q ≤ 47.  Fermat numbers, by contrast, structurally have no certificate at any prime.  What blocks the local route is *uniformity*: the Mills β is hypothetical, so one needs a certificate for every residual cubic at once.  That is Saito's Problem 1.1 restricted to these classes, with only an Artin-type heuristic behind it.
3. **The only Mills-specific lever, least-ness, is gap-bound limited** (§4).  Its exponent sits strictly between the BHP exponent and the RH exponent.
4. **The hard core shrank (§7, 2026-10-01).**  A second local lemma (paired roots) kills type (1)(2) at `T_j` whenever the 3-adic rate is c = 1 and `N(β)` is a cube mod `T_j`.  So unit β with c = 1 gets a Jacobi certificate as well; alone it kills 436 of 442 such cubics in a box.  What is left is c ≥ 2 (a mod-9/27 condition on f) or a non-cube norm.  There, the cube classes at `p = T_j` match random primes: nothing is forced.

Script: `scripts/mills-residual-probe.py {kron-control|filter|saito}`.  Prior work: `FINDING-MILLS-3ADIC.md` (phase 29, the six classes), `PROBE-MILLS-PROJECTIVE.md` (inert primes excluded), `PROBE-MILLS-TRANSCENDENCE.md` (Saito 2025, Theorems 1.7–1.8).

## 1. The premise, stated exactly

Suppose ξ is algebraic.  Saito (2024 Thm 1.2; 2025 Thm 1.7) gives a totally real cubic Pisot β = ξ^(3^m) satisfying (1.3): `β₂ < 0`, `|β₃| < −β₂ ≤ min(|β₃|^(17/23), β^(−17/40))`.  Write `T_j = Tr β^(3^j)`, `x_i = β_i^(3^j)` and `s_j = x₂ + x₃ < 0`.  Then for all large j:
- **(P1) primality:** `T_j = p_(m+j)` is prime (the floor equals the trace once `|s_j| < 1`);
- **(P2) least-ness:** the interval `(T_j³, T_(j+1))` contains no prime.  It has length `g_j = −3 b_j T_j + 3 e_j ≈ 3 T_j² |s_j|`, where `b_j = σ₂(x)` and `e_j = N(β)^(3^j)`.

(P2) is exactly least-ness.  Here is why.  Any A below ξ breaks off the chain at some first level k, at a prime q in `[p_(k−1)³, p_k)`.  From any prime beyond `exp(exp(32.9))` a chain continues forever (Cully-Hugill 2023, primes between consecutive cubes).  So for large k, least-ness says precisely that this interval holds no prime.  Nothing more about least-ness survives to large k.

In the unit case (`N(β) = ±1`) the gap has a symmetric form: `g_j = −3e_j(Tr α · Tr α^(−1) − 1)` with `α = β^(3^j)`.  This is an identity, not a factorization.

## 2. The difficulty check, lever by lever

The test: a lever must use something Mills has that these siblings lack.
- **S1:** every trace sequence `Tr γ^(3^j)` in the residual classes.  Fermat-shaped: composite i.o. is believed but unproved.
- **S2:** non-least members of `W(3^k)`.
- **S3:** totally real cubic Pisot β satisfying (1.3) but not Mills.

| Lever | Uses only | Separates? | Verdict |
|---|---|---|---|
| Saito (1.3) ∩ residual classes | the conjugate geometry | no: an explicit family satisfies (1.3) in each class.  For example `x³ − a x² − b x + 1` with `b ≈ c√a` gives `β₂ ≈ −(c+√(c²+4))/(2√a)` and `β₃ > 0`, and a, b can be chosen mod 3 freely.  The census has 184,513 such β below ~6000 (§5) | S3 contains it; not a closer |
| small-prime covering, q ≤ Q | f mod q | no: every finite set of congruence conditions leaves an infinite part of the 2-parameter (1.3) family, though every *explicit* β dies at some q (§5a) | S1 property, uniformity-blocked |
| projective / GL₃ / **Kronecker (new, §3)** | splitting of the prime `T_j` in K | no: the lemmas hold for every eventually-prime trace sequence | S1 property, burn-down only, but strong (§5) |
| the levels below m (`ξ^(3^(m−1)) = β^(1/3)`) | the real cube root | adds only `Tr β = nextprime(p_(m−1)³)`, a condition on the trace that the family meets at will | nothing |
| 3-adic size of the gap | (P1) | `v₃(g_j) ≥ j+1`, while `g_j ≈ x^(1/2+η)` dwarfs `3^j` | nothing |
| **least-ness (P2)** | the prime-free interval | **yes, the only lever that does**: S1, S2 and S3 all lack it.  In the census every local survivor has a prime within +3…+54 of `T₀³`, where Mills would need a prime-free stretch of 10⁵–10⁶ | blocked analytically (§4) |

## 3. The Kronecker lemma (new)

**Lemma K (sharpened, 2026-10-01).**  Let C be an n×n integer matrix and p a prime with `p ∤ det C`, and let c be coprime to `p(p − 1)`.  If the charpoly of C splits mod p, with any multiplicities, then `tr C^(c^m) mod p` is purely periodic in m.

*Proof.*
1. Each root λ lies in `𝔽_p^×`, so `(X − λ) ∣ X^(p−1) − 1`.  Hence `χ ∣ (X^(p−1) − 1)^n`.
2. Cayley–Hamilton then makes `U = C̄^(p−1)` unipotent.
3. So `U^(p^n) = 1`, and the order of `C̄` divides `p^n (p − 1)`, which is coprime to c.
4. `c^J ≡ 1` modulo that order (Euler).  So `C̄^(c^(m+J)) = C̄^(c^m)`. ∎

This needs no projective quotient and no squarefree hypothesis.  For c = 3 the coprimality is exactly `p ≡ 2 (mod 3)`.  (For c = 2 it never holds, consistent with Fermat.)  Lean: phase 60, `NumberTheory/Mills/Kronecker.lean`, PROVED in one lap (2026-10-01): the periodicity lemma, the cubic splitting criterion, the eventual non-square statement, the finite Jacobi certificate `composite_of_jacobi_hit`, and `mills_kronecker` (from BHP + Matomäki + Dubickas, Saito's inputs).

**Lemma K (original form).**  Let f be a monic irreducible integer cubic with discriminant D and companion matrix C, and let `T_j = tr C^(3^j)`.  Let p be a prime with `p ∤ 3·D·f(0)` and `p ≡ 2 (mod 3)`.  Suppose f splits completely mod p and `p | T_j`.  Then `p | T_(j+J)` for some J ≥ 1, and hence for infinitely many indices.

*Proof.*
1. Mod p, `α = C^(3^j)` corresponds to `(a₁, a₂, a₃) ∈ (𝔽_p^×)³`.  Its class modulo scalars is `(a₂/a₁, a₃/a₁)`, whose order L divides `p − 1`.
2. Since `3 ∤ p − 1`, we have `3 ∤ L`.  Take J ≥ 1 with `3^J ≡ 1 (mod L)`.
3. Then `α^(3^J) = a₁^(3^J − 1) α`, so `T_(j+J) = λ T_j ≡ 0 (mod p)`. ∎

The projective lemma (`PROBE-MILLS-PROJECTIVE.md`) excludes inert p for j ≥ 1.  Combining the two:

**Corollary.**  If `T_j` is prime for all j ≥ j₀ and `T_j → ∞`, then every large prime `T_j ≡ 2 (mod 3)` has type (1)(2) in `K = ℚ(β)`.  Equivalently, the Kronecker symbol `(D / T_j) = −1`.  Since `T_j ≡ Tr β (mod 3)` for all j (Frobenius: `p₃ ≡ e₁³`), this holds for every large j as soon as `Tr β ≡ 2 (mod 3)`.

**Mills consequences** (conditional on ξ algebraic, via Saito):
- The three **τ = −1 classes** are `(x+1)²(x−1)`, `x²(x+1)` and `(x+1)(x²+1)`, exactly the residual classes with `Tr β ≡ 2 (mod 3)`.  In them:
  - **K cannot be a cyclic cubic field.**  There D is a square, so `(D/p) = +1`, and both allowed types are excluded.
  - In the S3 case, `(D / p_k) = −1` for every large Mills prime.  `T_j mod |D|` is eventually periodic, so this is a **finite check on f**: the eventual cycle must avoid `(D/·) ∈ {0, +1}`.
- In the three **τ = +1 classes** with K cyclic, every large Mills prime splits completely.  This too is a congruence condition on `T_j`, because the cubic character has conductor dividing `√D`.
- The **hard core** is τ = +1 with K an S3 field.  There the allowed Frobenius classes {1, transpositions} map onto `Gal^ab = C₂`, so no congruence condition on `T_j` exists.  *(Corrected in §7: when c = 1 and `N(β)` is a cube mod `T_j`, transpositions are excluded too, and `(D/T_j) = +1` is a congruence condition after all.)*  The remaining exact condition is Kummer-theoretic: at a prime `T_j`, `v₃(projective order of β mod T_j) > j`.  That condition lives over `L(ζ_(3^c))` and is non-abelian over ℚ.

The exact condition for `p = T_j` (with `T_(j+i)` prime for all i ≥ 1) is `v₃(ord of β in (𝔽_p[x]/f)^× / 𝔽_p^×) > j`.  This single condition contains phase 29 (the GL₃ bound), the projective lemma (inert type), and Lemma K (split type at `p ≡ 2 (mod 3)`).

Confidence: Lemma K and its corollary are correct (95%).  Novelty: the corollary's sharpening of `PROBE-MILLS-PROJECTIVE.md` ("the projective order can still have a large 3-part for split … reductions"), namely that a split prime with `p ≡ 2 (mod 3)` has none, appears to be new (70%).

## 4. Why least-ness is blocked

In the algebraic branch the prime-free interval is `[(y − |s|)³, y³)` with `y = β^(3^j)` and `|s| ≈ y^(−γ)`, where `γ = −log|β₂| / log β ∈ (17/40, 1/2)`.  Its length is `x^θ` with `x = T_j³` and `θ = (2 − γ)/3 ∈ (1/2, 21/40]`.
- BHP (`x^0.525`) kills `θ > 21/40`.  That is exactly Saito's 17/40, and the existing Maze row says so.
- DH/RH kills `θ > 1/2`.  That is Saito's Thm 1.8.
- The window `θ ∈ (1/2, 21/40]` is where Mills lives.
- **"Almost all x" results cannot reach it.**  Via the explicit formula, a prime-free stretch of length `x^θ` is one coherence cell for zeros of height up to `x^(1−θ)`.  Zero-density estimates bound the *number* of exceptional cells, never which ones.  The Mills points supply one cell per scale.
- **A tempting dead end:** the phases `γ log x_j` evolve by ×3, the same dynamics that killed complex conjugates.  But the zeros needed at scale j have height about `x_j^(1−θ)` and change with j, so no fixed zero carries the ×3 orbit.
- **Proving too much:** a mechanism for primes in `[n³, n³ + n^(3/2+δ)]` that ignored the structure `n = Tr β^(3^j)` would beat BHP at every cube.  So a Mills-specific proof must couple (P1) and (P2).  No coupling is known.  The interval's integers `T³ − 3uT + 3e` (u between `b_j` and 0) are the cube-traces of neighbouring characteristic polynomials.  That is an arithmetic progression with difference `3T`, and composite APs are no contradiction.

## 5. Numerics (all with controls that fail)

`kron-control`:
- Over `|c₂|, |c₁| ≤ 12`, `|c₀| ≤ 6`: every prime `T_j` (j = 1, 2, `p < 10⁷`) with `p ≡ 2 (mod 3)` and f split satisfies `p | T_(j+J)`.  That is **79 of 79**.  J is predicted from the root-ratio orders and checked by iterating `M ↦ M³ mod p`, an independent route.
- **Control:** of 77 split prime traces with `p ≡ 1 (mod 3)`, the ratio order carries a 3-part beyond `3^j` in **32**.  There the lemma makes no prediction, so the `p ≡ 2` hypothesis does real work.

`filter` (totally real irreducible cubics with `|c₂|, |c₁| ≤ 30`, `|c₀| ≤ 10`):

| class | n | Kronecker/cyclic kills | covering q ≤ 13 survivors | then Kronecker survivors |
|---|---|---|---|---|
| x²(x+1) | 1372 | 1348 | 7 | 0 |
| (x+1)(x²+1) | 1565 | 1552 (4 undetermined) | 16 | 0 |
| (x+1)²(x−1) | 1406 | 1394 (1 undetermined) | 13 | 1 |
| x²(x−1) | 1372 | 0 | 7 | 7 |
| (x−1)(x²+1) | 1565 | 0 | 16 | 16 |
| (x−1)²(x+1) | 1406 | 1 (cyclic) | 13 | 13 |

- The Kronecker filter alone kills about 98% of the τ = −1 classes.  Its survivors cluster where the root ratio `u = r′/r` at each partially ramified prime ℓ has small multiplicative order (e.g. `u = −1`), which makes `((2 + u^(3^j)) / ℓ)` constant.
- The single τ = −1 survivor of both filters, `x³ + 7x² − 19x + 5`, dies to covering at q = 17.

`saito` (totally real cubic Pisot β ≲ 6000 with (1.3); `|N| ≤ β^(3/20)`):

| class | (1.3) | covering q ≤ 31 survivors | then Kronecker/cyclic survivors |
|---|---|---|---|
| (x+1)(x²+1) | 47095 | 53 | **0** |
| (x+1)²(x−1) | 38542 | 24 | **0** |
| x²(x+1) | 6649 | 6 | **0** |
| (x−1)²(x+1) | 47735 | 48 | 48 |
| (x−1)(x²+1) | 37856 | 37 | 37 |
| x²(x−1) | 6636 | 4 | 4 |

- Every one of the 89 local survivors fails least-ness at the first step.  A prime sits within +3…+54 of `T₀³`, where Mills needs `(T₀³, T₁)` prime-free over a stretch of 10⁵–10⁶.
- **This is the control for the difficulty check:** the local constraints are satisfiable, and only (P2) separates.

`saito`, continued: the 89 τ = +1 local survivors all die to a covering prime just beyond 31.  The counts are 37 (63 of them), 41 (11), 43 (9) and 47 (6).  None lasts past 47.  Spot check: for `x³ − 5995x² − 155x − 1`, `37 | T_j` for `j = 2, 20, 38, 56`, by direct matrix powers mod 37.

`tau-minus` (exhaustive, `c₂ ≡ 1 (mod 3)` in `[−299, 301]`, `|c₁| ≤ 300`, `0 < |c₀| ≤ 30`): 2,416,020 cubics in the three τ = −1 classes.
- 1939 totally real irreducible cubics survive covering at q ≤ 31.
- The Kronecker filter kills all but **1**, plus 2 whose cycle mod |D| did not close within the cap.
- The survivor `x³ − 281x² − 163x − 13` dies to covering at q = 41.

## 5a. The local route is uniformity-blocked, not Fermat-blocked

- **Fermat** has no local certificate at any prime, structurally.  Mod an odd q, the eventual cycle of `2^(2^n)` consists of elements of odd order.  `F_n ≡ 0` would need `2^(2^n) ≡ −1`, which has order 2.  This is the classical pairwise coprimality.
- **Residual cubics show no such escape at small primes.**  The forced 3-part lives only at the moving primes `T_j ≡ τ (mod 3^(j+1))`.  At a fixed small q, a trace-zero element of prime-to-3 projective order is an ordinary event.  Heuristically it has probability about `J(q)/q`, where `J(q)` is the length of the ×3 orbit, so every f should have a certificate almost surely.  The census agrees without exception.
- So the Fermat sibling does **not** refute the local route.  The statement it needs is uniform:

  **(LC)** For every monic irreducible cubic f in a residual class, either some prime q ≠ 3 has 0 in the eventual cycle of `tr C^(3^j) mod q`, or (τ = −1) the cycle mod |D| meets `(D/·) ≠ −1`.

  LC restricted to totally real Pisot f with (1.3) implies that Mills' constant is transcendental.  LC implies Saito's Problem 1.1 (composite i.o.) for these cubics, which is open, not false.
- **Why LC has no mechanism.**  Finding the certificate prime q from f means producing a prime whose ×3-orbit on `(𝔽_q[x]/f)^×` modulo scalars hits the trace-zero plane.  Even the simplest case (q ≡ 2 mod 3 split, where cubing permutes `𝔽_q^×`) asks the orbit of `(ρ₂, ρ₃) ↦ (ρ₂³, ρ₃³)` to meet `1 + y + z = 0`.  Its length is an order of 3 modulo a divisor of `q − 1`.  That is Artin's primitive-root territory, plus equidistribution along the orbit, uniformly in f.  It does not use least-ness, so it is not Mills-specific; LC would be a theorem about all residual cubics.

## 6. What would reopen it

- **(LC), even restricted to totally real Pisot with (1.3), or to τ = −1:** some way to produce the certificate prime from f.  The Fermat sibling does not refute it (§5a), but it is Artin-type and uniform in f.
- **Hard core (τ = +1, S3; after §7: c ≥ 2 or non-cube norm):** a law forcing the cubic residue symbol of β at the primes dividing `Tr β^(3^j)` (for instance a usable generator of 𝔭 | T_j).  Alternatively, any coupling of (P1) and (P2) that uses `T = Tr β^(3^j)`.  For example, an algebraic family of integers inside `(T³, T_(j+1))` with a forced prime value, or a zero-density input below exponent 21/40 for cubes of Pisot traces.

## 7. The hard core (2026-10-01): the paired-root lemma, and where it stops

Setting: τ = +1, K an S3 field, `p = T_j` prime, `s = v₃(p − 1)`, `v = v₃(projective order of β mod p)`.  Recurrence (`p | T_(j+J)`) is excluded iff `v > j` (§3).  Write the **3-adic rate** `c_j = s − j` for large j.  It is ≥ 1 because `T_j → 1` 3-adically in all three τ = +1 classes (Teichmüller residues 1+1−1, 0+0+1, 1+i−i).  For large j it is periodic in j with period ≤ 2, and it alternates only in `(x−1)(x²+1)` with `x²+1` inert at 3, where cubing swaps ±i.

**Paired-root lemma.**  Let p ≡ 1 (mod 3) with p ∤ D·N(β), and suppose f has type (1)(2) mod p: a root r ∈ 𝔽_p and a conjugate pair ρ, ρ^p ∈ 𝔽_(p²).  If `N(β)` is a cube mod p, then `v ≤ s − 1`.  Hence at `p = T_j` with `c_j = 1`, the prime p recurs, and `T_(j+J)` is composite.

*Proof.*
1. The projective group `(𝔽_p × 𝔽_(p²))^× / 𝔽_p^×` is isomorphic to `𝔽_(p²)^×` via `(r, ρ) ↦ ρ/r`.
2. Since 3 ∤ p + 1, the 3-part of z ∈ `𝔽_(p²)^×` has the same order as the 3-part of `N(z) = z^(p+1)`.
3. Here `N(ρ/r) = ρρ^p / r² = N(β)/r³`, which is a cube in 𝔽_p^×, so its 3-part has order at most `3^(s−1)`. ∎

In words: a Frobenius-conjugate pair of roots has a single cube class, because `ρ^p = ρ · ρ^(p−1)` and p ≡ 1 (mod 3).  The norm relation then forces the third root into the same class.  This is the "all three cube classes equal" pattern of the split case, but here it is forced.

**Consequence.**  For unit β, and for any β whose norm is ± a cube, at every large j with `c_j = 1` the prime `T_j` must split completely: inert is excluded by the projective lemma, and (1)(2) by this lemma.  So `(D / T_j) = +1`.  The τ = −1 Jacobi certificate (§3) therefore extends to these τ = +1 cubics: one value with `(D/·) ∈ {0, −1}` on the eventual cycle of `(T_j mod |D|, j mod 2)` at the c = 1 parities kills f.

**Numerics** (`scripts/mills-residual-probe.py {pair-control|tau-plus|hard-core}`):

- **`pair-control`** (all classes, `|c₂|, |c₁| ≤ 30`, unit, j = 1, 2, `p < 10⁷`): for every (1)(2) prime `T_j` with `s = j + 1`, **48 of 48** have `v ≤ j`.  In each, `p | T_(j+J)` with `J = ord_L(3)` was confirmed by a direct matrix power mod p, an independent route.  **Control:** for (1)(2) primes with `s ≥ j + 2`, only 6 of 24 have `v ≤ j`.
- **`tau-plus`** (totally real S3, τ = +1, `|c₂|, |c₁| ≤ 30`, `|c₀| ≤ 10`): c ≥ 2 at both parities in 166/1565 of `(x−1)(x²+1)`, 462/1402 of `(x−1)²(x+1)`, and 408/1370 of `x²(x−1)`.
  - In `(x−1)²(x+1)` (units, box 40), c ≥ 2 ⟺ `f(−1) ≡ 0 (mod 9)`, exactly, in 676 of 676 cases.  That is, the 3-adic root near −1 is a 3-adic cube.  A heuristic expansion agrees: `T_j − 1 ≈ −2·3^j log(−γ₃)`.
  - In `(x−1)(x²+1)`, `f(1) ≡ 0 (mod 9)` is necessary but not sufficient.
  - The filter on unit c = 1 cubics, on its own, kills **254/256** of `(x−1)(x²+1)` and **182/186** of `(x−1)²(x+1)`.  After covering at q ≤ 13 nothing survives.  `x²(x−1)` has no units (3 | c₀), so the lemma applies there only when `−c₀` is ± a cube.
- **`hard-core 60 1 4 2`** asks whether anything is forced at c ≥ 2.  It takes unit cubics with `c_j ≥ 2` and primes `T_j` with j ≤ 4, and compares each with 3 random primes having the same s and the same splitting type.
  - (1)(2) with `s − j = 2`: the root r is a non-cube (d = 1, no recurrence) in 30/46.  The control gives 28/46, and the heuristic is 2/3.
  - Split: the cube-class patterns match the control row by row.
  - **Nothing is forced:** the trace relation `x₁ + x₂ + x₃ ≡ 0` leaves the Kummer data at `T_j` looking random.

**What is left (the new hard core).**  τ = +1, K an S3 field, and either:
- (i) `c_j ≥ 2` at every parity (a congruence on f mod 9 or 27), or
- (ii) `N(β)` not a cube mod `T_j`.

In both cases the surviving local condition is a cubic residue symbol at the primes dividing `T_j`:
- (i): in the split case, the root ratios are not all `3^c`-th powers; in the (1)(2) case, r is not a `3^(c−1)`-th power.
- (ii): `(N(β) / T_j)₃ ≠ 1` whenever `(D/T_j) = −1`.

These are Frobenius conditions in `K(ζ₃, β^(1/3), β′^(1/3))`, which is non-abelian over ℚ.

**Why no reciprocity closes it.**
- β is a unit, so `K(ζ₃, β^(1/3))` is unramified outside 3.  The symbol at 𝔭 | p therefore depends on 𝔭's ray class mod `3^a`.
- `p ≡ 1 (mod 3^(j+c))` pins only the norm of that class, which is the cyclotomic part.
- The only other datum is `Tr β^(3^j) = p`.  That says nothing about any individual 𝔭, and no generator of 𝔭 is known.
- 3-adic data alone forces the symbol only if β is a local cube at *every* place above 3.  When 3 ∤ h(K(ζ₃)), that makes β a global cube, so after re-indexing to a primitive base it never happens.
- Partial local cube-ness (case (i)) is exactly what fails to determine the symbol, and the numerics confirm it.

**Difficulty check.**  Like Lemma K, the paired-root lemma holds for every eventually-prime trace sequence (S1), so it burns down density and does not separate Mills.  Confidence: lemma correct 97%.  Novelty: the "Frobenius pair shares a cube class" step is elementary; I know of no source applying it to Mills (60%).

Lean: not planted.  It is a natural phase-60 sibling (`𝔽_(p²)` norm plus the projective identification) if wanted.
