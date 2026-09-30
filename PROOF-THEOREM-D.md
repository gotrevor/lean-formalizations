# Theorem D — Saito's Problem 1.7 for `R(n) = c^n + s` (proof write-up, draft 2)

Ren, 2026-09-30.  Status: **paper proof, not yet in Lean; not yet refereed by anyone.**  The numerics are in `ROADMAP-PRIME-TOWERS.md` §1 (Theorem D) and `scripts/saito-17-shift-probe.py`.

**Problem** (K. Saito, arXiv:2504.14968, Problem 1.7):

> Find a non-reversible ILRS `(R(n))` such that for every Pisot number `α`, especially of degree 3, the numbers `⌊α^(R(n))⌋` are composite for infinitely many `n`.

**Theorem D.**  Let `c` be a prime, `d ≥ 1`, and `s ≥ s₀(d) := ⌈log(d + 1)/log κ⌉`, where `κ ≈ 1.3247` is the smallest Pisot number.  Put `R(n) = c^n + s`; this is an ILRS of order 1, `R(n+1) = c R(n) − (c − 1)s`, and non-reversible since `a₀ = c`.  Let `α` be a Pisot number of degree `d` with minimal polynomial `f`, and assume:
- **(ii)** `f ≢ X^d (mod c)`.

*(Draft 1 also assumed **(i)** `f` irreducible over `ℚ(ζ_M)`.  Draft 2 removes it: step 3–5 below replace Galois rigidity by a direct size argument after one automorphism.  Lemma 6 is no longer used in Theorem D; it is kept for Theorem E, where the shift is negative and size alone fails.)*

Then `⌊α^(R(n))⌋` is composite for infinitely many `n`.

**Complement (Proposition D′).**  If `f ≡ X^d (mod c)`, then `⌊α^N⌋ ≡ ε_N (mod c^(e(N)))` with `e(N) → ∞`, where `ε_N ∈ {0, −1}` is the floor offset.
- If `ε_N = 0` infinitely often along `N = R(n)`, those values are divisible by `c`, hence composite.
- If `ε_N = −1` for all large `n`, every value is `≡ −1` to growing `c`-adic precision, so it lies in every window of the prime-as-modulus filter, which then gives no information.  Example: `α = 2 + √2`, `c = 2`.
- For any non-reversible ILRS, taking `f = X² − MX + N` with `rad(a₀) ∣ M, N`, `0 < N < M − 1` and both conjugates in `(0, 1)` produces such an `α`.  **So Problem 1.7 in full cannot be settled by this method alone.**

---

## Notation
- `C` is the companion matrix of `f`, `α = α_1, α_2, …, α_d` are the roots of `f` in `ℂ` (Pisot: `|α_j| < 1` for `j ≥ 2`), and `K = ℚ(α_1, …, α_d)`.
- `C^N = Σ_k α_k^N E_k` with rank-one spectral projectors `E_k ∈ M_d(K)` (the roots are distinct because `f` is irreducible), so `tr(E_k C^s) = α_k^s`.
- Fix an embedding `ι : ℚ̄ → ℚ̄_c`.  For a `c`-adic unit `u` of a finite extension of `ℚ_c`, `ω(u)` is its Teichmüller representative and `⟨u⟩ = u/ω(u) ∈ 1 + 𝔪`.  Set `ω(u) = 0` for non-units.

## Lemma 1 (floor = trace + offset)
`⌊α^N⌋ = tr C^N + ε_N` with `ε_N ∈ {0, −1}`, for all `N` with `|δ_N| < 1`, where `δ_N = Σ_(j≥2) α_j^N`.  Since `δ_N → 0` this holds for all large `N`; `ε_N = −1` iff `δ_N > 0`.  (`δ_N ≠ 0` for large `N` unless there is a degenerate cancellation; if `δ_N = 0`, the value `α^N` is an integer.  Handle it separately or note that `ε_N = 0` then.)

## Lemma 2 (filter with a varying offset)
Let `p = ⌊α^(R(n))⌋` be prime with `p ∤ det C`, and let `ord_p(C) = c^a · o` with `c ∤ o`.  If `a ≤ n`, put `j = ord_o(c)`.  Then for all `k ≥ 1`, `C^(R(n+kj)) ≡ C^(R(n)) (mod p)`, so
`⌊α^(R(n+kj))⌋ ≡ ε_(R(n+kj)) − ε_(R(n)) (mod p)`.
*Proof.*  `R(n+kj) − R(n) = c^n (c^(kj) − 1)` is divisible by `c^a` (as `a ≤ n`) and by `o` (as `c^j ≡ 1 mod o`), hence by `ord_p(C)`.  Take traces and apply Lemma 1.  ∎

**Consequence.**  Suppose every `p_n = ⌊α^(R(n))⌋` is prime for `n ≥ n₀`.  Call `n` *good* if `v_c(ord_(p_n) C) > n`, and *stuck* otherwise.  For stuck `n`, Lemma 2 plus the growth `p_(n+kj) > p_n` force `ε_(R(n+kj)) ≠ ε_(R(n))` for every `k ≥ 1`; otherwise `p_n` would divide a larger prime.

## Lemma 3 (stuck indices are isolated; purely combinatorial)
If `n` is stuck with period `j`, then `n′ = n + j` is not stuck.
*Proof.*  Suppose `n′` is stuck with period `j′`.  Then:
- stuck at `n` with `k = 1` gives `ε(n′) = ε̄(n)`, where `ε̄` is the other value;
- stuck at `n′` with `k = j` gives `ε(n′ + j j′) = ε̄(n′) = ε(n)`;
- but `n′ + j j′ = n + j(1 + j′)`, so stuck at `n` with `k = 1 + j′` gives `ε(n′ + j j′) = ε̄(n)`.

Contradiction.  ∎

Hence **good indices occur infinitely often**, whatever the conjugates are (real, complex, or mixed).

## Lemma 4 (the window)
If `n` is good, there are `i ≤ d` and `ω_n ∈ W := μ_(gcd(d!, c−1))` (for `c = 2`: `W = {±1}`) with `p_n ≡ ω_n (mod c^(e_n))`, where `e_n ≥ ⌈n/d⌉ − v_c(d!) − 1 → ∞`.
*Proof.*  `ord_p(C)` divides `|GL_d(𝔽_p)| = p^(d(d−1)/2) ∏_(i≤d)(p^i − 1)`.  Since `p ≠ c`, `Σ_i v_c(p^i − 1) > n`, so some `i ≤ d` has `v_c(p^i − 1) > n/d`.  Write `p = ω(p)⟨p⟩`.  Then `ω(p)^i = 1` and `⟨p⟩^i ≡ 1 (mod c^(n/d))`, hence `⟨p⟩ ≡ 1 (mod c^(n/d − v_c(i)))` (for `c = 2`, lose one more power).  ∎

## Lemma 5 (the limit points)
Let `f_k` be the residue degree of `ι(α_k)` over `ℚ_c`, `D = lcm f_k`, and `M` the lcm of the orders of the roots of unity `ω(ι α_k)` together with `|W|`.  For each residue class `r (mod D)`,
`λ_r := lim_(n ≡ r (mod D)) tr C^(R(n)) = Σ_k ω(ι α_k)^(c^r) · ι(α_k)^s   (in ℚ̄_c)`.
*Proof.*  `ι(α_k)^(c^n) = ω^(c^n) ⟨·⟩^(c^n)`.  The factor `⟨·⟩^(c^n) → 1` in any finite extension, ramified or not: if `⟨u⟩ = 1 + x` with `v(x) > 0`, the binomial expansion shows `v((1 + x)^(c^n) − 1) → ∞`.  And `ω^(c^n)` depends only on `n mod f_k`.  Non-units contribute `→ 0`.  Then use `tr C^(c^n + s) = Σ_k α_k^(c^n) α_k^s`.  ∎

Pull back: `Λ_r := ι⁻¹(λ_r) = Σ_k ζ_k^(c^r) α_k^s ∈ K(ζ_M)`, where `ζ_k := ι⁻¹(ω(ι α_k))` is a root of unity or `0`.

## Lemma 6 (Galois rigidity)
Let `G = Gal(K(ζ_M)/ℚ(ζ_M))`.  By (i) it acts transitively on the roots and fixes every `ζ_k`.  Suppose `Σ_k z_k α_(σ(k))^s = t` for all `σ ∈ G`, with `z_k, t ∈ ℚ(ζ_M)` and `T := tr C^s ≠ 0`.  If `α^s > d − 1`, then `z_k = t/T` for all `k`.
*Proof.*  `z° := (t/T)·𝟙` is a solution, because `Σ_k α_(σk)^s = T`.  Let `η = z − z°`, so `Σ_k η_k α_(σk)^s = 0` for all `σ`.  Fix a complex embedding.  Pick `k₀` maximizing `|η_k|`, and `σ ∈ G` with `σ(k₀) = 1` (transitivity).  Then
`|η_(k₀)| α^s ≤ Σ_(k≠k₀) |η_k| |α_(σk)|^s ≤ |η_(k₀)| Σ_(j≥2) |α_j|^s < |η_(k₀)| (d − 1)`.
So `η_(k₀) = 0`, hence `η = 0`.  (The Pisot property concerns the root set, so any complex embedding works.)  ∎

*Remark.*  For `d ≤ 3`, dominance is unnecessary.  `S₃` acts on `ℂ³` as `𝟙 ⊕ std`, and `(α_k^s)` has nonzero sum and is non-constant.  In the `C₃` case the circulant has eigenvalues `Σ_j α_j^s ω^(jm) ≠ 0`.  So negative shifts `s < 0` also work in degree 3 (used for Theorem E).

## Proof of Theorem D
1. Assume every `p_n` is prime for `n ≥ n₀`.  Lemma 3 gives infinitely many good `n`; choose a residue class `r (mod D)`, an `ω ∈ W` and an `ε ∈ {0, −1}` such that infinitely many good `n ≡ r` have `ω_n = ω` and `ε_(R(n)) = ε`.
2. By Lemma 4, `tr C^(R(n)) + ε ≡ ω (mod c^(e_n))` along that subsequence.  By Lemma 5, `λ_r + ε = ω` in `ℤ_c`.  Pull back: `Λ_r = t := ι⁻¹(ω) − ε ∈ ℚ(ζ_M)`, with `|t| ≤ 2` in every complex embedding.
3. **(Draft 2.)**  `f ≢ X^d (mod c)`, so some root is a `c`-adic unit under `ι`: choose `k*` with `ζ_(k*) ≠ 0`.  Let `N` be the Galois closure of `K(ζ_M)` over `ℚ`.  `f` is irreducible over `ℚ`, so some `τ ∈ Gal(N/ℚ)` has `τ(α_(k*)) = α_1 = α`.  Apply `τ` to `Λ_r = t`:
   `Σ_k τ(ζ_k)^(c^r) · α_(π(k))^s = τ(t)`, where `π` is the permutation that `τ` induces on the roots.
   - Each `τ(ζ_k)` is a root of unity or `0`, and `τ(ζ_(k*)) ≠ 0`.
   - `τ(t) = τ(ι⁻¹ω) − ε` has modulus `≤ 2` in every complex embedding.
4. Fix the complex embedding in which `α_1 = α > 1` and `|α_j| < 1` for `j ≥ 2`.  Isolate the `k*` term:
   `α^s = |τ(ζ_(k*))^(c^r) α^s| ≤ |τ(t)| + Σ_(k≠k*) |α_(π(k))|^s < 2 + (d − 1) = d + 1`.
5. But `s ≥ s₀(d)` gives `α^s ≥ κ^s ≥ d + 1`.  **Contradiction.**  (`d = 1` is trivial: `⌊α^N⌋ = α^N` is composite.)  ∎
   - **Referee (2026-09-30, subagent): no error, ~90%.**  Hypothesis (i) was used only by Lemma 6.  Lemmas 1–5 need only irreducibility over `ℚ`, for distinct roots.
   - No Galois rigidity and no hypothesis on `ℚ(ζ_M)` are needed.  The abelian exception fields of draft 1 (conductor 7 at `c = 2`; conductor 13 at `c = 3`; e.g. `c = 7` with conductor 19, where 7 splits) are covered.
   - *(Draft 1's steps 3–5 used Lemma 6 to force all `ζ_k^(c^r)` equal, then `|t| = |T| > 2`.  That is correct under (i), but it is a detour.)*

## Proof of Proposition D′
If `f ≡ X^d (mod c)`, every `ι(α_k)` is a non-unit, so `tr C^N ≡ 0 (mod c^(e′(N)))` with `e′ → ∞`.  (Non-unit powers go to 0; their integer sum has growing valuation.)  Then `⌊α^N⌋ = tr C^N + ε_N` gives both claims.

For the "any ILRS" remark: `f = X² − MX + N` with `M, N ≡ 0 (mod rad a₀)` and `0 < N < M − 1`, with real conjugates in `(0, 1)`.  Then `α` is Pisot, `ε ≡ −1`, and the value is `≡ −1` modulo growing powers of every prime of `a₀`.  The method needs a prime of `a₀` to act as the base; each such prime sees the value in its window.  ∎

## Corollary (prime-free intervals, draft 2)
Survival of the shift `h` means `Λ_r = ζ′ − h − ε` for some root of unity `ζ′`, so `|τ(·)| ≤ |h| + 2`, and step 4 gives `α^s < d + |h| + 1`.
- So **for `s ≥ ⌈log(d + H + 1)/log κ⌉`, no `h` with `|h| ≤ H` survives**, for every Pisot `α` with `f ≢ X^d (mod c)`.  This also removes the unipotent classes `(X ∓ 1)^d`, whose survivor `h` has `|h| ≥ α^s − d − 1 > H`.
- The statement is "half-width `H` once `s ≥ s₀(d, H)`", not "every length at a fixed `s`": at a fixed `s` the bound is `H < α^s − d − 1`.
- This assumes the phase-41 engine's only input is `Λ_r ∉ {ζ′ − h − ε}` for every `r`, `ε`, `ζ′`, which the referee did not check against the Lean.

## Open points
1. ~~Remove (i).~~  **Done in draft 2** (2026-09-30) by the one-automorphism size argument.  This matches the numerics, which found no survivors in the abelian exception fields.
2. **`δ_N = 0` degenerate case** in Lemma 1 (only if some power `α^N` is an integer).  For Pisot `α` of degree ≥ 2 this never happens: `α^N ∈ ℤ` would make the conjugates `α_j^N = α^N` of modulus `> 1`.  So it is fine; record this in the paper.
3. **Uniform `s₀`.**  `⌈log(d + 1)/log κ⌉` (Siegel).  Numerics show `s ≥ 2` already suffices for `d ≤ 4` at `c ∈ {2, 3, 5, 7}`.
4. **Freshness before any outward use:** re-run `papers followups 2504.14968` and search for "Problem 1.7" solutions.
