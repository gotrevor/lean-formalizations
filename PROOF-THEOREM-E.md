# Theorem E — transcendence of `ξ(3^k − 2)` outside explicit classes (proof write-up, draft 1)

Ren, 2026-09-30.  Status: **paper proof, not in Lean, unrefereed.**  It builds on `PROOF-THEOREM-D.md` (Lemmas 1–6) and Saito, arXiv:2508.16068, Theorem 2.6.

`ξ(C_k)` is the least `A > 1` with `⌊A^(C_k)⌋` prime for every `k ≥ 1` (Saito's notation).

**Theorem E.**  `ξ := ξ(3^k − 2)` exists.  It is transcendental unless it is a cubic Pisot number with minimal polynomial `f` in one of:
- **E1.** `ℚ(ξ)` is the cyclic cubic field of conductor 13;
- **E2.** `f ≡ (X ∓ 1)³ (mod 3)` and `tr(ξ^(−2)) ∈ {0, ±1, ±2}`, with the floor offset `ε = −1` along the tower if `tr(ξ^(−2)) = 0`;
- **E3.** `f ≡ X³ (mod 3)` and `ε_(3^k − 2) = −1` for all large `k`.

Moreover:
- E2 with `tr(ξ^(−2)) ≠ 0` is impossible for totally real `ξ`, since `ξ^(−2) + β₂^(−2) + β₃^(−2) > 2`.
- E3 for totally real `ξ` requires the dominant conjugate `β₂` to be positive.

## Step 1: Saito's Type C applies
Saito's Theorem 2.6 (with `c = 3`; hypothesis `(2.2)` holds unconditionally by Mossinghoff–Trudgian–Yang) needs:
- `(C1)` `c₁ = C₁ = 1 ≥ 1` ✓.
- `(C2)` `c_(k+1) = (3^(k+1) − 2)/(3^k − 2) = 3 + 4/(3^k − 2) ≥ 3` ✓.
- `(C3)` `C_k ∈ ℕ` ✓.  (Real ratios `c_k` are allowed.)
- `(C4)` `gcd(3, C_m) = 1`, so `3^(φ(C_m)) ≡ 1 (mod C_m)` and `C_(m+φ(C_m)) = 3^m·3^(φ(C_m)) − 2 ≡ 3^m − 2 ≡ 0` ✓.
- `(C5)` `gcd(C_m, C_(m+1)) ∣ 3C_m − C_(m+1) = 4`, and every `C_m` is odd, so `agcd = 1` ✓.

Conclusion (Saito, §9, via Type B): `ξ` exists, and either `ξ` is transcendental or `ξ^g` is a cubic Pisot number with `g ∣ agcd = 1`.  So `ξ` itself is a cubic Pisot number with `⌊ξ^(3^k − 2)⌋` prime for all `k ≥ 1`.  (Type B already excludes degree 2.)

## Step 2: Theorem D's machinery with the negative shift `s = −2`
Put `R(n) = 3^n − 2`.  Lemmas 1–5 of `PROOF-THEOREM-D.md` hold verbatim.
- Lemma 2 uses `R(n+kj) − R(n) = 3^n(3^(kj) − 1)`.
- Lemma 5 gives `λ_r = Σ_k ω(ι α_k)^(3^r) ι(α_k)^(−2)` over the unit roots.  Non-units contribute 0 because `α^(3^n − 2) → 0` `3`-adically for a non-unit `α`.

So, assuming every value is prime, some residue class has `Λ_r = Σ_k ζ_k^(3^r) α_k^(−2) = t` with `t = ω − ε`, `ω ∈ {±1}` (the window at `c = 3` is `μ₂`) and `|t| ≤ 2`.

## Step 3: Galois rigidity in degree 3 (no Pisot dominance needed)
Let `G = Gal(K(ζ_M)/ℚ(ζ_M))`.  It is transitive on the three roots unless `ℚ(ξ) ⊂ ℚ(ζ_M)` (that is **E1**; `M ∣ lcm(26, 8)`, so the only abelian cubic field inside is the one of conductor 13).  Then `Σ_k z_k w_(σk) = t` for all `σ ∈ G`, with `w_k = α_k^(−2)` and `z_k = ζ_k^(3^r)`.
- **Sum over `σ`:** `(|G|/3)·T·Σ_k z_k = |G| t`, where `T = Σ_k w_k = tr(ξ^(−2)) ∈ ℚ`.
- **Rank.**  `G ∈ {S₃, C₃}` acting on `ℂ³`.  The span of `{σw}` contains the "standard" part because `w` is non-constant (the `|α_k|` are distinct: one exceeds 1, and the other two are `< 1` and different, or a complex pair whose `w`-values are conjugate but not equal to the real one).
  - For `S₃` the span is `std ⊕ (𝟙 if T ≠ 0)`.
  - For `C₃` the circulant eigenvalues `Σ_j w_j ω^(jm)` (`m = 1, 2`) are nonzero because `w_1 ≠ w_2 ≠ w_3` are not all equal and are real, or pair up under complex conjugation; to double-check in the cyclic, totally real case: `x + ωy + ω²z = 0` with real `x, y, z` forces `x = y = z`.
- **Conclusion:** `z_k` is constant, `z_k = z`, with `zT = t`.

## Step 4: the cases
- `z = 0`: every root is a non-unit at 3, i.e. `f ≡ X³ (mod 3)`.  Then `λ = 0`, so `t = 0`, `ω = ε`, and hence `ε = ω = −1` (as `ε ∈ {0, −1}` and `ω ∈ {±1}`).  Along the whole tower (not just good `n`), `⌊ξ^N⌋ ≡ ε_N` modulo growing powers of 3, so `ε_N = 0` makes the value divisible by 3.  Survival therefore needs `ε = −1` eventually always: **E3**.
- `z = ±1` and `T ≠ 0`: `t = zT` with `|t| ≤ 2`, so `T ∈ {±1, ±2}` (and `T ∈ ℚ` forces `t` rational).  All unit roots have Teichmüller `z`, i.e. `f ≡ (X − z)³ (mod 3)`: **E2**.
- `z = ±1` and `T = 0`: `t = 0`, so `ω = ε = −1`, and `f ≡ (X − z)³ (mod 3)` with value `≡ −1`: **E2** (`T = 0` subcase).
- Totally real `ξ` with `T ∈ {±1, ±2}` is impossible: `T = ξ^(−2) + β₂^(−2) + β₃^(−2) > 0 + 1 + 1`.
- E3 totally real: `ε_N = −1 ⟺ β₂^N + β₃^N > 0`; with `N = 3^n − 2` odd, this needs the dominant conjugate `β₂ > 0`.  ∎

## Step 5: minimality of `ξ` kills E3 and shrinks E2
`ξ` is the *least* element of `W(C_k)`.

**Claim: `ε_(C_k) = 0` for all large `k`**, i.e. the fractional part of `ξ^(C_k)` is `< p_k^(−0.425)`.
- *Room for a smaller constant.*  Let `k` be large (`p_k^(c_(k+1)) ≥ x₀`), and let `q` be the least prime `≥ y := p_k^(c_(k+1))`.  By Baker–Harman–Pintz, `q ≤ y + y^(0.525)` for large `y`.
- *The chain continues from `q`.*  Iterate `(2.2)` (Saito's Lemma 9.1 argument, valid for `x ≥ x₀`).  This gives `A′ ∈ W(C_k)` with `⌊A′^(C_i)⌋ = p_i` for `i ≤ k` and `⌊A′^(C_(k+1))⌋ = q`.
  - The earlier constraints hold because `A′^(C_k) ∈ [q^(1/c), (q+1)^(1/c)) ⊂ [p_k, p_k + 1)`, and `p_k ≥ p_i^(C_k/C_i)` along any valid chain, while `A′ < ξ < (p_i + 1)^(1/C_i)`.
- *Minimality.*  So `p_(k+1) ≤ q`, i.e. `ξ^(C_(k+1)) < q + 1 ≤ y + y^(0.525) + 1`.
- *Conclusion.*  Writing `ξ^(C_k) = p_k + φ_k`, we get `(p_k + φ_k)^(c_(k+1)) < p_k^(c_(k+1)) + y^(0.525) + 1`, which forces `φ_k ≪ p_k^(1 − 0.525·c_(k+1)) = p_k^(−0.575 + o(1))` (with `c_(k+1) → 3`).  In particular `φ_k` is small, so `ξ^(C_k)` sits just **above** `p_k`: `ε_(C_k) = 0` (`ξ^N = tr − δ_N` with `−1 < δ_N < 0`).  ∎

**Consequences.**
- **E3 is impossible** (Step 4 showed E3 needs `ε = −1` eventually always).
- **E2 with `T = 0` is impossible** (it needs `ε = −1`).
- **E2 with `T = ±2` is impossible** (`t = zT = ω − ε` with `|t| = 2` needs `ε = −1`).
- What remains of E2: `T = tr(ξ^(−2)) = ±1`, `ξ` complex, and `δ_(C_k) = 2r^(C_k) cos(C_k θ) < 0` for **all** large `k`, with `r = |β₂| < ξ^(−0.575 + o(1))`.  That is a trapped orbit of `x ↦ 3x + 4θ/2π (mod 1)` in a half-circle plus a size condition.

**Refined Theorem E.**  `ξ(3^k − 2)` is transcendental unless `ξ` is a complex cubic Pisot number with `f ≡ (X ∓ 1)³ (mod 3)`, `tr(ξ^(−2)) = ±1`, conjugate modulus `< ξ^(−0.575)`, and argument `θ` with `cos((3^k − 2)θ) < 0` for all large `k`; or `ξ` lies in the conductor-13 cyclic cubic field (E1, probably removable).  Unconditional (BHP + MTY24).

This parallels Saito's Theorem 1.7 for Mills (a size window `(1.3)` on a totally real cubic).  Here the survivor must be **complex**, sit in two residue classes mod 3, satisfy a trace equation, **and** have a trapped rotation orbit.

## Numerics
All 867 irreducible cubic Pisot `f` with coefficients in `[−9, 9]`, `c = 3`, `R = 3^n − 2`, precision `3^10`, true offsets `ε_n` for `n = 4..15`.
- 41 pass the window test; 37 are killed by `ε = 0 ⇒ 3 ∣ value`.
- The 4 survivors are all **E3** with a positive dominant conjugate: `x³ − 9x² + 3`, `x³ − 9x² + 6`, `x³ − 9x² + 3x + 3`, `x³ − 6x² + 3`.
- The one E2-type window hit, `(−9, −6, −2)` (`T = 0`, complex), is killed by `ε`.

## Comparison with Saito
- Saito's Theorem 1.9(C) settles `ξ(r·3^k − 1)` completely, but only for `r ≥ 4.003·10¹⁴`, and his Type C argument uses size only.
- Theorem E handles a small first term (`C₁ = 1`), where size says nothing, arithmetically.  In exchange it leaves congruence-defined exceptions.
- The same template gives `ξ(r·3^k − 1)` for every `r ≥ 1` (shift `s = −1`, `T = σ₂/σ₃`), with the analogous E1–E3.
- **E3 is Mersenne-shaped and, by Proposition D′, invisible to the prime-as-modulus method.**

## Open points
1. The `C₃`-case rank claim when two `w`-values coincide in modulus (the complex pair has `w₂ = w̄₃`, which is not equal to `w₁` since `|w₁| < 1 < |w₂|`).  Written above; to double-check.
2. E1 removal (decomposition group).
3. ~~Can E3 be excluded using minimality?~~  **Yes, Step 5.**
4. Can the trapped-orbit condition be excluded for algebraic `θ`?  It is a Mahler-type `3^k θ (mod 2π)` question, open in general.  Combining it with `tr(ξ^(−2)) = ±1` and the mod-3 class might leave a finite search: bounded `|β₂|`, `ξ` bounded via the `T` equation?  **Worth a probe.**
