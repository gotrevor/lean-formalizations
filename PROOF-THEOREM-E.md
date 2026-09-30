# Theorem E — the shifted Mills constant `ξ(3^k − 2)` is transcendental (proof write-up, draft 2)

Ren, 2026-09-30.  **Status: paper proof, not in Lean.**  Draft 2 incorporates an adversarial referee pass (a subagent, same night).  The referee found no fatal error and about 80% confidence after three patches, all applied below: Step 5 now cites Saito's Prop 3.1(iv), Step 3's `C₃` rank argument is completed, and the `b = 0` case of the E1 certificate is covered.

It builds on `PROOF-THEOREM-D.md` (Lemmas 1–6) and Saito, arXiv:2508.16068 (itself unrefereed; its Theorem 2.3/2.6 and Prop 3.1 are load-bearing here).

`ξ(C_k)` is the least `A > 1` with `⌊A^(C_k)⌋` prime for every `k ≥ 1` (Saito's notation; it exists by his Lemma 4.1 and Theorem 1.3).

> **Theorem E.**  `ξ := ξ(3^k − 2)` is transcendental.  Unconditional: it uses Baker–Harman–Pintz via Saito's Prop 3.1, and the Mossinghoff–Trudgian–Yang short-interval theorem only through Saito's existence/size lemma.

Saito's own Type C theorem kills the Pisot branch by **size only**, which is why his Theorem 1.9(C) for `ξ(r·3^k − 1)` needs `r ≥ 4.003·10¹⁴`.  Here the first term is `C₁ = 1`, where size says nothing; the Pisot branch is killed **arithmetically**.  The same proof gives `ξ(r·3^k − 1)` for every even `r ≥ 2` (see the end).

## Step 1: reduction to a cubic Pisot number (Saito, Theorem 2.6 / 2.3)
`C_k = 3^k − 2` satisfies:
- `(C1)` `C₁ = 1`.
- `(C2)` `c_(k+1) = 3 + 4/(3^k − 2) ≥ 3`.
- `(C3)` `C_k ∈ ℕ`; real ratios are allowed.
- `(C4)` `gcd(3, C_m) = 1`, so `C_m ∣ C_(m + φ(C_m))`.
- `(C5)` `gcd(C_m, C_(m+1)) ∣ 3C_m − C_(m+1) = −4`, and every `C_m` is odd, so `agcd = 1`.

By Theorem 2.6, **`ξ` is transcendental, or `ξ` itself (`g = 1`) is a cubic Pisot number** with `⌊ξ^(3^k − 2)⌋` prime for all `k`.  The dichotomy comes from Theorem 2.3 (Type B); degree 2 is excluded there.  Assume the latter for contradiction; let `f = X³ − σ₁X² + σ₂X − σ₃` be its minimal polynomial and `C` the companion matrix.

## Step 2: `ε = 0` eventually (Saito, Prop 3.1(iv))
Apply Prop 3.1 with `θ = 21/40` (BHP satisfies `(†)`).
- `(G1)`, `(G2)`, `(G4)` are clear; `(G3)`: `lim sup c_(k+1) = 3 > 1/(1 − θ) = 40/19`.
- `(3.1)`: `ξ^(C_m) ∉ ℕ`, since a power of a cubic Pisot number is cubic Pisot, not an integer.
- `I = {k : c_(k+1) ≥ 40/19 + ε} = ℕ`.
- Then (iv) gives `Tr(ξ^(C_k)) = ⌊ξ^(C_k)⌋` for all large `k`, i.e. **the floor offset is `ε_(C_k) = 0` eventually.**

*(Draft 1 proved this by an explicit minimality construction.  The referee found a gap: it used `p_k ≥ p_i^(C_k/C_i)`, which needs integer ratios.  Prop 3.1(iv) is the correct citation; its (i) also gives the fractional-part bound `{ξ^(C_k)} ≪ p_k^(−0.425)`.)*

## Step 3: the filter, with every large `n` good
Put `R(n) = 3^n − 2`, and write `p_n = ⌊ξ^(R(n))⌋`, which equals `tr C^(R(n))` for large `n` by Step 2.
- Lemma 2 of `PROOF-THEOREM-D.md`: if `v₃(ord_(p_n) C) ≤ n`, then `p_n ∣ p_(n+kj)` for all `k ≥ 1`.  Since `ε` is now constant there are no flips, so this contradicts primality.
- Hence **every** large `n` is good: `v₃(ord_(p_n) C) > n`.  (The stuck-index Lemma 3 is not needed.)
- Lemma 4: `p_n ≡ ω_n ∈ {±1} (mod 3^(e_n))` with `e_n → ∞` (the window at `c = 3, d = 3` is `μ₂`).
- Lemma 5: along a residue class `r (mod D)` with constant `ω`, `Λ_r := Σ_k ζ_k^(3^r) α_k^(−2) = ω ∈ {±1}`.  Here `ζ_k = ι⁻¹ ω(ι α_k)` (or `0` for non-units); non-units contribute `α^(3^n − 2) → 0`.

## Step 4: Galois rigidity (degree 3, no dominance needed)
Let `M` be the lcm of the Teichmüller orders and `|W| = 2`, so `M ∣ lcm(2, 8, 26) = 104`.  Suppose `ℚ(ξ) ⊄ ℚ(ζ_M)`.  Then `f` stays irreducible over `ℚ(ζ_M)`, and `G = Gal(K(ζ_M)/ℚ(ζ_M))` acts transitively on the roots while fixing each `ζ_k`.  Put `w_k = α_k^(−2)` and `z_k = ζ_k^(3^r)`; then `Σ_k z_k w_(σ(k)) = ω` for all `σ ∈ G`.
- **Sum over `σ`:** `(|G|/3)·T·Σ_k z_k = |G|·ω`, where `T = Σ_k w_k = tr(ξ^(−2)) = (σ₂² − 2σ₁σ₃)/σ₃² ∈ ℚ`.  So `T ≠ 0`.
- **`G ≅ S₃`:** `ℂ³ = 𝟙 ⊕ std`, and `w` is non-constant (`|w₁| < 1 < |w₂|, |w₃|`) with sum `T ≠ 0`, so the `G`-orbit of `w` spans `ℂ³` and the solution is unique: `z_k = ω/T` for all `k`.
- **`G ≅ C₃`:** the equations form a circulant system with eigenvalues `ŵ(0) = T` and `ŵ(m) = Σ_j w_j ζ₃^(jm)` (`m = 1, 2`).
  - If `ξ` is totally real, the `w_j` are real, not all equal, so `ŵ(1), ŵ(2) ≠ 0`.
  - If `ξ` is complex (`w₂ = w̄₃`), `ŵ(1)` could a priori vanish.  `G ≅ C₃` happens here when the `S₃` field's quadratic resolvent `ℚ(√disc)` lies in `ℚ(ζ_M)`.  (*Referee patch*, made precise.)
    - `ζ₃ ∉ K(ζ_M)`: `3 ∤ 104`, so `√−3 ∉ ℚ(ζ_M)`, and `K(ζ_M)/ℚ(ζ_M)` is cubic, so it cannot contain the quadratic `ℚ(ζ_M, √−3)`.
    - Hence some automorphism of `K(ζ_M, ζ₃)` fixes `K(ζ_M)`, and so each `w_j`, and sends `ζ₃ ↦ ζ₃²`.  It maps `ŵ(1) = 0` to `ŵ(2) = 0`.
    - Together with `ŵ(0) = T`, that makes `w` constant, which is impossible.
  - So the circulant is invertible and again `z_k = ω/T`.
- In all cases the `ζ_k^(3^r)` are equal to a common value `z`, with `zT = ω`.

## Step 5: the cases
- `z = 0`: all roots are non-units at 3, so `Λ_r = 0 ≠ ω`.  Impossible.
- `z ≠ 0`: `z` is a root of unity and `z = ω/T ∈ ℚ`, so `z = ±1` and `T = ±1`.  All roots then reduce to the same `z (mod 3)`, i.e. `f ≡ (X − z)³ ≡ X³ − z (mod 3)`: `σ₁ ≡ σ₂ ≡ 0`, `σ₃ ≡ z ≢ 0`.  Then `v₃(T) = v₃(σ₂² − 2σ₁σ₃) − 2v₃(σ₃) ≥ 1`, contradicting `T = ±1`.  (A repeated root `ζ̄` in `𝔽₃[X]` forces `ζ̄ ∈ 𝔽₃`, so no other `z` arises.)

## Step 6: the exceptional field `ℚ(ξ) ⊂ ℚ(ζ_M)` (E1) is empty
The only cubic subfield of `ℚ(ζ₁₀₄)` is `K`, the cyclic cubic field of conductor 13.  In it `3` is inert (3 has order 3 mod 13), `ℚ₃(ζ₁₃)` is unramified, and `ι ∘ τ₃ = Frob ∘ ι` on `ℚ(ζ₁₃)`.  Teichmüller commutes with Frobenius, which cubes `μ₂₆`, so with `α_k := τ_(3^k)(α)`:
`ζ_k = ζ₀^(3^k) = τ_(3^k)(ζ₀)` and `Λ_r = Tr_D(ζ₀^(3^r) · α^(−2))`, where `D = ⟨τ₃⟩ = {1, 3, 9}`.
- `ζ₀ = ±ζ₁₃^b` with `b ≠ 0`: `scripts/theorem-e-e1-certificate.py` shows that `K → ℚ(ζ₁₃)/ℚ`, `w ↦ Tr_D(ζ^b w)` has rank 3 for every `b = 1..12`.  So `Λ_r ∈ ℚ` forces `α^(−2) = 0`: impossible.
- `ζ₀ = ±1` (`b = 0`, i.e. `α ≡ ±1 (mod 3O_K)`; *referee patch*): the map is `Tr_(K/ℚ)`, always rational.  But then every `ζ_k = ζ₀`, so `z` is constant without any transitivity, and Step 5's congruence applies verbatim (`f ≡ (X ∓ 1)³`, `3 ∣ T`): contradiction.
- Non-unit `α` (inert, so every conjugate is a non-unit) is the `z = 0` case: contradiction.  ∎

## Theorem E+ (the whole shifted family; draft)
> **For every even `s ≠ 0` with `3 ∤ s`, `ξ(3^k + s)` is transcendental** (index `k` starting where `3^k + s ≥ 1`).  Unconditional, same caveats as Theorem E.

- **Reduction via Saito's Type B (Theorem 2.3), for both signs of `s`.**  `C_k = 3^k + s`.
  - `(B1)`–`(B4)`: ratios `c_(k+1) → 3`, all `≥ 2`, and `lim sup 3 > 40/19`.
  - `(B5)`: `gcd(3, C_m) = 1` (`3 ∤ s`), so `C_m ∣ C_(m + φ(C_m))`.
  - Conclusion: `ξ` is transcendental, or `ξ^g` is Pisot of degree `ℓ ∈ [3, 1 + 1/(57/40 − 1)] = [3, 3.35]`, so `ℓ = 3`, with `g ∣ C_k` for large `k`.  `agcd(3^k + s) = 1` for even `s` with `3 ∤ s` (it divides `gcd(C_m, C_(m+1)) ∣ 2s`, the `C_k` are odd, and no prime of `s` divides `3^m + s`; checked numerically for `|s| ≤ 16`), so `g = 1`.
  - Saito's `(B6)` (`C_k ≡ C_m mod L·C_m`) **fails** for these sequences: it is the non-reversibility.  That is exactly why his theorem stops at "cubic Pisot" here.
- **Step 2** (Prop 3.1(iv), same `(G)`-conditions): `ε = 0` eventually.
- **Steps 3–4** unchanged with shift `s` (for `s > 0`, `T = tr(ξ^s) > 0`; for `s < 0`, `T ≠ 0` is forced by the summed equation).  Rank: `w = (α_k^s)` is non-constant because the root moduli differ, so `S₃` and `C₃` both work as in Step 4.
- **Step 5, general `s ≠ 0`:** in the class `f ≡ (X − z)³ (mod 3)` every root (and its inverse) is `≡ z` modulo the prime above 3.  So `T = Σ α_k^s ≡ 3z^s ≡ 0`: `v₃(T) ≥ 1` (the denominator `σ₃^|s|` is prime to 3).  Hence `T ≠ ±1`.  No size input is needed.
- **Step 6:** the certificate is shift-independent (any `w ∈ K`), and `b = 0` is covered by Step 5.
- **`s = 0` (Mills' constant) is exactly where this fails**: `w_k = α_k^0 = 1` is constant, so Galois rigidity gives nothing.  The trace is Frobenius-invariant, and the phase-29 residual classes survive.  **Among the base-3 shifted Mills constants with even `s` and `3 ∤ s`, Mills' own is the only one left open** (Saito: transcendental under RH/DH).

**Still to do:**
- odd `s` (`agcd = 2`; `ξ²` Pisot: redo Lemma 5 with exponent `(3^n + s)/2`);
- `3 ∣ s` (`agcd ∈ {3, 6}`);
- a second independent read.

## Variants
- **`ξ(r·3^k − 1)`, `r ≥ 2` even.**  `agcd = 1` (Saito), shift `s = −1`, `T = tr(ξ^(−1)) = σ₂/σ₃`; in the `(X − z)³` class `σ₂ ≡ 0 ⇒ 3 ∣ T`.  Steps 2–6 are identical (the certificate is shift-independent).  This extends Saito's Theorem 1.9(C) from `r ≥ 4·10¹⁴` to all even `r`.  Odd `r` has `agcd = 2` (`ξ²` is Pisot): Lemma 5 then needs exponent `(r·3^n − 1)/2`, which is to do.
- **The obstruction for Mills itself (`s = 0`).**  `w_k = 1` is constant, so Step 4 gives nothing: the trace is Frobenius-invariant.  That is exactly the six residual classes of phase 29.

## Numerics (supporting, not load-bearing)
- 867 cubic Pisot `f` with coefficients in `[−9, 9]`, `R = 3^n − 2`, precision `3^10`.  The survivors of the window test with the true offsets are exactly 4 cases with `f ≡ X³ (mod 3)` and positive dominant conjugate.
- Those survivors all have `ε = −1`, which Step 2 excludes for the least constant (they are admissible Pisot numbers, just not `ξ`).
- All 6 conductor-13 Pisot numbers in `[−15, 15]³` fail the window test.

## Remaining risks
1. Saito 2508.16068 is unrefereed; Theorem 2.3/2.6 and Prop 3.1(iv) are load-bearing.
2. Theorem D's Lemmas 2, 4, 5 and 6: the referee found them OK.
3. Ordinary risk of an unrefereed argument.  Next: a second independent read, then decide on Lean (the Galois step is heavy; the rest is within reach).
