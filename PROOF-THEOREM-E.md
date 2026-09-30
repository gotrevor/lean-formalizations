# Theorem E — the shifted Mills constant `ξ(3^k − 2)` is transcendental (proof write-up, draft 2)

Ren, 2026-09-30.  **Status: paper proof, not in Lean.**  Draft 2 incorporates an adversarial referee pass (a subagent, same night).  The referee found no fatal error and about 80% confidence after three patches, all applied below: Step 5 now cites Saito's Prop 3.1(iv), Step 3's `C₃` rank argument is completed, and the `b = 0` case of the E1 certificate is covered.

It builds on `PROOF-THEOREM-D.md` (Lemmas 1–6) and Saito, arXiv:2508.16068 (itself unrefereed; its Theorem 2.3/2.6 and Prop 3.1 are load-bearing here).  **Version check (2026-09-30):** arXiv:2508.16068 has a v2 (2025-12-07); Theorems 1.9, 2.3, 2.6 and Proposition 3.1 read identically in v2, and v2 has nothing on shifted sequences `3^k + s`.  `papers followups 2508.16068` finds 0 citing papers.

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
> **For every even `s ≠ 0` with `3 ∤ s`, `ξ(C_k)` with `C_k = 3^k + s` is transcendental**, with the index starting at `k₀ = 1` if `s < 0` (where `3^k + s ≥ 1`), and at the least `k₀` with `3^(k₀) ≥ s` if `s > 0` (*referee 2*: Saito's existence theorem needs every ratio `c_(k+1) ≥ 2`, and `(3^(k+1) + s)/(3^k + s) ≥ 2 ⟺ 3^k ≥ s`).  So for example `ξ(3^k + 2)` from `k = 1`, and `ξ(3^k + 4)` from `k = 2`.  Unconditional, same caveats as Theorem E.

- **Reduction via Saito's Type B (Theorem 2.3), for both signs of `s`.**  `C_k = 3^k + s`.
  - `(B1)`–`(B4)`: ratios `c_(k+1) → 3`, all `≥ 2`, and `lim sup 3 > 40/19`.
  - `(B5)`: `gcd(3, C_m) = 1` (`3 ∤ s`), so `C_m ∣ C_(m + φ(C_m))`.
  - Conclusion: `ξ` is transcendental, or `ξ^g` is Pisot of degree `ℓ ∈ [3, 1 + 1/(57/40 − 1)] = [3, 3.35]`, so `ℓ = 3`, with `g ∣ C_k` for large `k`.  `agcd(3^k + s) = 1` for even `s` with `3 ∤ s` (it divides `gcd(C_m, C_(m+1)) ∣ 2s`; the `C_k` are odd, so an odd `d ∣ s` with `d ∣ 3^m + s` has `d ∣ 3^m`, hence `d = 1`), so `g = 1`.
  - Saito's `(B6)` (`C_k ≡ C_m mod L·C_m`) **fails** for these sequences: it is the non-reversibility.  That is exactly why his theorem stops at "cubic Pisot" here.
- **Step 2** (Prop 3.1(iv), same `(G)`-conditions): `ε = 0` eventually.
- **Steps 3–4** unchanged with shift `s` (for `s > 0`, `T = tr(ξ^s) > 0`; for `s < 0`, `T ≠ 0` is forced by the summed equation).  Rank: `w = (α_k^s)` is non-constant because the root moduli differ, so `S₃` and `C₃` both work as in Step 4.
- **Step 5, general `s ≠ 0`:** the load-bearing point (*referee 2*): `z_k = ζ_k^(3^r)`, and `x ↦ x^(3^r)` is a bijection on the prime-to-3 roots of unity, so `z = ±1` forces every `ζ_k = z`.  Then `σ₃ ≡ z ≢ 0`, so every root is a unit.  In the class `f ≡ (X − z)³ (mod 3)` every root (and its inverse) is `≡ z` modulo the prime above 3.  So `T = Σ α_k^s ≡ 3z^s ≡ 0`: `v₃(T) ≥ 1` (the denominator `σ₃^|s|` is prime to 3).  Hence `T ≠ ±1`.  No size input is needed.
- **Step 6:** the certificate is shift-independent (any `w ∈ K`), and `b = 0` is covered by Step 5.
- **The unshifted case `s = 0` (Mills' constant; outside this family, since `3 ∣ 0`) fails twice.**  The reduction fails: `agcd(3^k) = ∞`, so Type B only gives some `ξ^(3^j)` Pisot, not `ξ`.  The rigidity fails too: `w_k = α_k^0 = 1` is constant, the trace is Frobenius-invariant, and the phase-29 residual classes survive.  (Saito: transcendental under RH/DH.)

### E+ for even `s` with `3 ∣ s` (draft 3, 2026-09-30; closes all even `s ≠ 0`)
Let `s ≠ 0` be even with `a₀ = v₃(s) ≥ 1`, and start the index where every ratio is `≥ 2` and `C_k ≥ 1` (for `s > 0`: `3^k ≥ s`; for `s < 0`: `3^k + s ≥ 1`), reindexed so that `k = 1` is the first term.
- **`(B5′)` holds.**  `s` is even, so `|s| ≥ 2·3^(a₀)`, and the start rule (`3^k ≥ s`, or `3^k + s ≥ 1`) forces every index in range to have `k > a₀`.  Hence `v₃(C_k) = a₀` for all `k` (*referee 3*: draft 3 wrongly had `v₃(C_m) = m` for `m ≤ a₀`, a harmless misstatement because those indices never occur).  Write `C_m = 3^(a₀)·u` with `3 ∤ u`, and take `t = ord_u(3)`.  Then `u ∣ 3^m(3^t − 1) = C_(m+t) − C_m`, so `C_m ∣ C_(m+jt)` for every `j`, and `j` large gives the `≥ 29/10` ratio.
- **`agcd`.**  `gcd(C_m, C_(m+1)) ∣ 3C_m − C_(m+1) = 2s`.  The `C_k` are odd, and an odd prime `q ≠ 3` with `q ∣ s` and `q ∣ 3^m + s` would divide `3^m`.  So only `3` survives, and `gcd_(k ≥ K) C_k = 3^(a₀)` for large `K`.  Type B gives `g ∣ C_k` for all large `k`, so `g = 3^a` with `0 ≤ a ≤ a₀`.
- **Reduce to `β = ξ^(3^a)`**, cubic Pisot, with `⌊ξ^(C_k)⌋ = tr(β^(N_k))` for large `k` (Prop 3.1(iv), as in our `Saito2025TypeBTrace` conclusion), `N_k = 3^(k−a) + s′`, `s′ = s/3^a`.  Here `s′` is even and **nonzero**, and may still be divisible by 3.
- **Steps 3–5 for `β` with shift `s′`.**  None of them uses `3 ∤ s′`, and none uses minimality of `β`.
  - The filter (Lemma 2) needs only `N_(n+t) − N_n = 3^(n−a)(3^t − 1)`.
  - The window (Lemma 4) is unchanged (`d = 3`, `c = 3`, `μ₂`).
  - The limit points are `Λ_r = Σ_k ζ_k^(3^r) β_k^(s′)`.  `ω(β)^(3^(n−a) + s′)` is periodic in `n`, and `⟨β⟩^(3^(n−a)) → 1`.
  - The rigidity weights `w_k = β_k^(s′)` are non-constant because `s′ ≠ 0` and the moduli differ.
  - Step 5: `z = ±1` forces `f_β ≡ (X − z)³ (mod 3)`, so `T = tr(β^(s′)) ≡ 3z^(s′) ≡ 0 (mod 3)` and `T ≠ ±1`.
- **Step 6** (E1) is shift-independent.  **Conclusion: `ξ(3^k + s)` is transcendental for every even `s ≠ 0`** (index as above).  ~75%, same caveats as E+.

### E+ for odd `s` (draft 3; partial)
`C_k = 3^k + s` is even.  `agcd = 2·3^(v₃(s))`: the odd part is as above, and `v₂(3^m + s)` equals 1 for one parity of `m`.  After the `3^a` reduction above (which needs no parity), `g ∈ {1, 2}`.
- **Patches (*referee 3*).**
  - `(B5′)` for odd `s`: take `t = lcm(ord_u 3, ord_(2^b) 3)`, where `2^b ∥ C_m`.  This is needed because `v₂(3^k + s)` is unbounded along one parity when `−s ∈ ⟨3⟩ ⊂ ℤ₂^×`.
  - The `g = 2` filter needs `o ∣ 3^n(3^t − 1)/2`: take `t` a multiple of `ord_(2o)(3)`.
  - The hypothesis "`f_β` irreducible over `E`" in the generic case is redundant (`F` irreducible already gives transitivity), but it is harmless.
- **`g = 1`:** E+ verbatim.  Step 5's congruence `T = tr(ξ^s) ≡ 3z^s ≡ 0` does not care about parity.
- **`g = 2`,** `β = ξ²` cubic Pisot, `N_n = (3^n + s)/2`.  The Teichmüller part `ω(β_k)^(N_n)` is periodic in `n`.  `⟨β_k⟩^(N_n) → ⟨β_k⟩^(s/2)` (`s/2 ∈ ℤ₃`; `1 + 𝔪` is a pro-3 group).  `⟨β_k⟩^(s/2)` is a root of `Y² = β_k^s ω(β_k)^(−s)`, so it is algebraic, and after fixing square roots `δ_k` of `β_k`:
  `Λ_r = Σ_k a_k δ_k^s = ω`, with `a_k ∈ μ_(2m) ∪ {0}` and `m ∣ 26` or `m ∣ 8`.  All of this lies in `E(δ₁, δ₂, δ₃)` with `E = ℚ(μ_M)`, `M ∣ 208`.
  - **Generic case: `F(X) = f_β(X²)` irreducible over `E`.**  `G = Gal(E(δ)/E)` is transitive on the six roots `±δ_j` and fixes every `a_k` and `ω`.  For each `k` the multiset `{τ(δ_k) : τ ∈ G}` is `|G|/6` copies of each `±δ_j`.  Since `s` is odd, `Σ_(τ ∈ G) τ(δ_k)^s = 0`.  Summing the identity over `G` gives `0 = |G|·ω`: **contradiction.**  (This replaces the draft-2 sign-flip case analysis, which had gaps at non-unit indices where `a_k = 0`.)
  - **`f_β` reducible over `E`** (`ℚ(β)` is the conductor-13 field, E1).  **Open**: needs a `g = 2` analogue of the Step 6 certificate.
  - **Kummer-degenerate case: `f_β` irreducible over `E`, `F` reducible over `E`.**  Then `δ₁ = ξ ∈ E(β)`.  Since `ℚ(β) ∩ E = ℚ` (non-E1), `FE/F` (`F = ℚ(β)`) is abelian with group `Gal(E/ℚ)`, so its quadratic subextensions are `F(√d)` with `ℚ(√d) ⊂ E`.  Writing `ξ = u + v√d` with `ξ² ∈ F` forces `uv = 0`.
    - `v = 0`: `ξ ∈ F` is cubic and Pisot (its conjugates `±√β_j` have modulus `< 1`), which is the `g = 1` case, done.
    - `u = 0`: **`ξ = √d·γ`** with `γ ∈ F`, `d > 1` squarefree (`ξ` and `γ` are real), and `ℚ(√d) ⊂ ℚ(μ_208)`, i.e. `d ∈ {2, 13, 26}`.  The `E`-conjugates of `ξ` are `√d·γ_k`; re-sign the `a_k` (odd `s`) so that `δ_k = √d·γ_k`.  Then `Σ_k a_k γ_k^s = ω·d^(−s/2)`, and `G = Gal(E(β)/E)` permutes the `γ_k` transitively while fixing `a_k`, `√d` and `ω`.  **Step 4's rigidity** applies verbatim with weights `w_k = γ_k^s`: they are non-constant because the moduli differ, `3 ∤ 208` covers the `C₃` subcase, and `T″ := Σ γ_k^s = tr_(F/ℚ)(γ^s) ∈ ℚ` is nonzero because the summed equation has a nonzero right side.  So `a_k = z` for all `k` and `z·T″ = ω·d^(−s/2)`.  `z = 0` is impossible; otherwise `|z| = 1` in `ℂ` gives **`|T″| = d^(−s/2) ∉ ℚ`** (`s` odd, `d > 1` squarefree): **contradiction.**  *(Closed 2026-09-30, draft 3b.)*
  - So for odd `s`, the only open case is **E1 at `g = 2`**: `ℚ(ξ²)` is the conductor-13 cyclic cubic field.  It needs a finite certificate in the style of Step 6 over `ℚ(ζ₁₃, √d)`, `d ∈ {1, 2, 13, 26}`.
- Once E1 at `g = 2` closes: **E+ for every `s ≠ 0`.**
- **Referee 3 (2026-09-30, subagent):** no error.  The two gaps above are patched.  Confidence: all even `s ≠ 0` ~78%; odd-`s` generic step ~85%; odd `s` except E1 at `g = 2` ~72% (all conditional on Saito).  Numeric control: at `s = 1` the window hit for `X³ − 4X² + 1` mod `3^8` disappears at `3^15`, `3^30` and `3^60` (the limits flip sign with period 6, matching the odd `δ^s` structure).
- **Lead for E1 at `g = 2`, `s > 0`:** `K` is totally real, and in ℂ the local-trace identity `θ₁ + θ₂ + θ₃ = ±1` has `|θ_j| = |β_j|^(s/2)`.  So `β₁^(s/2) < 3`.  That leaves finitely many `(β, s)`, a computer check.  `s < 0` needs a different argument (the two large terms must nearly cancel).

## Variants
- **`ξ(r·3^k − 1)` for even `r`: NOT established** (*referee 2*; draft-1 claim withdrawn).  The limit points carry `ζ_k^(r·3^m)`, and for even `r` the map `x ↦ x^r` is not injective on the (even-order) Teichmüller roots.  So `z_k = ±1` no longer forces equal `ζ_k`, and `f ≡ (X − 1)^a (X + 1)^b (mod 3)` survives the congruence step.  The `b = 0` reduction of Step 6 breaks the same way (e.g. `13 ∣ r`).  Odd `r` has `agcd = 2`.  Open.
- **The obstruction for Mills itself (`s = 0`):** see the last bullet of Theorem E+.

## The constant (heuristic value)
Assume the greedy chain (least admissible prime at each step) never gets stuck.  This is the same assumption behind the published digits of Mills' constant, which rest on RH.  Then
`ξ(3^k − 2) ≈ 2.00663014725500738956382906826814896606031523146614463546077…`.
- The chain is `⌊ξ⌋ = 2`, `⌊ξ^7⌋ = 131`, `⌊ξ^25⌋ = 36448807`, then primes of 24, 73 and 220 digits (`k = 4, 5, 6`).
- The interval width after `k = 6` is `≈ 3.5·10^(−223)`.
- Computed 2026-09-30 by an ad-hoc greedy search (sympy `nextprime` + mpmath).  The theorem does **not** depend on these digits.

## Numerics (supporting, not load-bearing)
- 867 cubic Pisot `f` with coefficients in `[−9, 9]`, `R = 3^n − 2`, precision `3^10`.  The survivors of the window test with the true offsets are exactly 4 cases with `f ≡ X³ (mod 3)` and positive dominant conjugate.
- Those survivors all have `ε = −1`, which Step 2 excludes for the least constant (they are admissible Pisot numbers, just not `ξ`).
- All 6 conductor-13 Pisot numbers in `[−15, 15]³` fail the window test.

## Remaining risks
1. Saito 2508.16068 is unrefereed; Theorem 2.3/2.6 and Prop 3.1(iv) are load-bearing.
2. Theorem D's Lemmas 2, 4, 5 and 6: the referee found them OK.
3. Ordinary risk of an unrefereed argument.  Next: a second independent read, then decide on Lean (the Galois step is heavy; the rest is within reach).
