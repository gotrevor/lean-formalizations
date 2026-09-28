# PROBE: dropping Lemma 8 from Dubickas Theorem 1 (`c_eq_zero_or_two_noGap`)

**Verdict so far: NOT an obstruction — a complete elementary route exists.**  It is longer than
the `deg β ≤ 5` case analysis already in `DubickasNoGap.lean`, but it is uniform in the degree
and needs nothing beyond `Dubickas2022` + integrality of power sums of conjugates.  This file
records the route; the terminal combinatorial step is already formalized and axiom-clean in
`DubickasBRec.lean`.

## Setup (all of this is what `exists_pisot_trace_ident` already hands us)

`β` Pisot of degree `d`, conjugates `β = β₁, β₂, …, β_d` with `ρ := max_{l≥2}|β_l| < 1`;
`N = 2^j` (`j ≥ j₀`), `B := β^N`, `q := B⁻¹`.  Put

* `S_M := Σ_{l≥2} β_l^M` (`conjPowSum β M`), so `p_M := β^M + S_M ∈ ℤ`
  (`pisot_conjPowSum_add_mem_int`) for **every** `M`, not just powers of two;
* `e_k(N) := ` the `k`-th elementary symmetric function of `β₂^N, …, β_d^N` (so `e_1 = S_N`,
  `e_k = 0` for `k > L := d − 1`);
* `E_k(N) := ` the same for the **full** root set `β₁^N, …, β_d^N`, so
  `E_k = e_k + B·e_{k−1}`, and `k!·E_k ∈ ℤ` by Newton's identities from `p_{N}, …, p_{kN} ∈ ℤ`.

The hypothesis of `c_eq_zero_or_two_noGap` (Dubickas's exact recursion `y_{n+1} = y_n² − c` at
`d = 2`, `a₀ = 1`) is, after `exists_pisot_trace_ident`, **exactly**

> `E_2(N) = C` for all `N = 2^j`, `j ≥ j₀`, where `C := c/2`,

since `p_{2N} = p_N² − 2E_2(N)`.  In particular `C ∈ ℤ` (so `c ∈ 2ℤ` for free), and the goal
`c ∈ {0,2}` is `C ∈ {0,1}`.

## Step 1 — `E_3(N) = 0` for large `j` (the cubic gain)

Expanding Newton, `6E_3 = p_N³ − 3p_N p_{2N} + 2p_{3N}`, and substituting `p_M = β^M + S_M`
gives the **exact** identity

    E_3 = B·σ_N + (S_N³ − 3 S_N S_{2N} + 2 S_{3N})/6,     σ_N := (S_N² − S_{2N})/2 = e_2(N).

The second summand is `O(ρ^{3N}) → 0`; the first is `O(q) → 0` by the already-proved bound
`‖σ_N‖ ≤ K₂ q²` (`hσq` in `DubickasNoGap.lean`).  Since `6E_3 ∈ ℤ`, `E_3(N) = 0` eventually.
Hence `e_3(N) = −B·e_2(N)`, so `‖e_3‖ ≤ K₂ q` — **and** `‖σ_N‖ ≤ C₃ ρ^{3N} q`.

## Step 2 — `E_4(N) = C(1−C)/2 =: D`, a constant

`E_2(N) = E_2(2N) = C` gives `p_{2N} = p_N² − 2C` and `p_{4N} = p_{2N}² − 2C`; `E_3 = 0` gives
`p_{3N} = p_N³ − 3C p_N`.  Substituting all four into
`24E_4 = p_N⁴ − 6p_N²p_{2N} + 3p_{2N}² + 8p_N p_{3N} − 6p_{4N}` makes every power of `p_N`
cancel, leaving `24E_4 = 12C − 12C²`.  (`D ∈ ℤ` since `C(C−1)` is even.)

## Step 3 — the weight induction

Claim, by strong induction on `n`, with constants `C_n` uniform in `j ≥ j₀`:

* `n` even: `‖e_n(N)‖ ≤ C_n q²`;
* `n` odd: `‖e_n(N)‖ ≤ C_n q`.

*Odd `n`*: `‖E_n‖ ≤ ‖e_n‖ + B‖e_{n−1}‖ ≤ C ρ^{nN} + C q → 0` (using the **even** case `n−1`),
and `n!E_n ∈ ℤ`, so `E_n = 0` eventually; then `e_n = −B e_{n−1}` has weight `2 − 1 = 1`.

*Even `n = 2k`*: the Graeffe identity for the small conjugates,
`e_k(2N) = e_k(N)² + 2 Σ_{m=1}^{k} (−1)^m e_{k−m}(N) e_{k+m}(N)`
(from `∏(X−z)·∏(X+z) = ∏(X²−z²)`), isolates
`2(−1)^k e_{2k}(N) = e_k(2N) − e_k(N)² − 2 Σ_{m=1}^{k−1} (−1)^m e_{k−m} e_{k+m}`.
Every term on the right has weight `≥ 2`: `q_{2N} = q_N²`, so `e_k(2N)` has weight `≥ 2`;
`e_k(N)²` has weight `≥ 2`; and `e_{k−m}e_{k+m}` pairs two indices of **equal parity**, so its
weight is `1+1` or `2+2`.

## Step 4 — the asymptotic constants and the recursion

Refining Step 3 to `e_{2i} = a_{2i} q² + O(q³)`, `e_{2i+1} = a_{2i+1} q + O(q²)` (the same
induction, keeping the leading term), the odd step gives `a_{2i+1} = −a_{2i}` exactly, and
reading off the `q²`-coefficient in the even step turns the Graeffe identity into, with
`b i := a_{2i}`,

    2 b(n+1) = Σ_{u+v=n} b u · b v + (b (n/2) if n is even),    b 0 = −C.

Seeds, checked independently: `b 0 = −C` (from `B e_1 = C − e_2 → C`), `b 1 = a_2 = −D`
(Step 2 / the `k = 1` Graeffe step), `b 2 = a_4 = C·D = b 0 · b 1` (the `k = 2` Graeffe step).

## Step 5 — the finish (FORMALIZED, axiom-clean)

`e_k ≡ 0` for `k > L`, so `b` has **finite support**.  `eq_zero_or_one_of_bRec_finite_support`
(`DubickasBRec.lean`) then gives `C = 0 ∨ C = 1`, i.e. `c ∈ {0, 2}`.  ∎

Proof of Step 5: let `m` be the top of the support.  `n = 2m` in the recursion has
`b(2m+1) = 0` and only the `(m,m)` term surviving, so `b m² + b m = 0`, i.e. `b m = −1`.  Then
downward induction: `n = m + k` (`k < m`) has `b(m+k+1) = 0`, only `(m,k)` and `(k,m)` surviving
and the half-index `(m+k)/2` strictly between `k` and `m`, so `2 b m · b k = 0`, i.e. `b k = 0`.
If `m ≥ 1` this forces `b 0 = 0`, whence `b ≡ 0` and `b m = 0`, contradiction.  So `m = 0` and
`−C = b 0 = −1`.

## What is left to formalize (in order)

1. `Multiset.esymm`-based `e_k(N)`, and the Graeffe identity from `∏(X−z)∏(X+z) = ∏(X²−z²)`
   via `Mathlib/RingTheory/Polynomial/Vieta.lean`.
2. `k!·E_k(N) ∈ ℤ` — Newton's identities in multiset form from `pisot_conjPowSum_add_mem_int`.
   (For `k ≤ 4` this is explicit algebra; the general case needs multiset Newton.)
3. Steps 1–3 (analysis), then Step 4 (leading coefficients), then plug into Step 5.

Only item 2 in full generality is real mathlib spelunking; nothing here needs a lower bound on
`|S_N|`, which is what Lemma 8 (Smyth/Mignotte/Baker) was supplying.
