# PROBE: dropping Lemma 8 from Dubickas Theorem 1 (`c_eq_zero_or_two_noGap`)

**VERDICT (2026-09-28): NOT an obstruction — the route is COMPLETE, FORMALIZED and AXIOM-CLEAN.**
`c_eq_zero_or_two_noGap` is proved for **every** degree from `Dubickas2022` alone, and
`Dubickas2022PisotGap` (Lemma 8) has been dropped from `transcendental_growth_of_monic_quadratic`,
`theorem1` and `oeis_constants` and from the comparator challenge.  All three headlines
`#print axioms = [propext, Classical.choice, Quot.sound]`.  The `deg β ≤ 5` case analysis that this
probe started from is deleted: the degree-uniform argument below replaces it wholesale.

This file keeps the mathematical route (it is the readable form of the proof); the file map is at
the bottom.

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

## File map (everything below is sorry-free and `#print axioms`-clean)

| step | file | headline |
|---|---|---|
| Newton for multisets; `k!·eₖ ∈ ℤ` from integral power sums | `MultisetNewton.lean` | `multiset_isRatInt_factorial_mul_esymm` |
| Graeffe: `(−1)^k eₖ(s²) = Σ_{i+j=2k} (−1)^i eᵢ e_j` | `MultisetGraeffe.lean` | `esymm_map_sq` |
| bridge to `otherConj β`; `E_{k+1} = e_{k+1} + βᴺ eₖ`; crude `‖eₖ‖` bound; **the `k = 1, 2` Newton glue** | `DubickasEsymm.lean` | `eFull_succ`, `isRatInt_factorial_mul_eFull`, `norm_eSmall_le`, `eSmall_one`, `two_mul_eSmall_two` |
| Step 3, the parity-weight induction | `DubickasWeight.lean` | `weight_bound` |
| odd `Eₙ` vanish; the normalized `A n j` | `DubickasNormalized.lean` | `eFull_eq_zero_of_odd`, `AA_odd_succ` |
| Step 4, the finite-`j` recursion with error `O(q_j²)` | `DubickasBSeq.lean` | `bb_rec_approx` |
| Steps 4–5 assembled: eventual constancy of `E₂` ⇒ `z ∈ {0,1}` | `DubickasLimit.lean` | `eFull_two_const_eq_zero_or_one` |
| Step 5, the combinatorial finish | `DubickasBRec.lean` | `eq_zero_or_one_of_bRec_finite_support` |
| the conclusion, `c ∈ {0,2}` for every degree | `DubickasNoGap.lean` | `c_eq_zero_or_two_noGap` |

The last glue step (2026-09-28) was the observation that the *hypothesis* of
`eFull_two_const_eq_zero_or_one` is literally `exists_pisot_trace_ident`'s identity rewritten:
`eFull β 2 (2^j) = eSmall β 2 (2^j) + β^(2^j)·eSmall β 1 (2^j)` (`eFull_succ` at `k = 1`), with
`eSmall β 1 N = S_N` (`esymm 1 = sum`, `eSmall_one`) and `2·eSmall β 2 N = S_N² − S_(2N)`
(`two_mul_eSmall_two`, Newton at `k = 2` proved by multiset induction off `esymm_cons`).  So
`c = 2 βᴺ S_N + S_N² − S_(2N)` **is** `E₂(2^j) = c/2` — one `linear_combination` away.

Nothing in the route needs a lower bound on `|S_N|`, which is what Lemma 8
(Smyth/Mignotte/Baker) was supplying.  The only arithmetic input is `k!·Eₖ(N) ∈ ℤ` plus
`|β_l| < 1` for `l ≥ 2`; the only literature input left in the whole thread is `Dubickas2022`
(Lemma 6, the Corvaja–Zannier `p`-adic subspace theorem).
