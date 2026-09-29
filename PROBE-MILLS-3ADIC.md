# A 3-adic obstruction to an algebraic Mills constant (probe, 2026-09-29)

**Claim (new, as far as I can find).**  Let `C` be a square integer matrix with `det C ≠ 0`, and let `t_k = tr C^(3^k)`.  Suppose `t_k` is prime and strictly increasing for all large k.  Then `t_k → ±1` in `ℤ₃`.  Applied to Mills: if Mills' constant ξ is algebraic, then the Mills primes `⌊ξ^(3^k)⌋` converge to `+1` or `−1` 3-adically.  Take β = ξ^(3^m), a cubic Pisot number (Saito 2024, Thm 1.2), with minimal polynomial f.  Then f mod 3 must be one of six classes:
- `(x−1)²(x+1)` or `(x+1)²(x−1)`;
- `x²(x∓1)`;
- `(x∓1)(x²+1)`.

The other 21 monic cubics mod 3 are excluded unconditionally.

Confidence: argument correct 90%; new 75%.

## Why this is the gap Saito names

- Saito 2024 (arXiv:2404.19461), Remark 4.4: "The author does not have any good ideas on how to treat bₖ and eₖ simultaneously".  His Prop 5.1 extracts only `p_(k+1) ≡ p_k (mod 3)`.
- Saito 2025 (arXiv:2504.14968), Problem 1.1: prove that `⌊β^(3^n)⌋` is composite infinitely often, for every cubic Pisot β.  His periodicity method needs the exponent sequence to be "reversible".  `3^n` is not reversible, because `3^n mod L` never returns to 1 when `3 ∣ L`.
- Saito 2025 (arXiv:2508.16068), Thms 1.7–1.8 is the RH/DH route (formalized here in phase 14).
- `papers followups`: 2404.19461 has 2 citing papers (both Saito's own); 2508.16068 has none (checked 2026-09-29).

## The argument

1. **Modulus.**  Take the modulus to be the prime `p = t_m` itself.  Then `tr (C^(3^m))^n mod p` is periodic in n.  Its period divides the order of `g = C^(3^m)` in `GL_n(𝔽_p)`, and `|GL_n(𝔽_p)| = ∏ (p^n − p^i)`.
2. **Killing the 3-part.**  Suppose `v₃|GL_n(𝔽_p)| ≤ m`.  Then g has order prime to 3, so `3^j ≡ 1` modulo that order for `j = φ(M) ≥ 1`.
3. **Divisibility.**  Therefore `t_(m+j) = tr g^(3^j) ≡ tr g = t_m ≡ 0 (mod t_m)`.  Since `t_(m+j) > t_m` is prime, this is a contradiction.  So `v₃|GL_n(𝔽_(t_m))| > m` for all large m.
4. **The Gauss congruence** (Steinlein 2017) gives `t_(k+1) ≡ t_k (mod 3^(k+1))`, so `t_k → τ` in `ℤ₃`.  If `τ ≠ ±1`, lifting the exponent bounds `v₃(t^s − 1)` for s ≤ n, and so bounds `v₃|GL_n(𝔽_t)|`.  That contradicts step 3.  Hence `τ = ±1`.
5. **The six classes.**  `τ = Σ ω(βᵢ)`, where ω is the Teichmüller lift, and 0 is used for conjugates divisible by 3.  So `τ = ±1` depends only on f mod 3.

## Sanity checks

- **Fermat numbers fall in the residual case, as they must.**  `F_k = 2^(2^k) + 1 = tr diag(2,1)^(2^k)`, the analogue for base 2, tends to `1` in `ℤ₂`.  The method therefore cannot touch Fermat primes, which matches Saito's "similar to Fermat numbers" remark.
- **The residual case is genuinely residual.**  If `τ = 1`, then `v₃(p_m − 1) ≥ m+1`, and the 3-part can survive the `3^m`-th power.

## Numerics

`scripts/mills-3adic-probe.py` runs four checks: `gauss`, `mech`, `tau` and `chain`.
- **gauss:** the congruence holds on 11 cubics for m ≤ 6.
- **mech:** 68 of 68 prime moduli with a small 3-part divide `p_(m+j)`, with the order computed by an independent route.
- **tau:** over 2028 cubics, `τ ≡ ±1 (mod 3^7)` exactly when f mod 3 lies in the six classes.
- **chain:** the known-answer control uses 8 cubics where `p_2` really is prime (for example `x³−8x²−4x+1`, `p_2 = 221730077`).  In each case `p_2 | p_(2+j)` for the predicted j.

## Lean (phase 29)

`NumberTheory/Mills/ThreeAdic.lean` contains:
- `dvd_trace_pow_three_of_glCard` and `lt_padicValNat_glCard`, both unconditional;
- `threeAdic_pm_one`, which uses `Literature.GaussCongruenceTrace`;
- `mills_threeAdic` and `transcendental_of_not_pm_one`.

## What is left

- **Mills.**  Exclude the six residual classes for a totally real cubic Pisot β satisfying Saito's (1.3).
- **Problem 1.1 for totally real cubic Pisot β.**  The floor offset `h ∈ {0, −1}` is eventually constant because odd powers keep sign, so the argument applies with `τ + h`.  This is not in the Lean phase.
