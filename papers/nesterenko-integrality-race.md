# Nesterenko's method and odd zeta values: the integrality race is lost structurally

**2026-10-24.**  Probe: `nesterenko-integrality-race.py [r] [dmax]`.

## Setup

The extended Ramanujan system `q, E₂, E₄, E₆, g_{u,v}` with `g_{u,v} = Σ nᵘ σ₋ᵥ(n) qⁿ` has every
ingredient of Nesterenko's method except one:

| Ingredient | Status |
|---|---|
| δ-closed differential system | ✅ (`δ g_{u,v} = g_{u+1,v}`, `δ g_{v−1,v} ∈ ℚ[E₄,E₆]`) |
| Functional algebraic independence | ✅ Kozlov 2010 |
| Zero estimate, optimal exponent | ✅ Zorin, arXiv 1109.0025 (JTNB 2012) |
| Values reach odd zeta | ✅ `ζ(4n+3) ∈ ℚ(E₂(i), g_{0,4n+3}(i))`, Nesterenko 2011 |
| **Integral Taylor coefficients** | ❌ `g_{0,v}` has denominators `nᵛ` |

Fonseca, *Algebraic independence for values of integral curves* (Algebra & Number Theory 13
(2019) 643-694, arXiv 1710.00563), Theorem 1.2, proves that a curve with the D-property (ZL-density),
moderate growth and a model over `O_K[[q]]` (radii product 1) has `trdeg ≥ n − 1` at every point.
The extended system fails only the integral model, and fails it in every model: if `X` is a
finitely generated `ℤ`-model then `N·g_{0,3} ∈ ℤ[[q]]` for some integer `N`, which unbounded
denominators forbid.

## The race

Gain at `q = e^{−2π}` (Lemma 3.22 of Fonseca's survey arXiv 2011.14401): `2π ≈ 6.283` per order of
vanishing.  Cost: `log D(r,d)`, the lcm of denominators of `[qⁱ] g_{0,3}ʲ`, `i ≤ r`, `j ≤ d`.

`log D(r,d) / r`, exact rational arithmetic:

| d | r = 120 | r = 240 | r = 480 | napkin `3(1 + log d)` |
|---|---|---|---|---|
| 1 (control: `3ψ(r)/r → 3`) | 2.935 | 2.984 | 3.019 | 3.000 |
| 2 | 4.367 | 4.448 | 4.509 | 5.079 |
| 4 | 5.934 | 6.144 | 6.198 | 7.159 |
| 5 | 6.469 | 6.717 | **6.751** | 7.828 |
| 8 | 7.529 | 7.843 | 7.979 | 9.238 |

At fixed `d` the ratio rises with `r` toward the napkin value; it grows with `d` without bound and
passes `2π` at `d = 5`.  Nesterenko needs `d → ∞` with `r ~ dⁿ`, so the lower-bound step loses by a
`log d` factor.  Choosing another point does not help: the gain is `log(1/|z|)`, a constant.

The second loss is worse and needs no probe.  Siegel's lemma over `ℚ` clears row `i` by `D_i`, so
the auxiliary polynomial's height becomes `≈ (r/(s−r))·log D(r,·) ~ r ~ dⁿ` instead of
Nesterenko's `O(d log d)`.  Philippon's criterion needs heights far below the smallness exponent
`dⁿ`.  This holds even if the polynomial's degree in the `g`'s is held fixed (the module of
`g`-degree ≤ 1 is δ-stable, so the derivative step would survive, but the height does not).

## Reading

The failure is the values-versus-periods distinction made quantitative.  ζ(3) enters as the
constant of integration of `E₄` (three times), and integrating `qⁿ` produces exactly the `n³`
denominators.  Integer-coefficient (modular) functions carry no such constant.  The method's
regime is "heights polylogarithmic, smallness polynomial"; denominators push it to "both
exponential in `r`", which is the linear-forms regime of Apéry and Nesterenko's linear
independence criterion, where `π, e^π, Γ(1/4)` cannot serve as coefficients.

**Verdict, ~75%: the extended-Ramanujan route to odd zeta does not run on Nesterenko's machine as
built.**  Reopen only with a mechanism that removes the denominators (an integral model for some
other function whose value encodes ζ(3)) or a Philippon-type criterion tolerant of exponential
heights.  Not stated in any source found; the integrality hypothesis and its failure are, the
quantitative verdict is ours.
