# Infinite power tower — interval of convergence (Euler 1783)

**Result.** For `x > 0`, the infinite power tower `lim_{n→∞} ⁿx` (where
`ⁿx = x^(x^(··^x))`, `n` copies) converges **iff** `x ∈ [e^(-e), e^(1/e)]`
(Euler 1783). Numerically `[0.0660, 1.4447]`. The famous endpoint is
`e^(1/e) ≈ 1.44467` (so `√2^(√2^(··)) = 2` works, since `√2 < e^(1/e)`).

## Scope — BOTH halves of the convergence interval, machine-checked

### Upper half (`x ≥ 1`, sharp boundary `e^(1/e)`)
`t ↦ x^t` is increasing, so the tower is monotone; convergence is the elementary
"monotone, bounded above by the least fixed point of `t = x^t`" argument.

- `tower_converges` — for `1 ≤ x ≤ e^(1/e)`, converges to a fixed point `L = x^L`
  with `1 ≤ L ≤ e`. **PROVED.**
- `tower_diverges` — for `x > e^(1/e)`, the tower → +∞. **PROVED.**
- `tower_converges_iff` — on `[1,∞)`, converges iff `x ≤ e^(1/e)`. **PROVED.**

### Lower half (`e^(-e) ≤ x < 1`, the *oscillating* regime)
`t ↦ x^t` is decreasing, so the tower is no longer monotone: the even subsequence
`a(2n)` decreases to `γ`, the odd `a(2n+1)` increases to `β`, and `(β,γ)` is a
2-cycle of `f`. Convergence ⟺ `β = γ`. The crux — **no nontrivial 2-cycle for
`x ≥ e^(-e)`** (the bifurcation at the lower endpoint) — is proved via the slope
bound `g'(t) = (log x)²·x^(x^t)·x^t ≤ |log x|/e ≤ 1` (engine: `EngineLower.lean`):
a Banach contraction for `x > e^(-e)`, an antitone-on-interval argument at the
boundary `x = e^(-e)`. The same `add_one_le_exp` "max of `t·e^{-t}`" that drives
the upper half. (The often-cited "subtract the tangent-line inequalities" sketch
is mathematically invalid — see `EngineLower.lean`.)

- `tower_converges_lower` — for `e^(-e) ≤ x < 1`, converges to a fixed point. **PROVED.**
- `tower_converges_of_mem` — converges on the FULL Euler interval
  `[e^(-e), e^(1/e)]`. **PROVED.**

### Sharp lower divergence (`0 < x < e^(-e)`, the *genuine* 2-cycle)
Below the lower endpoint the tower diverges by oscillation: the fixed point `y` of
`f` becomes **repelling** (`g'(y) = (log y)² > 1`, because `x < e^(-e)` forces
`log y < -1`), so `g = f∘f` acquires two *attracting* fixed points `β₀ < y < γ₀` —
a genuine attracting 2-cycle of `f`. The even/odd subsequences are trapped on
opposite sides (`a(2n) ≥ γ₀ > y > β₀ ≥ a(2n+1)`), so their limits differ and no
overall limit exists. This is the sharp converse of `two_cycle_collapse`.

- `log_fixedpoint_lt_neg_one` — `x < e^(-e) ⟹ log y < -1` (the repelling seed).
- `strict_two_cycle_exists` — the attracting 2-cycle `β₀ < γ₀` (IVT on `g - id`
  both sides of `y`, using `g' > 1` on a neighbourhood of `y`).
- `tower_diverges_lower` — for `0 < x < e^(-e)`, the tower does **not** converge.
- `tower_converges_iff_full` — **headline (SHARP)**: for `x > 0`, converges **iff**
  `x ∈ [e^(-e), e^(1/e)]` (`Statement.lean`).

All of the above are machine-checked and **axiom-clean** (trust base
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`, no
custom axioms).

## What to audit
- `Statement.lean` — the three load-bearing statements (delegate to the engine).
- `Defs.lean` — `tower` (check the recursion + that `^` is `Real.rpow`),
  `eInvE = Real.exp (1 / Real.exp 1) = e^(1/e)` (written verbatim), and
  `endpoint_fixed_point` — machine-checked anchor that `(e^(1/e))^e = e`, the
  limit value at the top endpoint.
- `Engine.lean` — upper-half proofs. The only analytic input is
  `Real.add_one_le_exp` (`x+1 ≤ eˣ`), from which `log_le_div_e` (`log L ≤ L/e`)
  and `base_le_eInvE` (a fixed point forces `x ≤ e^(1/e)`) follow with no calculus.
- `EngineLower.lean` — lower-half proofs. Continuity/monotonicity of `f`,
  even/odd monotone-bounded subsequence convergence, the even/odd reassembly, and
  the crux `two_cycle_collapse` (slope bound `g' ≤ |log x|/e ≤ 1` ⟹ contraction /
  antitone). `Defs.endpoint_fixed_point_lower` anchors `(e^(-e))^(1/e) = 1/e`.

## Status
**DONE — SHARP `iff`, 2026-06-18.** Upper: `tower_converges`, `tower_diverges`,
`tower_converges_iff`. Lower: `tower_converges_lower`, `tower_converges_of_mem`
(convergence on the full `[e^(-e), e^(1/e)]`), `tower_diverges_lower` (divergence
for `0 < x < e^(-e)`, the genuine attracting 2-cycle), and the sharp headline
`tower_converges_iff_full` (`x > 0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`).
All PROVED and **axiom-clean**, including both cruxes `two_cycle_collapse` (no
2-cycle for `x ≥ e^(-e)`) and `strict_two_cycle_exists` (a 2-cycle exists for
`x < e^(-e)`). `lake build` green.

## Prior art
Not in mathlib (checked 2026-06-14 via Reservoir mirror + the "Is there code for
X?" Zulip): only a course exercise defining *natural-number* tetration `n ↑↑ k`
and an unrelated power-tower inequality (IMO 2010 Q5). The real-analysis
convergence interval is unformalized in the public Lean ecosystem. mathlib also
lacks the Lambert `W` function, which gives the closed form `L = -W(-ln x)/ln x`
(not needed for convergence).

## Source
- L. Euler, *De formulis exponentialibus replicatis* (1783).
- L. Lóczi, "The strange properties of the infinite power tower",
  arXiv:1908.05559 (modern survey with the full `[e^(-e), e^(1/e)]` analysis).
- Prompted by Michael Penn, "why only some infinite power towers are well
  defined" (YouTube, 2025): https://www.youtube.com/watch?v=z-SXMumnZB8
