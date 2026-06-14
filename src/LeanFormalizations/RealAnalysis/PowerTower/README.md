# Infinite power tower — interval of convergence (Euler 1783)

**Result.** For `x > 0`, the infinite power tower `lim_{n→∞} ⁿx` (where
`ⁿx = x^(x^(··^x))`, `n` copies) converges **iff** `x ∈ [e^(-e), e^(1/e)]`
(Euler 1783). Numerically `[0.0660, 1.4447]`. The famous endpoint is
`e^(1/e) ≈ 1.44467` (so `√2^(√2^(··)) = 2` works, since `√2 < e^(1/e)`).

## Scope of this side quest (upper half)
This formalizes the `x ≥ 1` regime, whose sharp boundary is `e^(1/e)`. There
`t ↦ x^t` is increasing, so the tower is monotone and convergence is the
elementary "monotone, bounded above by the least fixed point of `t = x^t`"
argument.

- `tower_converges` — for `1 ≤ x ≤ e^(1/e)`, converges to a fixed point `L = x^L`
  with `1 ≤ L ≤ e`. **PROVED.**
- `tower_diverges` — for `x > e^(1/e)`, the tower → +∞. **PROVED.**
- `tower_converges_iff` — the headline: on `[1,∞)`, converges iff `x ≤ e^(1/e)`.
  **PROVED** from the two facts above.

All three are machine-checked and axiom-clean (trust base
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`).

The lower half (`e^(-e) ≤ x < 1`, the *oscillating* regime — `t ↦ x^t` is
decreasing, so one analyzes the 2-cycle stability of `g(t) = x^(x^t)`, with the
even/odd subsequences splitting below `e^(-e)`) is more delicate and is deferred
to a separate file.

## What to audit
- `Statement.lean` — the three load-bearing statements (delegate to the engine).
- `Defs.lean` — `tower` (check the recursion + that `^` is `Real.rpow`),
  `eInvE = Real.exp (1 / Real.exp 1) = e^(1/e)` (written verbatim), and
  `endpoint_fixed_point` — machine-checked anchor that `(e^(1/e))^e = e`, the
  limit value at the top endpoint.
- `Engine.lean` — the actual proofs. The only analytic input is
  `Real.add_one_le_exp` (`x+1 ≤ eˣ`), from which `log_le_div_e` (`log L ≤ L/e`)
  and `base_le_eInvE` (a fixed point forces `x ≤ e^(1/e)`) follow with no calculus.

## Status
**DONE (upper half), 2026-06-14.** `tower_converges`, `tower_diverges`, and
`tower_converges_iff` are all PROVED and axiom-clean; the proofs live in
`Engine.lean` and `Statement.lean` delegates. The lower half (`e^(-e) ≤ x < 1`) is
deliberately NOT started (a separate future cycle). `lake build` green.

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
