# ON-LINE-REQUEST — power tower lower-half crux

## 2026-06-14 — `two_cycle_collapse` (the genuine lower-bound crux, `x ≥ e^(-e)`)

**Status of the run:** the mandatory headline `tower_converges_of_mem` (convergence
on the full Euler interval `[e^(-e), e^(1/e)]`) is PROVED in
`RealAnalysis/PowerTower/Statement.lean`, modulo ONE disclosed analytic axiom
`EngineLower.two_cycle_collapse`. All the surrounding analysis (continuity,
monotone-bounded even/odd subsequence convergence, limit relations, even/odd
reassembly) is machine-checked. I need the rigorous proof of the crux to discharge
the axiom.

**The exact statement needed** (cleanest, `c = log x`):

> Let `c < 0` with `-e ≤ c` (i.e. `x = e^c ≥ e^(-e)`). If `β, γ > 0`,
> `exp(c·β) = γ` and `exp(c·γ) = β`, then `β = γ`.

Equivalently in the power-tower variables: for `0 < x < 1` with `x ≥ e^(-e)`,
`x^β = γ ∧ x^γ = β ∧ β,γ > 0 ⟹ β = γ` (no nontrivial 2-cycle of `t ↦ x^t`).

**What I have already worked out (please confirm / correct / supersede):**
- The relations give `β·log β = γ·log γ` (so `β, γ` straddle `1/e`), and the
  problem reduces (set `p = -log β > 1`, `q = -log γ ∈ (0,1)`) to:
  **`p·e^{-p} = q·e^{-q}`, `p > 1 > q > 0` ⟹ `p·e^q > e`** (equivalently `p > e^{1-q}`).
  This is a TIGHT inequality (difference is `O((p-1)²)` near the bifurcation), so
  slack bounds (`log t ≤ t-1` etc.) do NOT close it.
- The `DIRECTION.md` "elementary" plan (Part C: subtract the two tangent-line
  inequalities `x^t ≥ y + (log y)(t-y)` at the fixed point `y`) is **mathematically
  invalid** — one cannot subtract inequalities, and numerically the tangent-at-`y`
  bound only pins `log y` to an interval *straddling* `-1`, never below it. Do not
  re-attempt that route.
- The correct mechanism I believe works: `g = f∘f` (`f t = x^t`) has derivative
  `g'(t) = c²·e^{c(f(t)+t)}`, maximized where `f(t)+t = e^{ct}+t` is minimal, giving
  `max g' = |c|/e ≤ 1`. So `g` is non-expansive ⟹ unique fixed point ⟹ `β=γ`.

**What I need from the open web:**
1. Lóczi, "The strange properties of the infinite power tower", arXiv:1908.05559,
   **§3** (the rigorous lower-bound `x ≥ e^(-e)` argument) — the exact lemma chain
   and which inequality does the work, so I can port it to Lean v4.29.1.
2. Any existing **Lean/mathlib formalization** of the power tower's interval of
   convergence (esp. the `e^(-e)` lower bound) to port directly.
3. A clean self-contained proof of the reduced inequality
   `p·e^{-p}=q·e^{-q}, p>1>q>0 ⟹ p·e^q > e` (or the `g'≤|c|/e` non-expansiveness)
   suitable for Lean — ideally one that avoids heavy MVT plumbing, or names the
   mathlib MVT/Lipschitz lemmas (`exists_hasDerivAt_eq_slope`,
   `Convex.lipschitzOnWith_of_nnorm_hasDerivWithin_le`, etc.) to use.

This unblocks discharging the only axiom in the lower-half deliverable.
