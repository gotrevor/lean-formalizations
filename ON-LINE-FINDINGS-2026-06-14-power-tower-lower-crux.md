# ON-LINE-FINDINGS — power-tower lower-half crux (`two_cycle_collapse`)

**Fulfills:** `ON-LINE-REQUEST.md` 2026-06-14 (the `x ≥ e^(-e)` no-2-cycle crux).
**Date:** 2026-06-14 (host session, networked).
**Sources read:** Lóczi, *The strange properties of the infinite power tower*,
arXiv:1908.05559 (ar5iv); Lynch, *Fractal Boundary of the Power Tower* (UCD, image-PDF,
not extractable but it concerns the **complex** boundary, not the real lower bound);
MathWorld "Power Tower"; reservoir-grep over 705 Lean repos; zulip-ro ITC corpus;
WebSearch. Cross-checked all lemma names against this repo's mathlib v4.29.1.

---

## 0. Heads-up: the request SELF-RESOLVED while this was being researched

By the time I looked, the live lap had already discharged it: commit **`cfe285c`**
("DISCHARGE the crux — tower_converges_of_mem fully axiom-clean") makes
`EngineLower.two_cycle_collapse` a **theorem** (no axiom), `src/` is sorry-free, and
the `.githooks` pre-commit gate means `lake build` was green at commit. The route you
took is the **contraction / derivative-bound** mechanism you proposed in the request
(`deriv_bound`: `g'(t) = (x^{x^t}·log x)(x^t·log x) < 1`). 

So treat this file as **independent verification + an elementary alternative + context**,
not an unblock. **One final check worth running** (it's the only thing that certifies
the discharge): `#print axioms tower_converges_of_mem` → expect
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `native_decide` on the
headline path. (I did NOT run a competing `lake build` while your lap was live.)

---

## 1. VERDICT on the contraction route you implemented: mathematically CORRECT ✅

Independently confirmed the derivative computation. With `f t = x^t = e^{ct}`,
`c = log x ∈ [-e, 0)`, and `g = f∘f`:

```
g'(t) = f'(f t)·f'(t) = (c·e^{c·f t})·(c·e^{c t}) = c²·e^{c(f t + t)}.
```

Since `c < 0`, this is maximized where `h(t) := f t + t = e^{ct} + t` is **minimized**.
`h'(t) = c·e^{ct} + 1 = 0 ⟹ e^{ct} = -1/c ⟹ f t = -1/c`, and there

```
max g' = c²·e^{c·h_min} = |c|²·e^{-(1+log|c|)} = |c|²·e^{-1}/|c| = |c|/e.
```

So **`max g' = |c|/e = |log x|/e`**. For `x ≥ e^{-e}` we have `|log x| ≤ e`, hence
`max g' ≤ 1`. ⟹ `g` is non-expansive ⟹ its two fixed points `β, γ` coincide. This is
exactly the bound your `deriv_bound`/`deriv_lt_one_boundary` lemmas encode. ✔

- **Interior `x > e^{-e}`:** `|c| < e ⟹ g' < 1` strictly everywhere ⟹ `g` is a strict
  contraction ⟹ unique fixed point. Clean. (Your `two_cycle_collapse_of_lt`.)
- **Boundary `x = e^{-e}`:** `|c| = e ⟹ max g' = 1`, attained at the **single** point
  where `f t + t` is minimal (`f t = 1/e`, i.e. `t = e^{-1}`); `g' < 1` elsewhere. So
  `∫_β^γ g' < γ-β` unless `β=γ` — non-expansive is still enough because equality
  `g'=1` is hit only on a null set. Your `deriv_lt_one_boundary` (excluding the single
  `t = Real.exp (-1)`) is the right way to encode this. ✔

**One subtlety to be sure you handled:** non-expansive (`|g'|≤1`) alone does NOT give a
unique fixed point in general (the identity is a counterexample). The boundary argument
must use that `g' < 1` *off a single point*, not just `g' ≤ 1`. Your
`deriv_lt_one_boundary {t} (ht : t ≠ Real.exp (-1))` signature shows you did. Good — but
this is the one place a too-weak `≤ 1` bound would silently let a phantom 2-cycle through,
so it's worth an extra eyeball.

---

## 2. CONFIRMED: the `DIRECTION.md` Part-C tangent-subtraction is invalid ✅

You were right to abandon it. From `β ≥ A` and `γ ≥ B` one **cannot** infer
`β - γ ≥ A - B` (subtracting inequalities flips the second one's direction). The step
"Subtract: `β - γ ≥ (log y)(γ - β)`" in `DIRECTION.md` lines 89-92 is a genuine logical
error, not just loose. Do not re-attempt it. (Adding the two is valid but yields a
relation that doesn't close the gap.)

---

## 3. ELEMENTARY ALTERNATIVE to the MVT route (cross-check + optional simplification)

Your reduction is **correct** (independently re-derived): a strict 2-cycle `β<γ` gives
`β·log β = γ·log γ`, forcing `β < 1/e < γ`; with `p := -log β > 1`, `q := -log γ ∈(0,1)`,

```
p·e^{-p} = q·e^{-q},     and     x ≥ e^{-e}  ⟺  p·e^q ≤ e.
```

So a 2-cycle with `x ≥ e^{-e}` needs `p·e^q ≤ e`. The crux is the **strict** inequality

> **(★)  `p·e^{-p} = q·e^{-q}`, `p > 1 > q > 0`  ⟹  `p·e^q > e`**  (equiv. `log p + q > 1`).

`(★)` contradicts `p·e^q ≤ e` for the **whole closed interval at once** (interior gives
`p e^q < e`, boundary gives `p e^q = e`; both contradict `> e`) — so it's arguably
cleaner than splitting interior/boundary. **Here is a fully elementary proof of `(★)`
resting only on `e^m > 1+m`** (`Real.add_one_lt_exp`), the same trick as your upper half:

**Proof of (★).**
1. Log the hypothesis: `log p - p = log q - q`  ⟹  `p - log p = m + e^{-m}` where
   `m := -log q > 0` (so `q = e^{-m}`).  *(constraint C′)*
2. Goal `p·e^q > e` ⟺ `log p + q > 1`. Using C′ to substitute `log p = p - m - e^{-m}`
   and `q = e^{-m}`, this is **exactly** `p > 1 + m`.
3. **Reduce to one variable.** `G(t) := t - log t` is strictly increasing on `[1,∞)`
   (`G'(t) = 1 - 1/t > 0` on `(1,∞)`). By C′, `G(p) = m + e^{-m}`. It therefore suffices
   to show `m + e^{-m} > G(1+m) = (1+m) - log(1+m)`, i.e.
   **`log(1+m) > 1 - e^{-m}`** for `m > 0`.  *(goal D)*
4. **Prove D from `e^m > 1+m`.** Let `D(m) = log(1+m) - 1 + e^{-m}`. Then `D(0) = 0` and
   ```
   D'(m) = 1/(1+m) - e^{-m} > 0   ⟺   e^m > 1+m,
   ```
   which is `Real.add_one_lt_exp` for `m ≠ 0`. So `D` is strictly increasing on `[0,∞)`,
   hence `D(m) > D(0) = 0` for `m > 0`. ∎

Everything rides on `add_one_lt_exp` + "positive derivative ⟹ strictly increasing" (used
twice: for `G` and for `D`). **No 2-D analysis, no Lipschitz/Banach machinery, no MVT
plumbing beyond the standard monotone-from-deriv lemma.** This is the "tight inequality,
slack bounds won't work" you flagged — and the reason it's tight (difference is
`O((1-q)²)` at the bifurcation) is precisely why the proof must route through the
*derivative* `D'`, never a first-order slack bound.

**Why mention it if you're already done:** (a) it's an independent witness that the
`e^{-e}` threshold is right, corroborating your axiom-clean discharge on the tight part;
(b) if a later pass wants to shrink `EngineLower.lean`'s analytic surface, this collapses
the boundary+interior cases into one strict scalar inequality.

---

## 4. What Lóczi §3 (arXiv:1908.05559) actually does — and its limit

Lóczi's lower-bound argument is the classical **linearization / cobweb** one, NOT a
self-contained elementary global proof. The mechanism: at the fixed point `y* = x^{y*}`
the iteration map `z(y) = x^y` has derivative

```
z'(y*) = x^{y*}·log x = y*·log x = log y*      (using log y* = y*·log x).
```

Local stability needs `|z'(y*)| < 1`, i.e. `|log y*| < 1`, i.e. `-1 < log y* < 1`, i.e.
`1/e < y* < e`; inverting `x = y*^{1/y*}` gives the interval `e^{-e} ≤ x ≤ e^{1/e}`. The
threshold `x = e^{-e}` is exactly where `z'(y*) = -1` (multiplier `-1`, the
period-doubling/2-cycle bifurcation). For `x < e^{-e}` the fixed point is repelling and a
**stable 2-cycle** appears.

**Caveat for porting:** this is *local* (linearized) stability — it does not by itself
prove the *global* `β = γ`. The rigorous global step is exactly what your even/odd
monotone-subsequence framework (`tendsto_of_even_odd` + `g_mono`) plus the crux
(`two_cycle_collapse`) already supplies. So **Lóczi §3 offers no lemma chain to port
beyond confirming the threshold mechanism** — your contraction bound (§1) and the
elementary `(★)` (§3) are both *more* rigorous than the paper on the crux itself. Don't
wait on the paper; you already have the better argument.

---

## 5. Existing Lean/mathlib formalization of the power-tower interval: NONE found

Searched: `reservoir-grep` over all 705 Reservoir packages (`tower` hits are all
algebra/Postnikov/scalar towers — unrelated), the zulip-ro "Is there code for X?" ITC
corpus (no tetration / infinite-power-tower / `e^{-e}` topic), and WebSearch. No mathlib
declaration and no third-party Lean repo formalizes the convergence interval
`[e^{-e}, e^{1/e}]` or the `e^{-e}` lower bound. **This repo's `PowerTower/` is, as far as
I can find, the first.** (Worth noting for the eventual `formal-conjectures`/blog framing.)

---

## 6. mathlib v4.29.1 lemma-name reference (verified against this repo's `.lake`)

- `Real.add_one_lt_exp {x : ℝ} (hx : x ≠ 0) : x + 1 < Real.exp x` — `Analysis/Complex/Exponential.lean`. (The engine of §3.)
- `Real.add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` — same file.
- `Real.rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z` — `Analysis/SpecialFunctions/Pow/Real.lean`. (Strict-anti for base `<1`.)
- Positive-derivative ⟹ strict mono (the §3 monotonicity, used for `G` and `D`):
  `strictMonoOn_of_deriv_pos (hs : Convex ℝ s) (hf : ContinuousOn f s) (hf' : ∀ x ∈ interior s, 0 < deriv f x) : StrictMonoOn f s` — `Analysis/Calculus/MeanValue.lean`. (Global form: `strictMono_of_deriv_pos`.) ⚠️ verify exact name on your toolchain.
- If you ever prefer the explicit Lipschitz/MVT route for §1:
  `exists_hasDerivAt_eq_slope` (MVT), `Convex.lipschitzOnWith_of_nnorm_hasDerivWithin_le`,
  and `Real.hasDerivAt_log (hx : x ≠ 0) : HasDerivAt Real.log x⁻¹ x` for `G'`.
