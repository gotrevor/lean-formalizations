# Can CDT's arithmetic holonomy bounds reach ζ(5) over ℝ?  A Beukers weight-6 probe

**2026-10-24.**  Probe: `papers/cdt-weight6-fuel.py <weight> <levels…>`.  Context: Calegari–Dimitrov–Tang (CDT), *The linear independence of 1, ζ(2), and L(2,χ₋₃)* (arXiv:2408.15403) and the ICM text (arXiv:2510.04156).  KB leaf: `claude/knowledge/core/projects/lean-journey/reference/2026-10-24-cdt-holonomy-bounds-odd-zetas.md`.

## Question

CDT's footnote: over ℝ, π-power periods mix into every known local system, so "we know of no simple analogous construction for ζ(2k+1) ∈ ℝ".  Beukers (1987) realizes ζ(3) *alone* with a Fricke-eigen weight-4 Eisenstein combination whose Euler factor P(s) kills the contaminating periods.  Does the weight-6 analogue realize ζ(5) alone, with enough fuel for CDT's bound?

## Setup

Write F = Σ_{d|N} c'_d G_d with G_d = d^{k/2} E_k(dτ).  Fricke swaps G_d and G_{N/d}, so an eigenform has c'_{N/d} = ε c'_d.  Its L-function is P(s) ζ(s) ζ(s−k+1), with P(s) = Σ c'_d d^{k/2−s}, and **P(k−s) = ε N^{s−k/2} P(s)**.  The Eichler integral's Fricke period polynomial carries:

- ζ(2k−1) at the degrees 0 and k−2;
- π-powers times P(2j) at the odd degrees;
- nothing at L(F, k/2) when ε = −1.

So the weight-2k realization of ζ(2k−1) alone needs P(0) = 0 (no constant term) and P(2j) = 0 for 0 < 2j < k−1.  The functional equation pairs these up.  It also needs P(k−1) ≠ 0.

- **k = 4 (ζ(3)):** for ε = −1 only P(0) = 0 is needed.  That takes a 2-dimensional eigenspace, which level 6 provides (Beukers).
- **k = 6 (ζ(5)):** P(0) = P(2) = 0, with P(4) following.  That takes a ≥ 3-dimensional eigenspace, so at least 6 divisors.

Fuel is computed in the Fricke Hauptmodul u = T = t + t∘w_N, with t an eta-quotient Hauptmodul of X₀(N).  H = E·(f − c) is single-valued at i/√N, and its singular u-values S are the other cusps and the other Fricke-coset elliptic points.  The probe reports disc fuel −log max|u_s − κ| and the univalent bound log(4/diam S).

**CDT thresholds** come from the univalent bound m ≤ log ρ/(log ρ − τ), using best-first denominator types:

| Case | Functions | Rate τ | Needed log ρ |
|---|---|---|---|
| ζ(3) | {1, H, ∂H} | 8/3 | > 4 |
| ζ(5) | {1, H, …, ∂³H} | 4.8 | > 6 |

The bare void condition alone needs log|φ′(0)| > 3.75, using the pair {1, H}.

## Results (`./papers/cdt-weight6-fuel.py 4 6` and `… 6 6 8 9 10 12 16 18 25`)

| N | weight | Eisenstein combination | non-base cusps (u) | disc fuel | univalent bound |
|---|---|---|---|---|---|
| 6 | 4 | ε=−1, unique (Beukers) ✅ | 1 (cusps 1/2 ~ 1/3) | **3.5255** = log(√2+1)⁴ ✅ | **4.9118** = log 4(√2+1)⁴ ✅ |
| 6, 8, 9, 10, 25 | 6 | **none** | – | – | – |
| 12 | 6 | ε=±1, one each | 0, 1 | 0 | 1.32 |
| 16 | 6 | ε=+1 only | 2, 4 | 0 | 0.69 |
| 18 | 6 | ε=±1, one each | 1, 1.5±0.87i | 0 | 0.84 |

The level-6 weight-4 row is the known-answer control, and it reproduces Beukers and Dimitrov exactly.

## Mechanism: purity costs cusps, and cusps cost fuel

Each extra P(2j) = 0 condition needs another dimension of eigenspace, which means more cusp classes on X₀(N)/w_N.  For ζ(5), at least two non-base cusp classes remain.  Their Hauptmodul values were distance ≥ 1 apart at every level tested.

A CDT template φ must omit every point where H has nontrivial monodromy, and cusps carry unipotent monodromy, so φ omits both cusp values.  φ also takes the base point only at the centre.  The universal cover of the thrice-punctured sphere, normalized by the λ-function, is extremal for that.  Hence **log|φ′(0)| ≤ log(16/|u₁ − u₂|) ≤ log 16 ≈ 2.77**, below the void threshold of 3.75, for **any** template, univalent or not.

ζ(3) escapes because it needs only one cusp class besides the base point.  Fricke merges cusps 1/2 and 1/3 into it, and that cusp sits next to an elliptic point.  That pair is the 4.91.

## What would reopen it (each untested)

- **Padding with integral G-functions** (CDT's §10 "pure functions"): enough ℚ(x)-independent ℤ⟦x⟧ functions that are single-valued on the template to drive τ = 5(1 − u²/m²) under 2.77.  A rough count needs on the order of 15 of them.  At |φ′(0)| ≈ 16 that is the unbounded-denominators borderline, where CDT's numerators blow up (CDT21 §2.1).  Odds this works: ≤ 5%.
- **Levels where X₀(N) has positive genus** but an Atkin–Lehner quotient has genus 0 (20, 30, …).  The full AL group is ruled out: for squarefree N, P(s) factors as ∏(1 + ε_p p^{k/2−s}), so P(0) ≠ 0.  Intermediate AL groups keep eigenspace dimension = cusp-class count, so the same "≥ 2 non-base cusps" argument applies.  It relies on the cusp values staying ≥ 1 apart, which was observed at every level tested but is not proved.
- **A non-modular ODE with ζ(5) alone as an archimedean Apéry limit.**  CDT know none, and neither do we.

## The three-number route (1, ζ(3), ζ(5))

CDT's Theorem A needs **simultaneous** Apéry limits that share one function: A(B − L/2) and A(C − ζ(2)/4), both overconvergent at the same point.  Beukers-type realizations put ζ(3) on a weight-2 E and ζ(5) on a weight-4 E′.  E′/E² is a modular function, so E′ is not a ℚ(x)-multiple of E, and the two Apéry limits do not share an A.  Ball–Rivoal forms are type I, a single form p₀ + p₃ζ(3) + p₅ζ(5), not simultaneous approximations.  I know of no common-denominator simultaneous approximations to ζ(3) and ζ(5) (~70%, not searched).

## Caveats

- **Elliptic-point numerics** at small Im τ (N = 18, 25) produce near-duplicate values.  These are artifacts of a truncated eta product.  They don't affect the bound, which the cusps dominate.
- **The λ-extremality step** is the standard argument behind CDT21's 1/16 threshold.  I have not written it out.
- **Verdict:** the weight-6 Beukers route to ζ(5) is closed at every genus-0 X₀(N) level (~85%).  The lane stays closed unless padding or a non-modular module turns up.
