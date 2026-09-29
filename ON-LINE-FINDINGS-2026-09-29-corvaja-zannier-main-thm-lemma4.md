# ON-LINE-FINDINGS 2026-09-29: Corvaja–Zannier (2004), Main Theorem + Lemma 4

**Request:** `ON-LINE-REQUEST.md` of 2026-09-28 (phase 9, commit `90abbbd`): verbatim CZ Main
Theorem, verbatim Lemma 4 + its machinery, and whether Lemma 4 is subspace-strength.

**Source read:** `papers/corvaja-zannier-2004-powers-algebraic.txt` (arXiv `math/0403522v1`,
30 Mar 2004, 12 pp.), already in the repo since 2026-09-28 22:51.  ⚠️ This is the **arXiv preprint**,
not the Acta Math. 193 (2004) 175–191 typeset version: page numbers below are preprint pages, and
I did not diff against the journal text.  The statements are also frozen verbatim as
`Literature.Stephan2026CZMain` / `Stephan2026CZLemma4` (see `DIRECTION.md` phase 13b), which is the
stronger source for the Lean route.

**Current-state note:** the request predates phases 10–17.  `DIRECTION.md` now routes both phase-9
leaves through Stephan's machine-checked CZ (`CorvajaZannierStephan.lean`, phase 13b, parked).  The
answers below matter mainly for Q3 and for the `corvajaZannier_lemma4` docstring.

## 1. Main Theorem (preprint p. 2) - verbatim modulo PDF extraction

> **Definition.** We call a (real) algebraic number α a *pseudo-Pisot number* if:
> (i) |α| > 1 and all its conjugates have (complex) absolute value strictly less then 1;
> (ii) α has an integral trace: Tr_{ℚ(α)/ℚ}(α) ∈ ℤ.

(In (i), "all its conjugates" means the conjugates *other than α*.  The algebraic integers among
pseudo-Pisot numbers are exactly the Pisot numbers.)

> **Main Theorem.** Let Γ ⊂ ℚ̄^× be a finitely generated multiplicative group of algebraic numbers,
> let δ ∈ ℚ̄^× be a non zero algebraic number and let ε > 0 be fixed.  Then there are only finitely
> many pairs (q, u) ∈ ℤ × Γ with d = [ℚ(u) : ℚ] such that |δqu| > 1, δqu is not a pseudo-Pisot
> number and
>
>   0 < ‖δqu‖ < H(u)^{−ε} q^{−d−ε}.   (1.1)

- `‖x‖` = distance to the nearest integer.
- `H` = **absolute** multiplicative Weil height, `H(x) = ∏_{v ∈ M_K} max{1, |x|_v}` with places
  normalized relative to `K` so the product formula holds (§2).
- `δ`, `u`, `Γ` have no further definition beyond the statement.  In the proof Γ is enlarged to the
  S-units `O_S^×` of a Galois number field `K ∋ δ`, with `S` Galois-stable and containing `M_∞`.
- Theorem 1 (the Mahler application) uses `δ = 1`, `q = 1`, `u = α^n`; Lemma 5 uses `q = q_{h−1}(n)`.
  Our `corvajaZannier_dichotomy` is the `δ = 1`, `Γ = ⟨α⟩` specialisation, with `H(α^n) = H(α)^n`
  turning `H(u)^{−ε}` into `e^{−ε' n}`.

Proof structure: Lemma 1 (Subspace Theorem, Schmidt 1D′), Lemma 2 (unit-equation theorem of
Evertse / van der Poorten–Schlickewei), Lemma 3 (the key new Subspace application, which descends
to a proper subfield `k′ ⊂ k`), then induction on a strictly decreasing chain of subfields.
(Minor slip in the induction as printed: the bound drifts from `q^{−d−ε}` to `q^{−1−ε}`.  Harmless
for us, since we fix `q`.)

## 2. Lemma 4 (preprint pp. 7–8) - verbatim modulo extraction

> **Lemma 4.** Let α be an algebraic number.  Suppose that for all n in an infinite set Ξ ⊂ ℕ, there
> exists a positive integer q_n ∈ ℤ such that the sequence Ξ ∋ n ↦ q_n satisfies
>
>   lim_{n→∞} (log q_n)/n = 0   and   Tr_{ℚ(α)/ℚ}(q_n αⁿ) ∈ ℤ ∖ {0}
>
> (the limit being taken for n ∈ Ξ).  Then α is either the h-th root of a rational number (for some
> positive integer h) or an algebraic integer.

Note: CZ allow **varying** `q_n` with `log q_n = o(n)`.  Our leaf fixes `q`, which is weaker and so
still implied.  It uses the trace over `ℚ(α)`, not a power sum over the minpoly of `αⁿ`, and has no
`hsmall` hypothesis.  Check that your `htr` (sum of the `aroots` of `minpoly ℚ (α^n)`) matches: it
differs from `Tr_{ℚ(α)/ℚ}(αⁿ)` by the factor `[ℚ(α) : ℚ(αⁿ)]` whenever `ℚ(αⁿ) ⊊ ℚ(α)`.  That
changes "nonzero integer" to "nonzero rational with bounded denominator", which your leaf absorbs
but a faithful `Literature/` statement would not.

**Proof machinery - the answer to "which machinery":**
1. Let `K` be the Galois closure and `h` the order of the torsion of `K^×`.  Pigeonhole `n = r + hm`.
2. Take `σ_1..σ_d` = the embeddings of `ℚ(α^h)`.  If `d = 1`, then `α^h ∈ ℚ` and you are done.
3. If α is not integral, pick a **finite place `w`** with `|α|_w > 1`.  Write
   `Tr(α^{r+hm}) = Σ_i λ_i σ_i(α^h)^m` with `λ_i = Σ_{τ ∈ T_i} τ(α^r)`, not all zero.
4. Integrality of `Tr(q_n αⁿ)` gives `|Tr(αⁿ)|_w ≤ |q_n|_w^{−1}`.  Then `log q_n = o(n)` gives
   `|Σ λ_i σ_i(α^{hm})|_w < |α^{hm}|_w · H(α^{hm})^{−ε}`.
5. **Lemma 1 (Subspace Theorem) at the non-archimedean place `w`** gives a nontrivial linear
   relation `Σ a_i σ_i(α^h)^m = 0` for infinitely many `m`.
6. **Skolem–Mahler–Lech** gives some `(σ_i(α)/σ_j(α))^h` equal to a root of unity, hence to 1 by the
   choice of `h`.  So `σ_i = σ_j` on `ℚ(α^h)`, a contradiction.

CZ: *"It is essentially an application of Lemma 1, so it still depends on the Subspace Theorem."*
There is **no** S-unit reduction and **no** appeal to the Main Theorem.  It is a direct p-adic Subspace
application followed by SML.

## 3. Is Lemma 4 subspace-strength?

**As CZ prove it: yes.**  Their proof runs through the Subspace Theorem (step 5).  The
`corvajaZannier_lemma4` docstring's *"Unlike `corvajaZannier_dichotomy` this is not
subspace-strength"* is Dubickas-derived and does **not** describe CZ's proof.  Reword it before it
reaches a `Literature/` statement.

**As a statement: probably not, but unproven here.**  The repo's own residual
(`isIntegral_of_bounded_den_mulClosed`, the Newton-identity valuation argument) already avoids
Subspace for multiplicatively closed index sets.  CZ's step 5 is doing the work of your tie case.
What your route still needs is the **p-adic SML step**: `v(Σ u_i^N) → 0` along an infinite `N`-set
implies some `u_i/u_j` is a root of unity.  That is a weaker target than Subspace, since
SML-type statements for a single power sum are classical (Skolem's p-adic analytic method), but it is
not elementary either.  The phase-9 plan "close Lemma 4 first, leave Subspace last" stays coherent
**only** along the repo's valuation route, not by following CZ.  Since phase 13b now takes Lemma 4
from `Stephan2026CZLemma4` anyway, the question may be moot.
