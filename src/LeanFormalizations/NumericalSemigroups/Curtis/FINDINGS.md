# Curtis 1990 — what the proof gives for free

Two consequences fall out of the formalization beyond the headline "no closed
formula". Each is a place where a careless *reading* of the Lean statements could
go wrong, so they are recorded here explicitly. Both are backed by checked theorems
in this directory.

## 1. Stronger than "not a polynomial" — "not algebraic"

`no_polynomial_relation` (in `Statement.lean`) is not merely "the Frobenius number
is not given by a single polynomial in the generators". It says **no nonzero
polynomial `F ∈ ℂ[X₁,X₂,X₃,Y]` vanishes on the graph at all** — i.e. the point
`(s₁, s₂, s₃, g⟨s₁,s₂,s₃⟩)` lies on *no proper hypersurface* of `ℂ⁴`. Equivalently,
the Frobenius number of a triple is **not algebraic** over its generators, and the
graph of the map `(s₁,s₂,s₃) ↦ g` is Zariski-dense in `ℂ⁴`.

The cleanest way to *feel* the strength of this is the `n = 2` contrast, formalized
in `Boundary.lean` as `n2_polynomial_relation_exists`: for **two** generators the
analogous statement is **false** — a single nonzero polynomial,
`X₀·X₁ − X₀ − X₁ − Y` (Sylvester / Chicken-McNugget), *does* vanish on the whole
2-generator graph. So the graph there lies on a hypersurface; Curtis's theorem is
exactly the statement that this collapses at `n = 3`. The content sits precisely on
the `n = 2` / `n = 3` boundary, not at "no formula for anything".

The "no finite menu of polynomials" form (`no_finite_polynomial_formula` and its
`ℤ`/`ℚ`/any-`ℂ`-algebra variants) is then a one-line corollary: a hypothetical menu
`f₀,…,f_{k−1}` gives the nonzero `F = ∏ (fᵢ − Y)`, which would vanish on the graph,
contradicting `no_polynomial_relation`.

## 2. Sub-families still have closed formulas — only a *universal* one is forbidden

Curtis forbids a **single formula valid over all admissible triples**, NOT formulas
for restricted families. Concretely:

- **`n = 2` (pairs):** Sylvester's `g(a,b) = ab − a − b` (mathlib's
  `frobeniusNumber_pair`); used as the witness in `n2_polynomial_relation_exists`.
- **Arithmetic progressions** `⟨a, a+d, a+2d, …⟩` have a known closed Frobenius
  formula (Roberts / Brauer); a finite sub-family, so no contradiction.

The Lean statement is the "no finite menu covering **all** admissible triples" form,
and must not be misread as "no per-family formula exists". The impossibility is
about a universal formula only. (`symmetric_guess_not_a_formula` in `Boundary.lean`
makes the universal claim tangible: the natural symmetric degree-2 guess
`Σ XᵢXⱼ − Σ Xᵢ` already fails on the single admissible triple `⟨3,7,8⟩`, giving `83`
instead of the true value `5`.)

## Faithfulness anchors

`Anchors.lean` pins the definitions to six hand-checked witnesses where mathlib's
`FrobeniusNumber` and Curtis's Lemma-2 value formula `(k−2)·s₂ + s₃ − s₁` agree:
`⟨3,7,8⟩→5`, `⟨3,7,11⟩→8`, `⟨3,13,14⟩→11`, `⟨5,11,23⟩→29` (two of these also proved
a second way, directly from the definition). These rule out a *vacuously* true
mis-statement of the headline. One further anchor, `frobeniusNumber_6_9_20` (the
classic Chicken-McNugget number `43`), checks mathlib's `FrobeniusNumber` on a
triple *outside* Curtis's admissible family (`6` is not prime), exercising the
predicate on a different surface.
