/-
# Wiring edges between the Diophantine literature inputs

Each theorem derives one literature `Prop` from another, so the bedrock shrinks to fewer,
deeper assumptions.  Sources (local-only, gitignored): `papers/mahler-1957-fractional-parts-ii`,
`papers/ridout-1957-rational-approximations`, `papers/ridout-1958-p-adic-roth` (`.pdf`/`.txt`).

## `mahler_of_ridout1957` — Mahler (1957), §3, verbatim route

Let `α = u/v` in lowest terms, `u > v ≥ 2`; put `λ = log v / log u ∈ (0, 1)`, so `v = u^λ`.
Take `P` = prime factors of `v`, `Q` = prime factors of `u`, `ϑ = 1` (Ridout's `α`),
`μ = 1 − λ`, `ν = 0`, `c = 2`, and `κ = 1 − λ + ε'` for a small `ε' > 0` tied to `ε`
(Mahler's `κ` makes `(u/v)^n · u^(−κ n) = e^(−ε n)`, i.e. `κ = 1 − λ + ε / log u`).
For each `n` let `p* = round((u/v)^n)` (Mahler's "integer nearest to `ϑ(u/v)^n`"),
`p = p* vⁿ`, `q = uⁿ` (`q* = 1`).  For large `n`: `0 < p* < 2 (u/v)ⁿ = 2 v^(n(1−λ)/λ)`…
Mahler concludes `0 < p* ≤ c p^μ` (condition (4)).  `(u/v)ⁿ` is not an integer (`v ≥ 2`, coprime),
so `p/q ≠ 1`; Ridout's finiteness then says `|1 − p/q| ≥ q^(−κ)` for all but finitely many `n`,
i.e. `|(u/v)ⁿ − p*| ≥ (u/v)ⁿ u^(−κn) = e^(−εn)`.  ⚠️ Check Mahler's exponent bookkeeping in
the PDF (`papers/mahler-1957-fractional-parts-ii.pdf`, p. 123–124) rather than this sketch; the
text extraction dropped his displayed formulas, so render the page if needed.  Distinct `n`
give distinct `q = uⁿ`, so finitely many `(p, q)` means finitely many `n`.

## `ridoutSUnitDen_of_ridout1957`
`μ = 1`, `ν = 0`, `P = ∅`: `p* = p`, `q* = 1`, `q` an `S`-unit; exponent `1 + δ > 1`.  Reduce
the lowest-terms rational to a pair.  (`α` irrational ⇒ `α − p/q ≠ 0`.)

## `roth_of_ridout1958`
`t = 0` (no primes); `f` = the minimal polynomial of `α` scaled to `ℤ[X]` (degree `≥ 2` since `α`
is irrational).  For bounded `α`, `max(|h|, q) ≤ (|α| + 1) q` once `|α − h/q| < 1`, so
`|α − h/q| < q^(−(2+δ))` implies Ridout's inequality with `κ = 2 + δ/2` for large `q`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Diophantine

open LeanFormalizations.Literature

/-- **Mahler (1957) from Ridout (1957)**, as in Mahler's §3. -/
theorem mahler_of_ridout1957 (h : Ridout1957) : Mahler1957 := by
  sorry

/-- The `S`-unit-denominator corollary from Ridout's 1957 theorem. -/
theorem ridoutSUnitDen_of_ridout1957 (h : Ridout1957) : Ridout1957SUnitDen := by
  sorry

/-- Roth's theorem is the `t = 0` case of Ridout's `p`-adic theorem. -/
theorem roth_of_ridout1958 (h : Ridout1958) : Roth1955 := by
  sorry

end LeanFormalizations.Diophantine
