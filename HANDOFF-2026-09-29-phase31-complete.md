# HANDOFF 2026-09-29 — phase 31 COMPLETE: the projective-order lemma

`src/LeanFormalizations/NumberTheory/Mills/Projective.lean` is **sorry-free**; all four frozen
statements are machine-checked and `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).
Full `lake build` green; `scripts/fact-graph` rerun (30 edges, 29 hypotheses).

## The four

| statement | route |
|---|---|
| `dvd_trace_of_irreducible_mod` | `K = AdjoinRoot F` (`F` = reduced charpoly) is a field of `p³` elements; `x^(p²+p+1)` is Frobenius-fixed hence in the prime field; `9 ∤ p²+p+1`; `m ≥ 1` kills the 3-part of the projective order `d`; `j = φ(d)` gives `x^(3^(m+j)) = λ x^(3^m)`; transfer via `F ∣ X^(3^(m+j)) − C λ·X^(3^m)` + Cayley–Hamilton |
| `not_irreducible_mod_eventually` | mirrors `lt_padicValNat_glCard`: the prime `t_k` would divide the strictly larger prime `t_(k+j)` |
| `composite_of_irreducible_divisor` | iterate the lemma for arbitrarily late `k` with `q ∣ t_k`; `t_k → +∞` makes `t_k > q`, so `t_k` has a proper divisor |
| `mills_reducible_mod_primes` | `exists_companion_root` (see below) + the second item, rewriting `((⌊·⌋₊ : ℤ)).toNat` |

## Two hypotheses are not needed

`p ≠ 3` and `p ∤ det C` are both unused in `dvd_trace_of_irreducible_mod`.  `9` never divides
`p²+p+1` (`decide` over `ZMod 9`), *including* at `p = 3`; and `AdjoinRoot.root F ≠ 0` follows from
`F.natDegree = 3 > 1 = natDegree X`, not from the determinant.  The statements being frozen, the
hypotheses are kept.

## Infrastructure added (reusable)

* `exists_algebraMap_eq_of_pow_eq` — in a finite field `K` over `ZMod p`, `z^p = z ⟹ z` is in the
  image of `algebraMap`.  Proof: `X^p − X` has at most `p` roots and the `p` scalars are all roots,
  so the root finset *is* the scalar finset.  (mathlib has no such lemma at this pin.)
* `not_nine_dvd : ¬ 9 ∣ p²+p+1` for every `p : ℕ`, by `decide` over `ZMod 9`.
* `companion3_charpoly : (companion3 a b c).charpoly = X³ + C a·X² + C b·X + C c`.
* `exists_companion_root` — a private restatement of the frozen
  `exists_companion_of_algebraic_mills` with the extra conclusion that `A^(3^m)` is a root of the
  charpoly over `ℝ`.  Its proof is a copy of the ThreeAdic one (including the private
  `exists_vieta_of_cubic_pisot`) plus a `linear_combination` off the Vieta relations.  **If
  ThreeAdic is ever unfrozen, move the root conclusion there and delete the copy.**

## Gotchas

1. `AdjoinRoot.lift` wants a *commutative* target, so it cannot map into a matrix ring.  Do the
   transfer at polynomial level instead: `AdjoinRoot.mk_eq_zero` gives divisibility, then
   `Polynomial.aeval D` (which is fine for noncommutative `A`) plus `Matrix.aeval_self_charpoly`.
2. `Module.Finite.of_basis`, not `FiniteDimensional.of_fintype_basis` (gone at this pin).
3. `QuotientGroup.eq'` does not exist; use `QuotientGroup.mk'_eq_mk' : mk' N x = mk' N y ↔ ∃ z ∈ N, x * z = y`.
4. `ZMod.natCast_zmod_eq_zero_iff_dvd` does not exist for `ℕ` (only the `ℤ` version
   `intCast_zmod_eq_zero_iff_dvd`); use `CharP.cast_eq_zero_iff`.
5. `AdjoinRoot.of F` vs `algebraMap _ (AdjoinRoot F)`: bridge with `AdjoinRoot.algebraMap_eq`.

## What this does and does not buy

It restricts which primes can be Mills primes (Frobenius at a late Mills prime cannot be a 3-cycle)
and gives a one-prime certificate per `β`.  It does **not** eliminate any of the six coefficient
classes mod 3 — see `PROBE-MILLS-PROJECTIVE.md` § "The new missing step": the open target is to
force some prime `q ≠ 3` with `f` irreducible mod `q` to divide the sparse sequence `t_k`.
