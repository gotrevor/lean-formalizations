# HANDOFF 2026-09-30 — phase 55 COMPLETE: Theorem D, quadratic case

Branch `main`, HEAD `4c28ffe` (+ this doc), `lake build` green (8776 jobs).

## Result

`src/LeanFormalizations/NumberTheory/Mills/TheoremDQuadratic.lean` is **sorry-free**.
The frozen headline

```
floor_pow_prime_pow_add_not_prime :
  α + β = a → α·β = b → 1 < α → |β| < 1 → ¬IsSquare (a²−4b) →
  c.Prime → ¬ c ∣ b → ¬ c ∣ a²−4b → 4 ≤ s →
  ∃ᶠ n in atTop, ¬ (⌊α^(c^n+s)⌋₊).Prime
```

is **axiom-clean**: `[propext, Classical.choice, Quot.sound]`.
`scripts/fact-graph` rerun: 30 edges, 31 hypotheses.

## The route actually taken (differs from the file header)

The header proposed the paper route: `K = ℚ(α, ζ_(q−1))`, a prime `𝔓 ∣ c` of `𝒪_K`, Teichmüller
representatives, Krull separation, then a complex embedding.  **None of that is used.**  The
insight that collapsed it:

> Everything the Teichmüller limit `T = x·I + y·C` contributes is three *integer polynomial
> equations* in `(x, y)`: `A_Q(x,y) = 1`, `B_Q(x,y) = 0` (i.e. `T^Q = I`), and
> `x·V_s + y·V_(s+1) = t` (i.e. `tr(T·C^s) = t`), where `(x·I+y·C)^N = A_N·I + B_N·C`.

Because these have rational coefficients, they can be read in ℤ, ℚ, ℂ and `MvPolynomial` alike
(`torsionPair_map`), so `u = x+yα`, `v = x+yβ` satisfy `u^Q = A_Q + B_Q·α = 1` over ℂ *by the same
polynomial identity* — no embedding of one field into another is ever needed.

The `c`-adic → archimedean transfer is then **Nullstellensatz + integrality**
(`exists_complex_zero_of_all_levels`): a system with integer solutions mod `c^k` for every `k` but
no complex solution would satisfy `1 = Σ gᵢfᵢ` over ℚ; clearing the `gᵢ`'s denominators
(`exists_denominator`) yields a *nonzero integer* `D` with `D = Σ zᵢfᵢ(p)` at every integer point,
so a level-`k` point forces `c^k ∣ D` for all `k`.

## Map of the file (all proved)

| step | lemma | content |
|---|---|---|
| 1a | `pow_add_pow_eq_lucasV`, `floor_pow_eq_lucasV_add` | `⌊α^N⌋ = V_N(a,b) + ε`, `ε ∈ {0,−1}` |
| — | `compMat`, `compMat_sq`, `trace_compMat_pow` | companion matrix bridge, `tr(C^N) = V_N` |
| 1b | `lucasV_congr_of_order`, `lucasV_stuck_period` | the prime-as-modulus filter |
| — | `golden_le_sq`, `floor_pow_strictMono` | `α ≥ φ`; the floors strictly increase |
| 1c | `good_unbounded` | good indices unbounded (global choice of periods + phase 44 Lemma 3) |
| 1d | `stuck_alternation` | at a stuck `n`, `ε` alternates |
| 1e | `good_window`, `pow_dvd_sub_or_add_of_lt_padicValNat_all` | `p_n ≡ ±1 mod c^(n/2)`, **including `c = 2`** |
| 1f | `exists_class_frequently`, `index_le_floor` | pigeonhole on `(n mod 2, t)`; linear growth |
| 2 | `torsion_congr_levels`, `compMat_pow_congr_one` | integer solutions mod `c^k`, `Q = |GL₂(𝔽_c)|` |
| 3 | `exists_complex_zero_of_all_levels`, `exists_denominator`, `torsionPair_map` | the transfer |
| 4 | `eq_of_mem_pow_all` | Krull (kept; now unused by the main line) |
| 5 | `alpha_pow_four_gt_three`, `spectral_ne_small_int` | `α^4 > 3`; `‖uα^s+vβ^s‖ > 2 ≥ |t|` |

## Two corrections made to the plan, worth remembering

* **The residue modulus is forced to be 2.**  `spectral_identity` was first stated over a free
  modulus `f`; that version is *false* at `f = 1`, since `ζᵢ^(c^n)` genuinely depends on `n mod 2`.
  `c² ≡ 1 (mod q−1)` for `q ∈ {c, c²}` pins the Teichmüller period to a divisor of 2.
* **`c = 2` needed its own window.**  Phase 37's `pow_dvd_sub_or_add_of_lt_padicValNat` assumes `c`
  odd (`c` divides at most one of `p ∓ 1`).  At `c = 2` both are even but **`4` divides at most
  one**, so `min(v₂(p−1), v₂(p+1)) = 1` and the same bound goes through.

## Two proofs where integrality of `b` did the real work

`alpha_pow_four_gt_three` (`α⁴ > 3`) and `golden_le_sq` (`α + 1 ≤ α²`) both avoid square roots and
the discriminant hypothesis entirely: bounding `α` forces `a = α+β` into a tiny integer range, and
then `b = α(a−α)` is pinned strictly between consecutive integers.

## Lean gotchas from this phase

* `ring` does **not** close matrix power identities (noncommutative) — use `pow_add`, `← pow_succ`.
* `MvPolynomial.C a` gets normalised to `↑a` (intCast) by `simp`, breaking later `rw`s; state
  polynomials with `((a : ℤ) : MvPolynomial σ ℤ)` from the start and simp with `map_intCast`.
* `MvPolynomial.eval₂_comp f g p : f (eval g p) = eval₂ f (f ∘ g) p` is the lemma for pushing a
  coefficient ring hom through an evaluation.
* mathlib's Nullstellensatz needs `[Finite σ]`.
* `Rat.den_mul_eq_num` is the clearing-denominators primitive.

## Next

`DIRECTION.md` phase 55 is met.  Untouched designated-open work elsewhere: the two active-crux
`sorry`s in `NumberTheory/Transcendence/DubickasNoSubspace.lean` (see
`PENDING_WORK.md` §PHASE 9) — not part of this phase, deliberately not attacked.
