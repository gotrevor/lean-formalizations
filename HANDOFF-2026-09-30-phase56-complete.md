# HANDOFF 2026-09-30 — phase 56 COMPLETE: Theorem D in **every degree** + the plastic number

`lake build` green (8777 jobs).  `src/LeanFormalizations/NumberTheory/Mills/TheoremDGeneral.lean`
is **sorry-free**, and both frozen statements are **axiom-clean**
(`[propext, Classical.choice, Quot.sound]`):

```
floor_pow_prime_pow_add_not_prime_general :
  f.Monic → Irreducible f → 2 ≤ f.natDegree → aeval α f = 0 → 1 < α →
  (∀ z ∈ (f.map ℤ→ℂ).roots, z ≠ α → ‖z‖ < 1) →
  c.Prime → ¬ c ∣ f.coeff 0 → (f.natDegree : ℝ) + 1 < α ^ s →
  ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime

plastic_floor_pow_prime_pow_add_not_prime :
  ρ ^ 3 = ρ + 1 → 1 < ρ → c.Prime → ∃ᶠ n in atTop, ¬ (⌊ρ ^ (c ^ n + 5)⌋₊).Prime
```

`scripts/fact-graph` rerun: 30 edges, 31 hypotheses.

## The two structural insights that made degree `d` work

### 1. The Vandermonde conjugation (lap 1) — replaces "C is diagonalizable"

Phase 55 got the whole spectral side from explicit `2 × 2` formulas; the file header proposed
diagonalisability for degree `d`.  Neither is needed.  For a root `z` of monic `f`, the **row**
`(1, z, …, z^(d-1))` is a left eigenvector of the companion matrix (`sum_pow_mul_compM`: the
`j + 1 = d` coordinate is exactly `f(z) = 0` plus monicity), so

```
vandermonde e * compM f = diagonal e * vandermonde e
```

and `vandermonde e` is invertible at distinct roots.  *One* conjugation then yields **both** facts
the size argument needs — no diagonalisability theory, no minimal polynomial, no field embeddings:

* `trace_polyMat_mul_compM_pow : tr (P(C) · C^s) = ∑_k P(e k) · (e k)^s`
* `polyVal_pow_eq_one : P(C)^Q = 1 → P(e k)^Q = 1`

It also gives `traceSeq_eq_root_sum` (`V_N = ∑_k (e k)^N`) for free, i.e. step 1 with no Newton
identities.

### 2. `w := p_n` makes the trace congruence exact (lap 7)

Phase 55 carried a small integer `t = ±1 − ε` and pigeonholed on `(n mod 2, t)`, because its window
gives `p ≡ ±1`.  In degree `d` the window gives `p^i ≡ 1 (mod c^e)` for some `i ≤ d` — a genuine
`c`-adic root of unity — so the Teichmüller residue **must** enter the system as a variable `w`
with `w^m = 1`.  The payoff: taking `w = p_n` makes `V_(c^n+s) − (w − ε) = 0` *identically*, so only
the root-of-unity half of the level hypothesis needs a modulus, and the residue-class pigeonhole
disappears — only the pair `(i, ε) ∈ Fin (d+1) × Bool` has to be fixed.

## Map of the file (all proved)

| step | lemma | content |
|---|---|---|
| — | `compM`, `compM_map` | companion matrix over any ring; commutes with ring homs |
| 1 | `sum_pow_mul_compM`, `vandermonde_mul_compM`, `vandermonde_mul_polyMat` | the conjugation |
| 1 | `conj_pow`, `conj_trace`, `conj_eq_one`, `vandermonde_isUnit_det` | conjugation helpers |
| 1 | `trace_polyMat_mul_compM_pow`, `polyVal_pow_eq_one` | the two payoffs |
| 1a | `traceSeq`, `traceSeq_cast`, `traceSeq_eq_root_sum`, `exists_root_enum` | `V_N = ∑ (e k)^N` |
| 1b | `eventually_floor_eq_traceSeq` | `⌊α^N⌋ ∈ {V_N, V_N − 1}` for large `N` |
| 2a | `compM_det_ne_zero` | `det C ≠ 0` over a field when `f(0) ≠ 0` (kernel cascade) |
| 2b | `compM_pow_congr_one`, `glCard_pos` | `C^(Q c^n) ≡ I (mod c^(n+1))`, `Q = |GL_d(𝔽_c)|` |
| 2c | `compM_pow_mulVec_e0`, `compM_mulVec_last`, `eq_of_commute_of_mulVec_e0`, `compM_pow_natDegree`, `exists_coords` | Cayley–Hamilton via the cyclic vector `e₀` |
| 1c | `exists_floor_strictMono`, `exists_floor_gt` | growth (α ≥ φ is FALSE in degree `d`) |
| 1c | `orderOf_dvd_glCard_d`, `traceSeq_congr_of_order`, `traceSeq_stuck_period` | the filter |
| 1d | `stuck_alternation_general` | the offset alternates at a stuck `n` |
| 1f | `exists_val_frequently` | pigeonhole over a finite type |
| 3 | `exists_complex_zero_of_family` | Nullstellensatz + integrality, arbitrary finite family |
| 5–6 | `trace_polyMat_mul`, `map_polyMat_pow_sub_one`, `exists_spectral_solution` | the `d²+2` system |
| 7 | `norm_eq_one_of_pow_eq_one`, `not_exists_spectral_of_large` | `α^s ≤ 2 + (d−1) = d+1` |
| — | `eval_map_complex_of_aeval`, `compM_det_ne_zero_int` | plumbing for the assembly |

## Three places the degree-2 proof genuinely does **not** generalize

* **`det (compMat a b) = b` by hand.**  In degree `d` the determinant is `(−1)^d f(0)`, and proving
  that means isolating the full-cycle permutation in `det_apply`.  Avoided: over a field it is
  enough that `C *ᵥ u = 0 ⟹ u = 0`, a two-step cascade (row `0` reads `f(0) u_(d−1) = 0`, then
  row `j+1` reads `u_j = 0`).
* **`α ≥ φ` (`golden_le_sq`).**  False in degree `d` — the plastic number `1.3247 < 1.618`, i.e.
  exactly the case the corollary is about.  Replaced by the *eventual* bound: once
  `α^N (α − 1) ≥ 1` we get `α^(N+1) ≥ α^N + 1`.  Every use was "for all `n ≥ n₀`" anyway.
* **A closed formula for the offset** (`decide (0 < β^N)`).  In degree `d` the offset only comes
  from a disjunction, so `stuck_alternation_general` takes an abstract `(ε, off)` pair.

## Lean gotchas from this phase

* `*ᵥ` does not parse without `open Matrix`; write `Matrix.mulVec M v`.
* `Matrix.mulVec_single` normalises to `MulOpposite.op x • M.col j` — the usable form is the
  one-liner `mulVec_single_one : (M *ᵥ Pi.single j 1) i = M i j` (`simp [mulVec, dotProduct,
  Pi.single_apply]`), and `rw [← mulVec_single_one]` needs all three explicit arguments.
* `Matrix.dotProduct` is now root-level `dotProduct`.
* `hmon.natDegree_map` needs `[Nontrivial R]`; use `eval_eq_sum_range'` + `natDegree_map_le`
  instead when the ring is arbitrary (`ZMod (c^k)` has no automatic instance).
* `set S := …` then `rw [hS] at h` breaks when a later term's *type* depends on `S`
  (`S.equivFin`); use `obtain ⟨S, hS⟩ : ∃ S, S = … := ⟨_, rfl⟩` and pull the facts you need out
  *before* introducing the dependent term.
* `#S` (`Finset.card` notation) is not in scope here; write `S.card`.
* `Ideal.mem_span_range_iff_exists_fun` is the finite-family analogue of `Submodule.mem_span_insert`
  chains; `Submodule.span_induction` cases are `mem/zero/add/smul`.
* `monicity!` and `compute_degree!` handle `X^3 - X - 1`;
  `Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` is the cubic irreducibility route
  (over `ℤ`, so `r ∣ 1` finishes it).

## Next

`DIRECTION.md` phase 56 is met.  Untouched designated-open work elsewhere: the two active-crux
`sorry`s in `NumberTheory/Transcendence/DubickasNoSubspace.lean` (`PENDING_WORK.md` §PHASE 9) —
not part of this phase, deliberately not attacked.
