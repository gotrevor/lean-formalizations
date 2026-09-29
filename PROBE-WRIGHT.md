# Probe: is the least Wright constant irrational?  (2026-09-29)

**Verdict: open, and demoted.**  Nobody has published on it, and I see no proof route.  Candidate #2 in the new-math ledger drops from ~10-15% to **<3%**, and no phase 15 is planted.

## The object

`W = {ω : ⌊tower ω n⌋ prime ∀ n ≥ 1}` (`NumberTheory/Mills/Wright.lean`).  Its least element comes from the greedy chain: `q₁ = 2`, `q_{k+1} = nextprime(2^{q_k})`, giving 2, 5, 37, 137438953481, …, and `ω_min = lim invtower(q_k, k)`, which is `⨆ wa` in `Wright.lean`.

- `ω_min ≈ 1.25164759779046301759443205362334696916…` (`scripts/wright-least.py`; the level-5 correction is about 2^(−1.4·10¹¹)).  This matches Baillie arXiv:1705.09741 §6, which bounds it as 1.25164… < c < 1.25806….
- ⚠️ **1.9287800 is Wright's *example*, not the least constant.**  The survival note and OEIS A086238 framing conflated the two.

## Freshness (sources read 2026-09-29)

- **Baillie 1705.09741**: computational only (fourth prime, smallest-prime chain in §6); proves the reciprocal sum of Wright's primes is transcendental.  Makes no claim about ω.  Forward citations: Plouffe ×2 and Finch errata, nothing arithmetic.
- **Saito–Takeda 2112.14383** (Mathematika 2022): treats `W(c_k) = {A : ⌊A^{c₁⋯c_k}⌋ prime}`, i.e. power maps, not towers.  They show the minimum is transcendental when `c_k → ∞` (e.g. `W(k)`).  Wright's tower is not of this form.  Forward citations: only Saito 2024 and 2025.
- **Saito 2021 2102.04038** (Hausdorff dimension): mentions Wright's map `λ_W` only as motivation.
- **Saito 2024 2404.19461 / Saito 2025 2508.16068**: Wright appears in the introduction only.  Open questions there are ξ₂ (Q1.6) and the cubic Pisot branch.
- Kobayashi–Saito–Takeda 1912.09125 is about `x^{x^{x…}}` at algebraic x, which is unrelated.
- **Instrument limits.**  Semantic Scholar forward citations plus two web searches.  A search summary claimed "open", but that is not a source.  The claim here is only that none of the papers above addresses it.

## Why no route

Every Mills/ST22/Saito argument runs on **algebraic structure that survives the iteration**:

- If `A` is algebraic, then every `A^{3^k}` or `A^{C_k}` stays in one number field of bounded degree.  Then "`A^{3^k}` is within `p_k^{-c}` of an integer" meets Pisot, Liouville or Subspace machinery.
- For ST22's minima, the approximants `p_k^{1/C_k}` are algebraic.

For the tower, a rational `ω = a/b` makes only **level 1** algebraic: `g₁ = 2^{a/b}`.  Gelfond–Schneider already makes `g₂ = 2^{g₁}` transcendental.  Nothing is *known* about level 3 and beyond: `2^x` for transcendental `x` may be algebraic as far as current theory can say.  (An earlier draft of this note claimed every later level was transcendental; only Schanuel's conjecture would give that.)

The only information is the asymptotic one, that `g_k` sits within about `q_{k+1}·2^{−q_k}` above the integer `q_k`, for all k.  The `g_k` carry no common field, so turning that into a contradiction means controlling fractional parts of `2^x` along a transcendental orbit.  That is strictly harder than Mahler's (3/2)^n problem.  The natural approximants `invtower(q_k, k)` are iterated logarithms, not algebraic numbers, so the ST22 Liouville route has nothing to bite on.

Confidence that this is out of reach with known tools: ~85%.

## Pinned

Recorded in `src/LeanFormalizations/Maze.lean` as a `noCommonField` row, anchored on the frozen `Maze.WrightLevelTwoTranscendental` (with `Literature.GelfondSchneider1934`).  Its `reopenIf` field names the new idea required.
