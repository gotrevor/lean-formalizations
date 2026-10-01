# Door 2′ for Erdős #385: F(n) − n ~ √n for almost all n

Opened 2026-10-01.  Source of the door: Tao's blog reply (2024-08-19, see `LIT-ERDOS-385.md` §2):
"almost all n have `F(n) = n + n^{1/2+o(1)}`" should be "well within reach" via Huxley /
Guth–Maynard technology.  No proof was given.  The LIT sweep found no write-up.
Probe: `scripts/erdos385-almostall-probe.py [N] [delta]`.

## 1. The theorem

**Theorem A (target).**  For every fixed `δ ∈ (0, 1/4)`,

  `#{ n ≤ X : F(n) < n + (1 − δ)√n } = o(X)`.

`F(n) ≤ n + √n` holds trivially (`p(m) ≤ √m`).  Letting `δ → 0` slowly gives
**`F(n) = n + (1 + o(1))√n` for almost all n.**

- This is stronger than Tao's `n^{1/2+o(1)}`.  It is the Erdős–Eggleton–Selfridge "possibly
  always `≥ n + (1 − o(1))√n`" on a density-one set, and it implies #385(ii) on that set.
- Exceptional set: `o(X)`, plausibly `≪ X exp(−c (log X)^{1/3−ε})`, the same shape as Guth–Maynard
  Cor 1.4 for primes.
- An `X^{1−δ}` exceptional set is **not** claimed.  The region `σ → 1` only yields the
  Vinogradov–Korobov saving, never a power.

**Theorem B (minimal-scale version, optional).**  For `θ > θ₀`, almost all intervals
`[x − x^θ, x]` contain a semiprime `pq` with `p, q ∈ [x^{1/2−η}, x^{1/2+η}]`, hence a composite `m`
with `p(m) > x^θ`.

| Input | θ₀ | Confidence |
|---|---|---|
| Classical MVT + Montgomery–Halász–Huxley | 1/4 | ~70% |
| Guth–Maynard Thm 1.1 large values | 1/5 | ~60% |
| Zero-density route (pairs of zeros, GM Thm 1.2, `A = 30/13`): `θ₀ = 1 − 2/A` | 2/15 | ~45% |

Theorem B says nothing about the every-`n` problem.  That needs all scales `log n ≪ h ≪ √n` at
once, at every `n`.

**Numerics** (`erdos385-almostall-probe.py 2e7 0.2`, fraction of each dyadic block `[2^k, 2^{k+1})`):

| k | `(F−n)/√n < 0.5` | `< 0.8` | `< 0.9` | no balanced witness (δ = 0.2) |
|---|---|---|---|---|
| 14 | 0.398 | 0.879 | 0.967 | 0.780 |
| 18 | 0.093 | 0.722 | 0.923 | 0.510 |
| 22 | 0.0016 | 0.410 | 0.804 | 0.160 |
| 23 | 0.0003 | 0.318 | 0.759 | 0.093 |

Every column decreases.  The approach to 1 is slow, as expected: the balanced-witness count per
window is about `δ²√n/log² n`.

## 2. Proof outline

**S1. Reduction (elementary; proved below in words).**
- Take primes `p ≤ q` with `pq ∈ (n − h, n)`, `h ≤ (δ/2)√n` and `p ≥ (1 − δ/2)√n`.
- Then `m = pq` is composite with `p(m) = p`, and `F(n) − n ≥ p − (n − m) ≥ (1 − δ)√n`.
- So it suffices that almost every `n` has such a "balanced witness".

**S2. Localise.**
- Work with `n ∈ [Z, (1 + δ/8)Z]`.  Take `p ∈ J_Z = [(1 − δ/2)√Z, (1 − δ/4)√Z]` and `q` any prime.
  Then `q ≈ n/p > p` automatically, and `h = (δ/2)√Z`.
- `C(x) = #{(p, q) : p ∈ J_Z, x − h < pq ≤ x}`.  Its long-interval mean is
  `≍_δ h/log² Z > 0` by PNT.
- Cover `[X, 2X]` by `O_δ(1)` such ranges.

**S3. Parseval lemma: variance to a Dirichlet mean square.**
- With `T = Z/h ≍ √Z/δ` and `A(s) = Σ_{m=pq} m^{−s}`:
  `(1/Z)∫|C(x)/h − (long average)|² dx ≪ 1/T₀ + ∫_{T₀}^{T}|A(1+it)|² dt + max_{T′ ≥ T}(Z/(hT′))∫_{T′}^{2T′}|A(1+it)|² dt`.
- The shape is Matomäki–Radziwiłł, Annals 2016, arXiv:1501.04585, **Lemma 14** (read this
  session).
- ⚠️ As stated, MR's Lemma 14 has an additive `(log X)^{−2/15}` term, from their choice
  `h₂ = X/(log X)^{1/5}`.  That is too weak for a sequence of density `≍ 1/log² X`.  We need the
  same lemma with `h₂ = X/T₀`, `T₀ = exp((log X)^{1/3})`, and error `≪ 1/T₀`.  I expect this to
  follow from the same proof (~75%).  To verify against the proof, not the statement.

**S4. Decouple.**  `A(s) ≈ P(s)·Q(s)`, with `P(s) = Σ_{p∈J_Z} p^{−s}` and `Q(s) = Σ_{q ∈ Q_Z} q^{−s}`.
Both have length `≍ √Z`.  The `pq ∈ [Z, 4Z]` constraint is handled by splitting `J_Z` into
`(log Z)^{C}` short pieces (standard; MR §3-style).  Both lengths are `< T`.  **This is the crux:
both factors are shorter than `X/h`, so the mean value theorem on one factor loses `T/N`.**  That
is exactly why the almost-prime literature (Teräväinen, Matomäki–Teräväinen) uses one small factor,
and why it does not cover us.

**S5. Pointwise Vinogradov–Korobov.**
- For `T₀ ≤ |t| ≤ T`: `|Σ_{p∈J} p^{−it}| ≤ |J|·exp(−c (log Z)^{1/3}(log log Z)^{−1/3})`.
- This comes from the VK zero-free region plus the explicit formula (standard;
  Iwaniec–Kowalski §8.5).  An exact citable lemma for a prime sum over `[(1−δ/2)√Z, (1−δ/4)√Z]`
  is still to be located.

**S6. Large values plus Cauchy–Schwarz (the hardest step).**
- Split `[T₀, T]` into unit intervals and dyadic blocks
  `B(λ₁, λ₂) = {t : |D_P(t)| ≍ λ₁K, |D_Q(t)| ≍ λ₂K}`, with `K ≍ δ√Z/log Z` the number of terms.
- On a block, `∫_B |D_P D_Q|² ≤ |B| λ₁²λ₂²K⁴ ≤ (R_P(λ₁)λ₁⁴)^{1/2}(R_Q(λ₂)λ₂⁴)^{1/2} K⁴`, using
  `min ≤ geometric mean`.
- The classical bound (GM eq. (1.1), MVT + Montgomery–Halász–Huxley):
  `R ≤ T^{o(1)}(N²V^{−2} + T min(N V^{−2}, N⁴V^{−6}))`, with `V = λK`, `N ≍ √Z`.  This gives
  `R λ⁴ ≪ polylog·[λ² δ^{−2} + T·min(λ²/(δ²N), λ^{−2}/(δ⁶N²))]`.
  - First term: `≪ exp(−c(log Z)^{1/3})·polylog` by S5, since every `λ` on `[T₀, T]` is VK-small.
  - Second term: at worst `T δ^{−4} N^{−3/2} ≍ δ^{−5} Z^{−1/4}`.
- Summing `O(log² Z)` blocks: `∫_{T₀}^{T}|A(1+it)|² = o(main²)`.  The `T′ ≥ T` tail is the plain
  mean value theorem, since `Z/(hT′) ≤ 1`.
- ⚠️ **The risk is the `T^{o(1)}`.**  The only saving near `σ = 1` is the VK factor
  `exp(−(log)^{1/3})`.  So every loss must be polylog, never `Z^{ε}`.  GM state (1.1) with
  `T^{o(1)}`.  I believe the classical MVT + Halász–Montgomery + Huxley-subdivision bounds hold with
  `(log T)^{O(1)}` (~75%; check Ivić, *The Riemann zeta-function*, the large-values chapter, or
  Montgomery, *Topics*, ch. 7).
- Fallback if only `T^{ε}` is available: route the `λ → 1` region through ζ-zeros (Huxley-style
  zero detection: `|P(1+it)| ≥ P^{−(1−σ)}` forces a zero with `β ≥ σ − o(1)` near `t`).  There the
  losses are known to be polylog.

**S7. Chebyshev.**  The variance is `o(main²)`, so `#{x : C(x) = 0} = o(Z)` per range.  Summing
ranges gives Theorem A.

**Confidence the outline closes: ~70%.**  The hardest step is S6 together with S3: precise
bookkeeping at density `1/log² X` with only a VK saving.  Neither step has an identified gap
beyond "check the constants are polylog".

## 3. Difficulty check (feedback_difficulty_locus)

- **Proved implications.**  S1 (balanced witness ⇒ `F(n) − n ≥ (1 − δ)√n`) is elementary.
  Variance ⇒ exceptional set is Chebyshev.  Trivially `F(n) ≤ n + √n`.
- **Unproved premise.**  `∫_{T₀}^{T}|P(1+it)Q(1+it)|² dt = o(main²)` for two prime polynomials of
  length `≍ √X < T = X/h`.
- **Mechanism.**  VK pointwise + classical large values + Cauchy–Schwarz over blocks.  All inputs
  have been in print since about 1972.  The idea is to use the **free bilinear structure** of a
  semiprime: the block bound uses `R·N^{4σ−4}` (a fourth-moment quantity), which decays.  A single
  polynomial only has `R·N^{2σ−2}`, whose first term is exactly 1.
- **Known-false / known-boundary siblings.**
  1. *Primes in almost all intervals below Huxley/GM.*  The argument needs a product of two
     polynomials.  On one polynomial (Λ alone) the MVT term contributes `R V²/N² ≤ 1`, with no
     saving.  So it says nothing about primes, and cannot beat `θ > 1/6` or `θ > 2/15`.  Passes.
  2. *Every n.*  A variance bound only controls measure, so it cannot touch the every-`n`
     statement.  Tao's Siegel-zero scenario lives in residue classes at scales `h ≲` conductor.
     Our `h ≍ √X` covers all classes, and the argument uses only ζ, never `L(s, χ)`.  Passes.
  3. *Support sanity.*  With both `p, q > √x` there are no products `≤ x`.  The S2 main term is 0
     there, so the method predicts nothing false.  Passes.
  4. *Scale sanity.*  Theorem B's classical `θ₀ = 1/4` is above GM's prime threshold `2/15`.  That
     is consistent: semiprimes with balanced factors via generic large values should not beat the
     zero-density method for primes.  Passes.
- **Novelty.**  Not found by the LIT sweep.  Tao calls it within reach.  Theorem A's `(1 + o(1))√n`
  form is stronger than his stated `n^{1/2+o(1)}`.  Before calling it new: run `papers followups` on
  Teräväinen arXiv:1510.06005 and Matomäki–Teräväinen arXiv:2207.05038, and search "products of two
  primes of similar size in short intervals".

## 4. Lean reality and conjecture-graph shape

This is analytic and heavy.  Plancherel/Perron-level Fourier analysis on ℝ and zeta zero-free
regions are far beyond a lap.  So the analytic inputs enter as **literature hypothesis Props**,
stated faithfully, and a treadmill proves the **wiring**.

**Literature Props** (each cites its source verbatim; none is an `axiom`):

```lean
/-- Guth–Maynard 2024, arXiv:2405.20552, Theorem 1.1 (large values), verbatim:
|b n| ≤ 1, t_r 1-separated in [0,T], |∑_{N ≤ n ≤ 2N} b n * n^(i t_r)| ≥ V for r ≤ R ⇒
R ≤ T^{o(1)} (N^2 V^-2 + N^(18/5) V^-4 + T N^(12/5) V^-4).  The o(1) is rendered as ∀ ε, ∃ C. -/
def Literature.GuthMaynard2024LargeValues : Prop := sorry -- encode faithfully

/-- Classical large values (MVT + Montgomery–Halász–Huxley) WITH POLYLOG LOSS, as GM eq. (1.1)
but (log T)^C in place of T^{o(1)}.  Source to pin before freezing (Ivić / Montgomery Topics). -/
def Literature.ClassicalLargeValuesPolylog : Prop := sorry

/-- Vinogradov–Korobov bound for prime sums ∑_{P<p≤P'} p^{-it}, P' ≤ 2P, T₀ ≤ |t| ≤ T. -/
def Literature.VinogradovKorobovPrimeSum : Prop := sorry

/-- Parseval short-sum lemma, MR16 Lemma 14 shape with h₂ = X/T₀ and error 1/T₀ (S3). -/
def Literature.ShortSumParseval : Prop := sorry
```

**Wiring theorems** (treadmill targets, most tractable first):

```lean
/-- Same definition as formal-conjectures `Erdos385.F` (restated, not imported). -/
noncomputable def F385 (n : ℕ) : ℕ := sSup {m + m.minFac | (m < n) (_ : ¬ m.Prime ∧ 1 < m)}

-- W1 (elementary, one lap): balanced witness ⇒ margin.  Route: m = p*q, minFac = p, unfold sSup.
theorem F385_ge_of_balanced (n p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hlt : p * q < n) : (n : ℤ) + p - (n - p * q) ≤ F385 n := by sorry

-- W2 (one lap): Chebyshev.  A discrete variance bound for the window counts gives a density-zero
-- exceptional set.
theorem density_zero_of_variance {c : ℕ → ℝ} {μ : ℕ → ℝ} (hμ : ∀ᶠ X in atTop, 0 < μ X)
    (hvar : Tendsto (fun X => (∑ x ∈ Finset.Icc X (2*X), (c x - μ X)^2) / (X * μ X ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun X => ((Finset.Icc X (2*X)).filter (fun x => c x = 0)).card / (X : ℝ))
      atTop (𝓝 0) := by sorry

-- W3 (several laps): block decomposition + Cauchy–Schwarz.  Discrete mean square of a product
-- of two bounded-coefficient polynomials over 1-separated points, from large values + a
-- pointwise bound.  Pure inequality bookkeeping, no analysis.

-- Headline edge:
theorem almost_all_F385 (hLV : Literature.ClassicalLargeValuesPolylog)
    (hVK : Literature.VinogradovKorobovPrimeSum) (hP : Literature.ShortSumParseval)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun X : ℕ => (((Finset.range X).filter
      (fun n => (F385 n : ℝ) < n + (1 - δ) * Real.sqrt n)).card : ℝ) / X) atTop (𝓝 0) := by
  sorry
```

Node map:
- W1, W2 green: elementary; S1 and S7 frozen as Lean.
- W3 green: the combinatorial heart of S6 as a theorem about finite sums.
- Headline green, Prop-gated: Theorem A modulo four faithful literature statements.
- An open companion node, `TheoremB θ` for `θ ∈ (2/15, 1/4]`, is not planted until the
  zero-density route has a written mechanism.

**Order of work.**
1. Paper first: pin S3's variant and S6's polylog large-values source.  This is a reading task,
   about one session.
2. Write the proof properly in `PROOF-ALMOSTALL-385.md`.
3. Only then freeze the four Props and run a treadmill on W1 → W2 → W3 → headline.
