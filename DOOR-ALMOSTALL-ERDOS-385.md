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

## Source checks (2026-10-01)

Sources opened this session: Matomäki–Radziwiłł, arXiv:1501.04585 (full text via `pdftotext`), and
Teräväinen, arXiv:1510.06005 (full text).  Iwaniec–Kowalski, Ivić and Montgomery's *Topics* were
**not** opened; anything resting on them is marked.

### Check (2): MR Lemma 14's `(log X)^{−2/15}` is a parameter artifact, not intrinsic.  ✅ (95%)

MR16 Lemma 14, verbatim: "Let `|a_m| ≤ 1`.  Assume `1 ≤ h₁ ≤ h₂ = X/(log X)^{1/5}`.  Consider, for
`X ≤ x ≤ 2X`, `S_j(x) = Σ_{x≤m≤x+h_j} a_m` and write `A(s) := Σ_{X≤m≤4X} a_m/m^s`.  Then
`(1/X)∫_X^{2X} |S₁(x)/h₁ − S₂(x)/h₂|² dx ≪ 1/(log X)^{2/15} + ∫_{1+i(log X)^{1/15}}^{1+iX/h₁} |A(s)|²|ds|
+ max_{T≥X/h₁} (X/h₁)(1/T)∫_{1+iT}^{1+2iT} |A(s)|²|ds|`."

In the proof, `T₀ := (log X)^{1/15}` and `h₂` enter in exactly one place: the low-frequency part
`U_j`, where `|(1/h₁)U₁ − (1/h₂)U₂| ≪ T₀² h₂/X`.  Squaring gives the additive term.  Nothing else
uses their values.

Better still, the general-parameter form is **in print**.  Teräväinen 2016, arXiv:1510.06005,
**Lemma 1**, verbatim:
- Let `S_h(x) = (1/h)Σ_{x≤n≤x+h} a_n`, where `a_n` are complex numbers, and let
  `2 ≤ h₁ ≤ h₂ ≤ X/T₀³` with `T₀ ≥ 1`.  Also let `F(s) = Σ_{n∼X} a_n/n^s`.
- Then `(1/X)∫_X^{2X}|S_{h₁}(x) − S_{h₂}(x)|² dx ≪ 1/T₀ + ∫_{T₀}^{X/h₁}|F(1+it)|² dt
  + max_{T≥X/h₁} (X/(T h₁))∫_T^{2T}|F(1+it)|² dt`.
- His proof line: "This is Lemma 14 in the paper [MR] (except that we do not specify the value of
  `T₀`)."  The statement omits `|a_n| ≤ 1`, but the `1/T₀` term needs bounded coefficients; the Prop
  below adds that hypothesis (faithful-or-weaker).

So S3 holds with error `1/T₀`, as the outline needed.

### Check (1): polylog-loss large values are NOT NEEDED for Theorem A.  ⚠️ The outline's S4/S6 crux is mistaken.  (85%)

S4 says both factors are shorter than `T = X/h`, so "the mean value theorem on one factor loses
`T/N`".  But at the Theorem A scale `h ≍ δ√Z` we have `T ≍ √Z/δ` and `N ≍ √Z`.  So **`T/N ≍ 1/δ`
is a constant**, and the cheapest argument closes:

`∫_{T₀}^{T}|P(1+it)Q(1+it)|² dt ≤ sup_{T₀≤|t|≤T}|P(1+it)|² · ∫_{−T}^{T}|Q(1+it)|² dt`.

**Second factor (MVT).**  MR16 Lemma 6, verbatim: "Let `A(s) = Σ_{n≤N} a_n n^{−s}`.  Then
`∫_{−T}^{T}|A(it)|² dt = (T + O(N))Σ_{n≤N}|a_n|²`.  Proof: See [IK, Theorem 9.1]."  With
`b_q = 1/q` over `q ∈ [√Z, 1.5√Z]`, this is `≪ (√Z/δ + √Z)·1/(√Z log Z) ≪ 1/(δ log Z)`.

**First factor (VK pointwise).**  Use smooth `p`-weights `w(p) = f(p/√Z)`, `0 ≤ f ≤ 1`, supported in
`[1−δ/2, 1−δ/4]`.  This costs nothing: `S₁(x) > 0` still forces a prime `p` in the support.  The
estimate is MR16, proof of Lemma 11, the display after (15):
- `Σ_n Λ(n) n^{it} f(n/P) = f̃(1+it)/(1+it)·P^{1+it} + O(P exp(−log P/(log T)^{2/3+ε})(log T)²)`.
- MR derive it by shifting to `σ = 1 − c(log T)^{−2/3+ε}` (the VK region) and using Ivić (1.52)
  for `ζ′/ζ`.
- `f̃(1+it) ≪_{δ,B} (1+|t|)^{−B}`.  The `1/log n` and prime-power adjustments are smooth or
  negligible.
- With `P = √Z` and `|t| ∈ [T₀, 2Z]` this gives
  `|P(1+it)| ≪_δ T₀^{−B} + exp(−c(log Z)^{1/3−ε})`.

**Bookkeeping.**  `a_m = Σ_{m=pq} w(p)1_{q∈[√Z,1.5√Z]}` has `|a_m| ≤ 1` (since `p < √Z ≤ q`) and
support in `[X, 2X)` with `X = (1−δ/2)Z`.  The long-range density is `μ ≫ δ/log² Z`.  Take
`T₀ = exp((log Z)^{1/3})` and `h₂ = X/T₀³`.  The `h₂`-averages are `≥ c₀δ/log² Z` by PNT in
intervals of length `√Z·exp(−3(log Z)^{1/3})` at height `√Z`.  De la Vallée Poussin's error
`exp(−c√log)` already suffices for that; VK is not needed there.

The three terms of Lemma 1:
- `1/T₀`.
- `∫_{T₀}^{X/h₁} ≪ sup|P|²/(δ log Z)`.
- The tail.  For `X/h₁ ≤ T ≤ Z`, the same sup × MVT gives `≪ sup|P|²/(δ log Z)`.  For `T > Z`,
  MVT on `A` itself gives `(X/(h₁T))(T + O(X))Σ_m a_m²/m² ≪ 1/h₁`.

Chebyshev then gives `meas{x : S_{h₁}(x) = 0} ≪ X·δ^{−2}log⁴Z·(1/T₀ + δ^{−1}exp(−c(log Z)^{1/3−ε}))`.
A bad `n` forces `S_{h₁}(x) = 0` on an `x`-interval of length `≍ h₁`, and each `x` serves `≍ h₁`
values of `n`.  So the count of exceptional `n` is `≪` this measure.

So **no large-values estimate, no Halász–Montgomery, no Huxley, no Guth–Maynard** enters Theorem A.
Those matter only for Theorem B (`h = x^θ`, `θ < 1/2`, where `T/N = x^{1/2−θ}` is a power).  For
Theorem B, the polylog question stays open.  I did not open IK ch. 9 or Ivić; MR16 Lemma 7 (well-spaced
MVT) does carry only `log 2N`.

Novelty, revised: with the crux gone, Theorem A is a routine MR/Teräväinen-template variance
argument (one VK-small factor, MVT on the other).  An expert would call it an exercise (85%).  That
matches Tao's "well within reach".  It is still apparently unwritten, and the `(1+o(1))√n` form is
sharper than his remark.

### Check (3): the exceptional set is `X exp(−(log X)^{1/3−ε})`, confirming the guess.  (80%)

The only saving is the VK pointwise bound for a prime sum of length `P = √X` at heights `T ≍ X^{O(1)}`.
That bound is `exp(−log P/(log T)^{2/3+ε}) = exp(−(log X)^{1/3−ε})`, and the `1/T₀` term is matched to
it.  So this route gives `#{n ≤ X : F(n) < n + (1−δ)√n} ≪_δ X exp(−c(log X)^{1/3−ε})`, and no better
without new zero-density input near `σ = 1`.  For the narrower set of **bad** `n` (`F(n) ≤ n`), the
exceptional-set door's elementary `X exp(−(log X)^{1/2−ε})` (if its outline closes) is quantitatively
stronger.  The two doors are complementary, not redundant.

### Verdict: freeze as phase E3

**E3 (Theorem A).**  For every `δ ∈ (0, 1/4)`:
`#{ n ≤ X : F(n) < n + (1 − δ)√n } = o(X)` as `X → ∞`, where
`F(n) = max_{m<n, m composite}(m + p(m))`.

Optional strengthening E3′: `≪_δ X exp(−(log X)^{1/4})`.  It is safe, because `1/4 < 1/3`.

Literature Props E3 needs.  Each is faithful-or-weaker; **drop** `GuthMaynard2024LargeValues` and
`ClassicalLargeValuesPolylog` from E3:

1. `Literature.Teravainen2016ParsevalShortSums`: Teräväinen arXiv:1510.06005 **Lemma 1** verbatim
   (quoted above), with the added hypothesis `|a_n| ≤ 1`, an absolute implied constant, and
   `n ∼ X` read as `X ≤ n < 2X`.
2. `Literature.MeanValueTheoremDirichlet`: `∫_{−T}^{T}|Σ_{n≤N} a_n n^{−it}|² dt ≤ C(T + N)Σ|a_n|²`.
   This is the upper-bound half of IK Theorem 9.1 (Montgomery–Vaughan), as quoted in MR16 Lemma 6.
3. `Literature.VKSmoothPrimeSum`: for smooth `f` supported in `[1/2, 2]`, every `ε > 0`, and all
   `T ≥ 2`, `P ≥ 2`, `|t| ≤ T`:
   `|Σ_n Λ(n) n^{it} f(n/P) − f̃(1+it)P^{1+it}/(1+it)| ≤ C_{f,ε} P exp(−log P/(log T)^{2/3+ε})(log T)²`.
   Source: MR16, proof of Lemma 11 (eq. (15) and the following display), from the VK zero-free
   region plus Ivić (1.52).  ⚠️ This is a displayed step, not a numbered lemma, so state it with the
   `f`-dependent constant exactly as derived.  (85% the statement is right; a numbered source in IK
   ch. 8 or Koukoulopoulos's book would be better, and I have not located one.)
4. `Literature.PNTShortIntervals`: `π(y + H) − π(y) ≥ H/(2 log y)` for `H ≥ y·exp(−(log y)^{2/5})`,
   `y ≥ y₀`.  This is weaker than de la Vallée Poussin's PNT error, so it is likely dischargeable from
   PNT+ `MediumPNT`, which the repo already imports (~60%, not checked).

Wiring for the treadmill:
- W1 (balanced witness ⇒ margin) is unchanged.
- W2 (variance ⇒ density zero) is unchanged.
- **W3 collapses to one inequality**: `∫|PQ|² ≤ sup|P|²·∫|Q|²` plus MVT.  Drop the block/Cauchy–Schwarz
  plan.
- Headline: `almost_all_F385` with hypotheses `(hP1 hP2 hP3 hP4)` in place of `hLV hVK hP`.

## E3 literature Props (corrected 2026-10-01)

Supersedes the four-item list under "Verdict: freeze as phase E3" above.  Two of those items were
false as written (independent referee, `PROOF-ERDOS-385-ALMOST-ALL.md` issues 3 and 4), which would have
made the Lean headline vacuous.  Each Prop below is stated precisely enough to transcribe verbatim.
Each comes with a **known-false control**: an instance that refutes a wrong transcription, so a lap
can test the Lean statement before relying on it.  Notation: $e(\cdot)$ is not used; $n^{-s} = \exp(-s\log n)$;
$\Lambda$ is von Mangoldt; all integrals are Lebesgue on $\mathbb R$.

### Prop 1. `Literature.MR16Lemma14` (Parseval bound for short sums; two-sided, complex coefficients)

There is an absolute constant $C$ such that for all real $X \ge 2$, $T_0 \ge 1$, $h_1, h_2$ with
$2 \le h_1 \le h_2 \le X/T_0^3$, and all $a : \mathbb N \to \mathbb C$ with $|a_m| \le 1$ for all $m$ and
$a_m = 0$ unless $X \le m \le 4X$: writing $S_j(x) = \sum_{x \le m \le x + h_j} a_m$ and
$A(s) = \sum_m a_m m^{-s}$,
$$\frac1X\int_X^{2X}\Big|\frac{S_1(x)}{h_1} - \frac{S_2(x)}{h_2}\Big|^2dx \le C\Big(\frac1{T_0} + \int_{T_0 \le |t| \le X/h_1}|A(1+it)|^2dt + \sup_{T \ge X/(2h_1)}\frac{X}{h_1T}\int_{T \le |t| \le 2T}|A(1+it)|^2dt\Big).$$
Source: Matomäki–Radziwiłł, Annals 2016, arXiv:1501.04585, **Lemma 14** and its proof (eq. (19));
general $T_0$ as in Teräväinen arXiv:1510.06005 **Lemma 1**.  Faithful-or-weaker: the printed
statements integrate over $t > 0$ only (valid only for real $a_m$, since then $|A(1-it)| = |A(1+it)|$),
print the tail threshold $X/h_1$ where the proof gives $X/(2h_j)$, and Teräväinen omits $|a_m| \le 1$,
which MR's proof uses.  The two-sided form is what the proof proves for complex $a_m$.  For Theorem A
the $a_m$ are real, so this is all that is used.

- **Control 1a (one-sided integrals are false for complex $a$).**  $a_m = m^{-i\tau}\,\mathbf 1_{[X,2X)}(m)$,
  $\tau = X/(10h_1)$, $h_1 \le X/(10T_0^3)$, $h_2 = X/T_0^3$.  Then $|S_1/h_1| \ge 0.9 - o(1)$ and
  $|S_2/h_2| \ll T_0^3/\tau \to 0$, so the left side is $\asymp 1$.  With integrals over $t > 0$ only,
  $|A(1+it)| \ll 1/|t+\tau| + o(1)$ is small for every $t > 0$ and the right side tends to $0$:
  **false**.  With $|t|$ the right side picks up $t \approx -\tau$, where $|A| \asymp 1$: consistent.
- **Control 1b (the hypothesis $h_2 \le X/T_0^3$ is load-bearing).**  $a_m = m^{-iT_0/2}\mathbf 1_{[X,2X)}(m)$,
  $T_0 \ge 24$, $h_1 = 2$, but $h_2 = X$ (violating $h_2 \le X/T_0^3$).  Then $|S_1(x)/h_1| = 1 - o(1)$,
  $|S_2(x)/h_2| \le 12/T_0 + o(1)$, so the left side is $\ge (1 - 12/T_0)^2 - o(1)$; on the right,
  $|A(1+it)| \ll 1/|t + T_0/2|$ is $\ll 1/T_0$ on $|t| \ge T_0$, so the right side is $\ll C/T_0$:
  **false** for large $T_0$.  A transcription that drops the hypothesis is refutable.

### Prop 2. `Literature.MontgomeryVaughanMVT` (mean value theorem, upper half)

There is an absolute constant $C$ such that for all integers $N \ge 1$, reals $T > 0$, and
$a : \mathbb N \to \mathbb C$ with $a_n = 0$ for $n = 0$ and $n > N$:
$$\int_{-T}^{T}\Big|\sum_{n \le N} a_n n^{-it}\Big|^2dt \le C\,(T + N)\sum_{n\le N}|a_n|^2.$$
Source: Iwaniec–Kowalski Theorem 9.1 (Montgomery–Vaughan 1974), as quoted in MR16 Lemma 6.  Weaker
than the source (upper bound only, unspecified $C$).  Used in Lemma 5 and Proposition 6 with
coefficients $a_n/n$ (i.e. on the line $\mathrm{Re}\,s = 1$).

- **Control 2 (the $+N$ term is load-bearing).**  Drop it: $\int_{-T}^T|\sum a_nn^{-it}|^2 \le CT\sum|a_n|^2$.
  Take $a_n = 1$ for $n \le N$, $T = 1$: the left side is $\asymp N^2$ (as $\sum_{n\le N}n^{-it} \approx N^{1-it}/(1-it)$
  for $|t| \le 1$), the right side is $CN$: **false**.

### Prop 3. `Literature.VKZeroFreeLogDeriv` (Vinogradov–Korobov region with a log-derivative bound)

There are constants $c_0 > 0$ and $C_0$ such that for all real $T \ge 3$, $\sigma$, $y$ with
$$\sigma \ge 1 - \frac{c_0}{(\log T)^{2/3}(\log\log T)^{1/3}},\qquad |y| \le T,\qquad \sigma + iy \ne 1,$$
we have $\zeta(\sigma + iy) \ne 0$ and
$$\Big|\frac{\zeta'}{\zeta}(\sigma+iy) + \frac1{\sigma+iy-1}\Big| \le C_0\log T.$$
Source: Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Theorem 6.19 (zero-free region)
and Theorem 3.11 (log-derivative bound from a zero-free region and a growth bound), with $c_0$ taken as
a fraction of the zero-free constant.  ⚠️ Theorem numbers from memory, not re-opened (80%); the
statement is textbook.  Weaker than the source in the bound ($\log T$ instead of
$(\log T)^{2/3}(\log\log T)^{1/3}$).  This **replaces** the old Prop 3 (`VKSmoothPrimeSum`), which
lacked $P \le T$ and used MR's non-standard Mellin normalisation; the smoothed prime sum is now
**Lemma VK** of the PROOF file, a wiring node proved from this Prop (see below), not a literature input.
Order of quantifiers matters: $c_0, C_0$ come before $T$.

- **Control 3a (quantifier order).**  The variant "$\forall c_0 > 0$" is **false**: with $c_0$ large
  and $T = 15$ the region contains $\rho_1 = \frac12 + 14.1347\ldots i$, a zero of $\zeta$.  The variant
  "$\forall T\,\exists c_0$" is vacuous (take $c_0$ tiny per $T$) and would make Lemma 4 unprovable.
- **Control 3b (the pole term).**  Dropping $+\frac{1}{\sigma+iy-1}$ makes the bound false near $s = 1$
  ($\zeta'/\zeta(s) \sim -1/(s-1)$), e.g. at $\sigma = 1 + 1/T$, $y = 0$, where $|\zeta'/\zeta| \approx T > C_0\log T$.

### Prop 4. Short-interval PNT: prefer the `MediumPNT`-dischargeable form

**4 (Lean form, a theorem, not a Prop).**  There are $c > 0$ and $y_0$ such that for all $y \ge y_0$ and
$H$ with $y\exp(-c(\log y)^{1/10}) \le H \le y$:
$$\pi(y + H) - \pi(y) \ge \frac{H}{2\log(2y)}.$$
This follows from PNT+ `MediumPNT` ($\psi(x) - x = O(x\exp(-c'(\log x)^{1/10}))$, the version proved in
the repo's pinned PNT+; its `StrongPNT` is commented out there) by differencing $\psi$, discarding prime
powers ($O(\sqrt y\log y)$) and partial summation, with $c = c'/2$.  It needs the parameter change in
`PROOF-ERDOS-385-ALMOST-ALL.md` §1 "Lean note": $T_0 = \exp(\kappa(\log Z)^{1/10})$, which weakens the
exceptional-set rate to $\exp(-c''(\log Y)^{1/10})$ but keeps $o(Y)$.  Mertens over
$[a\sqrt Z, b\sqrt Z]$ (Lemma 3) also follows from `MediumPNT` by partial summation.

**4′ (literature Prop, only if the $1/3$-rate is wanted).**  `Literature.PNTdlVP`: $\psi(x) = x + O(x\exp(-c\sqrt{\log x}))$
for some $c > 0$ (de la Vallée Poussin; Davenport ch. 18), from which the paper's range
$H \ge y\exp(-4(\log y)^{1/3})$ follows.

- **Control 4 (the lower limit on $H$ is load-bearing).**  With "$H \ge \log y$" in place of the stated
  range the statement is **false**: prime gaps exceed $2\log p$ infinitely often (Westzynthius 1931,
  indeed any multiple of $\log p$), and $y = p_n$ at such a gap has $\pi(y + \log y) - \pi(y) = 0$.

### Wiring nodes and the headline (for the ROADMAP)

- **Node `SmoothPrimeSumVK`** = Lemma VK (PROOF §1): hypotheses $f$ smooth with compact support in
  $(0,\infty)$, $P \ge 2$, $T \ge 3$, **$P \le T$**, $|t| \le T/2$; standard Mellin $\tilde f(s) = \int_0^\infty f(x)x^{s-1}dx$;
  main term $\tilde f(1-it)P^{1-it}$ (no $1/(1-it)$).  Edge `smoothPrimeSumVK_of_VKZ` from Prop 3 by Mellin
  inversion and a rectangle contour.  PNT+ already has `MellinCalculus`, `ResidueCalcOnRectangles` and
  the smoothed-Chebyshev contour argument behind `MediumPNT`, which is this edge with $t = 0$ and the
  classical region; porting it with the twist $n^{-it}$ and the VK region is the realistic Lean route (~60%
  feasible in a few laps).
  - Control 3c (for the node): drop $P \le T$ and fix $T = 3$; then the node claims
    $\sum\Lambda(n)f(n/P) = \tilde f(1)P + O(P^{1-\theta})$ with $\theta = 1/(\log 3)^{2/3+\varepsilon}$ close to
    $0.94$, contradicting the $\Omega(P^{1/2})$ oscillation from the zeros on the critical line (explicit
    formula; ~90%).  Control 3d: with MR's main term $\tilde f(1-it)P^{1-it}/(1-it)$ under the standard
    transform, $t = 1$ and $f$ a nonnegative bump concentrated near $1$ (so $\tilde f(1-i) \approx \int f \ne 0$)
    give a discrepancy $\asymp P$: **false**.
- **W1** (balanced witness ⇒ margin): PROOF Lemmas 1-2.  Elementary.
- **W2** (variance ⇒ count, Chebyshev + covering): PROOF §7.  Elementary.
- **W3** (the variance bound): PROOF Proposition 6 from Props 1, 2, node `SmoothPrimeSumVK`, and Lemma 5.
  One inequality, $\int|PQ|^2 \le \sup|P|^2\int|Q|^2$.
- **Headline `almost_all_F385`**: for every $\delta \in (0, 1/4)$,
  $\#\{n \le X : F(n) < n + (1-\delta)\sqrt n\}/X \to 0$ as $X \to \infty$, with hypotheses Props 1-3
  (Prop 4 as a theorem from `MediumPNT`).  Freeze the $o(X)$ form; the rate is a later strengthening.

