# Literature: Erdős #385 / #430 (companion to `PROBE-ERDOS-385.md`)

Searched 2026-10-01.  Instruments:
- arXiv export API, by title, abstract and author.
- `papers followups` on Granville 2010.01211, Sawin 1809.05137 and BBR 1302.0625.
- Full text (pdftotext) of BBR, Sawin 2018, Sawin–Shusterman, Gorodetsky, Granville and Ford.
- Tao's 2024-08-19 post including all 24 comments.
- The erdosproblems pages for #385, #430 and #463, plus the #385 forum thread.
- `gh pr list` on google-deepmind/formal-conjectures.

A miss below means "not found by these instruments".

## 1. Function-field analogue

**Already posed.**  Will Sawin stated the `F_q[T]` analogue himself, in the comments on Tao's post
(2024-08-22): given monic `f`, find `g` such that the least prime factor of `f − g` has degree
`> deg g`.  He then analysed the semiprime case at fixed `q` using GRH alone (no geometric input):
- The count of `ab` with `deg(f − ab) < deg a ≤ deg b` is a sum over short-interval characters.
  The trivial character gives the main term `q^n`.
- Each of the `q^{n−m} − 1` other characters contributes at most `(n − m − 1)² q^{n/2}` under GRH.
  That is not enough.
- Strong GUE-type assumptions on magnitudes only reach `(n − m − 1)`.  Phase or ratios-conjecture
  control would be needed.

Tao replied that GUE-type hypotheses "narrow the gap" but probably don't close it.

**Large-q limit: an immediate corollary.**  Bank, Bary-Soroker, Rosenzweig, *Prime polynomials in
short intervals and in arithmetic progressions*, arXiv:1302.0625, Thm 2.3:

> For every partition λ of k, every q, every f ∈ M(k,q) and 3 ≤ m < k,
> `|π_q(f + P_{≤m}; λ) − P(λ) q^{m+1}| ≤ c(k) q^{m+1/2}`.
> Here `P(λ)` is the probability that a permutation in S_k has cycle type λ.  One may take m = 1
> if p ∤ k(k − 1), and m = 2 if p ≠ 2 or deg f′ > 1.

Take λ = (m + 1, k − m − 1) with k ≥ 2m + 2.  Then for q ≥ q₀(k), every f has a composite
`g ∈ f + P_{≤m}` with every factor of degree `> m ≥ deg(f − g)`.  Taking m ≈ k/2 − 1 gives the
analogue of `F(n) ≥ n + (1 − o(1))√n`.  Confidence 95%.

**q polynomially large in n: very likely a corollary as well.**  Sawin, *Square-root cancellation
for sums of factorization functions over short intervals in function fields*, arXiv:1809.05137:
- Thm 4.5 / Cor 4.4 bound every irreducible-representation factorization function on a short
  interval by `3(n+2)^{O(n)} q^{(n − m + ⌊n/p⌋ − ⌊m/p⌋ + 1)/2}`.
- The indicator of a cycle type is a combination of these.
- So the analogue should hold whenever p > n and q ≥ (n+2)^C for a modest C.  Abstract: "not yet
  nontrivial in the large n limit".
- I did not compute C.  Confidence 70%.

**Fixed q, n → ∞: open, and stuck at the square-root barrier.**  Gorodetsky, *Mean values of
arithmetic functions in short intervals and in arithmetic progressions in the large-degree limit*,
arXiv:1810.00483, Thm 1.1 (fixed q):

> `|⟨α⟩_{I(f₀,h)} − ⟨α⟩_{M_n}| ≤ max|α| · q^{n/2 − h − 1} · e^{O_q(n log log n / log n)}`
> for any factorization function α, where `I(f₀,h) = {f : deg(f − f₀) ≤ h}`.

This is nontrivial only for `lim sup h/n > 1/2`.  The #385 analogue needs two factors of degree
`> h`, so `h < n/2`.  That is just below Gorodetsky's range: the same square-root wall as the
integers under RH.

Sawin–Shusterman's fixed-q parity breaking (arXiv:1808.04001) works for special q, Thm 1.1 needing
`q > 685090 p²`.  It works through Möbius on special subspaces `r + s^p` (via Pellet), Chowla
correlations, and Burgess-beating character sums (Thm 1.4: `q > e²/η²`).  Not found by followups:
any application to semiprime or rough-composite counts in short intervals below the square root.

**On framing.**  "No Siegel zeros in `F_q[T]`" is true (Weil RH) but is the wrong selling point.
Even at fixed q with full RH, the obstruction that remains is the square-root barrier, and Sawin
already worked out how far GRH/GUE gets.  Siegel zeros are one enemy; the RH-level barrier is
another, as Tao also says.

**Verdict, door 1:** large-q is a one-line BBR corollary (not new).  Fixed q is open and already
scoped by Sawin.  The only new opening is SS-style special-q geometry, which is a hard research
lane, not a quick test.  Downgrade door 1 from first to "speculative".

## 2. Exceptional-set results

- **Zero density is trivial**: bad ⇒ n − 1 prime (CKS, Tao blog comments, 2024-08-21/23).  CKS
  also shows `F(n) ≥ n` always (`m = n − 2` gives equality when `n = p + 1`).  So bad ⟺
  `F(n) = n`.  And `F(p² + 1) − (p² + 1) ≥ p − 2`, so `lim sup (F(n) − n) = ∞` trivially.
- **Tao (blog reply, 2024-08-19), the strong almost-all form "should be well within reach"**:
  - Huxley (θ > 1/6), now Guth–Maynard arXiv:2405.20552 (θ > 2/15), give primes in almost all
    `[n − n^θ, n]`.
  - "The same technology should show, for θ slightly below 1/2, that almost all such intervals
    contain semiprimes whose prime factors are at least `n^θ`."
  - That would give `F(n) = n + n^{1/2 + o(1)}` for almost all n.
  - Stated without proof.  Not found written up anywhere (arXiv abstract searches for
    semiprimes / E₂ / rough numbers in almost all short intervals with large factors).
- **Almost-prime literature has the wrong factor size.**  Teräväinen arXiv:1510.06005 (E₂ in almost
  all `[x, x + log^{3.51} x]`) and Matomäki–Teräväinen arXiv:2207.05038 (`log^{2.1}`) use one
  *small* prime factor.  We need both factors larger than the interval length.
- **Sawin's reformulation (blog)**: the semiprime case ⟺ ∃ prime `p < √n`, `p ∤ n`, `⌊n/p⌋` prime.
  This is the same as our form 2.  Ma–Wu arXiv:2112.12426 count primes in `{⌊x/n⌋ : n ≤ x}`, but
  n runs over all integers, not primes; not directly usable.
- **grpaseman (blog, 2024-08-22)**: covering by open intervals `(pq, pq + p)`, `p < q` primes,
  leaves 495 uncovered integers up to 10^7, the largest 267689.

**Verdict, door 2:** retarget it.  The worthwhile almost-all theorem is Tao's: for almost all n,
`F(n) − n ≥ n^{1/2 − ε}`.  That covers parts (ii) and lb on a density-one set.  It goes via
zero-density / large-value estimates for semiprimes in almost all intervals of length `n^θ`, θ
just below 1/2.  Tao calls it within reach and no one has written it.  The X/(log X)^B count of
bad n is weaker and less interesting.

## 3. The Ford and Granville Siegel-zero papers Tao cites

- **Granville, "Sieving intervals and Siegel zeros"**, arXiv:2010.01211, Acta Arith. 205 (2022),
  1-19 (zbMATH 1504.11089).
  - Assuming infinitely many Siegel zeros, for each v > 1 there are arbitrarily large x, X, y,
    z = y^{1/v} with `S(x,y,z) = (F(v)+o(1))G(z)y` and `S(X,y,z) = (f(v)+o(1))G(z)y` (Cor 1).
  - So the linear-sieve bounds are sharp for intervals.  For v ≤ 2, f(v) = 0: an interval of
    length y, sieved by `0 mod p` for p ≤ √y, can have almost no survivors.
  - Cor 2: `J(m) ≫ ω(m)(log ω(m))^B` (Jacobsthal).  Cor 3: admissible sets of length y with
    `~2y/log y` elements.
- **Ford, "Large prime gaps and progressions with few primes"**, arXiv:1907.11994, Riv. Mat. Univ.
  Parma 12 (2021), 41-47 (zbMATH 1480.11111).
  - Progressions with few primes (e.g. from exceptional zeros, Thm 1.4) imply larger prime gaps.
- Neither mentions Erdős, least prime factors, or #385 (pdftotext grep).
  - Granville's Cor 1 is exactly Tao's one-scale enemy: classes `0 mod p` at a specific location.
  - But it is one scale at a time.  No conditional construction of infinitely many bad n
    (all scales at once, every survivor prime) was found.  Followups of 2010.01211 (8 papers)
    include nothing on #385.

**Verdict, door 3 (repulsion / inverse):** a conditional *disproof* is open too.  The missing step
in both directions is the same: making one n bad at every scale simultaneously.  That
cross-scale coupling is the only genuinely unexplored joint.  It is also what a proof via
repulsion would have to exploit.

## 4. Mechanism ideas in comments and the forum

- **Tao blog (24 comments):**
  - Sawin's function-field analysis (§1).
  - Tao's almost-all claim (§2).
  - CKS's reductions (§2).
  - grpaseman's covering statistics.
  - Tao's reply to Sawin: "outside chance that the ability to work with the best-case m rather
    than the worst-case m might possibly help narrow the gap even further, but I don't see a
    mechanism ... saving an additional factor of maybe √n perhaps, at best."
  - Nothing else mathematical.
- **erdosproblems forum #385 (2 comments):** computation only.
  - Leandre Jack (2026-09-03): to 10^11, code at github.com/leandrejack-afk/erdos-computations.
  - Aleksanndr_NFA (2026-09-23): to 1.0011·10^12, min `F(n) − n` per shard ≈ 0.9√n.
- **#430 page:** no comments.  **#463 page:** no comments.

**Verdict:** Tao's "best-case m" remark (optimising over which semiprime shape m to use) is the
one unexploited idea on record.  It lives inside door 3.

## 5. Related problems and Lean statements

- **#463** (open): is there f → ∞ such that for all large n there is a composite m with
  `n + f(n) < m < n + p(m)`?
  - This is the upward mirror of #385, with a growing gap.
  - Er92e asks whether `n − min_{m>n}(m − p(m)) ~ c n^{1/2}`.
  - In formal-conjectures as `ErdosProblems/463.lean` (`erdos_463`, `m.Composite ∧ n + f n < m ∧
    m < n + m.minFac`).
- **formal-conjectures #385**: `ErdosProblems/385.lean` (parts i, ii, variant lb; PR #1858;
  `trivial_ub` proved in PR #4147).
  - PR #2903 (closed, 2026-03) claimed all three "formally solved" via an answer-loophole.  It was
    not a proof.
- **formal-conjectures #430**: **open PR #5261** (leandrejack-afk, 2026-09-03) adds
  `ErdosProblems/430.lean`.  So our catalog note "not in formal-conjectures" is true of `main` but
  a statement is in flight.  Don't duplicate it; a review or equivalence edge could attach there.

**Verdict:** add #463 to the wish list as a sibling (same mechanism, upward).  Drop "state #430
for FC" as a by-product; PR #5261 covers it.
