# OEIS: what we would add

Everything below is ready to submit, but is **not** submitted.  OEIS's
[Use of AI for OEIS Submissions](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)
(approved 2026-08-29) forbids AI-generated comment text, AI text in replies to editors, and AI
co-authorship.  This work is AI-assisted end to end, so we are not contributing (decided
2026-09-28).  This page keeps the edits lined up in case either side changes its mind.

Trevor has an approved OEIS account ([User:Trevor_Morris](https://oeis.org/wiki/User:Trevor_Morris)).
To edit an entry: sign in at oeis.org/login, open the entry, click **edit** next to the data.
Typing `~~~~` at the end of a comment signs and dates it.

## 1. The literature hole: transcendence of the growth constants

A003095 and A000058 cite Wagner–Ziegler (2020) for *irrationality* of their growth constants.
None of the five sequences below, nor the three constant entries, cites Dubickas (2022), which
proves the constants *transcendental*.

| Dubickas | recursion | sequence | OEIS constant |
|---|---|---|---|
| κ = 1.502837… | x² + 1 | A003095 (a(0) = 0) | A076949 = 1.2259024… |
| ζ = 1.678458… | x² − 1 | A003096 (a(0) = 2) | A077124 = 1.295553… |
| γ = 1.597910… | x² − x + 1 | A000058, Sylvester | A076393 = 1.2640847… (Vardi) |
| η | x² + x + 1 | A002065 (a(0) = 0) | 1.385089… (in-entry, no A-number) |
| τ | x² + 2x + 1 | A004019 (a(0) = 0) | "b" in Bottomley's formula |

Each OEIS constant is the square root of Dubickas's (his indexing starts one step earlier).
The square root of a transcendental number is transcendental.  Re-derive the η and τ
normalisations from the entry offsets before submitting.

**Link (%H), for all eight entries** (bibliographic data):

```
Artūras Dubickas, <a href="https://doi.org/10.1007/s11139-021-00428-5">Transcendency of some constants related to integer sequences of polynomial iterations</a>, Ramanujan J. 57 (2022), 569-581.
```

**Comment (%C), the fact to state** (under OEIS rules the submitter writes the wording):
the growth constant `lim a(n)^(1/2^n)` is transcendental, by Dubickas's Theorem 1.  For
A000058, Vardi's `c = A076393` has `lim a(n)^(1/2^n) = c^2`.

**Lean.**  `src/LeanFormalizations/NumberTheory/Transcendence/Dubickas.lean`
(`transcendental_growth_of_monic_quadratic`, `theorem1`, `oeis_constants`).  It is conditional
on one hypothesis, Dubickas's Lemma 6 (Corvaja–Zannier, from the `p`-adic Subspace Theorem).
His Lemma 8 has been eliminated (`DubickasNoGap.lean`).  Why Lemma 6 has no elementary route:
`PROBE-DUBICKAS-NOSUBSPACE.md`.  Trevor's rule: no Lean link for this claim until it is
unconditional.

## 2. A000058: an offset mismatch

Murthy's comment (Sep 24 2003) reads: "a(1) = 2, then the smallest number == 1 (mod all
previous terms).  a(2n+6) == 443 (mod 1000) and a(2n+7) == 807 (mod 1000)."  It is correct in
its own 1-based indexing, but the entry has offset 0 (a(0) = 2), under which a(4) = 1807 and
a(5) = 3263443, so the residues are a(2n+4) ≡ 807 and a(2n+5) ≡ 443 (mod 1000).  Fix: re-index
in place and append `[Indices adjusted to offset 0 by _Trevor Morris_, <date>]` (precedent: the
"[Corrected by …]" note on A003095).  Lean: `sylvesterSeq_mod_1000` in
`NumberTheory/PolyIteration/Siblings.lean`.

## 3. Unconditional Lean formalizations of existing comments and formulas

All sorry-free with the standard axioms only.  Link format precedent: A117531, A252864, A237271
(`Name, <a href="…">title</a>, year.`).

**A003095**: `NumberTheory/PolyIteration/A003095.lean`
strong divisibility (and the shifted `a(n+k) ∓ a(k)` families, Bala 2026); Bala's identities
`a(n+m) − a(m) = a(n)² ∏ (a(n+k) + a(k))`, `a(n)² ∣ a(n+m) − a(m)` (for `m ≥ 1`),
`a(n) − a(k) ∣ a(mn) − a(mk)`; all four Bala conjectures as proved by Harden (exact periods 2,
6, 6 modulo `2^k`, `10^k`, `20^k`, with Harden's thresholds, and the digit stability of
`a(6n+i) mod 10^k`); Somos's cubic relation; the last-digit cycle; `a(n) ≡ n (mod 2)`.

**A000058**: `NumberTheory/PolyIteration/Siblings.lean`
`a(n) = 1 + a(0)⋯a(n−1)`; pairwise coprime; `Σ 1/a(n) = 1`; no term is a square; `−3` is a
quadratic residue modulo every prime factor; Wilson's `a(k)² + 1 ∣ a(k+1)² + 1`;
`a(n) + a(n+1) ∣ a(n)a(n+1) − 1`; Bala's `a(n+2) − a(n+1) = a(n)² (a(n+1) − a(n))`; residues
modulo 3000, 1000 (offset-0 form) and 864 (`a(n+2) ≡ 7 + 36n`); Mohanty's coprime family;
`a(n+k) − a(k)` is a strong divisibility sequence.

**A003096, A002065, A004019**: same file.  A003096: no term after a(1) is prime, consecutive
terms coprime.  A002065: strong divisibility sequence (the entry says only "divisibility").
A004019: `a(n) = A003095(n)² = A003095(n+1) − 1`, strong divisibility, shifted family.

**Any `a(n+1) = P(a(n))`**: `NumberTheory/PolyIteration/Sylvester.lean` (Sylvester's theorem,
Bala's Theorem 1) and the general section of `Siblings.lean` (Bala's divisibility formulas; his
`a(n) ≠ a(k)` proviso turns out to be unnecessary).

## 4. Before submitting anything

* Link to files on `main` by path, and keep the linked files where they are (moving one breaks
  the OEIS link) and building on current mathlib.
* Check each Lean statement against the entry's current offset and wording.
* Under OEIS's AI rules: human-written comment text, no AI text in pink-box replies, no AI
  credit.
