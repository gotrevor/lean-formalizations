# Sun 2026, "Catalan's constant is irrational" — analysis, refutation, and the salvage

**Status: the paper is wrong.  There is no irrationality proof here.  One piece is worth
formalizing anyway.**  This file is a self-contained briefing: hand it to a fresh session and it
should need nothing else except the PDF sitting next to it.

| | |
|---|---|
| Paper | Zhi-Wei Sun, *Catalan's constant is irrational*, [arXiv:2609.04176v1](https://arxiv.org/abs/2609.04176), 3 Sep 2026 |
| Local PDF | `papers/sun-2026-catalan-irrationality.pdf` (gitignored, local-only) |
| Check script | `papers/sun-2026-catalan-twoadic-check.py` (committed; uv shebang, run it directly) |
| Analysed | 2026-09-04, against **v1**.  Everything below is a claim about v1. |
| Author | Nanjing University; a serious number theorist (the K = L(2, χ₋₃) series conjectures are his) |
| AI provenance | Acknowledgments: *"The author's many rounds of conversations with AI provide the basis of this paper... The whole proof has passed the verification of Chatgpt 5.6 Solar."* |

## 1. What it claims

`G = β(2) = Σₖ (−1)ᵏ/(2k+1)² = 0.9159655…` is irrational.  This is a genuinely famous open
problem — arguably the most famous open irrationality question after Euler–Mascheroni γ.
Calegari–Dimitrov–Tang ([arXiv:2408.15403](https://arxiv.org/abs/2408.15403), 2024) proved the
sibling `L(2, χ₋₃)` irrational and said explicitly that their method does **not** reach `G`.
Sun's acknowledgments say he first asked the AI to push CDT through, failed repeatedly, and then
supplied the weighting idea himself.

## 2. The architecture (five stages, in the paper's own words plus what they mean)

Assume for contradiction `G = a/q`, `gcd(a,q) = 1`.  Define tails and **weighted** tails:

```
S_{m−1} = Σ_{k<m} (−1)ᵏ/(2k+1)²        T_m = (−1)^m (G − S_{m−1}) = Σ_{r≥0} (−1)^r/(2m+2r+1)²
u_m = T_m / (2m+1)                      T_m + T_{m+1} = 1/(2m+1)²        0 < T_m < 1/(2m+1)²
```

The `1/(2m+1)` weight is Sun's own contribution and the reason the construction closes at all.
Then, with parameters `B > S` (eventually `S = ⌊B/20⌋`, `ρ = S/B = 1/20`), `D = 2B`,
`N = 2B + S + 3`, and `Πᵢ = ∏_{h=1}^{B} (2(h+i)+1)²`:

1. **§2, Thm 2.1.**  The `(S+3) × S` weighted finite-difference residual matrix
   `R_{a,j} = Σ_{i=0}^{a+2B} (−1)ⁱ C(a+2B, i) Πᵢ u_{i+j}` has full column rank `S`.
2. **§3.**  Pick `A ⊂ {0,…,S+2}`, `|A| = S`, with `det R[A,J] ≠ 0`.  Three binomial Newton
   columns complete the selected minor to one `N × N` determinant, producing the scalar
   `q̂_B = ± F_B · det R[A,J] / ∏_{i<N} Πᵢ`, where `F_B = ∏_{r<2B} r!`  … **(3.5)**
   and its exact minimal integerizer `H_B^min :=` denominator of `q^S q̂_B`.
   So `N_B := q^S H_B^min q̂_B ∈ ℤ \ {0}`  … **(3.8)**
3. **§4.**  Cauchy–Binet on `qR` = Pascal × diagonal × Cauchy; each summand carries a Vandermonde
   `V(I)` twice, a fixed `V(J) = ∏_{0≤u<v<S}(v−u)`, and a Cauchy determinant.
4. **§5–§8.**  For every odd prime power a local saturation theorem (Thm 5.1, `a_{Q,B} ≥ m^A_{Q,B}`)
   converts local lower bounds into an upper bound on the positive-part height (Cor 5.2), then the
   three prime ranges `Q ≤ S`, `S < p < B`, `p > B` are evaluated (`c_odd`, `Λ_mid`, `83/2400`).
5. **§9.**  A ledger at `ρ = 1/20` claims `log|N_B| ≤ −δ₀B² + o(B²)` with `δ₀ > 0.00966242…`, hence
   `0 < |N_B| < 1` for large `B`.  Contradiction, QED.

## 3. The fatal error

**Read the 2-adic valuation of the paper's own integer `N_B`.**

- Every `Πᵢ = ∏(2(h+i)+1)²` is a product of odd squares ⇒ `v₂(∏_{i<N} Πᵢ) = 0` **exactly**.
- **Lemma 5.4** (the paper's own): with `G = a/q`, `qT_m = ±(a − q·S_{m−1})` and `S_{m−1}` has odd
  denominators, so every entry of `qR` is in `ℤ₍₂₎`; hence `v₂(q^S det R[A,J]) ≥ 0` and
  `H_B^min` is odd.
- Therefore, from (3.5):
  `v₂(N_B) = v₂(F_B) + v₂(q^S det R[A,J]) ≥ v₂(F_B)`.
- `v₂(F_B) = Σ_{r<2B} v₂(r!) = Σ_{r<2B}(r − s₂(r)) = 2B² − O(B log B) = 2B²(1+o(1))`
  (measured: `v₂(F_B)/2B²` = 0.958 at B=100, 0.9941 at B=1000, 0.9993 at B=10⁴).

A **nonzero** integer divisible by `2^{v₂(F_B)}` satisfies

```
log|N_B| ≥ (2 log 2) B² (1 + o(1)) ≈ +1.386 B²          while Theorem 9.1 claims  ≤ −0.00966 B².
```

The ledger is off by ≈ **1.4 B²**.  Note this kills §9 regardless of the sign of `δ₀`: even the raw
claimed quadratic coefficient `4ρ − 2ρ² = 39/200 = 0.195` is far below `2 log 2 = 1.386`.

### Where exactly it goes wrong

Prop 9.5's sentence *"The B² log B terms cancel because the denominator baseline `a_{Q,B}` and the
real normalization come from the same fixed scalar"* is the false step.  At the **real** place
`F_B ~ 2B² log(2B)` genuinely can cancel against `∏Πᵢ ~ 4B² log B`; **2-adically `∏Πᵢ` contributes
nothing at all**, so `F_B`'s entire `2^{2B²}` survives into `N_B`.  There is no cancellation
available at p = 2, and the paper never looks (Remark 9.3 asserts the prime 2 "is not silently
discarded" and then only discusses `H_B^min`'s positive part, which is indeed 0 — that is the wrong
quantity).

A second, independent symptom of the same bookkeeping looseness, which others spotted: the fixed
Vandermonde `V(J) = ∏_{0≤u<v<S}(v−u)` is dropped in Lemma 5.3 (legal for a *lower* bound) and never
restored in the §9 ledger, leaving an uncancelled `(ρ²/2) B² log B = B² log B / 800 → ∞`.

Smaller defects noted in the public discussion, all repairable and none of them the real problem:
a sign `(−1)^{j−1}` vs `(−1)^j` and a `k=0` index issue around (2.3)–(2.4); (2.5) reads
`n ∈ {2B, 2B+S+2}` where the next page needs the whole range; `D` and `F_D` used before definition
(dimensions force `D = 2B`, `F_D = F_B`).

### Numerical confirmation (this is our own measurement, not a relay)

`papers/sun-2026-catalan-twoadic-check.py` builds the paper's `R`, `q̂_B`, `H_B^min`, `N_B`
**exactly over ℚ** (`fractions.Fraction`) under a fake rational `G = a/q`, for every admissible row
set `A`, and prints valuations.  Run it directly (uv shebang, ~2 s):

```
./papers/sun-2026-catalan-twoadic-check.py
```

Result at `B = 4, 5, 6`: `v₂(H_B^min) = 0` in every case (Lemma 5.4 confirmed), and
`v₂(N_B) = v₂(F_B) + v₂(q^S det R) ≥ v₂(F_B)` in every case, with `|N_B|` running **43 to 125
decimal digits**.  The inequality `v₂(N_B) ≥ v₂(F_B)` is a structural identity holding at every `B`;
the asymptotic `v₂(F_B) ~ 2B²` then does the killing.  (Theorem 9.1 is asymptotic, so the small-`B`
digit counts are *not themselves* the refutation — the structural identity plus the asymptotic is.)

## 4. Is it patchable?

**No, not as a patch.**  The gap is ~1.4 B² against a margin of 0.0097 B²: two orders of magnitude,
not a lost constant.  Any repair must change the *construction* so that `F_B` no longer enters `N_B`
against an all-odd normalizer — i.e. redo stages 3–5.  Stages 1–2 survive; nothing downstream of §3
does.  Sun was reported (WeChat, 2026-09-04) to be claiming a correction; **if you pick this up
later, first check whether a v2 exists and whether its normalization changed**, because everything
in §3 above is a statement about v1 only.

## 5. What is worth formalizing

### 🟢 Target A — Theorem 2.1, full column rank of the weighted residual matrix

The one clean, correct, self-contained mathematical object in the paper, and completely independent
of the broken asymptotics.  Statement:

> For integers `B > S > 0`, with `Πᵢ = ∏_{h=1}^{B}(2(h+i)+1)²` and
> `u_m = T_m/(2m+1)` the weighted Catalan tails, the `(S+3) × S` matrix
> `R_{a,j} = Σ_{i=0}^{a+2B} (−1)ⁱ C(a+2B, i) Πᵢ u_{i+j}` (`0 ≤ a ≤ S+2`, `1 ≤ j ≤ S`)
> has rank `S`.

Proof ingredients, all elementary and all in mathlib's reach:
- the telescoping identity (2.3): `T_{i+j} = (−1)ʲ T_i + Σ_{0≤k<j} (−1)^{j−1−k}/(2(i+k)+1)²`;
- the finite-difference annihilation of polynomials of degree `< n`
  (`Σ_i (−1)ⁱ C(n,i) p(i) = 0`, van Lint–Wilson p.126 (13.13)) — mathlib has this shape via
  `Finset.sum_range_choose_mul_pow` / Newton forward differences; check
  `Mathlib/Analysis/Calculus/FDeriv` no, rather `Mathlib/Combinatorics/…` and
  `Polynomial.sub_one_pow…`; a hand-rolled induction is fine and is probably faster than the hunt;
- Newton interpolation degree bound, then the auxiliary
  `K(X) = (2X+3)²[A(X)D_λ(X+1) + A(X+1)D_λ(X)] − D_λ(X)D_λ(X+1)` with `2B+S+2` integer zeros plus
  `deg G₀ = 2B−S−2` half-integer zeros plus `K(−3/2) = 0`, versus `deg K ≤ 4B`, forcing `K ≡ 0`;
- the `K ≡ 0` branch is excluded by the Gosper-style functional equation
  `R(X) + R(X+1) = 1/(2X+3)²` having no rational solution (paper's §2 tail, p.6, worth reading
  closely — this is the one step where the write-up is thin).

Estimated shape: a few hundred lines, one file, no exotic imports, `Matrix.rank` over `ℝ` (or over
the field `ℚ(G)`).  Fits the house pattern of a self-contained `NumberTheory/` leaf.
**Caveat before starting:** Thm 2.1's proof is the part of the paper least scrutinized publicly —
we checked it by reading, not by machine.  Expect to find at least the (2.3) sign slip.

### 🟢 Target B — the refutation as a machine-checked no-go

Genuinely mechanizable and small: define the paper's `q̂_B`/`N_B` schematically and prove

```
(∀ i, Odd (Πᵢ)) → (2-integrality of qR) → 2 ^ v₂(F_B) ∣ N_B → N_B ≠ 0 → |N_B| ≥ 2 ^ v₂(F_B)
```

The last implication is trivial in Lean (`Int.le_of_dvd`); the content is the divisibility, which
needs the determinant `v₂ ≥ 0` argument.  Combined with `v₂(F_B) ≥ 2B² − O(B log B)` it is a
complete, checkable contradiction with Theorem 9.1's statement.  This is a nice artifact — a Lean
certificate that a headline AI-assisted claim is false — but it is *adjudication*, not mathematics,
so weigh it as such.

### 🔴 Not a target

The main theorem.  There is nothing to formalize; Catalan's constant remains open.

## 6. Surrounding context you'll want

- **Community reaction (2026-09-04):** r/math and r/mathematics both lit up within hours; an OpenAI
  researcher posted the "claimed negative bound is wrong" call on X; multiple people independently
  ran the paper through models and converged on Prop 9.5 / the same 2-adic contradiction.  The
  interesting meta-fact is the *speed* of refutation, and that the author's stated verification
  (`"passed the verification of Chatgpt 5.6 Solar"`) was the same model family that produced the
  proof — self-verification by the generating context, which is close to no verification.
- **Our π/e work** is unrelated in method: `src/LeanFormalizations/NumberTheory/Transcendence/`
  (`ETranscendental.lean`, `PiLindemann.lean`, `PiTranscendental.lean`),
  `transcendental_pi_axiomClean`, axiom-clean, built on mathlib's `exp_polynomial_approx`.
  ⚠️ Correction to something I said in session: Trevor **did** open a mathlib PR on that subject —
  [mathlib4#43144](https://github.com/leanprover-community/mathlib4/pull/43144), a `docs/100.yaml`
  claim on entry 53 ("Pi is Transcendental") adding `authors` + `links.result` pointing at our
  external Lean 4 file.  Open as of 2026-09-04, self-labelled `LLM-generated`, no reviews.  It is a
  documentation-pointer PR, not a mathematics PR, which is why it is compatible with the standing
  "no mathlib PRs" stance; the in-mathlib slot belongs to
  [#28013](https://github.com/leanprover-community/mathlib4/pull/28013) (Yuyang Zhao,
  Lindemann–Weierstrass) when it lands.
- **Frontier for `G`:** Calegari–Dimitrov–Tang's arithmetic-holonomy method is the live line, and
  they say `G` is out of its reach.  Nesterenko (Steklov 292, 2016), Rivoal (Ramanujan J 11, 2006),
  Rivoal–Zudilin (Math. Ann. 326, 2003) and Zudilin (Abh. Hamburg 89, 2019) are the standard
  approach-and-obstruction references, all cited in the paper.
- **KB leaf** with the transferable lesson:
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/2026-09-04-catalan-irrationality-claim-refuted.md`.

## 7. The transferable lesson 🔬

**A real-place cancellation is not a p-adic cancellation.**  When a ledger says "these two big
factors cancel because they come from the same scalar," check it one prime at a time: a factorial in
the numerator against an all-odd denominator cancels perfectly at ∞ and not at all at 2.  That audit
is cheap, decisive, and applies to *any* Nesterenko/Apéry-style irrationality argument — and it is
exactly the sort of bookkeeping an LLM-assembled asymptotic ledger drops, because the ledger is
written at one place and never re-read at the others.
