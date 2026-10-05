# Faithfulness audit: `Literature.Saito2025TypeBTrace`

Target: `src/LeanFormalizations/Literature/Saito2025.lean` (`Saito2025TypeBTrace`, `powTrace`) and `IsPisot` in `src/LeanFormalizations/Literature/Pisot.lean`, checked against K. Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068v3 (local text `papers/saito-2025-transcendency-variants-mills.txt`, which carries the stamp "arXiv:2508.16068v3 [math.NT] 7 Dec 2025").  Audited 2026-10-05.

## Verdict

**Faithful-or-weaker: yes, with caveats that need no change to the Lean statement.**  Confidence 93% that the Prop is implied by what v3 of the paper states and proves.  That figure covers faithfulness only.  Whether the paper itself is correct is a separate question, discussed briefly below.

One structural point first.  The Prop is not one numbered statement from the paper.  It combines what Theorem 2.3 *states* with Proposition 3.1(iv), which Theorem 2.3's statement does not mention.  The combination is licensed by the *proof* of Theorem 2.3 (Section 8, first two paragraphs), which checks every hypothesis of Proposition 3.1, (3.1) included, from (B1) to (B5) with θ = 21/40, and then uses the `g` of Proposition 3.1(ii) as the `g` of Theorem 2.3.  I traced that step and it holds (rows 9 and 10 below).

## Paper statements used

* **W and ξ** (Section 1): `W(C_k) = {A > 1 : ⌊A^(C_k)⌋ ∈ P for every k ∈ ℕ}` with ℕ the positive integers, and `ξ(C_k)` is the smallest element of `W(C_k)`.  Lemma 4.1: if `W` is non-empty, the smallest element exists.  Theorem 1.3: `c_1 > 0` and `c_(k+1) ≥ 2` for all k make `W` non-empty.
* **Notation**: `c_1 = C_1`, `c_(k+1) = C_(k+1)/C_k`, so `C_k = c_1 ⋯ c_k`.
* **Theorem 2.3 (Type B)**: under (B1) `c_1 ≥ 1`, (B2) `c_(k+1) ≥ 2` for all k ∈ ℕ, (B3) `lim sup c_(k+1) > 40/19`, (B4) `C_k ∈ ℕ`, ξ exists.  For ε small enough that `I = {k : c_(k+1) ≥ 40/19 + ε}` is infinite, assume (B5): for every m ∈ ℕ there is k ∈ I, k > m, with `C_m | C_k`.  Then ξ is transcendental, or some `g ∈ ℕ` makes `ξ^g` a Pisot number of degree ℓ with `3 ≤ ℓ ≤ 1 + (19/40 · lim sup c_(k+1) − 1)^(−1)`, and `g | C_k` for every sufficiently large k ∈ I.  (B6) and the second conclusion are not used.
* **Proposition 3.1**: θ ∈ [1/2, 1) satisfying (†); (G1) to (G4) as (B1) to (B4) with `1/(1 − θ)` in place of 40/19 in (G3), and (G4) only for large k.  Further assume (3.1) `ξ^(C_m) ∉ ℕ` for every m, and that ξ is algebraic.  Take ε with (3.2) `0 < ε < lim sup c_(k+1) − 1/(1 − θ)` and the corresponding I.  Then (ii) there is g with `β = ξ^g` Pisot of degree ℓ, `2 ≤ ℓ ≤ 1 + ((1 − θ) lim sup c_(k+1) − 1)^(−1)`, and `g | C_k` for large k ∈ I; (iv) `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` for every sufficiently large k ∈ I.
* **Theorem 1.6** (Baker, Harman, Pintz): (†) holds for θ = 21/40, so `1/(1 − θ) = 40/19`.
* **Tr** (Section 3): `Tr(β) = β_1 + ⋯ + β_ℓ`, the sum of all conjugates of β over ℚ.  Lemma 5.8 uses `Tr(β^s) = β_1^s + ⋯ + β_ℓ^s`, justified by Lemma 5.7 (a power of a degree-ℓ Pisot number is a Pisot number of degree ℓ).

## Clause-by-clause comparison

Hypotheses must be at least as strong as the paper's; conclusions at most as strong.

| # | Lean clause | Paper counterpart | Direction | OK? |
|---|---|---|---|---|
| 1 | `C : ℕ → ℕ` | real `c_k` with (B4) `C_k ∈ ℕ` | Lean is the special case `c_1 = C 1`, `c_(k+1) = C (k+1) / C k`; any Lean `C` gives a paper sequence | yes |
| 2 | `1 ≤ C 1` | (B1) `c_1 ≥ 1`, and Theorem 1.3 (1) `c_1 > 0` | identical | yes |
| 3 | `∀ k ≥ 1, 2 * C k ≤ C (k + 1)` | (B2) `c_(k+1) ≥ 2` for all k ∈ ℕ (positive), Theorem 1.3 (2) | identical; rows 2 and 3 give `C k ≥ 1` for k ≥ 1, so the division is legal | yes |
| 4 | `∀ K, ∃ k ≥ K, 29/10 * C k ≤ C (k+1)` | (B3) `lim sup c_(k+1) > 40/19` | gives `lim sup ≥ 29/10 > 40/19` (40/19 ≈ 2.105); stronger.  Also redundant given row 5 | yes |
| 5 | `∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ 29/10 * C k ≤ C (k+1)` | (B5) for the chosen I | the witness k lies in `I_ε` for every `ε ≤ 29/10 − 40/19 = 151/190`.  So (B5) holds whether one reads the paper's "sufficiently small ε" as one fixed ε or as every small ε | yes |
| 6 | `C 0` unconstrained, all quantifiers over k ≥ 1 or "k ≥ K" | paper indexes from k = 1 | `C 0` never enters: W uses `k ≥ 1`, row 5 has `k > m ≥ 1`, and the conclusion's `K` can be taken ≥ 1 | yes |
| 7 | `∃ ξ, IsLeast {A | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ C k⌋₊).Prime} ξ` | "ξ = ξ(C_k) exists", the least element of `W(C_k)` (Theorem 2.3 first sentence; Theorem 1.3 with Lemma 4.1) | same set: for `A > 1` the `ℕ`-floor equals the `ℤ`-floor, and `Nat.Prime` is membership in P.  `IsLeast` is the paper's ξ, the *least* element, not an arbitrary admissible A.  `IsLeast` is unique, so the `∃` is harmless | yes |
| 8 | `Transcendental ℚ ξ ∨ …` | "either ξ is transcendental, or …"; Prop 3.1 runs under "ξ is algebraic" | `Transcendental ℚ ξ` is `¬ IsAlgebraic ℚ ξ`, so the right disjunct is exactly the algebraic case where Prop 3.1 applies | yes |
| 9 | (no Lean hypothesis for (3.1)) | Prop 3.1 assumes (3.1) `ξ^(C_m) ∉ ℕ` for all m | derived in Section 8 from (B5): if `ξ^(C_m) = n ∈ ℕ`, then n ≥ 2, take k > m with `C_m | C_k` from row 5, and `ξ^(C_k) = n^(C_k/C_m)` with `C_k/C_m ≥ 2` (C strictly increasing by row 3) is composite, yet equals `⌊ξ^(C_k)⌋`, a prime.  Row 5 supplies exactly what this needs | yes |
| 10 | (implicit) θ = 21/40 | Prop 3.1 needs θ ∈ [1/2, 1) with (†), and (3.2) for ε | 21/40 ∈ [1/2, 1); (†) is Theorem 1.6 (BHP).  Choosing ε = 151/380 gives (3.2) since `lim sup − 40/19 ≥ 151/190 > 151/380`, and `I_ε ⊇ {k : 29/10 C_k ≤ C_(k+1)}` | yes |
| 11 | `∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g)` | `g ∈ ℕ` (positive), `ξ^g` Pisot | identical; `IsPisot` checked below | yes |
| 12 | `(minpoly ℚ (ξ ^ g)).natDegree = 3` | `3 ≤ ℓ ≤ 1 + (19/40 · lim sup c_(k+1) − 1)^(−1)` | with `L = lim sup ≥ 29/10`: `19/40 · 29/10 = 551/400`, so the bound is at most `1 + 400/151 ≈ 3.649 < 4`, hence ℓ = 3.  A larger L only lowers the bound.  If `L = ∞` the paper's bound reads `ℓ ≤ 1`, the Pisot branch is empty and the paper gives "transcendental", stronger than Lean | yes |
| 13 | `∃ K, ∀ k ≥ K, 29/10 * C k ≤ C (k+1) → g ∣ C k ∧ …` | Theorem 2.3 and Prop 3.1(ii): `g | C_k` for every sufficiently large k ∈ I | stated explicitly in both.  Lean asks it only on a subset of `I_ε` (row 10); take K as the max of the two thresholds | yes |
| 14 | `powTrace (ξ ^ g) (C k / g) = (⌊ξ ^ C k⌋₊ : ℂ)` | Prop 3.1(iv): `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` for every sufficiently large k ∈ I | exact equality (no ε slack), proved from (i), (ii) and Lemma 5.8, for the least ξ, under exactly the hypotheses of rows 9 and 10.  `C k / g` is `ℕ` division, exact because the same conjunct asserts `g ∣ C k` | yes |
| 15 | same `g` in rows 11 to 14 | Theorem 2.3's g is the g of Prop 3.1(ii) ("by (ii), there exists g"), and (iv) is stated for that β = ξ^g | in the proof g is the least positive integer with ξ^g Pisot (Lemma 6.1), one g throughout | yes |

### `powTrace` against Saito's Tr

`powTrace β N` sums `z^N` over `(minpoly ℚ β).aroots ℂ`.  The minimal polynomial over ℚ is separable and splits over ℂ, so `aroots` is the multiset of the ℓ distinct conjugates `β_1, …, β_ℓ`, each once, and `powTrace β N = β_1^N + ⋯ + β_ℓ^N`.  Saito's `Tr(β^N)` is the sum of the conjugates *of* `β^N`.  The two agree when `β^N` has the same degree as β, which Lemma 5.7 gives for every Pisot β; the Lean conclusion applies `powTrace` only to `β = ξ^g` with `IsPisot (ξ ^ g)` in the same disjunct.  The Lean form is in fact the one Saito computes with (Lemma 5.8 rewrites Tr to `β_1^s + ⋯ + β_ℓ^s` first).  Faithful.

### `IsPisot` against Saito's definition

Saito: a real algebraic integer β > 1 all of whose conjugates over ℚ except β itself lie in the open unit disc.  Lean: `1 < β ∧ IsIntegral ℤ β ∧ ∀ z ∈ ((minpoly ℚ β).aroots ℂ).erase (β : ℂ), ‖z‖ < 1`.  Since the roots are distinct, `erase` removes exactly β.  Identical.  "Degree ℓ" is the degree of the minimal polynomial over ℚ, which is the Lean `natDegree`.

## Answers to the specific questions

* **(a) least or any A?**  Least.  The paper defines ξ(C_k) as the smallest element of `W(C_k)` and the Lean Prop uses `IsLeast` on the same set.  The minimality is load-bearing in the paper (Lemma 5.2 derives a contradiction from a smaller ζ ∈ W), so a statement about an arbitrary admissible A would be unfaithful; this one is not.
* **(b) exact trace?**  Yes, ε = 0: `Tr(β^(C_k/g)) = ⌊ξ^(C_k)⌋` exactly, for the least ξ, for large k ∈ I.  Extra hypotheses beyond (G1) to (G4): (†) for θ, (3.1), and ξ algebraic.  All are covered (rows 8 to 10).
* **(c) indexing**: paper k ≥ 1 with `C_1 = c_1`; Lean uses k ≥ 1 throughout and `C 0` is inert (row 6).
* **(d) lim sup ≥ 29/10 to ℓ = 3**: the bound is `< 3.649` (row 12), and ℓ ≥ 3 is part of Theorem 2.3's statement.  The ℓ = 2 exclusion in Section 8 uses Prop 3.1(iii) (golden ratio, `C_k/g` an odd prime for large k ∈ I) plus (B5): `C_m/g` would be a prime properly dividing the prime `C_k/g`.  Sound.
* **(e) g | C_k for large k ∈ I**: stated verbatim in Theorem 2.3 and Prop 3.1(ii).
* **(f) (3.1) automatic?**  The docstring gives two reasons.  The first ("Saito's proof of Theorem 2.3 obtains it from (B5)") is correct and sufficient (row 9).  The second ("for a Pisot ξ^g of degree 3 it is automatic") is true as a fact (`ξ^(g C_m)` would be both a degree-3 Pisot number by Lemma 5.7 and an integer) but circular as a justification, since Prop 3.1 needs (3.1) *before* it produces the Pisot number.  Harmless, because the first reason carries it.  Suggested docstring wording below.
* **(g) powTrace**: matches (section above).

## Defects

**None in the Lean statement.**  No change to `Saito2025TypeBTrace`, `powTrace` or `IsPisot` is needed.

Docstring-only suggestions (not applied; .lean files untouched by this audit):

1. Replace the (3.1) bullet with: "Prop 3.1 also assumes (3.1), `ξ^(C_m) ∉ ℕ` for every m.  Saito's proof of Theorem 2.3 (Section 8, first paragraph) derives it from (B5): an integer `ξ^(C_m)` would make `ξ^(C_k)` composite for the k > m with `C_m ∣ C_k`, yet it equals the prime `⌊ξ^(C_k)⌋`.  Our (B5′) supplies that k, so no extra hypothesis is needed."
2. Add the journal reference: "Ramanujan J. **70** (2026), no. 4, Art. 69, doi:10.1007/s11139-026-01443-0 (accepted 2026-07-23).  Audited against arXiv v3; the journal text has not been compared."
3. Say explicitly that the combination of Theorem 2.3 with Prop 3.1(iv) rests on the proof of Theorem 2.3 in Section 8, not on its statement.

## Paper soundness (outside the faithfulness question)

While tracing the chain I read Lemmas 4.1, 5.1, 5.2, 5.3, 5.7, 5.8, 5.9, 5.14, 6.1, 6.2, Proposition 3.1 (i), (ii), (iii), (iv) and the first part of Section 8, and found no gap affecting the cases the Prop is applied to.  One edge case: when `lim sup c_(k+1) = ∞`, the application of Lemma 6.1 in the proof of Prop 3.1(ii) needs a constant K absorbing `⌊ξ^(C_k)⌋^(−t_k)` against `ξ^(−C_k t_k)` with `t_k` unbounded, which fails if `c_(k+1)` grows faster than `ξ^(C_k)`.  Truncating `t_k` at any constant repairs it, and the Lean Prop needs only `ℓ ≤ 3.649`, which the truncated argument still yields.  The downstream families (`C_k = 3^(k+j) + s`) have lim sup 3, so the case is not exercised.  This is a spot read, not a referee report.

## Freshness

* **arXiv**: the export API returns `http://arxiv.org/abs/2508.16068v3`, entry `<updated>` 2025-12-07T07:32:02Z.  The abs page's submission history lists v1 (2025-08-22), v2 (2025-09-22) and v3 (2025-12-07).  The local text is v3, the latest version.  `PROOF-THEOREM-E.md` line 5 says "a v2 (2025-12-07)"; the 2025-12-07 version is v3 (v2 is 2025-09-22).
* **Journal**: Crossref (`api.crossref.org/works/10.1007/s11139-026-01443-0`) registers a Springer journal article with the same title and author: *The Ramanujan Journal* vol. 70, issue 4, article number 69, received 4 February 2026, accepted 23 July 2026, first online 10 August 2026, print August 2026.  `doi.org` resolves to `link.springer.com/10.1007/s11139-026-01443-0`, whose page shows "Published: 10 August 2026" and the abstract (it adds "if ξ(C_k) exists" to the v3 abstract's first sentence).  So `PROBE-MILLS-TRANSCENDENCE.md`'s Ramanujan J. citation is confirmed, and `PROOF-THEOREM-E.md`'s "unrefereed" (lines 5, 125, 145, 147) is stale: the paper was accepted after peer review.
* **Not compared**: the published full text is behind a paywall, so I could not check whether Theorem 2.3 or Proposition 3.1 changed between v3 (December 2025) and the accepted version (submitted February 2026, accepted July 2026).  Theorem numbering in the published version is unverified.  If access becomes available, re-check those two statements and Section 8.
