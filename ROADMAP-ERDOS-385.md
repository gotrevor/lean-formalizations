# Roadmap: Erdős #385 / #430 (branch `erdos-385`)

Synthesis of `PROBE-ERDOS-385.md`, `LIT-ERDOS-385.md`, `DOOR-FF-`, `DOOR-ALMOSTALL-` and
`DOOR-EXCEPTIONAL-ERDOS-385.md` (2026-10-01).  **Lean is the record**: every conclusion below
has a Lean form, named in backticks.  The prose files are drafts.

## Where the problem stands

- **#385(i) for every `n`** (equivalently #430): parity-blocked (Tao 2024).  Infinitely many
  Siegel zeroes would give a one-scale enemy (`Literature.Granville2022Cor1`), and a sieve-only
  argument would refute a true statement (`Erdos385.SieveOnlySibling`, true by
  `Literature.FGKMT2018Eq12`).  No door here; `Maze.lean` rows record both.
- **What we can do**, as new math, in increasing strength:
  - the elementary rigidity of bad `n` (E1);
  - the elementary count of bad `n` (E2);
  - Tao's unproved "almost all" remark, in a sharper form (E3).

## Conjecture graph

Nodes (`def … : Prop`, open or literature):
- `Literature.BrunUniformGap`
- `Literature.BBR2015Thm23TwoFactor`
- `Literature.Gorodetsky2018Thm11`
- `Literature.FGKMT2018Eq12`
- `Literature.SiegelZerosInfinitelyOften`, `Literature.OneScaleSieveEnemy`,
  `Literature.Granville2022Cor1`
- `Erdos385.FF385 K` (open)
- `Erdos385.CrossScaleRepulsion` (open, no signal)
- `Erdos385.SieveOnlySibling`
- `Erdos385.BadCountExpBound` (paper only)
- `Erdos385.AlmostAllF385` (the E3 target)

Edges and theorems (frozen, `sorry` until proved):

| Edge | From → to | File |
|---|---|---|
| `le_F`, `bad_iff_F_eq`, `bad_iff_forall_sub`, `prime_sub_one_of_bad` | elementary | `Rigidity.lean` |
| `primorial_dvd_of_minFac_sub_le` (Lemma R) | elementary | `Rigidity.lean` |
| `primorial_dvd_or_exists_prime_pair_of_bad`, `exists_prime_pair_of_bad` (R′) | Lemma R | `Rigidity.lean` |
| `exists_composite_mem_terms_iff`, `erdos430_iff_erdos385_i` | elementary (#430 ⟺ #385(i)) | `Rigidity.lean` |
| `ffGood_of_eval_ne_zero`, `X_pow_card_sub_X_dvd_of_not_ffGood`, `card_le_natDegree_of_not_ffGood`, `ffGood_of_natDegree_lt_card`, `ffGood_of_ffWitness` | elementary | `FunctionField.lean` |
| `ffWitness_of_BBR` | BBR → depth-`m` witnesses for `q ≥ q₀` | `FunctionField.lean` |
| `noCarrier_of_bad`, `eventually_not_bad_of_crossScaleRepulsion` | repulsion → #385(i) | `Graph.lean` |
| `sieveOnlySibling_of_FGKMT` | FGKMT → sibling | `Graph.lean` |
| `card_bad_le` | Brun + R′ → `#{bad ≤ X} ≪ X log log X / log² X` | `Count.lean` |

All files are under `src/LeanFormalizations/NumberTheory/Erdos385/`, except the literature Props
in `src/LeanFormalizations/Literature/Erdos385.lean`.  Data checks:
- `scripts/test_erdos385_rigidity.py` (every `Rigidity.lean` statement, brute force);
- `scripts/test_erdos385_ff_probe.py`.

## Phase queue

**E1 (PLANTED 2026-10-01): elementary rigidity.**
- Target: `Rigidity.lean`; stop when that file is sorry-free.
- Route: in the file header.  Lemma R is a strong induction over primes; R′ and the dichotomy
  follow from Lemma R; #430 unpacks `terms`.
- Budget: 1–2 laps.

**E1b: function-field facts and cheap graph edges.**
- Targets: `FunctionField.lean`, plus `noCarrier_of_bad`,
  `eventually_not_bad_of_crossScaleRepulsion` and `sieveOnlySibling_of_FGKMT` in `Graph.lean`.
- Stop when both files are sorry-free.
- Route in each header.  `ffWitness_of_BBR` is the only nontrivial one (UFD factor matching plus
  a size estimate).

**E2: the elementary count.**
- Target: `Count.lean`, the single statement `card_bad_le` from `Literature.BrunUniformGap`.
- Route in the header.  Needs Chebyshev-type bounds on `primorial`, `π(y)`, and
  `h/φ(h) ≪ log log h` (mathlib or PNT+).
- Optional: discharge `BrunUniformGap` from mathlib's `SelbergSieve` along PNT+'s
  Brun–Titchmarsh (a side quest, not a stop condition).

**E3: almost all (ready to plant; statements to write in `AlmostAll.lean`).**
- Freeze: `AlmostAllF385`, i.e. for all `δ ∈ (0, 1/4)`,
  `#{n ≤ X : F(n) < n + (1 − δ)√n} = o(X)`.
- From four literature Props, per the "Source checks (2026-10-01)" section of
  `DOOR-ALMOSTALL-ERDOS-385.md`:
  1. Teräväinen arXiv:1510.06005 Lemma 1, with the added hypothesis `|a_n| ≤ 1`;
  2. the upper half of Iwaniec–Kowalski Thm 9.1 (the mean value theorem);
  3. the smooth Vinogradov–Korobov prime sum (from the proof of MR16 Lemma 11);
  4. PNT in short intervals (possibly dischargeable from PNT+ `MediumPNT`).
- No large-value estimates are needed.  The W3 bookkeeping collapses to one inequality,
  `sup|P|² · ∫|Q|²`.
- Wiring theorems:
  - W1: the balanced-witness reduction.  A semiprime `pq ∈ (n − p, n)` with `p ≥ (1 − δ)√n`
    gives `F(n) ≥ n + (1−δ)√n − O(1)`.
  - W2: the variance-to-density step.
  - W3: the block inequality.
- Then `almost_all_F385 : … → AlmostAllF385`.
- Confidence the outline closes: 70% before the source checks, higher after.

**E4: paper only, no Lean.**
- `BadCountExpBound`, `DOOR-EXCEPTIONAL` A2: `≪ X exp(−(log X)^{1/2−ε})`, from the large sieve
  plus McDiarmid.  75% that the outline closes; mathlib has neither tool.
- The node is stated; there is no proof route in Lean.

## Closed routes (`Maze.lean` rows)

- function field, large `q` (superseded: BBR);
- function field, fixed `q` (square-root barrier: Gorodetsky);
- sieve-only arguments (`SieveOnlySibling`);
- every `n` via one-scale methods (Siegel: Granville);
- repulsion (no signal in the data).
