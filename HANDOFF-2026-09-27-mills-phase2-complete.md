# HANDOFF 2026-09-27 — Mills lane phase 2 COMPLETE

Branch `mills`, HEAD `2d9e696`.  `lake build` green (8680 jobs).
**`src/LeanFormalizations/NumberTheory/Mills/` is sorry-free.**  Every headline reports
`[propext, Classical.choice, Quot.sound]`:

| theorem | source | conditional on |
|---|---|---|
| `wright` | Wright 1951 | — (Bertrand, in mathlib) |
| `exists_mills_of_primeBetweenCubes`, `exists_least_of_primeBetweenCubes` | Mills 1947 | `PrimeBetweenCubesFrom N` (Ingham) |
| `exists_least_of_exists` | — | — |
| `lower_bound_of_RH` | Caldwell–Cheng 2005 | `Schoenfeld1976` |
| `exists_mills_of_BHP` | Mills + BHP | `BakerHarmanPintz2001` |
| `irrational` | Saito 2024 | `BakerHarmanPintz2001`, `Matomaki2007`, `Mahler1957` |

Frozen statements verified untouched: `git diff 46899d0..HEAD` is EMPTY on
`Literature/Primes.lean`, `Mills/Basic.lean`, `Mills/Wright.lean`.  All 19 host-guarded
declarations `#check` clean.

## New files

* **`Mills/Chain.lean`** — `exists_shifted_of_chain`: the nested-interval engine with the chain
  at exponents `3^(k+1)` instead of `3^k` (`Basic.lean`'s version produces a Mills number `≳ 2`;
  Mills' *constant* needs the shift).  Used by both `RH.lean` and `Irrational.lean`.
* **`Mills/Schoenfeld.lean`** — Caldwell–Cheng Lemma 5 in full, plus two reusable analytic
  atoms: `nine_log_sq_lt_sqrt : 9 log²m < 32 √m` (four terms of the exponential series at
  `u/2`, closed by `nlinarith` with the hint `u(u−5)² ≥ 0`) and its repackaging
  `log_lt_two_rpow : log m < 2 m^(1/4)`.  **That single inequality pays for both halves of
  phase 2** — the prime-in-a-cube-gap bound AND Saito's Lemma 3.8 threshold.
* **`Mills/Irrational.lean`** — the whole Saito route at `c ≡ 3`.

## The structural points worth keeping

1. **`c ≡ 3` makes Lemma 3.8 self-propagating.**  `Rich d₁ q` ("`[q³, q³+q²]` is prime-rich")
   is *literally* Lemma 3.8's hypothesis at `X = q³`, `η = 2/3`, because `(q³)^(2/3) = q²`.
   So the chain induction of Saito's proof collapses to one `Nat.rec` over one lemma
   application (`hstep`), with no per-step case analysis.
2. **`γ = 2/3` is the exponent that makes Matomäki's cap a constant** (`D·x^(2/3−γ) = D`).
   That is why Lemma 3.8's contrapositive closes without any asymptotics beyond
   `d₂X^η/log X > D`.
3. **`mdigit_dist_le` avoids rpow roots entirely.**  Saito's `(1+x)^{1/3} < 1+x` is replaced by
   `(1+t)³ ≥ 1+3t` with `t = 2/p_k^(57/40)`; the resulting slack `6 > 2` is exactly what
   absorbs the `+1` the floor contributes.
4. `θ_b = 1 − 21/40 − 1/3 = 17/120 > 0` is the whole reason `b = 3` works; it shows up as the
   exponent `−17/40` in `mdigit_dist_le` and as `γ = (17/240) log p_1` in `saito_lemma39`.

## Performance gotchas earned this lap (worth the reference corpus)

* **`gseq 3 = lpa ((gseq 2)^3) := rfl` HANGS** (>20 min).  `lpa n = Nat.find …`, and the defeq
  checker tries to *evaluate* it over two billion candidates.  Fix: state the unfolding lemma
  with a **variable** index (`gseq_succ (k) : gseq (k+1) = lpa ((gseq k)^3) := rfl`) and `rw`
  with it.  Same trap for any `Nat.find`/`Nat.rec` def at a numeral.
* **`interval_cases m` over a 10-digit range** (`2521008881 < m < 2521008887`) never returns.
  Use `have : m = … ∨ … := by omega; rcases`.  Under ~10^4 wide it is fine.
* **`set p := mdigit A k` + `rw [hb_le k]`** leaves the *unfolded* `mdigit A k` in the goal, so
  `omega` atomises it separately from `p` and fails.  Fold back with `rw [← hpdef]` first.
* `∃ A > 1, P A` with `A`'s type inferable only from `P` defaults `A : ℕ`.  Write
  `∃ A : ℝ, 1 < A ∧ …`.
* `⨆ n, f n` inside `⟨…, …⟩` swallows the comma — parenthesise it.
* `decide +kernel` on `Nat.Prime` over a 30-wide range timed out where `interval_cases … <;>
  norm_num` was instant; norm_num's prime extension beat the kernel here.

## What is genuinely left (a different lane, not a hole)

`Literature/Primes.lean` holds five published theorems as hypotheses.  Discharging any one —
Schoenfeld's explicit RH bound, Baker–Harman–Pintz, Matomäki's Lemma 9 — is a research-scale
formalization project of its own.  They are hypotheses in every signature, so nothing here is
vacuous or overclaimed.
