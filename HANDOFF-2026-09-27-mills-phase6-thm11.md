# Handoff: Mills phase 6 — Saito Theorem 1.1 COMPLETE (modulo one lemma)

**Date**: 2026-09-27 · **Branch**: `mills` · **HEAD**: `1958c07` · Working tree clean.
Full `lake build`: 8692 jobs, success (pre-commit re-ran it). Nothing pushed (no egress).

## 🎯 Where phase 6 stands

`DIRECTION.md` phase 6 is Saito's Theorems 1.1 and 1.2 in `Mills/Transcendental.lean`.
This lap took it from three opaque `sorry`s to **two precisely-located obligations**:

| target | status |
|---|---|
| `exists_minMillsC_of_BHP` | **PROVED, axiom-clean** |
| `transcendental_of_four_le` (Thm 1.1, all `c ≥ 4`) | **PROVED**, `sorryAx` from `saito_lemma36C` only |
| `transcendental_or_pisot` (Thm 1.2) | open (`Transcendental.lean:79`) |
| `saito_lemma36C` (general-`c` Matomäki minimality) | open (`SaitoDigits.lean:114`) — gates both |

## 🧠 Three ideas worth inheriting

**1. Saito's Lemma 3.9 (`log`/`exp`) is unnecessary on the transcendence route.**
Saito derives `|ξ^(C_k) − p_k| ≤ e^(−γC_k)` and only re-derives the finer bound in §4. But it is
the *finer* bound Dubickas consumes, and it falls out of the elementary expansion with no
logarithms: Bernoulli `(1+t)ᶜ ≥ 1+ct` at `t = 2/pₖ^(19c/40)` gives
`A^(c^(k+1)) − pₖ ≤ 2/pₖ^μ` with `μ = 19c/40 − 1`, and `A^(c^(k+1)) < 2pₖ` converts that to
`2^(μ+1)·A^(−μc^(k+1))` — Dubickas's input shape, constant included. See `SaitoDigits.lean`.
(The `exp` form is still needed for *irrationality*, where Mahler wants `e^(−εn)`.)

**2. `∃ᶠ`, not `∀ᶠ`.** The decay for `β = A^(c^(m+1))` exists only along `n = cʲ`, while the
Dubickas–Corvaja–Zannier gap bound holds for all large `n`. A subsequence is enough to conclude
`|β₂| ≤ β^(−μ)`, so `le_of_pow_le_const_mul_pow` and `pisot_degree_bound` take `∃ᶠ`. Stating
them with `∀ᶠ` would have made the assembly impossible; this was the one real design decision.

**3. The `c = 4` case does not need Saito's Lemma 4.2.** Saito identifies `t_k = p_k` first.
Unnecessary: with `n = cʲ` even, `wⁿ > 0`, so the integer `t = βⁿ + wⁿ` exceeds `βⁿ`, hence
`t ≥ ⌊βⁿ⌋ + 1` and `wⁿ = t − βⁿ > 1/2` once `frac(βⁿ) < 1/2` — contradicting `|w| < 1` directly.
Relatedly: a degree-2 Pisot number's other conjugate is the **real** number `t₁ − β`, with no
field theory at all (the `n = 1` trace over a singleton multiset *is* the conjugate).

## 📁 New files (all green; only `SaitoDigits.lean:114` carries a `sorry`)

* `Mills/SaitoPisot.lean` — Lemma 4.1's Claim `(ℓ−1)μ ≤ 1` (`pisot_degree_bound`), the `k → ∞`
  step, `pisot_one_le_prod_norm` (via the integer minimal polynomial's `coeff 0`),
  `pisot_conjPowSum_add_mem_int` (trace of an algebraic integer, `trace_eq_sum_embeddings` +
  `PowerBasis.liftEquiv'`), `card_otherConj_add_one`, `conjMax_lt_one`, `norm_conjPowSum_le`,
  `pisot_two_le_natDegree`. **Sorry-free.**
* `Mills/SaitoLemma41.lean` — `exists_pisot_of_decay` (both Dubickas branches) and
  `transcendental_of_decay`. **Sorry-free.**
* `Mills/SaitoDegreeTwo.lean` — `exists_real_conj_of_natDegree_two`, `pow_add_pow_mem_int`,
  `not_pisot_two_of_even` (Lemma 4.3, `b = 4`). **Sorry-free.**
* `Mills/BasicC.lean` — the nested-interval construction for any `c ≥ 2`. **Sorry-free.**
* `Mills/SaitoGeneral.lean` — `pow_succ_ge_add_mul`, `primeBetweenPows_of_BHP` (`c ≥ 3`),
  `exists_leastC_of_exists`, `exists_leastMillsC_of_BHP`. **Sorry-free.**
* `Mills/SaitoDigits.lean` — `mdigitC`, Lemma 3.5, `le_add_rpow_of_pow_le`,
  `decay_of_lemma36C` (+ `_round_` corollary), `millsC_not_intCast`, `eventually_rpow_neg_lt`,
  `transcendentalC_of_five_le`, `transcendentalC_of_four`, and **`saito_lemma36C` (the sorry)**.

## 🎬 Next actions, in order

1. **`saito_lemma36C`** — the only thing between Theorem 1.1 and a finished proof. The `c = 3`
   case *is* proved: `saito_lemma36` in `Irrational.lean` (~200 lines). This is that argument
   with `3 → c`: `Rich`, `saito_lemma38`, `rich_chain` and `Chain.exists_shifted_of_chain` all
   generalise, with Lemma 3.8's exponent `2/3` becoming `(c−1)/c`. Long but mechanical — expect
   grind, not insight. Consider generalising the `c = 3` file's helpers in place rather than
   copying (but **never change an existing statement**).
2. **`transcendental_or_pisot`** (Thm 1.2). At `c = 3`, `μ = 17/40`, so the Claim gives
   `card ≤ 40/17`, i.e. degree 2 or 3. Degree 3 is the *disjunct* (Saito's open Remark 4.4), so
   only degree 2 must be killed, via Lemma 4.3's `b = 3` case:
   `t_{3n} = t_n³ − 3(βw)ⁿ t_n` with `βw ∈ ℤ` gives `p_k ∣ p_{k+1}`, impossible for distinct
   primes. **Prerequisite:** a lemma `βw = ((minpoly ℤ β).coeff 0 : ℝ)` — extract it from the
   proof of `pisot_one_le_prod_norm`, which already computes `Q.eval 0` in both forms.

## ⚠️ Gotchas confirmed this lap

- `push_neg` is deprecated in this pin — use `push Not at h`.
- `Nat.pos_pow_of_pos` does not exist; use `Nat.pow_pos`. `Nat.lt_pow_self (h : 1 < b) : n < b ^ n`.
- `Complex.norm_real : ‖(r:ℂ)‖ = ‖r‖` gives the **real norm**, not `|r|` — chain it with
  `Real.norm_eq_abs`.
- `minpoly.coeff_zero_ne_zero` needs a **field** base; for `ℤ` go through the `ℚ`-minimal
  polynomial and `minpoly.isIntegrallyClosed_eq_field_fractions'`.
- `Int.natCast_floor_eq_floor (0 ≤ r) : (⌊r⌋₊ : ℤ) = ⌊r⌋`; `Int.self_sub_floor`,
  `abs_sub_round_eq_min` are the round/floor bridge.
- `Literature/` is FROZEN (`Primes.lean`, `Pisot.lean`). `IsMills`/`IsMinMills`/`IsMillsC`/
  `IsMinMillsC` and the three phase-6 theorem statements are the audit surface — never tidy them.
- `DIRECTION.md` is operator-owned; do not edit.

---
**→ Next session: start at `saito_lemma36C`.** It gates everything. Do not reopen the proved
parts (`SaitoPisot`, `SaitoLemma41`, `SaitoDegreeTwo`, `BasicC`, `SaitoGeneral` are all
sorry-free and axiom-clean), and do not re-derive the three ideas above.
