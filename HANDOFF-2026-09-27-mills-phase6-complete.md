# Handoff: Mills phase 6 COMPLETE — Saito Theorems 1.1 and 1.2 proved, axiom-clean

**Date**: 2026-09-27 · **Branch**: `mills` · **HEAD**: `a2cd140` · Working tree clean.
Full `lake build`: 8695 jobs, success.  `src/` is **sorry-free**.  Nothing pushed (no egress).

## ✅ DIRECTION.md phase 6 stop condition is met

`Mills/` is sorry-free and every phase-6 headline reports only
`[propext, Classical.choice, Quot.sound]` (verified with `#print axioms`):

| theorem (`Mills/Transcendental.lean`) | content |
|---|---|
| `exists_minMillsC_of_BHP` | `ξ_c` exists for every integer `c ≥ 3` (Saito Cor 3.4) |
| `transcendental_of_four_le` | **Theorem 1.1**: `ξ_c` is transcendental for every integer `c ≥ 4` |
| `transcendental_or_pisot` | **Theorem 1.2**: `ξ₃` is transcendental, or `ξ₃^(3^m)` is Pisot of degree 3 for some `m ≥ 1` |

Hypotheses are exactly the four frozen literature `Prop`s the operator named:
`BakerHarmanPintz2001`, `Matomaki2007`, `Dubickas2022`, `Dubickas2022PisotGap`.
No frozen statement was edited, and none turned out to be mis-stated.

## 🧠 What this lap added (the last two obligations)

### 1. `saito_lemma36C` — Lemma 3.6 for general `c` (was THE crux)

Two new sorry-free files:

* **`Mills/ChainC.lean`** — `exists_shifted_of_chainC`: `Chain.lean`'s shifted nested-interval
  engine for any `c ≥ 2`.  Needed because Lemma 3.6 must turn the rich-prime chain back into a
  Mills number of exponent `c`.
* **`Mills/SaitoRich.lean`** — `RichC`, `etaC c = 1 − 1/c`, and **`saito_lemma38C`** (Lemma 3.8
  for general `c`), plus `pow_lt_of_prime`, `succ_lt_add_one_pow`, `pow_add_two_ge_{real,nat}`.

**The design insight worth inheriting.** At `c = 3` the *inner* Matomäki exponent and the *outer*
window exponent coincide (both `2/3`), so `Irrational.lean` uses one symbol for both.  They are
different things:

* inner `γ = 1 − 1/c`, at which Matomäki's theorem is instantiated — `(qᶜ)^γ = q^(c−1)`;
* outer `η ∈ [1/2, 1 − 1/c]`, free.

Separating them is what makes `saito_lemma38C` instantiable *twice*: at `η = 21/40` (window
supplied by Baker–Harman–Pintz) and at `η = 1 − 1/c` (window supplied by the previous chain step).
`21c/40 ≤ c − 1` for `c ≥ 40/19` is exactly why one step can feed the next
(`rpow_21_40_le_rpow_sub_one`).  And `2/3 − γ ≤ 0` for `c ≥ 3`, so Matomäki's count
`D x^(2/3−γ)` collapses to the bare constant `D` — at `c = 3` this was an equality-to-`0`
coincidence, in general it is an inequality.

Two elementary ingredients replaced estimates Saito leaves implicit:
* `(1 + 1/(2c))^c ≤ 17/10`, from `1 + t ≤ exp t` and `exp(1/2)² = e < 2.89`.  This keeps the
  window's `c`-th powers inside `[Xᶜ, 2Xᶜ]` with no binomial expansion.
* `(u+1)ᶜ ≥ uᶜ + 2u^(c−1) + u^(c−2)`, by splitting off `(u+1)²` — again no binomial theorem.
  It gives *both* the pairwise disjointness of the Matomäki windows *and* the upper half of the
  chain condition `b(m+1) + 1 < (b m + 1)ᶜ`.

### 2. Lemma 4.3 at `b = 3` — `not_pisot_two_of_cube` (`Mills/SaitoDegreeTwo.lean`)

The mechanism is the Dickson/Newton identity at `b = 3`.  With `t_n = βⁿ + wⁿ ∈ ℤ` and
`P = βw ∈ ℤ`,

    t_{3n} = t_n³ − 3 Pⁿ t_n,

so `t_n ∣ t_{3n}`.  Along `n = 3ʲ` both `t_n` and `t_{3n}` are **digits of `A`** — hence primes —
and `t_{3n} > t_n³ > t_n`.  A prime properly divides a prime: contradiction.  No field theory.

Missing prerequisite, now proved: **`pisot_two_prod_mem_int`** —
`βw = ∏(−root) = Q(0) = (minpoly ℤ β).coeff 0`.  It is the same computation as
`pisot_one_le_prod_norm`, keeping the *value* instead of its modulus.

Assembly of Theorem 1.2: with `μ = 19·3/40 − 1 = 17/40`, Lemma 4.1's Claim gives
`card(otherConj) · μ ≤ 1`, i.e. `card ≤ 40/17 < 3`, so the degree is 2 or 3.  Degree 2 dies by
`not_pisot_two_of_cube`; degree 3 **is** the disjunct — Saito's open Remark 4.4.

## ⚠️ Gotchas confirmed this lap

- `gcongr` cannot discharge the `0 ≤ Real.log (pᶜ)` side goal of a division-monotonicity step.
  Use `div_le_div_of_nonneg_right h (Real.log_nonneg …)` explicitly.
- `Nat.cast_sub` takes `(R := ℝ)`, not `(α := ℝ)`.
- `set x := e with hx` does **not** fold occurrences of `e` created *later* by `refine`; re-`rw
  [← hx]` before `omega`.
- A transient `failed to open file …/Mathlib/…/*.ir: Bad file descriptor` out of the mathlib build
  tree is spurious (orbstack/CoW); just rerun `lake build`.
- Carried over and still true: `push_neg` is deprecated (`push Not at h`); `Nat.pow_pos` not
  `Nat.pos_pow_of_pos`; `Nat.lt_pow_self (h : 1 < b) : n < b ^ n`.

## 🎬 If there is a phase 7

Nothing in `Mills/` is open.  Natural continuations, none of them authorised here:

1. **Saito's Remark 4.4** — rule out `ξ₃^(3^m)` Pisot of degree 3, which would upgrade Theorem 1.2
   to "Mills' constant is transcendental".  This is open in the literature; the Dickson identity
   generalises (`D_c` for odd `c` has no constant term, so the divisibility argument is the right
   shape), but degree 3 has *two* other conjugates and `t_n` is no longer `βⁿ + wⁿ` with `w` real.
2. **Saito Theorem 1.4** (unbounded exponent sequences `c_k`) — not needed for 1.1/1.2, which are
   the constant-`c_k` case.
3. Discharging `BakerHarmanPintz2001` / `Matomaki2007` themselves — multi-year analytic number
   theory, deliberately axiomatised.

**Do not reopen** `SaitoPisot`, `SaitoLemma41`, `SaitoDegreeTwo`, `BasicC`, `SaitoGeneral`,
`ChainC`, `SaitoRich`, `SaitoDigits` — all sorry-free and axiom-clean.  `Literature/` is frozen;
`DIRECTION.md` is operator-owned.
