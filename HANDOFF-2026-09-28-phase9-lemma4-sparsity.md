# Handoff: Dubickas phase 9 — CZ Lemma 4 dissected to a single sharp obstruction (SPARSITY)

**Date**: 2026-09-28 · **Branch**: `main` · **HEAD**: `4aa07e0` · working tree clean
· **Build**: 🟢 `lake build` green, **8708 jobs** (pre-commit hook verified on all four commits this
session) · nothing pushed (no egress; the host pushes)
· Headlines re-verified axiom-clean: `theorem1`, `oeis_constants` = `[propext, Classical.choice, Quot.sound]`

## 🎯 Assignment

DIRECTION.md phase 9: make the ⚓ OEIS-linked `Dubickas.lean` headlines unconditional by proving
`exists_pisot_pow_noD` without `Dubickas2022`, or by a direct `c_eq_zero_or_two_uncond`; **a precise
obstruction in `PROBE-DUBICKAS-NOSUBSPACE.md` is a full success.**  Everything this session is in
`src/LeanFormalizations/NumberTheory/Transcendence/DubickasNoSubspace.lean` + the two docs.

## ✅ What this session proved (all axiom-clean)

Four green commits, each a step of the Corvaja–Zannier Lemma 4 attack:

1. `ea25ae6` **the bridge**: `conjField α` (= `adjoin ℚ ((minpoly ℚ α).rootSet ℂ)`) is a
   `NumberField` by *global* instances (unconditionally — a transcendental `α` has `minpoly = 0` and
   an empty root set), `conjMultiset α` via `Multiset.pmap` (no `Splits`/`aroots_map` detour),
   `conjMultiset_pow_sum_coe`, `exists_valuation_one_lt`, `exists_max_image_multiset`,
   `exists_dominant_max`, `conj_bounded_den`, and **`exists_tie_of_bounded_den`** — Lemma 4's
   hypothesis *forces a tie*: if `α` is not an algebraic integer, at some prime two **distinct**
   conjugates share the maximal valuation, which is `> 1`.
2. `f6ed50b` **the tie case reduced to ONE local leaf**: `false_of_bounded_den_of_nondegenerate`
   (split `R` at `v` into the dominant part `W` and the rest; `|W| = 1` is
   `no_bounded_den_of_unique_max_valuation`, `|W| ≥ 2` normalizes to units `u = w/z` and needs only
   `v(Σ u^N) ≤ B r^N`, `r < 1`) and `isIntegral_of_bounded_den_of_nondegenerate`.  The leaf
   `valuation_sum_unit_pow_nondegenerate` is the *only* new `sorry`.
3. `6b5521a` **the archimedean side is COFINITE**: `tracePowSum_near_int` — once one pseudo-Pisot
   exponent `n₁` exists, each conjugate either collapses onto `α^(2^n)` for *all* `n ≥ n₁` or lies
   in the open unit disc, so `2 U_(2^n) = k(2 y_n) + O(max(α⁻¹,ρ)^(2^n))` for **all** large `n`;
   hence `tracePowSum_den_grows` (+ `one_div_den_le_dist_int`): for every large `n`, either
   `2 U_(2^n) ∈ ℤ` or its denominator is `≳ α^(2^n)`.  With the unique-dominant case this forces the
   local dominant valuation `D_v ≥ α`.
4. `4aa07e0` **the double tie CLOSES elementarily**: the Graeffe identity
   `2(u₁u₂)^N = (u₁^N+u₂^N)² − (u₁^(2N)+u₂^(2N))` has valuation *exactly* `v 2` on the left, so
   `valuation_two_le_of_two_unit_pow_sums` / `false_of_two_unit_pow_sums_small` /
   `valuation_sum_unit_pow_card_two` prove the leaf for `card U = 2` over a doubling-closed exponent
   set, **with no nondegeneracy hypothesis**.  Helper: `exists_mul_pow_lt` (`ℤₘ₀`).

## ⛔ Open `sorry`s in `src/` (exactly three, all named literature/crux leaves)

| leaf | status |
|---|---|
| `corvajaZannier_dichotomy` (CZ main thm p. 177 = Dubickas Lemma 3) | the `p`-adic Subspace Theorem wall; do not attack head-on |
| `corvajaZannier_lemma4` (CZ Lemma 4) | first branch proved in the nondegenerate case; missing = degenerate branch (see below) |
| `valuation_sum_unit_pow_nondegenerate` | the local leaf; **proved for `card U = 2` + doubling-closed exponent sets** |

## 🧠 The obstruction, as sharp as it now gets (full write-up in `PROBE-DUBICKAS-NOSUBSPACE.md`)

* **The residual is SPARSITY, not `p`-adic analysis.**  Newton's identities
  (`j e_j = Σ_i (−1)^(i−1) e_(j−i) p_i`) collapse the tie case for *any* tie size `k` as soon as the
  exponent set is closed under multiplication by `1, …, k` (then `ord_v(k! ∏ u_i^N) → ∞` while
  `∏ u_i` is a unit).  Our exponent set `{2^n : n ∈ S}` is only known **infinite**.
* ⚠ **Strassmann's theorem would NOT have closed it either** (correction of an earlier lap's claim):
  it forces the exponent set to grow like a tower, and `{2^(2^j)}` does.
* **Ranked next attack**: make the pseudo-Pisot index set `S` **cofinite** (it comes out of CZ's
  Lemma 3, whose *other* branch is a "for all large `n`" statement — so this is a question about how
  the two branches are split).  The archimedean side is already cofinite
  (`tracePowSum_den_grows`); it is the exact-integer side that is sparse.  If `S` can be made
  cofinite (or doubling-closed, or bounded-gap), Lemma 4 becomes **elementary outright** and the
  whole tie problem disappears.
* **Second gap**: the *degenerate* branch of Lemma 4.  `w^l = w'^l` for distinct conjugates gives
  only `deg(α^l) < deg α` (fibres of `w ↦ w^l` all have size `[ℚ(α):ℚ(α^l)]`, one has `≥ 2`), a
  *descent* that cannot be iterated because the exponent set becomes `{N | lN ∈ S}`.
* **A bypass examined and REFUTED**: `c_eq_zero_or_two_uncond` needs integrality only at
  `pisot_conjPowSum_add_mem_int` inside `exists_pisot_trace_ident` (everything else —
  `base_bound_of_eFull_two`, the `bb`/`qq` analysis, `eq_zero_or_one_of_bRec_finite_support` — uses
  only `β > 1`, algebraic, other conjugates inside the unit disc).  `den(Tr β^N) ≪ β^N` would
  suffice, but `9X² − 18X + 2` (root `β = 1 + √7/3 ≈ 1.8819`, other conjugate `≈ 0.118`, trace
  `2 ∈ ℤ`) is a genuine pseudo-Pisot number with `den(Tr β^N) = 3^N ≫ β^N`.

## ⚠️ Gotchas from this session

* `NumberField (conjField α)` works as a **global instance** — the earlier handoff's "must be a
  `haveI` inside the proof" is obsolete (the adjoin of a root set is finite-dimensional even when
  `minpoly = 0`).
* `isAlgebraic_of_mem_rootSet` is in the **root** namespace, not `Polynomial`.
* `Multiset.sum_eq_card_nsmul` does not exist — a 5-line `multiset_sum_const` induction is in the
  file.  `Multiset.card_pos` (not `one_le_card_iff_ne_zero`); `Multiset.sum_map_div` exists.
* `ℤₘ₀` order API is thin: `pow_le_pow_left₀` takes `(0 ≤ a)` **first**, `pow_le_pow_of_le_one` (not
  `…_right_of_le_one₀`), and `x < y` from `1 < y * x⁻¹` needs
  `rw [← div_eq_mul_inv, lt_div_iff₀ hx0, one_mul]`.
* `algebraMap (𝓞 L) L 2 = 2` is easiest via the `((2 : ℤ) : L)` route + `map_intCast`.
* `hD` remains on the three `Dubickas.lean` headlines **on purpose** — never route a headline through
  a `sorry`.

## 📄 Read first next lap

`DIRECTION.md` (CURRENT DIRECTIVE), then `PROBE-DUBICKAS-NOSUBSPACE.md` (sections "sixth lap" and
"seventh lap" are this session's), then `PENDING_WORK.md`'s ranked next attack.
`ON-LINE-REQUEST.md` (CZ 2004 pp. 176–179) is **still unanswered** — it would settle whether CZ's own
Lemma 4 is subspace-strength.
