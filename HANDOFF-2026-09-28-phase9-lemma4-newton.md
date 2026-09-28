# Handoff: Dubickas phase 9 — Newton kills every tie size; the residual is a clean three-way

**Date**: 2026-09-28 · **Branch**: `main` · **HEAD**: `4f04412` · working tree clean
· **Build**: 🟢 `lake build` green, **8708 jobs** (pre-commit hook verified on both proof commits)
· nothing pushed (no egress; the host pushes)
· Headlines re-verified axiom-clean: `theorem1`, `oeis_constants`,
  `transcendental_growth_of_monic_quadratic` = `[propext, Classical.choice, Quot.sound]`

## 🎯 Assignment (review lap #2 of phase 9 + two grind commits)

`DIRECTION.md` → **CURRENT DIRECTIVE** was rewritten this lap (altitude laps own it; a grind lap must
obey, not edit).  Read it first.  Verdict it records: **`corvajaZannier_dichotomy` = Corvaja–Zannier
2004's main theorem = the `p`-adic Subspace Theorem, and it STAYS a disclosed leaf** — the reason is
structural, not effort: the object to bound is a linear form in the `d` monomials `σ(α)^N`, which is
exactly what forces Subspace over Roth/Ridout, and the one-dimensional archimedean route provably
only re-derives the vacuous `M(α) ≥ α`.  The live objective is **three disclosed leaves → one**.

## ✅ What this lap landed (two green commits, everything axiom-clean)

**`c3b13fd` — Newton's identities kill EVERY tie size.**
* `valuation_natCast_le_one`, `valuation_multiset_prod_eq_one`, `valuation_finset_sum_le`,
  `valuation_esymm_le_one`, `multiset_esymm_card` — the local toolkit.
* **`valuation_factorial_mul_esymm_le`** — for a multiset `x` of `v`-units with `|x| = k`, if
  `v(p_l(x)) ≤ ε` for `1 ≤ l ≤ k` then `v(j! · e_j(x)) ≤ ε` for `1 ≤ j ≤ k`.  **No induction**:
  multiply the repo's `multiset_mul_esymm_eq_sum` through by `(j−1)!`; each summand is then
  `(valuation ≤ 1) · p_(j−i)` because `v(m!) ≤ 1` and `v(e_i) ≤ 1` separately.
* **`valuation_sum_unit_pow_mulClosed`** — `v`-units `u_1..u_k` (`k ≥ 1`) plus an infinite exponent
  set closed under multiplication by `1..k` cannot have `v(Σ u_i^N) ≤ B r^N`, `r < 1`: at `j = k`,
  `e_k(x) = (∏u_i)^N` is a unit, so the left side is the **fixed nonzero** `v(k!)`.
  **No nondegeneracy hypothesis; `k = 1` (no-tie) included.**
* `false_of_bounded_den_mulClosed`, `isIntegral_of_bounded_den_mulClosed` — CZ's Lemma 4 for a
  multiplicatively-closed exponent set, **with no escape branch**: conclusion `IsIntegral ℤ α`, not
  `IsIntegral ℤ α ∨ ∃ l, α^l ∈ ℚ`.
* The superseded leaf `valuation_sum_unit_pow_nondegenerate` was **deleted**: `src/` went from
  **three** disclosed `sorry`s to **two**, both now named published CZ statements.
  ⚠ Strassmann's theorem is NOT needed anywhere — the fifth/sixth laps' plan for it is obsolete.

**`4f04412` — the denominator CEILING, the cofiniteness dichotomy, the `ζ₃` witness.**
* `isIntegral_multiset_sum`, **`exists_common_integral_multiple`** — one positive integer `D` with
  `D w` an algebraic integer for *every* conjugate `w` (mathlib's `exists_integral_multiples ℤ ℚ`
  applied inside `conjField α`, which is a `NumberField`).
* **`exists_tracePowSum_den_dvd`** — hence `den(U_N) ∣ D^N` (`D^N U_N = Σ_w (Dw)^N` is a sum of
  algebraic integers and rational).  *The upper bound the sixth lap lacked.*
* **`tracePowSum_int_of_near_int_of_den_lt`** — the **cofiniteness dichotomy**: if `2 U_(2^n)` is
  within `C₂ r^(2^n)` of an integer for all large `n` (`tracePowSum_near_int`) and `D r < 1`, then
  `2 U_(2^n)` is *exactly* an integer for **every** large `n`.
* **`false_of_bounded_den_tie_le`** — Lemma 4's local step refined: closure needed only up to `K`,
  a bound on the **tie size** at `v`.  `false_of_bounded_den_mulClosed` is now the `K = |R|`
  corollary; `K = 2` needs mere **doubling** closure.
* **`isIntegral_of_tie_le_two_of_den_lt`** (capstone) — `D r < 1` **and** every dominant-valuation
  tie of size ≤ 2 ⟹ `α` **is** an algebraic integer.

## ⛔ Open `sorry`s in `src/` (exactly TWO, both named published theorems)

| leaf | status |
|---|---|
| `corvajaZannier_dichotomy` (CZ 2004 main thm p. 177 = Dubickas Lemma 3) | the `p`-adic Subspace Theorem. **Do not attack**; `DIRECTION.md` forbids it and forbids adding the `Prop` to `Literature/` |
| `corvajaZannier_lemma4` (CZ 2004 Lemma 4) | proved *outright* for a multiplicatively-closed exponent set (`isIntegral_of_bounded_den_mulClosed`); as **stated** (S merely infinite) it is still open, and the gap is entirely exponent-set density |

`hD` therefore still sits on the three `Dubickas.lean` headlines — never route a headline through a
`sorry`.

## 🧠 The obstruction, as of this lap (full write-up: `PROBE-DUBICKAS-NOSUBSPACE.md`, eighth lap)

For a **non-integral** growth constant `α`, at least one of:
1. `D ≥ min(α, ρ⁻¹)` — a Mahler-measure lower bound nothing supplies (`9X² − 18X + 2` shows
   pseudo-Pisot-ness alone does not forbid it);
2. some prime of `conjField α` carries a **triple** tie of dominant valuations;
3. CZ Lemma 3's pseudo-Pisot index set `S` is sparse.

**The `ζ₃` witness (new, definitive).**  `u_i = ζ₃^i c` (`i = 0,1,2`) at a prime whose local field
contains `ζ₃` has `Σ_i u_i^N = 0` whenever `3 ∤ N`, in particular for **every** `N = 2^n`.  So
*doubling* closure provably cannot be pushed past tie size 2 — the seventh lap's hope is refuted —
and the requirement is exactly closure under multiplication by `1, …, k`.  The witness is degenerate
(`u_1^3 = u_2^3`), i.e. it IS CZ's `α^l ∈ ℚ` branch, whose descent is blocked because
`{N | 3N ∈ S}` is empty for `S ⊆ {2^n}`.

## 📌 Next actions (ranked; see `PENDING_WORK.md` top)

1. **Attack residual (2): are `p`-adic ties confined to archimedean-dominant conjugates?**  The
   archimedean-dominant conjugates are known to differ by **2-power** roots of unity
   (`norm_eq_of_pow_eq` + the collapse in `tracePowSum_near_int`).  If a dominant-*valuation* tie at a
   prime can only involve archimedean-dominant conjugates, then every tie ratio is a 2-power root of
   unity, the tie size is a power of `2`, and the **Graeffe tower** (doubling-only) closes it — which
   `tracePowSum_int_of_near_int_of_den_lt` does supply.  Concrete, local, checkable.
   To make the Graeffe route work one needs the esymm form of the Graeffe transform
   (`e_m(x²)` in terms of `e_j(x)`); `MultisetGraeffe.lean` is the place to look/extend.
2. Residual (1): any lower bound on `D` in terms of `α` (equivalently on `M(α)`).
3. `ON-LINE-REQUEST.md` (CZ 2004 pp. 176–179) is **still unanswered** — it would settle whether CZ's
   own Lemma 4 is subspace-strength and how their `α^l ∈ ℚ` descent handles sparse exponent sets.

## ⚠️ Gotchas from this lap

* `Multiset.esymm` is `((s.powersetCard n).map Multiset.prod).sum`; `esymm s s.card = s.prod` via
  `Multiset.powersetCard_self` (`multiset_esymm_card` in the file).
* `congr 1` strips `Multiset.sum` from a goal `(s.map f).sum = (s.map g).sum`, leaving a *multiset*
  equality — so finish with `Multiset.map_congr rfl`, **never** `funext` (it fails to unify).
* `Valuation.map_neg` works on `(-1 : L)` (it elaborates as `Neg.neg 1`), so
  `v((-1)^k) = 1` is `map_pow` + `Valuation.map_neg` + `map_one` + `one_pow`.
* `exists_integral_multiples ℤ ℚ (L := …)` (`RingTheory/DedekindDomain/IntegralClosure.lean`) gives
  one multiplier for a whole `Finset` of a number field — much less work than scaling minpolys.
* `IntermediateField.algebraMap_apply` is `rfl`, so `algebraMap (conjField α) ℂ w = ↑w` needs only a
  `simp only`.
* `rw [heq]` where `heq : D₀ = ↑D₀.natAbs` loops/fails (the RHS contains `D₀`); go through
  `(Int.cast_natCast _).symm` and case on `Int.natAbs_eq` at the `ℤ` level instead.
* `Rat.den_dvd a b : ((a /. b).den : ℤ) ∣ b` — get the `/.` form via
  `Rat.divInt_eq_div` + `eq_div_iff`.
* `exists_mul_pow_lt` had to be **moved earlier** in the file (it is used by
  `valuation_sum_unit_pow_mulClosed`, which now precedes the Graeffe section).
* `DubickasNoSubspace.lean` now imports `…Transcendence.MultisetNewton` (no cycle: it imports only
  Mathlib).

## 📄 Read first next lap

`DIRECTION.md` (CURRENT DIRECTIVE — binding), then `PENDING_WORK.md` top (§PHASE 9, the ✅/⚠ block),
then `PROBE-DUBICKAS-NOSUBSPACE.md` eighth-lap sections.  `STATUS.md` was refreshed this lap.
