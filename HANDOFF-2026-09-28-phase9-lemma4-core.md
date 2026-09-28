# Handoff: Dubickas phase 9 — Lemma 6 split; its non-subspace half (CZ Lemma 4) under attack

**Date**: 2026-09-28 · **Branch**: `main` · **HEAD**: `0b5a7bc` · working tree clean
· **Build**: 🟢 `lake build` green, **8708 jobs** (verified by the pre-commit hook on every commit
this session) · nothing pushed (no egress; the host pushes)

## 🎯 Assignment and where it stands

DIRECTION.md phase 9: make the ⚓ OEIS-linked `Dubickas.lean` headlines unconditional by proving
`exists_pisot_pow_noD` without `Dubickas2022` (his Lemma 6), or by a direct
`c_eq_zero_or_two_uncond`; a precise obstruction in `PROBE-DUBICKAS-NOSUBSPACE.md` is a full
success.  **Outcome so far: Lemma 6 is fully dissected and half of it is proved.**

Everything lives in `src/LeanFormalizations/NumberTheory/Transcendence/DubickasNoSubspace.lean`
(plus one new theorem in `NumberTheory/Diophantine/Edges.lean`).  `src/` holds **exactly two
disclosed `sorry`s**, both named literature leaves, nothing else.

## 🧠 The structural insight of this session (don't re-derive)

Dubickas's Lemma 6 is *not* atomic.  From his p. 574–575 it is

    Lemma 6  =  Lemma 3 (Corvaja–Zannier's main theorem, p. 177 — the ONLY subspace step)
             ∨  Lemma 5 (elementary, given CZ's Lemma 4)

and CZ's Lemma 4 (trace of `q α^(s n)` a nonzero integer ⇒ `α` is an algebraic integer or an
`l`-th root of a rational) is a **valuation/trace argument, not subspace-strength**.  So the repo's
`Dubickas2022` hypothesis now decomposes into one generational wall and one multi-lap-but-doable
theorem.  Chip Lemma 4 before touching Lemma 3.

## ✅ Proved this session (all `[propext, Classical.choice, Quot.sound]`)

* `Diophantine.mahler_mul_of_ridout1957` — **Mahler (1957 II) with an integer multiplier**, from
  `Ridout1957` (Mahler's §3 route with `ϑ = q`, `c = 2q`).  Needed because our approximants are
  half-integers: `‖2α^N‖` small says nothing about `‖α^N‖`.
* `isPisot_of_rat_den_one`, `round_dist_le_of_bnd`, `exists_pisot_pow_of_rat`,
  `exists_pisot_pow_of_pow_rat` — **Lemma 6's conclusion holds unconditionally (from `Ridout1957`)
  whenever some `α^(2^a)` is rational.**  This is Dubickas's own §2 route for Wagner–Ziegler Thm 1.
* `IsPseudoPisotMul`, `isPisot_of_pseudoPisotMul`, `otherConj_eq_zero_of_pow_rat`,
  `eq_rat_of_otherConj_eq_zero`, `card_otherConj_pow_le` — **all of Dubickas's Lemma 5**, plus the
  `deg α^N ≤ deg α` bound that turns his "we may assume the trace is nonzero" into a proof.
* `aroots_pow_mem` (conjugates of a power are powers of conjugates, via
  `(minpoly ℚ (α^N)).comp (X^N)` — no embeddings), `norm_lt_one_of_pseudoPisotMul`,
  `norm_eq_of_pow_eq` — every conjugate of `α` is inside the unit disc or is `ζα`.
* `tracePowSum`, `tracePowSum_rat`, `tracePowSum_recurrence` (`Σ_{k ≤ d} p_k U_(N+k) = 0`),
  `isIntegral_int_iff_minpoly_den` — Lemma 4's scaffolding.
* `exists_one_lt_mul_pow`, `valuation_multiset_sum_lt`,
  **`no_bounded_den_of_unique_max_valuation`** — the ultrametric **no-tie core of Lemma 4** for an
  arbitrary number field.
* `exists_pisot_pow_pseudoPisot_core` and `exists_pisot_pow_noD (hR : Ridout1957)` are *proved*
  from the two leaves below.

## ⛔ The two open leaves (both in `DubickasNoSubspace.lean`)

1. `corvajaZannier_dichotomy` — CZ 2004 main theorem, p. 177 (= Dubickas Lemma 3).  **The wall**:
   `p`-adic Subspace Theorem; mathlib has nothing.  Do not attack head-on.
2. `corvajaZannier_lemma4` — CZ 2004, Lemma 4.  **Next lap's target.**  Carries the free extra
   hypothesis `hsmall` (every conjugate of `α` is in the unit disc or has modulus `α`), discharged
   at the call site.  Two pieces remain:
   * **(a) the bridge** — build the splitting field of `minpoly ℚ α` inside `ℂ`
     (`IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet ℂ)`; `finiteDimensional_adjoin` works,
     probe verified, and the `NumberField` instance must be introduced with `haveI` *inside* a proof
     whose statement is the general one — a `theorem`-level instance argument cannot be inferred),
     transfer `tracePowSum` into it, and get the dominating prime from
     `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` (contrapositive).
   * **(b) the tie case** — several conjugates of maximal valuation; this is where CZ's
     `α^l ∈ ℚ` branch comes from (witness `2X² − 3`: `u_N = 0` for every odd `N`, `α² = 3/2`).
     Reduces mod the maximal ideal to `Σ x̄_σ^N = 0` in a finite field for infinitely many `N`;
     a small `p`-adic Skolem–Mahler–Lech step.

## 📄 Docs to read first

* `PROBE-DUBICKAS-NOSUBSPACE.md` — the full obstruction write-up: what is proved, the two refuted
  leads (**archimedean Liouville/Roth is provably vacuous here — it only re-derives `M(α) ≥ α`**;
  the Böttcher coordinate is not of Mahler-method shape), the worked `d = 2` Newton-polygon
  analysis, and the proposed literature `Prop`s (`CorvajaZannier2004` preferred over a raw
  `SchlickeweiSubspace`).  DIRECTION forbids stating them in `Literature/` — propose only.
* `PENDING_WORK.md` — leads with the phase-9 status and the ranked next attack.
* `ON-LINE-REQUEST.md` — **filed 2026-09-28, unanswered**: CZ 2004 pp. 176–179 (verbatim main
  theorem, verbatim Lemma 4, and *which machinery their proof of Lemma 4 uses*).  If a findings doc
  appears, read it before inventing a proof of Lemma 4, then `git mv` it to `archive/findings/`.

## ⚠️ Gotchas from this session

* `hD` is still on the three `Dubickas.lean` headlines **on purpose**.  Never route a headline
  through a `sorry`; `theorem1`/`oeis_constants` were re-verified axiom-clean after every commit.
* `Edges.lean`'s `end LeanFormalizations.Diophantine` is not at EOF-adjacent — appending a theorem
  to that file puts it *outside* the namespace and `Ridout1957` silently auto-binds as a variable.
* `linarith`/`nlinarith` blow the heartbeat budget when `lv / lu` appears as a division inside
  `set`-bound locals; introduce `lam` as an *opaque* local (`obtain ⟨lam, h⟩ : ∃ x, x = lv / lu`)
  and pre-expand products by hand (`mul_add`/`mul_sub` + the `f2` identity), then plain `linarith`.
* `Rat.den_eq_one_iff` takes the rational explicitly: `(Rat.den_eq_one_iff _).1`.
* `Multiplicative.toAdd_pow` does not exist under that name; use bare `toAdd_pow`.
* `ℤₘ₀` order lemmas are thin: `exists_one_lt_mul_pow` had to be proved by hand via
  `WithZero.ne_zero_iff_exists` + `WithZero.coe_lt_coe` + `toAdd_pow`.
