# HANDOFF 2026-09-28 — Dubickas phase 8 COMPLETE: Lemma 8 is gone, `src/` is sorry-free

Branch `main`, HEAD at handoff `1827ad9` (+ this docs commit).  `lake build` green (**8707 jobs**).
`scripts/comparator-probe Dubickas` → identical.  **`src/` contains no `sorry`, no `admit`, no
declared `axiom`.**

## What landed

DIRECTION phase 8 asked for `c_eq_zero_or_two_noGap` from `Dubickas2022` alone, then to drop `hG`
from the `Dubickas.lean` headlines and the comparator challenge.  **All three done.**

1. **`c_eq_zero_or_two_noGap` is proved for every degree** (`DubickasNoGap.lean`, 61 lines).  The
   whole `deg β ≤ 5` case analysis — and with it the last `sorry` in `src/` (the disclosed
   `deg β ≥ 6` branch) — is **deleted**; the degree-uniform route replaces it wholesale.
2. **`hG : Dubickas2022PisotGap` dropped** from `transcendental_growth_of_monic_quadratic`,
   `theorem1`, `oeis_constants` (file path and every public name unchanged — ⚓ OEIS-linked) and
   from `Comparator/Dubickas/Challenge.lean` (+ its docstring).
3. `#print axioms` on all four, re-run this lap:

```
transcendental_growth_of_monic_quadratic : [propext, Classical.choice, Quot.sound]
theorem1                                 : [propext, Classical.choice, Quot.sound]
oeis_constants                           : [propext, Classical.choice, Quot.sound]
c_eq_zero_or_two_noGap                   : [propext, Classical.choice, Quot.sound]
```

`Dubickas2022` (his Lemma 6, Corvaja–Zannier ⇒ the `p`-adic Subspace Theorem) is now the **sole**
hypothesis under the OEIS-linked constants A076949 / A077124 / A076393 (Vardi).

## The idea (one sentence, then the glue)

The exact recursion identity `c = 2 βᴺ S_N + S_N² − S_(2N)` that `exists_pisot_trace_ident` hands
us **is** the statement that the second elementary symmetric function of the conjugates of `βᴺ` is
the constant `c/2` along the Graeffe tower `N = 2^j`; and *eventual constancy of `E₂` alone* forces
`c/2 ∈ {0,1}` (`eFull_two_const_eq_zero_or_one`, built last lap).  Lemma 8 was only ever supplying
a **lower** bound on `|S_N|` — the new route never wants one, which is why it is degree-uniform.

The glue this lap was two Newton identities at `k = 1, 2`, in `DubickasEsymm.lean`:

* `esymm_one_eq_sum : s.esymm 1 = s.sum` — `simp [Multiset.esymm, Multiset.powersetCard_one]`;
* `sq_sum_eq_psum_add_two_esymm : s.sum ^ 2 = s.psum 2 + 2 * s.esymm 2` — **multiset induction**
  off `Multiset.esymm_cons`, `linear_combination ih` in the cons step.  Much shorter than
  instantiating `multiset_mul_esymm_eq_sum` at `k = 2` (which would need `Finset.antidiagonal 2`
  computed and filtered);
* hence `eSmall_one : eSmall β 1 N = conjPowSum β N` and
  `two_mul_eSmall_two : 2 * eSmall β 2 N = conjPowSum β N ^ 2 - conjPowSum β (2 * N)`.

Then `eFull_succ halgβ 1 (2^j)` + those two + `rw [show (2:ℕ)^(j+1) = 2 * 2^j from ...]` makes
`hE2 : ∀ j ≥ j₀, eFull β 2 (2^j) = (c:ℂ)/2` a single `linear_combination h2 / 2 - h / 2`.  The
final `c/2 = 0 ∨ c/2 = 1` → `c = 0 ∨ c = 2` is `linear_combination 2 * h` then `exact_mod_cast`.

Full route + file map: **`PROBE-DUBICKAS-NOGAP.md`** (now marked CLOSED, verdict recorded).

## Where the project is

`src/` is sorry-free and axiom-free, so the frontier is **hypothesis discharge only**.  Ranked
table in `PENDING_WORK.md`; the binding order is `DIRECTION.md` → **CURRENT DIRECTIVE** (set this
lap, outranks this handoff).  Summary:

| next | why |
|---|---|
| 🟠 `Dubickas2022` (Lemma 6) | the only hypothesis left under the OEIS headlines; needs the `p`-adic Subspace Theorem, absent from mathlib — chip a *prerequisite* (heights / places), not the theorem |
| 🟡 Saito Remark 4.4 | degree-3 Pisot refinement of `transcendental_or_pisot`, `Mills/` |
| 🟡 Catalan phase 2 | probe-first; **never** claim `Irrational catalanConst` |
| 🟡 BHP / Matomäki / Ingham | primes in short intervals, the bedrock under Mills |

## Gotchas worth keeping

* `Multiset.esymm` has no `esymm_one` in mathlib; `Multiset.powersetCard_one : powersetCard 1 s =
  s.map singleton` is what makes the one-line `simp` work.  `Multiset.esymm_cons` /
  `Multiset.esymm_zero'` are **this repo's** lemmas (`MultisetGraeffe.lean`), not mathlib's.
* `2 ^ (j + 1)` does not unify with `2 * 2 ^ j`; rewrite with `pow_succ` + `ring` *before* using
  `two_mul_eSmall_two`.
* Dropping a hypothesis from a comparator challenge needs nothing but the same edit on both sides —
  `scripts/comparator-probe <Result>` catches a mismatch locally in ~1 min instead of a CI round
  trip.  Keep the unused `Dubickas2022PisotGap` **in** `Comparator/Dubickas/Support/Pisot.lean`: it
  mirrors `src/.../Literature/Pisot.lean` on purpose so auto-generated `_proof_N` names match.

Docs refreshed this lap: `STATUS.md` (header, Where-it-stands, new lap bullet, ledger re-run from
real `#print axioms`, pointers), `DIRECTION.md` (CURRENT DIRECTIVE), `PENDING_WORK.md` (frontier
table), `PROBE-DUBICKAS-NOGAP.md` (verdict + file map), `Mills/SaitoDigits.lean` header (its "the
only `sorry` here" note was stale — `saito_lemma36C` is proved conditionally on BHP + Matomäki).
