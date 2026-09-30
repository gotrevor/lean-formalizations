# HANDOFF 2026-09-30 — phase 49 COMPLETE: the Gauss (Dold) congruence for matrix traces is PROVED

`NumberTheory/Mills/GaussCongruenceProof.lean` is **sorry-free**; all three frozen statements are
`#print axioms`-clean (`propext, Classical.choice, Quot.sound`):

| statement | content |
|---|---|
| `gaussCongruenceTrace_holds` | `Literature.GaussCongruenceTrace` — for every `n`, integer `C`, prime `p`, `k`: `p^(k+1) ∣ tr(C^(p^(k+1))) − tr(C^(p^k))` |
| `mills_threeAdic'` | phase 29's 3-adic pinning, with the Gauss hypothesis DISCHARGED |
| `transcendental_of_not_pm_one'` | phase 29's transcendence criterion, likewise unconditional in it |

The Literature hypothesis (Steinlein, AMM 2017) is no longer a hypothesis of our own results: any
downstream use can be fed `gaussCongruenceTrace_holds`.  `Literature/GaussCongruence.lean` itself is
untouched (frozen), so `scripts/fact-graph` still lists the *def* as a 📚 node; the discharge lives
in the Mills file.

## The route actually taken (one economization over the header's plan)

Walk sums: `tr(C^N) = Σ_{w : Fin N → Fin n} ∏_{t : Fin N} C (w t) (w (t+1))` (`trace_pow_eq_sum_cw`,
proved through a linear-path lemma `pow_apply_eq_sum` + `cw_eq_plw`).  `ℤ/N` acts by rotation
(`rotE`), the walk weight is invariant (`cw_rotE`).

The header suggested handling `Σ_u f(u)^p ≡ Σ_u f(u)` by grouping words by minimal period
(primitive words, Möbius-style bookkeeping).  **That is not needed.**  The observation that collapses
it: `Σ_t`-products of `p`-th powers are the walk weights of the **entrywise** `p`-th power matrix, so

    (fixed part of the length-p^(k+1) walk sum) = tr((C^{(p)})^{p^k}),   C^{(p)}_{ij} := (C_{ij})^p

(`cw_repw`, `sum_over_fixed`).  Hence the whole theorem reduces to a *difference* statement about two
matrices congruent mod `p`, and THAT has a clean induction on `k` with a moving modulus:

    key : (∀ i j, p^(m+1) ∣ A i j − B i j) → p^(k+m+1) ∣ tr(A^(p^k)) − tr(B^(p^k))

whose step is exactly: free part of the walk sum (orbit size `p^k`, summand divisible by `p^(m+1)`)
plus fixed part = the same statement one level down for the entrywise powers, which gain one power of
`p` (`dvd_pow_sub_pow_step`, the `(a−b)·Σ a^i b^{p−1−i}` factorization).  No primitive-period
analysis anywhere.

Reusable pieces (none `private`):
- `dvd_sum_of_free` — abstract: an `N`-cycle acting freely on a `Finset`, an invariant `F` with
  `q ∣ F`, gives `N·q ∣ Σ F`.  Proved by fibering over the orbit-as-a-Finset (a complete invariant),
  no `MulAction`/quotient machinery.
- `pow_dvd_period` — a word of length `p^(k+1)` with any period `0 < j < p^(k+1)` already has period
  `p^k` (minimal period via `Nat.find`, divides every period, divides `p^(k+1)`, is `< p^(k+1)`).
- `prod_ofNat_mod` — `∏_{t : Fin (M·p)} H (t mod M) = (∏_{s : Fin M} H s)^p`, by induction on `p`
  through `Fin.prod_univ_add`.
- `repw`/`resw` + `sum_over_fixed` — fixed words ↔ length-`M` words.

## Gotchas worth remembering

- `NatCast (Fin N)` is deliberately NOT an instance in mathlib (coercion loops); use `Fin.ofNat N j`
  and the local helpers `ofNat_succ`, `ofNat_add`, `ofNat_val_lt`, `ofNat_mod_dvd`.
- `rw [pow_succ]` on a goal mixing `p^(k+1) : ℕ` (an exponent) and `(p:ℤ)^(k+m+1)` hits the wrong
  one; use `rw [show p ^ (k+1) = p^k * p from pow_succ p k]`.
- Rewriting a `Nat` equation that occurs in a `Fin _` **type index** fails (motive); go through
  `Fintype.prod_equiv (finCongr h)` instead (`prod_ofNat_mod`).
- `congr 2` on `u (Fin.ofNat M x) = u (Fin.ofNat M y)` strips too much; use `congrArg u`.

## NEXT

Phase 49's stop condition is met.  Open frontier for the Mills campaign is unchanged:
`ShiftedTraceRigidity` (phases 45–48 built its sub-nodes R4/window/Teichmüller); the remaining
sub-nodes of `PROOF-THEOREM-E.md` Steps 3–6 are the next real crux.
