# Phase 58 COMPLETE — `ξ(3^(k+j) + s)` transcendental for even `s ≥ 8`, `3 ∤ s`

Target `src/LeanFormalizations/NumberTheory/Mills/ShiftedMillsLarge.lean` is **sorry-free** and
`xi_shifted_large_transcendental` is **axiom-clean** (`propext`, `Classical.choice`, `Quot.sound`).
Conditional only on the two literature `Prop` hypotheses `Saito2025TypeBTrace` and
`Siegel1944SmallestPisot` — **no rigidity node** (contrast phase 45's `ShiftedTraceRigidity`).

## What went in
* `largeC j s k = 3^(k+j) + s` plus its arithmetic: oddness (`s` even), `3 ∤ C_k`,
  doubling `2C_k ≤ C_(k+1)` from `hj`, the `29/10` ratio from `19 s ≤ 3^(k+j)`.
* `largeC_B5`: `(B5′)` via Euler with `t = φ(C_m)·i`, `i := 19s + m + 1`, so the same `k` carries
  both `C_m ∣ C_k` and the ratio bound (`t ≥ i` and `3^t > t`).
* `eq_one_of_eventually_dvd`: `g ∣ 3C_k − C_(k+1) = 2s`, `C_k` odd ⇒ `g ∣ s` ⇒ `g ∣ 3^(k+j)` with
  `3 ∤ g` ⇒ `g = 1`.
* Steps 4–5 (reusable): `minpoly ℤ β` for a Pisot `β` — monic, irreducible
  (`minpoly.prime_of_isIntegrallyClosed`), degree = `(minpoly ℚ β).natDegree`, conjugate bound
  transported, and **`powTrace_eq_traceSeq`**: Saito's `Tr(β^N)` = phase-56 `traceSeq (minpoly ℤ β) N`
  (roots multiset = image of `exists_root_enum`'s injective `e`, via
  `Multiset.eq_of_le_of_card_le`).  This is the bridge between Saito's trace identity and the
  companion-matrix machinery; expect to reuse it.
* `four_lt_pisot_pow` (Siegel): `κ^8 = 2κ² + 3κ + 2 > 4` by `linear_combination (κ^5+κ^3+κ^2+κ+2)*hκ`.
* `dvd_traceSeq_of_map_eq_X_pow`: `f ≡ X^d (mod c)` ⇒ `compM (ZMod c) f` nilpotent
  (`aeval_compM_self`) ⇒ `c ∣ traceSeq f N` for `N ≥ d`.  This is what kills Theorem D's
  excluded class: the prime `⌊ξ^(C_k)⌋` would be 3, contradicting `exists_floor_gt`.

## Next
`DIRECTION.md` has no phase 59 yet.  Natural continuations: (a) drop `s ≥ 8` by replacing Siegel's
bound with a direct estimate on `ξ`; (b) drop `3 ∤ s` / `s` even by handling the remaining residues;
(c) attack `ShiftedTraceRigidity` itself (phase 45's open node), now that
`powTrace_eq_traceSeq` puts Saito's traces into the integer matrix world.
