# HANDOFF 2026-10-05 — phase 61, node D planted + E1(−) proved (branch `mills-eplus`)

HEAD 6a5d6c4 (+ this note).  No uncommitted edits.  Scoped target: `ShiftedMillsAll.lean` sorry-free.
⚠ The target file's text is already sorry-free, but `halfShiftTraceRigidity_holds` now routes through
`Mills/HalfShiftRigidity.lean`, which still has open `sorry`s.  Do NOT `box done` until
`#print axioms ShiftedMillsAll.xi_shift_transcendental` shows no `sorryAx`.

## This lap (review lap)
- DIRECTION.md CURRENT DIRECTIVE rewritten: node D only, route below.  PENDING_WORK + STATUS updated.
- `Mills/HalfShiftRigidity.lean` created; `not_halfPrimeTraces` assembled from leaves and wired into
  `ShiftedMillsAll.halfShiftTraceRigidity_holds` (compiles).
- PROVED: `exists_int_poly` (ℤ[ζ₁₃] integrally closed, via
  `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime` on `cycField 13`),
  `thirteen_dvd_of_aeval` (Φ₁₃ ∣ P − n, eval at 1), `tau_pow_aeval`, `tau_pow_root`, `sum_orbit`,
  **`half_e1_minus`** (τ³γ = −γ ⇒ 13 ∣ every trace).

## Open leaves (HalfShiftRigidity.lean), suggested order
1. `half_e1` assembly: flip over `cycField 26` ⇒ v_k ∈ ℚ(ζ₁₃); pick j with u_j ≠ 0; u_j = ε ζ^a
   (as in `ShiftRigidity.exists_code`), c = ζ^(7a), γ = v_j/(c e_j^m) (s = 2m+1), γ² = ε e_j;
   τ (`exists_tau`) 3-cycles roots (copy `hpfix`/`three_cycle_of` from `e1_empty`); τ³γ = ±γ.
   (−) → `half_e1_minus` + `not_prime_of_dvd` (needs `halfExp_tendsto`).  (+) → new `half_e1_plus`:
   δ_k = τ^i γ cycled by τ, w_k = δ_k^s, a_k = v_k/w_k, a_k² = ε u_k; need lemma "a ∈ ℚ[ζ₁₃],
   a^52 = 1 ⇒ a^26 = 1" (i ∉ ℚ(ζ₁₃): ζ·b primitive 52nd root ⇒ cycField 52 ≤ cycField 13, finrank
   24 ∤ 12, `IntermediateField.finrank_dvd_of_le_right`); then `ShiftRigidity.e1_core` ⇒ a const
   (⇒ u const, contradicts non-constancy — ADD hypothesis `hnc : ¬ ∀ k, u k = u 0` to `half_e1`
   and pass it in `not_halfPrimeTraces`) or w const (moduli).
2. `not_prime_of_dvd`, `three_dvd_of_cube` (copy from `not_primeTraces_of_cube`), `halfExp_tendsto`.
3. `flip_mem` (single automorphism over M; case on which of the other two v's flip).
4. `circulant_const_mu` (copy `circulant_const`; equilateral: all-unimodular ⇒ c = 0 via b_k = c̄ a_k;
   one zero ⇒ u1³ = −u2³, u1+u2 = 3c ≠ 0, gcd(6,M) ∣ 2 ⇒ contradiction).
5. `half_generic` (M = adjoin ℚ (μ_2Q ∪ roots); σ³ fixes M; δ₀ := σ^i d; circulant).
6. `exists_root_cycField_26` (degree of x over cycField 26 divides 2).
7. Transfer: `window_half` (copy `window_shift`, period 2j), `exists_entry_nonscalar`,
   `exists_half_solution` (halfSys = shiftSys with P'^2 and the non-scalar row), `exists_half_spectral`.
