# HANDOFF 2026-10-05 — phase 61 (Theorem E+), branch `mills-eplus`, HEAD 4f9b93f

Target: `src/LeanFormalizations/NumberTheory/Mills/ShiftedMillsAll.lean` sorry-free.

## Done (axiom-clean)
- A `shiftedTraceRigidity_of_shift`; B `xi_shift_transcendental_of_rigidity` (helpers in the same file:
  `shiftC_cast/_pos/_two_mul_le/_ratio`, `not_pow_dvd_shiftC`, `shiftC_B5` (ordCompl), `shiftC_gcd`
  (g = 3^b·{1,2}), `shiftC_div_three_pow`).
- Node C wired: `shiftTraceRigidity_holds` := `ShiftRigidity.not_primeTraces` (new file `Mills/ShiftRigidity.lean`).
  Proved there: `rigidity_generic` (3-cycle over L via `exists_three_cycle`, `circulant_const`,
  `equilateral_zero`; needs only c = ω/tr(β^s) ∈ ℚ, `sum_zpow_rat`), `eq_one_or_neg_one_of_const`,
  `not_mem_cycField_two/eight` (`three_dvd_totient`).

## Open (node C, in ShiftRigidity.lean)
1. `not_primeTraces_of_cube`: f ≡ (X−z)³ mod 3 ⇒ 3 ∣ traceSeq (UnipotentTrace.three_dvd_trace_pow on compM,
   z=0 via ShiftedMillsLarge.dvd_traceSeq_of_map_eq_X_pow) + traces → ∞ (eventually_floor_eq_traceSeq).
2. `exists_spectral` (biggest): model = TheoremDMixed.floor_pow_prime_pow_add_not_prime_full +
   exists_spectral_solution_mixed.  Needs: window for exponent (3^n+s).toNat (generalize
   ShiftedWindow.window_of_eventually_prime; w² ≡ 1); limit T=C^(3^ν) with T^(Q+1) ≡ T, Q=3^f−1 by
   factor type of f mod 3 (finite check over the 27 cubics, native_decide OK, then pow_c_pow_congr);
   variable U with U·C^(s⁻) = T·C^(s⁺), tr U = w; nondegeneracy y·(T∓I)_ab = 1 (pigeonhole entry;
   C∓1 not nilpotent mod 3 outside cube class); transfer `exists_zero_of_family`; read eigenvalues via
   Vandermonde (TheoremDGeneral).
3. `e1_empty` (Q=26, root in ℚ(μ26)=ℚ(ζ13)): extra integer equation P(h(C)) = P(C)³ with h(α)=σ₃(α)
   (Frobenius congruence σ₃(x) ≡ x³ mod 3 in ℤ[ζ13]; disc f prime to 3 since f mod 3 irreducible),
   gives u_(σk)=u_k³; then rank-3 certificate `scripts/theorem-e-e1-certificate.py` (native_decide).
Node D (`halfShiftTraceRigidity_holds`) untouched.
