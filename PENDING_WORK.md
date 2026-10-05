## phase 65 lap 2 (2026-10-05): records closed under Lemma 8; the 3-adic route REFUTED on the unipotent class
* `ShiftRigidityDeg.eventuallyRecordShift_of_pisotGap` PROVED (axioms: propext, choice, Quot.sound).
  Card ≤ 2 → `eventually_record_of_card_le_two`; card ≥ 3 → `pisot_degree_bound` at μ = 1 via
  `‖S(n)‖ ≤ fract < 1/P ≤ 2β^(−n)` at the last record before each non-record.
  So `xi_shift_transcendental_of_pisotGap` rests only on the two degree-≥4 rigidity leaves.
* Crux finding (`Mills/ShiftRigidityUnipotent.lean`, kernel): `unipotent_trace_congr`.  For the quartic
  Pisot f₀ = X⁴ − 4X³ − X + 1 ≡ (X−1)⁴ (mod 3), s = −1, tr C^(3^n−1) ≡ tr β^(−1) = 1 (mod 3^(n−1)).
  The cubic cube-class kill (tr ≡ 3z^m ≡ 0) is a degree-3 accident; in degree 4 window + Teichmüller +
  spectral data are all consistent.  Maze row added (anchor `unipotent_trace_congr`).
  `pisot_f₀` is a sorry (~99%, numerics).  New open node `UnipotentCovering`.
* Next attack on the crux: (a) split `shiftTraceRigidity_ge_four` into unipotent class vs rest as two
  named leaves (rest = generalised spectral route: Galois element acting fixed-point-freely, ±1
  constant excluded since C ∓ 1 not nilpotent mod 3); (b) on the unipotent class, use the window's
  Step 1 more sharply: 3^(n+1) | ord(C mod p_n) with v₃(p_n − 1) = n − O(1) forces an eigenvalue of
  C mod p_n generating the 3-Sylow of F_{p^i}^*, i ∈ {3} for ℓ = 4 (f mod p_n has a cubic factor).
  Test whether that compounding constraint contradicts anything (sibling: run it on X⁴−aX³−1 too).

## phase 64a lap 2 (2026-10-05): control: decay alone admits degree 4
* `DecayDegreeFour.decay_admits_degree_four` (sorry ~90%): X⁴ − aX³ − 1 is a quartic Pisot with decay μ < 1/3 at every n.
  So the 5/9 wall cannot be closed by any decay-only degree bound.  Next: a dominant-triple analogue of
  `lower_along_records` that uses the orbit n ↦ 3n − d.

## phase 64a lap 1 (2026-10-05): E+ for θ < 5/9 PROVED; the 5/9 wall named
* `SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval'` (θ < 5/9) and
  `xi_shifted_transcendental_of_shortInterval'` (Theorem E): no sorryAx.  `ingham_of_bhp` proved.
  `xi_shift_transcendental_ingham` and `xi_shifted_transcendental_ingham` are wired from the frozen
  `xi_shift_transcendental_of_shortInterval`, whose only `sorry` is the branch θ ∈ [5/9, 2/3).
* New `Mills/SaitoTypeBThetaParts.lean`: θ-parametric copies of bhp_step … saitoTypeB_shift
  (parameters θ, ratio floor ρ ∈ (2,3), decay μ ∈ (1/3, 1], μ ≤ (1−θ)ρ − 1), `shiftC_ratio_ev`.
  `SaitoTypeB.xi_shift_transcendental_of_shift_disj` factors the classical endgame (statement of
  `xi_shift_transcendental_classical` unchanged).
* **Why not 2/3**: the decay exponent is μ < 2 − 3θ and the Baker-free degree bound is
  (ℓ−1)μ ≤ 1; the endgame is degree-3 only, so μ > 1/3 ⇔ θ < 5/9.  Ingham's 5/8 is above.
  Open node `SaitoTypeBTheta.ShiftPisotDegreeLeThree θ`; Maze row added.
* Next attack: exclude Pisot degree ℓ ≥ 4 for the E+ orbit n ↦ 3n − d (all large k records ⇒
  decay at every k).  Candidate: a degree-ℓ version of `e2_zero_of_nonrecord` — but for ℓ ≥ 4
  non-records only force f < p^(−2), compatible with norm ≥ 1 (f ≳ p^(−(ℓ−1))); so the record
  step itself (`eventually_record_of_card_le_two`) also needs a new idea beyond degree 3.

## phase 62 lap 4 (2026-10-05): DONE — headline has no sorryAx
`#print axioms SaitoTypeB.xi_shift_transcendental_classical` = [propext, Classical.choice, Quot.sound,
+ two native_decide certs].  Closed this lap via new `Mills/DominantPair.lean`:
`lower_along_records` (Mignotte-lite dominant set {γ} or {γ,γ̄}; `zpow_eq_one_of_records`:
u^(2n_k) → −1 along records with gaps ≤ T and g n_r = 3^(r−k) g n_k − s(3^(r−k)−1) ⇒
u^(2s(3^t−1)) = 1 ⇒ γ^N = γ̄^N, contradicting `pow_ne_pow_of_roots`).  Gives
`NoGap.conjPowSum_lower_of_recurrence` (Rec = univ, g = 2) and `card_le_two_of_records`
(record_decay + card_mul_le_of_lower: L·151/400 ≤ 1).  Remaining src sorry `saitoTypeBLeast_holds`
(general C, needs Matomäki + Baker) is OFF the done path by directive.

## phase 62 lap 3 (2026-10-05 review lap): the three open leaves, two Baker-free mechanisms
Done-path `sorryAx` comes from exactly: `finite_e2_zero_orbit` (4b), `card_le_two_of_records` (3),
`NoGap.conjPowSum_lower_of_recurrence`.  Decomposition (new file `Mills/Skolem.lean` + `Mills/DominantPair.lean`):
 (I) SKOLEM, prove the stronger `∀ᶠ n, e2pow β n ≠ 0` for every cubic Pisot `β` (4b follows).
  I1 `skolem_det_ne_zero` (DECISIVE, pure): `U c z = Σ_{k≤z} C(z,k) p^(2k) c_k`, `β_k, α_k ∈ ℤ` with
     `β_{0,1,2} = 0,1,0`, `α_{0,1,2} = 0,0,1`; for `0 < a < b`, `U β a U α b − U β b U α a ≠ 0`.  In `ℚ_[p]`:
     term `(k,k')` is `p^(2(k+k')) β_k α_k' G`, `k!k'! G = ab(b−a) H` (falling factorials, `sub_dvd_eval_sub`);
     main `(1,2)` = `p^6 ab(b−a)/2`; others `≤ p^(−7)‖ab(b−a)‖` since `2 v_p(k!) ≤ k − 1`.
  I2 explicit Cayley–Hamilton on `Fin 3`; `ℓ(D^k) = α_k ℓ(D²) + β_k ℓ(D) + γ_k ℓ(1)`.
  I3 `A^P ≡ 1 mod p²` (unit of finite ring `Matrix (Fin 3) (Fin 3) (ZMod (p²))`, `p ∤ det A`).
  I4 three zeros on `n0 + P·ℕ` ⇒ `ℓ` kills `1, D, D²` ⇒ whole class zero.
  I5 bridge: `e2pow β n = w n`, `w` the integer recurrence of `X³ − e₂X² + e₁e₃X − e₃²` (Vieta on `β, γ1, γ2`).
  I6 non-degeneracy: real pair ⇒ `e2pow ≠ 0` (sizes); complex pair ⇒ `u^(2P) = 1` contradiction (II2).
 ✅ (I) DONE (lap 3): `Skolem.eventually_ne_zero_of_recurrence`, `E2Skolem.eventually_e2_ne_zero` (every cubic
    Pisot, all large n), `finite_e2_zero_orbit` and `eventually_record_of_card_le_two` axiom-clean.
    `PisotGalois.pow_ne_pow_of_roots` (II2 general form) and `eq_or_eq_conj_of_norm_eq` (II1) PROVED.
 (II) DOMINANT PAIR.
  II1 Mignotte-lite: other conjugates `γ, δ` with `|γ| = |δ|` ⇒ `δ ∈ {γ, γ̄}` (all conjugates of `ρ = γγ̄`
      have modulus `< 1`; product of roots of `minpoly ℤ ρ` is a nonzero integer).
  II2 non-real other conjugate `γ` ⇒ `γ/|γ|` not a root of unity (`σ γ = β` ⇒ `|σ γ̄| = β`).
  II3 `S(n) = R^n (2 Re u^n or ±1) + O(R'^n)`, `R' < R`.
  II4 records with gaps `≤ T` + `n_(k+1) = 3n_k − d`: `Re u^(n_r) → 0` ⇒ `u^(2n_r) → −1` ⇒ for a gap `t`
      occurring infinitely often `u^(d(3^t−1)) = 1`.  Gives `lower_along_records` ⇒ both (3) and NoGap.

## phase 62 lap 2 (2026-10-05): Baker-free route via RECORDS (Mills/SaitoTypeBRecords.lean)
xi_shift_transcendental_classical now proved from saitoTypeB_shift (no hG).  Open on path:
 1. records_pisot PROVED (record_decay + minimal-g gcd argument).
    Nat.nth records; exists_pisot_of_decay_subseq').  Elementary, do first.
 2. record_gap_bounded PROVED (resultant norm one_le_norm_prod_pow_sub + Saito (5.1)).
 3. card_le_two_of_records (needs conjPowSum_lower_of_recurrence generalised to bounded gaps).
 4. eventually_record_of_card_le_two PROVED from 4a e2_zero_of_nonrecord PROVED + 4b finite_e2_zero_orbit (sorry, 3-adic Skolem).
 + NoGap.conjPowSum_lower_of_recurrence (Smyth/Mignotte + a_k² dynamics).

## phase 62 (2026-10-05, lap 1, branch `mills-eplus`): crux = Baker-free Type B for E+
DONE: `SaitoTypeBParts.lean` sorry-free; `saitoTypeBLeastEv_holds (hB hD hG)` and
`xi_shift_transcendental_classical' (hB hD hG)` free of sorryAx; `xi_shifted_transcendental_classical`
reduced to `xi_shift_transcendental_classical`.
OPEN (the frozen done-criterion): drop `hG`.  `SaitoTypeBNoGap.lean`:
 (b) `conjPowSum_lower_of_recurrence` (sorry, ~90%): Smyth via Galois (AlgQ, `exists_algEquiv_of_roots`
     in TheoremDMixed) + the `a_k² → −1`, `a_(k+1)² → −v²` argument.  Removes hG from case (II) for E+.
 (a) `SparseNoCancel` (reopen node, Maze row): Saito case (I), sparse decay β^(−19n/10), degree ≥ 3.
     Norm bound gives only β^(−(ℓ−1)n).  Borderline at ℓ = 3 (rate 2 vs 1.9; for s < 0 the constant
     ξ^(−2|s|)/3 wins).  Needs a new idea for ℓ ≥ 4.
NEXT: prove (b); restate Type B for exact-recurrence C with hS : SparseNoCancel in place of hG.

## phase 61 (2026-10-05 review lap, branch `mills-eplus`): crux = node D `halfShiftTraceRigidity_holds`
A, B, C proved (C: `ShiftRigidity.not_primeTraces`, native_decide certs `cm3_check`, `E1Cert.cert_all`).
Node D route (decomposition lives in `Mills/HalfShiftRigidity.lean`; paper = PROOF-THEOREM-E.md "E+ for odd s"):
 D1 cube class for any exponent sequence → ∞ (generalise `not_primeTraces_of_cube`).
 D2 `window_half`: exponent N_n = (3^n+s)/2; period 2j in the filter (3^n(3^{Kj}−1) ∣ 3^n(3^{2Kj}−1)/2).
 D3 transfer: `P^(3^F) = P`, `P'^2 C^a = P C^b`, `w² = 1`, `tr P' = w`, `y·Σ r (P − P₀₀•1) = 1`
    (T = C^(3^ν) is not scalar mod 3 outside the cube class).  Spectral data: `v_k² = u_k α_k^s`,
    `Σ v_k = ω`, `u` non-constant.
 D4 flip lemma: if `M ∋ v_k²` for all k then `v_k ∈ M` (an automorphism over M flipping one v_k:
    |S|=1 ⇒ v_k = 0, |S|=2 ⇒ v_l = ω ⇒ |α_l| = 1, |S|=3 ⇒ ω = 0).
 D5 generic (no root in ℚ(μ_{2Q})): M = ℚ(μ_{2Q}, roots); 3-cycle σ over ℚ(μ_{2Q}); δ with δ² = α from
    some v_j (u_j ≠ 0); σ³ fixes M; a_k = v_k/δ_k^s ∈ μ_{2Q} ∪ {0} fixed by σ; circulant with roots of
    unity (equilateral case needs a primitive 6th root, impossible as 3 ∤ 2Q) ⇒ a constant ⇒ u constant.
 D6 E1 at g = 2 (a root in ℚ(μ_52) ⇒ one in ℚ(μ_26)): flip over ℚ(ζ₁₃) ⇒ v_k ∈ ℚ(ζ₁₃); γ = v_j/(c α_j^m),
    γ² = ±α_j; τ: ζ ↦ ζ² 3-cycles roots, τ³γ = ±γ.  (+) g = Π(X − τ^iγ) ∈ ℤ[X] Pisot, tr g^(2N) = tr f^N ⇒
    node C.  (−) γ = h(ζ), h ∈ ℤ[X] (integral closure), Φ₁₃ ∣ h(X⁸)+h(X) ⇒ 13 ∣ h(1) ⇒ 13 ∣ every trace.

## ✅ phase E10 DONE (2026-10-01): Remainder.lean sorry-free, all axiom-clean; see HANDOFF-2026-10-01-erdos385-E10-done.md

## phase E9b (2026-10-01 review lap, branch `erdos-385-c`): crux = `localZeroDetect_of_richert`
Headline-path open leaves (PowerSaving/): `localZeroDetect_of_richert` (ZeroDetect.lean, 75%) and
`largeValueCount_of_zeroDetect` (ZeroCount.lean, 85%).  `nearOneLargeValues_of_density` is OFF path
(not derivable for slow-Mellin weights; Maze row).  Decomposition of the crux (ZeroDetect header):
 (a) `local_logDeriv_bound`: zero-free disc `‖ρ − (1+η₂+iy₀)‖ ≤ 5η₂/2` ⇒ `|ζ'/ζ(σ+iy₀)| ≤
     K(log|y₀| + (loglog|y₀| + log(1/η₂) + 1)/η₂)` for `σ ∈ [1−η₂, 1+3η₂]` — `local_landau` with
     δ = 4η₂; M from Richert (σ ≤ 1, exponent B⁺(3η₂)^{3/2}) and `ZetaUpperBnd` (σ ∈ [1, 2]);
     centre `ZetaLowerBound3` at σ = 1+η₂.  Model: Landau/Zeta.lean `zeta_disc_growth`, `zeta_local`.
 (b) rectangle shift on `[σ₁, σ₂] × [−U, U]` (generalise `rect_shift_norm`).
 (c) assembly modelled on `vertical_integral_bound`: V4 at Re 2; tails |y| > P; shift to
     c = 1 + 1/log P (|H| ≤ 3 log P via `logDeriv_zeta_dirichlet_bound`); split at L; shift to
     σ₁ = 1 − η₂, η₂ = η + 3 loglog P/log P; Mellin bounds from `mellin_pointwise` (y^{−4}).
 Then the transport (ZeroCount.lean header).
 PROGRESS (325b5f7): (a) PROVED (`local_logDeriv_bound`); (b) PROVED (`rect_shift_gen`); (c) started:
 `box_H_bound`, `zc_tail`, `zc_eventually` proved in ZeroContour.lean; next zc_rect1/zc_split/zc_rect2.
 ✅ CRUX PROVED (2026-10-01): `localZeroDetect_of_richert` axiom-clean ([propext, choice, Quot.sound]),
 A = 8, via `zc_rect1`/`zc_split`/`zc_rect2` (ZeroContour.lean), `zc_numeric` + `vkDev_lt_of_zeroFree`
 (ZeroDetect.lean).  NEXT = transport `largeValueCount_of_zeroDetect` (ZeroCount.lean:34).
## ✅ (2026-10-01): phase E8 COMPLETE.  `badCountQuasiPower_holds` (moonshot:
#bad ≤ C X exp(−log X/(32400 (log log X)²))) and `badCountExp_threeQuarters` (milestone, derived via
`rpow_le_quasi`) both proved, [propext, Classical.choice, Quot.sound] — UNCONDITIONAL (no lit Props).
Final step in `QuasiPower/Final.lean`: m = ⌊(log₂X/8)^{1/4}⌋, `term_pool`, `term_main`, `exp_target_ge`.
Remaining gap to the framework ceiling X^{1−o(1)}: the (log log X)² loss (window size k ≍ m⁴/log²m).

## ✅ (2026-10-01, session B): LinearSieve SCOPE COMPLETE.  `aLow_ge_fl'` (FLLowerB.lean) proved:
Buchstab from 2 + `siftMax_le_fl` per prime + `sum_Vw_div` telescoping + `rankin_error_sum`
(u e^{−2u} ≤ 4e^{−s}/u, Mertens first; no dyadic sum).  `linearSieveIntervalLower_holds`,
`fundamental_lemma`, `lowerAt_pos`: [propext, Classical.choice, Quot.sound].  LinearSieve/ sorry-free.

## CLAIM (2026-10-01 11:52, session B): A's handoff ended its lap; B is now implementing the FL lower
half `aLow_ge_fl` in NEW file `LinearSieve/FLLowerB.lean` (reuses A's `Vw`, `sum_Vw_div`,
`primeProd_log_bounds`; no hypothesis — uses `siftMax_mul_le` directly; no dyadic sum).  If A resumes,
please take something else or coordinate here before touching `aLow_ge_fl`.

## (2026-10-01, session B): FL UPPER HALF DONE, axiom-clean.  `bUp_le_fl` (FLUpper.lean):
b(s) ≤ e^{−γ}s + M e^{−s}.  Step (b) for session A = `siftMax_mul_le` (FLUniform.lean):
  S⁺(M,w)·(1 − e^K ξ^{−8/log w}) ≤ M/Π(w−1) + selE w ξ²   for all w ≥ 2, ξ ≥ 1  (K = rankK).
(Multiplicative form — no division; with log ξ ≥ log M/4 the factor is ≥ 1 − e^K e^{−2 log M/log w}.)
`fundamental_lemma` is now wired from `bUp_le_fl` + the single leaf `aLow_ge_fl` (Leaves.lean, A's).
Tip for A: the dyadic sum is avoidable — with u = L/log p ≥ s, u e^{−2u} ≤ D e^{−s}/u, so the error is
≤ D e^{−s} Σ_{p<z} log p/(pL) ≤ D e^{−s}(1/s + B/L) by `sum_log_div_le` (FLUniform).

## CLAIMS (2026-10-01, session A): `phi_buchstab` + `buchstab_limit_b` DONE (A).  A now takes FL
lower half (B's plan step (d)) in a NEW file `LinearSieve/FLLower.lean`, stated against an explicit
hypothesis `UpperFLHyp` (B's step (b) shape: S⁺(M,w) ≤ M·V(w)(1+K e^{−c log ξ/log w}) + (Cξ log ξ)²).
B keeps (a)–(c) and the final wiring of `fundamental_lemma`.  Only finite-range s matters trivially
(a ≥ 0 ≥ Cs − Me^{−s} for s ≤ s₀ with M large), so (d) is needed for large s only.

## phase E5 lap 3b (2026-10-01): comparison_functions proved from two leaves (DelaySolution.lean)
`delay_solution` (pure delay-ODE: Q=2sω, P=m; positivity via (s−1)P(s)=∫_{s−1}^s P; window-average
contraction for ω) and `omega_le` (ω∞ ≤ e^{−γ} ⇔ λ ≥ 1; route: rough-number count Φ with forward
Buchstab + PNT on (1,2], Φ ≤ S⁺ ≤ Cs+Me^{−s}).  λ = C/ω∞ ≥ 1 IS needed (β = 2λ ≥ b = 2 on (1,2]).

## phase E5 lap 3 (2026-10-01): crux decomposed into named leaves (`LinearSieve/Leaves.lean`)
`lowerAt_pos` proved from `aLow_pos_of_leaves` via `lower_of_aLow_pos` (Normalized.lean; aLow/bUp =
liminf/limsup normalisations).  `bUp_le_two` PROVED (UpperBoundary.lean).  Open leaves (sorry):
aLow_nonneg, aLow_mono, bUp_mono, buchstab_limit_a/b, fundamental_lemma (|·−Cs| ≤ M e^{−s}),
comparison_functions (α,β), and the assembly `aLow_pos_of_leaves` (comparison_principle on
K = max(α−a, b−β, 0)).  ⚠ two sessions worked this branch concurrently; lap-2's note says λ ≥ 1 is
not needed — but K = 0 on (1,2] needs b ≤ β = 2λ there, so with b ≤ 2 we do need λ ≥ 1 (ω_∞ = e^{−γ}).
Assembly `aLow_pos_of_leaves` PROVED (Assembly.lean `pos_of_delay_system`).  Next: bookkeeping leaves (aLow_nonneg, monotonicity), then buchstab_limit_a/b.

## ⚠ COLLISION (2026-10-01 11:xx): two writers in this worktree
Another session (not visible to ListAgents) commits to `erdos-385` here concurrently, with its own
design (`Normalized.lean`/`Leaves.lean`: aLow/bUp liminf, leaf sorries).  Duplicates landed:
`upperAt_two` (Crux.lean) ≈ the other side's `bUp ≤ 2` (92dcceb).  Host: run only one session.

## phase E5 lap 2 (2026-10-01): crux normalised to `lowerAt_pos`
`siftMin_lower` proved from `lowerAt_pos : ∀ s > 2, ∃ c > 0, LowerAt s c` (Crux.lean; `LowerAt`/`UpperAt`
are the ε–N₀ normal forms of a(s), b(s)).  Insight: positivity of α = λ(sω − m/2) on (2,3] is
2λ log(s−1), independent of λ — so the rough-number/PNT argument for λ ≥ 1 is NOT needed; only
λ = e^{C₃}/ω_∞ (C₃ = mertensThirdConst, no γ needed) plus decay sω−sω_∞, m = O(1/Γ).
Next: leaves `upperAt_two` (b ≤ 2 on [1,2] from siftMax_le_log), limit Buchstab, fundamental lemma.

## phase E5 lap 1 (2026-10-01): linear sieve reduced to one crux, route fixed
`linearSieveIntervalLower_holds` is proved from `LinearSieve.siftMin_lower` (Crux.lean, disclosed sorry).
`LinearSieve/Buchstab.lean` (sorry-free): self-similar problem class, exact Buchstab identity,
`siftMin_buchstab` / `siftMax_buchstab`.  Refuted: one Buchstab step on Selberg reaches only s ≳ 2.05
(Maze row).  Route for the crux (5 steps, LinearSieve.lean header): Selberg 1-dim, limit Buchstab
inequalities, fundamental lemma, JR comparison functions with λ = e^{-γ}/ω_∞ ≥ 1 via forward
rough-number Buchstab + PNT, and a derivative-free comparison principle (weight u − 1, Tonelli).
Step 5 DONE (`comparison_principle`); step 1 DONE (`LinearSieve/Selberg.lean` `siftMax_le_selberg`: S⁺ ≤ N/G + E²).  G ≥ log ξ DONE (`LinearSieve/GLower.lean` `log_le_selG`, also `sum_inv_le_prod`).  E ≤ ξ·Π(ξ) DONE (`selE_le`, Π = mertensP).  Π(ξ) ≪ log ξ DONE (`MertensBound.lean` `mertensP_le_log`, `siftMax_le_log`: S⁺ ≤ N/log ξ + (Cξ log ξ)² for ξ < z).  Next: plant steps 2–4 as named sorries in `LinearSieve/Limits.lean`;
most novel) and step 1 (copy of Brun/PairSieve).

## phase E4b DONE (2026-10-01): `Literature.McDiarmidFinite` discharged
`mcDiarmidFinite_holds` axiom-clean.  Key move: average over coordinates in `s` by `s.piecewise z x` with `z` ranging over the full product (no sub-product types); the coordinate-swap involution on `Ω × Ω` gives both the tower property and the mean-zero condition for Hoeffding.  E4 (`Exceptional.lean`, branch `erdos-385-brun`) now needs only `ArithLargeSieve` and `LinearSieveIntervalLower` once merged.

## phase 57 DONE (2026-09-30) — Theorem D in full: PROVED and axiom-clean

## Phase 60 DONE (2026-10-01)
`Mills/Kronecker.lean` sorry-free, `#print axioms` = {propext, Classical.choice, Quot.sound} for all 7.
Key moves: split + det≠0 ⇒ charpoly ∣ (X^(p−1)−1)^n ∣ X^(p^n(p−1))−1 (Frobenius in the commutative
ring `(ZMod p)[X]`, so no matrix CharP needed) ⇒ D^(p^n(p−1)) = 1 ⇒ Euler on c.  `charDisc ≠ 0`
from new `Projective.exists_companion_root_vieta` (distinct complex roots via `Irreducible.separable`).

`NumberTheory/Mills/TheoremDMixed.lean` is sorry-free; `floor_pow_prime_pow_add_not_prime_full` is
`#print axioms`-clean.  See `HANDOFF-2026-09-30-phase57-complete.md`.  The crux
(`exists_mixed_limit`):
for `f ≢ X^d (mod c)` there are `L, Q ≥ 1` with, for every `n`, `T := C^(L·c^n)` satisfying

* `T^(Q+1) ≡ T (mod c^(n+1))`, and
* `det (1 − T^Q) ≡ 0 (mod c^(n+1))`.

### The design decision that removed a Hensel lift

The header route asks for `tr(T^Q) ≡ m` with `1 ≤ m ≤ d` the number of unit roots.  Getting the
integer `m` needs the Hensel coprime factorization `f ≡ X^r·g (mod c^k)`, the CRT splitting of
`(ℤ/c^k)[X]/f`, and the rank of an idempotent over `ℤ/c^k` — none of which is in mathlib.
**Replace that equation by `det (1 − T^Q) = 0`.**  Over `ℂ` it reads `∏_k (1 − u_k^Q) = 0`, i.e.
*some* `u_k ≠ 0` — exactly what step 3 consumes — and it is a single integer polynomial equation,
so the Nullstellensatz transfer takes it unchanged.  Mod `c^(n+1)` it is free: `T^Q` is idempotent,
`ZMod (c^(n+1))` has no nontrivial idempotents, so `det(1 − T^Q) = 0` ⟺ `T^Q ≠ 0`, and `T^Q ≠ 0`
is visible already mod `c`.  No `m`, no rank, no Hensel.

### How `T` itself is built (phase 56's `C^(Q c^n) ≡ I` has no analogue)

`C mod c` is singular, so there is no `Q` with `D^Q = 1`.  What survives is eventual periodicity in
the *finite monoid* `Mat_d(𝔽_c)`: `∃ a, Q ≥ 1, D^(a+Q) = D^a` (`exists_period`), and then with
`L := a·Q` every positive multiple of `L` gives the same element (`pow_mul_period`), so `D^L` is
idempotent and `D^(L(Q+1)) = D^L`.  That base congruence mod `c` is lifted to `c^(n+1)` by phase
47's `TeichmullerCongruence.pow_congr_lift` (`pow_c_pow_congr`).  `D^L ≠ 0` is the *only* use of
`f ≢ X^d (mod c)`, via `map_eq_X_pow_of_compM_pow_eq_zero`: a vanishing power of the companion
matrix forces `f mod c ∣ X^M`, hence `= X^d` (`modByMonic` + the cyclic vector `e₀` + `prime_X`).

### Steps 2–4, as built

The solution is taken in `AlgQ := algebraicClosure ℚ ℂ`, not in `ℂ`: step 3 conjugates by a field
automorphism, and `Aut(ℂ/ℚ)` is not constructible in mathlib, while `T^(Q+1) = T` already forces
every spectral value into `{0} ∪ μ_Q`, so the solution is algebraic anyway.  `exists_zero_of_family`
and `exists_root_enum_field` are phase 56's Nullstellensatz and root enumeration generalized from
`ℂ` to any algebraically closed characteristic-zero field (all the proofs used about `ℂ`).
`transport_solution` carries a solution along any ring hom — the system has integer coefficients —
which is what makes both the automorphism `τ` and the inclusion `AlgQ ↪ ℂ` legitimate.

### finding (2026-09-30, phase 49): the composite-base descent is FALSE

`CoveringEngine.lean`'s header wishes for a Gauss-type descent
`V(c^(k+1)) ≡ V(c^k) (mod c^(k+1))` for general odd `c`.  It is now available for every PRIME `c`
and every progression of exponents (`gaussCongruence_mul`), but **not** for composite `c`:
`gauss_anchor_composite` in `GaussCongruenceProof.lean` exhibits `C = !![1,2;3,4]` with
`9^2 ∤ tr(C^(9^2)) − tr(C^9)`.  So any engine step that wants composite `c` must go through the
full Möbius form `n ∣ Σ_{d ∣ n} μ(n/d) tr(C^d)` — which is now PROVED and axiom-clean in the same
file (`dold_congruence` / `dold_congruence'`), by divisor pairing off `gaussCongruence_mul`, with no
primitive-period decomposition needed.

## phase 49 DONE (2026-09-30): Gauss/Dold congruence for matrix traces PROVED

`NumberTheory/Mills/GaussCongruenceProof.lean` sorry-free + axiom-clean; `Literature.GaussCongruenceTrace` discharged (`gaussCongruenceTrace_holds`), phase 29's two 3-adic results restated unconditionally in it.  Key insight: the rotation-fixed part of the walk sum is the trace for the ENTRYWISE `p`-th power matrix, which turns step 3 into the moving-modulus induction `key` and kills the primitive-period/Möbius bookkeeping.  See `HANDOFF-2026-09-30-phase49-complete.md`.

## phase 47 (2026-09-30) — CLOSED: `A^(c^n)` is eventually periodic `c`-adically

`NumberTheory/Mills/TeichmullerCongruence.lean` is sorry-free; `pow_prime_pow_period_congr` is
`#print axioms`-clean (`propext, Classical.choice, Quot.sound`).  For `A` invertible mod `c` there
are `f ≥ 1` and `a` with `A^(c^(n+f)) ≡ A^(c^n) (mod c^(n-a+1))` for all `n ≥ a` — i.e. the
`c`-adic limit points of `A^(c^n)` are the `f` values `lim_m A^(c^(a+r+mf))`, `r < f`.  This is
sub-node R2 of `ShiftedTraceRigidity` (`ROADMAP-PRIME-TOWERS.md` §4-live).

**Route correction vs the file header (less machinery).**  The header proposed the binomial
expansion `(Y + c^e Z)^c` with `c ∣ binom(c,i)`.  That is avoidable: use the *geometric-sum*
factorization `X^c - Y^c = (∑_{k<c} X^k Y^(c-1-k))·(X - Y)` (`Commute.geom_sum₂_mul`, valid for
commuting matrices).  Mod `c` every one of the `c` summands collapses to `Y^(c-1)`, so the cofactor
is `≡ c·Y^(c-1) ≡ 0 (mod c)`; multiplying by `c^e ∣ X - Y` gives `c^(e+1)` with no binomial
coefficients and no `Z` / no smul-divisibility bookkeeping at all.  `pow_congr_lift` is the reusable
form (two commuting matrices, unlike `SmulDvd.pow_prime_pow` which is relative to `1`).
The mod-`c` base step is `SharedConjecture.exists_trace_pow_congr`'s order splitting verbatim
(`Nat.ordProj_mul_ordCompl_eq_self` + `Nat.ModEq.pow_totient`), with `a = N.factorization c`,
`f = φ(ord_compl[c] N)`, `N = |GL_d(ZMod c)|`.
`mapMatrix_eq_of_dvd` / `dvd_of_mapMatrix_eq` are the entrywise-congruence ↔ `ZMod c`-reduction
bridge; note `ψ M i j` is *defeq* (not `simp`-equal) to `((M i j : ℤ) : ZMod c)`, so close that step
with `rw [hsum]; rfl` + `exact`, never `simpa` (which pushes `map` under the `∑` and mismatches).

### Next attack on `ShiftedTraceRigidity`
R2 is now available; the open sub-nodes are the *identification* of the `f` limit points with
Teichmüller lifts of the eigenvalues (needs `ℤ_c` or a resultant-free surrogate) and the step from
"finitely many limit points" to "the window `μ_(d!)` is visited finitely often".

## phase 42 (2026-09-30) — CLOSED: Theorem B (2×2 traces at odd primes, classified)

`NumberTheory/Mills/TraceClassification.lean` is sorry-free; all three frozen statements are
`#print axioms`-clean.  `DoubleExpTraceComposite` now holds for `n = 2` at every odd prime `c`
with `det C ≡ ±1 (mod c)`, `c ∤ tr C · disc C`, outside the `Φ₃`/`Φ₆` classes — and those classes
are proved to be genuine survivors.

Two route corrections vs the file header (both toward *less* machinery):
* **Statement 3 needs no derivative/Taylor argument.**  The header proposed "`lucasV τ 1 c = τ`
  and the derivative is `≡ 0 (mod c)`".  Two-variable Taylor in `(x, q)` is avoidable: Cayley–
  Hamilton in `lucasU` coordinates gives `C^6 = U₆ • C − (det C · U₅) • 1` with
  `U₆(±1,1) = 0`, `U₅(±1,1) = −1`, so `C^6 ≡ 1 (mod c)`; phase 41's matrix LTE
  (`SmulDvd.pow_prime_pow`) lifts that to `D^6 ≡ 1 (mod c^(n+1))` for `D = C^(c^n)`; hence
  `tr D^7 ≡ tr D`, and `V₇(s,1) − s = s(s²−1)(s²−2)(s²−4) = (s − τ)·W` with `c ∤ W` for `c ≥ 5`.
  Using `tr D^6 ≡ 2` instead would only give `(s − τ)²` — half the exponent.  **`D^7` is the
  trick**: the odd power keeps the factor `(s²−1)` linear in `(s − τ)` after dividing by units.
* **Statement 2 needs no monotonicity.**  `hgrow` (`|tr C^(c^n)| → ∞`) plus phase 33's
  iterated-return chain replaces `lucasV_strictMono`: a prime `p = |t n + h|` whose `c`-part of
  `|GL₂(𝔽_p)|` is `≤ n` returns to the *same absolute value* at infinitely many later indices,
  contradicting `|t n| → ∞`.

New reusable lemmas (all public, in `TraceClassification`):
`lucasU` + `pow_eq_lucasU_smul` (CH in `U`-coordinates), `dvd_lucasU_sub`, `dvd_lucasV_sub'`
(congruence in *both* arguments), `dvd_lucasV_sub_q`, `pow_succ_dvd_pow_sub_pow` /
`pow_pow_dvd_sub` (LTE via `geom_sum₂_mul`, no binomial coefficients — needs no primality
for the one-step version), `lucasV_seven`, `lucasV_one_one_prime` / `lucasV_tau_one_prime`
(period 6), `dvd_two_mul_lucasV_sub_pow_q` / `lucasV_prime_mod_q` (Frobenius `V_c(x,q) ≡ x`
for *every* `q`, generalizing phase 35's `q = −1`), `lucasV_one_growth`
(`|x| ≥ 3 ⟹ |x| + 3 ≤ |V_c(x,1)|`).

Next from the roadmap: §1 **Theorem A** (order `d`, inert primes; Tribonacci at `c = 3`).  The
phase-41 engine is already `d`-generic, so only the certificate is missing; the `d ≥ 3` wall
recorded below is unchanged.

---

## phase 17 (2026-09-29) — CLOSED

`ExponentialsKnown.lean` is sorry-free and axiom-clean.  Both open statements closed:
`fiveExponentials_of_shifted` (via the new `Literature.Baker1966`) and
`strongSixExponentials_of_schanuel` (Roy's strong six exponentials under Schanuel, through the
new `AffineRankOne.const_ratio` derivation argument + `StrongSix.exists_logBasis`).  See
`HANDOFF-2026-09-29-phase17-complete.md`.

---

## Theorem C beyond `d = 2`: the wall, reformulated (2026-09-30)

The filter, the mechanism and the whole steps-3–5 assembly are now `d`-generic in Lean:
`FibonacciCoveringAllPrimes.exists_shift_pow_congr` (any `n × n` matrix, any prime) and
`LucasCoveringAllPrimes.covering_of_good_seq` / `prime_free_of_covering_seq` (any `t : ℕ → ℤ`, the
latter needing only `|t n| → ∞`, no monotonicity).  So for a new family the ONLY missing input is
the certificate — "the `±1` window is visited finitely often".

**Sharper statement of the `d ≥ 3` wall.**  `exists_shift_pow_congr` says `A^(c^n)` is `c`-adically
Cauchy along each class `n mod d'`, so a limit `Λ ∈ M_d(ℤ_c)` exists; and because
`A^(c^(n+d')) = (A^(c^n))^(c^(d'))`, the limit satisfies

> `Λ^(c^(d') − 1) = I`.

So each limit point is a **torsion** element of `GL_d(ℤ_c)` of order coprime to `c` — its
eigenvalues are Teichmüller lifts of `𝔽_(c^d)`-roots of unity.  The certificate needed is exactly:
*no such torsion element in the closure of `⟨A⟩` has `(i,j)` entry equal to `s − h` with `s = ±1`
and `|h| ≤ H`.*  At `d = 2` the exact composition `U((2J+1)N) = Φ_J(U N)` makes this elementary and
avoids the lifts entirely (that is what phases 40/41 exploit); at `d ≥ 3` Saito's free `b_k` blocks
the exact composition, so the lifts appear to be unavoidable.  This is a more precise wall than the
roadmap's original "no exact composition in `d = 3`", and it says what to build: the Teichmüller
lift of `𝔽_(c^d)` inside `ℤ_c`-algebras, i.e. `W(𝔽_(c^d))` and its Frobenius.

Numerics (`scripts/order-d-inert-probe.py`) say the certificate is TRUE for Tribonacci, so this is
a formalization wall, not a mathematical unknown.

## Theorem C leftover: the `c = 5` survivors `h = ±1` — CLOSED 2026-09-30

`fib_five_pow_covering`/`fib_five_pow_prime_free` cover `|h| ≤ H` with `h ≠ ±1`.  `h = ±1` are
genuine filter survivors at `c = 5` (the window condition `F(5^n) + h ≡ ±1 (mod 5^e)` holds
identically because `5^n ∣ F(5^n)`), so no covering prime exists by this mechanism.  They need the
elementary route instead:

  `F(m+n) + (−1)^n F(m−n) = F(m) L(n)`

with `(m,n) = (2k+1, 2k)` giving `F(4k+1) + 1 = F(2k+1) L(2k)`, and `(m,n) = (2k, 2k+1)` giving
`F(4k+1) − 1 = F(2k) L(2k+1)`.  Since `5^n ≡ 1 (mod 4)`, every `5^n` is of the form `4k+1`.  Both
factors exceed `1` for `k ≥ 2`, so `F(5^n) ± 1` is composite for all `n ≥ 1`.  Checked by hand:
`F(5)−1 = 4 = F(2)L(3)`, `F(5)+1 = 6 = F(3)L(2)`, `F(9)−1 = 33 = F(4)L(5)`, `F(9)+1 = 35 = F(5)L(4)`.

**DONE** (`fib_five_pow_pm_one_not_prime`, `fib_five_pow_prime_free_all`,
`fib_prime_pow_prime_free_all`).  The general `F(m+n) + (−1)^n F(m−n) = F(m)L(n)` identity was NOT
needed: the two instances follow from `F(4k+1) = F(2k+1)² + F(2k)²` (`Nat.fib_two_mul_add_one`) plus
Cassini at the even index, since
`F1² + F0² + 1 = 2F1² − F1F0 = F1·L(2k)` and `F1² + F0² − 1 = 2F0² + F0F1 = F0·L(2k+1)` are both
one `linarith` from `F1² − F1F0 − F0² = 1`.  `k ≥ 6` (i.e. `n ≥ 2`) is what makes both factors
exceed `1`; at `k = 1` the factorisation `F(5) − 1 = F(2)·L(3) = 1·4` is trivial.

**Theorem C is now closed for every prime.**  Next targets are roadmap §1 Theorem B (2×2 traces,
odd `c`, `det ≡ ±1`) and Theorem A (order `d`, inert primes); both should reuse
`exists_shift_pow_congr`, `covering_of_good` and `prime_free_of_covering` rather than rebuilding
the convergence or the assembly.

## Phase 41 (next): Theorem C for Fibonacci at every prime `c`

Phase 40 closed Theorem C at `c = 2` (`FibonacciCovering.lean`, sorry-free, axiom-clean,
`4887023`).  The covering machinery is already `c`-generic:
`exists_entry_pow_congr_mul` (general `n × n`, general prime `c`) and
`PmOne.of_prime_factors` (all prime factors `≡ ±1 mod q^e` ⟹ the number is) transfer verbatim.

**Groundwork landed 2026-09-30** in `NumberTheory/Mills/FibonacciCoveringAllPrimes.lean`
(sorry-free, axiom-clean): `PmOneMod` (the `±1` closure modulo an ARBITRARY modulus, generalizing
phase 40's `PmOne e`), `glCard_two_eq`, `padicValNat_glCard_two_self` (`v_c|GL₂(𝔽_c)| = 1`, so the
base prime is good at every `c`), and `pow_dvd_sub_or_add_of_lt_padicValNat_odd` — crux 1 below,
now CLOSED, and indeed easier than `c = 2` as predicted.

**Crux 1 is done.  The real wall is the certificate, and it is sharper than the roadmap says:**
Phase 40's certificate `2^(n+1) ∣ 5F(2^n)²+3` is **single-index**, which is exactly why
`exists_good_prime_factor` comes out as `∀ᶠ n`.  The roadmap proposes replacing it by phase 37's
`Φ_J` fixed-point obstruction (`FibonacciAllPrimes.fibOddPoly_far`: `Φ_J(x) − x ∉ {0, ±2}` for
`x ≠ 0`).  **That obstruction is two-index, and naive two-index comparison is NOT enough** — this
lap's finding, recorded so a later lap does not rediscover it:

> From `c^e ∣ F(c^n) − x` and `c^e ∣ F(c^(n+d)) − x'` one gets `c^e ∣ Φ_J(x) − x'` with
> `2J + 1 = c^d` (odd for every `d`, since `c` is odd).  Concluding `Φ_J(x) = x'` needs
> `c^e > |Φ_J(x)| + |x'|`, and `|Φ_J(x)| ≍ φ^(c^d)`.  So the threshold on `n` for comparing `n`
> and `n + d` grows like `c^d`: two-index comparison shows only that bad indices are
> **exponentially sparse**, never that they are finitely many.  It therefore gives neither
> `∀ᶠ n, ∃ good p` nor a single index good for all `|h| ≤ H` simultaneously (different shifts can
> stay bad at different indices).

Fixing `d = 2` does bound `|Φ_J(x)|` in terms of `c` and `H` alone, and then the argument closes.
So the phase-41 crux is precisely the `c`-adic convergence statement

> **`c^(n+1) ∣ F(c^(n+2)) − F(c^n)` for every odd prime `c`** (any `c^(κn)`, `κ > 0`, suffices).

**CLOSED 2026-09-30** — `exists_shift_fib_prime_pow_congr`: for every prime `c` there is a shift
`d ≥ 1` with `c^n ∣ F(c^(n+d)) − F(c^n)` for all `n ≥ 1`.  The shift `d` (rather than the guessed
`d = 2`) is what makes it elementary, and it costs nothing downstream since `c^d` is still odd and
still bounded by `c` alone.  The general statement is `exists_shift_pow_congr`: for ANY integer
matrix `A` with `c ∤ det A`,
`c^(n−s+1) ∣ (A^(c^(n+d)))ᵢⱼ − (A^(c^n))ᵢⱼ` for `n ≥ s`, with `s ≤ v_c|GLₙ(𝔽_c)|`.
**No lifting machinery is used** — this was the key realisation; the Teichmüller/Witt route is
avoidable:
  1. `A^T ≡ 1 (mod c)` for `T = |GLₙ(𝔽_c)|` (Lagrange);
  2. raising to the `c`-th power gains one factor of `c` — and *without* binomial coefficients:
     `Z^c − 1 = (∑_{i<c} Z^i)(Z − 1)` and `∑_{i<c} Z^i ≡ c·1 ≡ 0 (mod c)`, so the sum contributes
     the extra `c` (`SmulDvd.pow_prime_gain`, `SmulDvd.pow_prime_pow`);
  3. `e ∣ c^d − 1` with `d = φ(e)` and `e` the `c`-free part of `T`, so `T c^(n−s)` divides the
     exponent gap `c^(n+d) − c^n = c^n(c^d − 1)`.
Divisibility of matrices is carried by `SmulDvd a M := ∃ B, M = a • B`, which multiplies on both
sides (`Matrix.smul_mul`/`Matrix.mul_smul`) and is exactly `a ∣ Mᵢⱼ` entrywise.

This is the quantitative form of "Frobenius permutes the Teichmüller lifts of `α, β`, and its
square fixes them".  With it: `c^e ∣ F(c^n) − x` plus `dvd_fibOddPoly_sub` gives
`c^e ∣ Φ_J(x) − F(c^(n+2))`, hence `c^e ∣ Φ_J(x) − x` for `e ≤ n+1`, and `fibOddPoly_far` finishes
(`x ≠ 0` from `FibonacciAllPrimes.not_dvd_fib_prime_pow`).  Base case `n = 0` is
`F(c²) ≡ F(1) (mod c)`, i.e. `F(cM) ≡ (5|c) F(M) (mod c)` twice.  The inductive step is the open
part; note it cannot be a contraction/LTE argument (the multiplier at the fixed point is a unit),
so it wants the `c`-adic lift directly.  `c = 5` stays separate, via `F(4k+1) ± 1`.

## PHASE 15 (2026-09-29) — CLOSED: consequences of Schanuel's conjecture

`NumberTheory/Transcendence/Schanuel.lean` sorry-free, all ten frozen statements axiom-clean.
Details + reusable toolkit + gotchas: `HANDOFF-2026-09-29-phase15-complete.md`.
Unconditional by-products for other threads: `linearIndependent_log_primes` (ℤ and ℚ),
`factorization_prod_primes`, `isAlgebraic_two_rpow_rat`, `irrational_two_rpow_rat`,
`linearIndependent_int_of_nat` (mathlib has no `LinearIndependent ℕ` API),
`eq_zero_of_algebraicIndependent_linear`.

**Next attack (nothing blocked):** more Schanuel consequences are now cheap — `2^√2`, `e^{e^e}`,
`π` together with logs of primes, `e + log 2`, Baker's theorem as the `n`-generator version of
the log-primes argument.  The four-exponentials conjecture IS a Schanuel consequence (Waldschmidt 2000 Ex. 1.8; corrected 2026-09-29, the phase-15 note said otherwise) - phase 16 derives it.

---

## PHASE 13 (2026-09-29) — Corvaja–Zannier from Stephan's Subspace Theorem

`NumberTheory/Transcendence/CorvajaZannier.lean`.  **CZ's Lemma 1 is PROVED** (both the
archimedean and the finite distinguished-place forms), from `Literature.Stephan2026Subspace`
alone.  The chain, all machine-checked:

* `exists_dual_infinite_of_stephan` — Stephan's `Finset` of proper subspaces → *one* nontrivial
  linear form vanishing on an infinite subset.  (Pigeonhole + a nonzero dual killing a proper
  subspace, via the quotient; `Submodule.exists_dual_map_eq_bot_of_lt_top` is unusable here —
  elaborating `⊥ : Submodule K K` blows instance search.)
* `IsSUnit`, `prod_places_eq_one_of_isSUnit`, `mulHeight_eq_prod_S` — the product formula and the
  height, restricted to `S`.  mathlib's `InfinitePlace`/`FinitePlace` normalisation (`v x ^ v.mult`
  at infinite places) is **exactly** Stephan's `approxProd` normalisation, i.e. CZ's absolute
  normalisation raised to `[K:ℚ]`; since the Subspace inequality is homogeneous in that power, no
  exponent bookkeeping is needed.  (This settles the "check the exponent bookkeeping once, early"
  worry in the file header.)
* `approxProd_of_prod_eq` — the algebraic heart: if `∏ᵢ |L_{v,i}(x)|_v = c(v) · ∏ᵢ |xᵢ|_v` at every
  place, then `approxProd = (∏_S c) / H(x)^n`.  Serves CZ Lemma 1 *and* Lemma 3.
* `czForm` / `czFormFamily` / `linearIndependent_czFormFamily` — the forms and their independence
  (only `lam i₀ ≠ 0` is needed).
* `czL` / `czC` / `prod_czL` — the place-indexed family and its deviation factor.
* `finitePlace_val_ne_infinitePlace_val` — a finite and an infinite place are never the same
  absolute value (finite places are nonarchimedean at `1+1`; infinite ones give `2`).
* **`czLemma1_arch`**, **`czLemma1_fin`** — CZ Lemma 1.

**Deliberate restatement.** CZ bound `|Σλσ(u)|_w < max|σᵢ(u)|_w · H(u)^(−ε)`; we bound by
`H(x)^(−ε)` for the *tuple* `x`.  A caller with CZ's hypothesis gets ours at `ε/C` from
`H(x) ≤ H(u)^C`; that comparison is the next small leaf (`mulHeight_tuple_le`).

### Also proved this lap (steps 7–12)

* `hasFiniteMulSupport_iSup`, `mulHeight_le_prod_S_of_sIntegral`, **`approxProd_le_of_prod_le`** —
  the *inequality* interface for `S`-**integral** tuples (CZ's Lemma-3 point `(p, qσᵢ(u))` is not a
  tuple of units): places off `S` contribute `≤ 1`, so `∏_{v∈S}‖x‖_v ≥ H(x)`.
* `exists_smul_infinitePlace`, **`prod_infinitePlace_sub_ratCast`** — CZ's (2.3)–(2.4).  The
  Galois group acts transitively on the infinite places of a Galois `K/ℚ` (all lie over ℚ's unique
  infinite place, and `Subsingleton (InfinitePlace ℚ)` is in mathlib), so `v = σ_v • v₀`; since
  `p` is *rational* and hence Galois-fixed, every archimedean factor is the **same** real number
  `|y − p|_{v₀}`, and `∑_v mult = [K:ℚ]` collapses the product.  This is the whole content of
  (2.4) and it is three lines once the transitivity is available.
* `infinitePlace_ratCast`, `finitePlace_intCast_le_one`, **`prod_S_int_mul_sUnit_le`** — CZ's
  (2.6): `∏_S |q u|_v ≤ |q|^[K:ℚ]` for `u` an `S`-unit and `q ∈ ℤ`.
* `czSubForm` / `czSubFamily` / **`linearIndependent_czSubFamily`** — the Lemma-3 forms
  `x₀ − ρ_v(δ)x_i` indexed by `Option ι`; independence is *unconditional* (unipotent change of
  basis), unlike the Lemma-1 family.
* **`czLemma3_subspace`** — CZ (2.7): an infinite family of nonzero `S`-integral points whose
  Lemma-3 double product is `≤ H(x)^(−ε)` satisfies one fixed nontrivial relation
  `a₀p + Σ aⱼ q σⱼ(u) = 0` infinitely often.

So **every Subspace-Theorem application in Corvaja–Zannier's paper is now discharged** except
Lemma 2 (the unit-equation theorem, which CZ cite to [S, Ch. 4] rather than prove).

### Next attack (in order)
1. **Assemble CZ Lemma 3** from `czLemma3_subspace` + `prod_infinitePlace_sub_ratCast` +
   `prod_S_int_mul_sUnit_le`: feed the numerator hypothesis of `czLemma3_subspace` using
   `‖δqu‖ < q^(−d−ε)H(u)^(−ε)`, then run CZ's **Claim** (eliminate `a₀` by applying `σⱼ`/`τ` and
   subtracting — pure Galois bookkeeping) and land in `czLemma1_arch`.
2. CZ **Lemma 2** (unit equation) — cited by CZ to [S, Ch. 4]; a *separate* Subspace application
   and the one genuinely missing input.  State it as a named leaf; note it also **replaces
   Skolem–Mahler–Lech** in Lemma 4 (two-term relation `aβᵢ^m + bβⱼ^m = 0` at two exponents forces
   `(βᵢ/βⱼ)^(m−m') = 1`), and mathlib has no SML, so routing Lemma 4 through Lemma 2 is strictly
   cheaper than through SML.
3. **Lemma 4** from `czLemma1_fin` + Lemma 2 — the finite-place form of Lemma 1 is exactly what
   CZ use there, and it is already proved.
4. Main Theorem: descent along the finite subfield lattice of `K`.

## PHASE 12 — CLOSED 2026-09-29: `Diophantine/StephanEdges.lean` sorry-free + axiom-clean

All five phase-12 theorems derived from `Literature.Stephan2026Ridout` (Stephan's machine-checked
Ridout, `{β | |ξ−β| ‖β.num‖_{S₁} ‖β.den‖_{S₂} ≤ H(β)^(−2−ε)}` finite); `lake build` green, each
`#print axioms`-clean (`propext`/`Classical.choice`/`Quot.sound`).  `NumberTheory/Diophantine/`
is sorry-free.

* **New `S`-adic bookkeeping** (private, top of the file).  `toPrimes S hS : Finset Nat.Primes`
  packages a `Finset ℕ` of primes, with `prod_toPrimes` transporting products back to `ℕ`.
  `prod_zpow_of_subset`: `∏_{p∈S} p^(−v_p d) = 1/d` when `d.primeFactors ⊆ S`, from
  `Nat.prod_factorization_pow_eq_self` plus `Finset.prod_subset` (terms off the support are `1`).
  Hence `prod_padicNorm_nat` (`S`-unit ⇒ the factor is exactly `1/d`) and
  `prod_padicNorm_int_le` (`d ∣ m` ⇒ the factor is `≤ 1/d`, per prime via
  `padicNorm.dvd_iff_norm_le` at `Nat.ordProj_dvd`).
* **`exists_height_threshold`**: the height comparison both one-dimensional edges need —
  once `r.den > ⌈((|α|+1)^(2+δ/2))^(2/δ)⌉₊`, `r.den^(−2−δ) ≤ H(r)^(−2−δ/2)`, because
  `H(r) ≤ (|α|+1) r.den`.  `roth1955_of_stephan` is then `S₁ = S₂ = ∅`;
  `ridoutSUnitDen_of_stephan` is `S₂ = S`, which contributes exactly `1/q` and turns
  `q^(−1−δ)` into `q^(−2−δ)`.
* **`mahler_mul_of_stephan`** — the real content.  `β = P vⁿ / uⁿ` with `P = round(q αⁿ)`;
  everything is read off the single cross-multiplication `β.num · uⁿ = P vⁿ · β.den`:
  `vⁿ ∣ β.num` (coprime to `uⁿ`), `β.den ∣ uⁿ`, and `β.num ≤ 2q β.den` (from `P ≤ 2q αⁿ`).
  So `‖β‖_{S₁} ≤ v^(−n)`, `‖β‖_{S₂} = 1/β.den`, `H(β) ≤ 2q β.den`, and the product is
  `≤ e^(−εn)/(uⁿ β.den)`.  With `ε' = ε/(2 log u)` the target reduces to
  `e^(−εn) (2q)^(2+ε') β.den^(1+ε') ≤ uⁿ`, and `β.den ≤ uⁿ` gives
  `β.den^(ε') ≤ e^(nε/2)`, leaving the constant condition `(2q)^(2+ε') ≤ e^(nε/2)`.
* **No injectivity needed.**  Unlike `mahler_mul_of_ridout1957` (which injects `n ↦ uⁿ`), reducing
  `β` to lowest terms destroys the `n`-marker.  Instead: a *finite* set of rationals all `≠ q`
  keeps a positive distance `m` from `q` (`Finset.min'` over the image of the `erase`), while
  `|q − β| ≤ (v/u)ⁿ → 0`.  That is strictly cleaner than the Ridout-1957 route.
* **Gotchas.**  `(max a b : ℝ)` with `a b : ℕ` elaborates as `max ↑a ↑b`, not `↑(max a b)` — no
  `Nat.cast_max` needed (and it will *fail*).  `div_le_div_iff` is now `div_le_div_iff₀`.
  `Nat.ord_proj_dvd` → `Nat.ordProj_dvd`; `Nat.pos_pow_of_pos` → `pow_pos`.
  `set` for `A`/`P`/`N`/`U`/`β` blew the `isDefEq` heartbeat budget (the known let-valued-locals
  trap) — all five are `obtain ⟨x, hx⟩ : ∃ y, y = e := ⟨_, rfl⟩` instead, plus
  `set_option maxHeartbeats 1000000` on the one big theorem.
* `Mills.irrational_of_stephan = irrational hB hM (mahler1957_of_stephan hS)`.

Remaining open in the repo: only phase 9's two DISCLOSED Corvaja–Zannier leaves in
`Transcendence/DubickasNoSubspace.lean`.

---

## PHASE 11 — CLOSED 2026-09-29: `PolyIteration/Siblings.lean` sorry-free + axiom-clean

All 25 phase-11 obligations discharged; `lake build` green, every headline `#print axioms`-clean
(`propext`/`Classical.choice`/`Quot.sound` only — no `sorryAx`, no `native_decide`).

* **Bala's general divisibilities** rest on one new workhorse, `sub_dvd_sub_addMul`:
  `u n − u k ∣ u (B + d·n) − u (B + d·k)` for every base `B` and multiplier `d`, by induction on `d`
  splitting `u(B+dn+n) − u(B+dk+k)` into a `sub_dvd_sub_shift` of the IH plus a
  `sub_dvd_sub_shift` of `u n − u k` itself.  `sub_dvd_sub_lin` is then `r = s + d` /
  `s = r + d` case-split (the `r < s` branch is `.neg_right` of the other); `sub_dvd_sub_mul` is
  `B = 0`; `sub_dvd_det` is the two-term telescope
  `u(sk)(u(rn)−u(rk)) − u(rk)(u(sn)−u(sk))`.
* **Sylvester A000058.** `a n ≥ n + 2` (hence `≥ 2`) is the workhorse for the field_simp'd
  Egyptian-fraction induction.  `HasSum … 1` avoids any comparison test: nonneg terms +
  `summable_of_sum_range_le` with `c = 1` from the closed form, then
  `tendsto_nhds_unique … .tendsto_sum_nat` against `1 − 1/(a n − 1) → 1`
  (`squeeze_zero` vs `1/(n+1)`).
* **No squares**: `a 0 % 4 = 2`, `a n % 4 = 3` for `n ≥ 1`, killed by `∀ x : ZMod 4, x*x ≠ 2 ∧ ≠ 3`
  via `decide`.  **`−3` a QR**: `4·a(n+1) = (2 a n − 1)² + 3`, so `(2 a n − 1)²  = −3` in `ZMod p`;
  the `n = 0` leaf is `p = 2` and `IsSquare (-3 : ZMod 2)` — note `decide` on the *substituted*
  goal trips "expected type must not contain free variables", so that fact lives in its own
  private lemma `neg_three_isSquare_two`.
* **The residue cycles** are `Int.ModEq` inductions through one step lemma
  (`x ≡ y → x²−x+1 ≡ y²−y+1`).  mod 1000 is derived from mod 3000 by
  `Int.emod_emod_of_dvd`.  mod 864 needs the genuinely non-trivial step
  `864 ∣ 432·n·(1+3n)`, discharged by `n` even / odd (one of `n`, `1+3n` is even) — this is why the
  progression has exactly 24 terms.
* **Mohanty**: `IsCoprime m (b n)` for all `n` (via `IsCoprime.add_mul_left_right`, since
  `b(n+1) = b n² + m(1 − b n)`), plus `b i ∣ b j − m` for `i < j`; then `intGcd_congr_of_dvd_sub`
  transports `gcd(b i, b j) = gcd(b i, m) = 1`.  `0 < m` is not needed.
* **A003096 non-primality**: `a(m+2) = (a(m+1)−1)(a(m+1)+1)` with `a(m+1) ≥ 3`, refuted through
  `Prime.irreducible.isUnit_or_isUnit` + `Int.isUnit_iff` + `omega`.
* **A002065 / A004019** are direct Sylvester/Bala instances (`X²+X+1`, `(X+1)²`);
  `a004019 n = a003095 n ²` and `= a003095 (n+1) − 1` are one-line inductions.

**Stop condition met**: `NumberTheory/PolyIteration/` is sorry-free.  Phase 9's two disclosed
Corvaja–Zannier `sorry`s in `NumberTheory/Transcendence/DubickasNoSubspace.lean` remain, untouched.

---

# PENDING_WORK — lean-formalizations

## PHASE 10 — CLOSED 2026-09-28: `NumberTheory/PolyIteration/` sorry-free + axiom-clean

`Sylvester.lean` (3 theorems) and `A003095.lean` (16 theorems) are fully proved; `#print axioms`
shows only `propext, Classical.choice, Quot.sound` on every one.

One faithfulness correction, recorded here and in the `A003095.lean` header: **`a003095_sq_dvd`
as frozen was false.**  `a(n)^2 ∣ a(n+m) − a(m)` fails at `m = 0` (it reads `a(n)^2 ∣ a(n)`;
`n = 2` gives `4 ∤ 2`).  Added `1 ≤ m`, the same hypothesis Bala's product identity carries.
Nothing else needed adjusting — every other threshold (`k−1`, `3k−5`, `2k−1`, `⌊k/2⌋`) is sharp
enough to prove as stated.

Reusable: `sub_dvd_sub_shift` (iteration preserves index-shifted differences),
`intGcd_congr_of_dvd_sub`, `a003095_mod_two`, `a003095_mod_five`, and the two Harden towers
`a003095_two_pow_dvd` / `a003095_five_pow_dvd`.

## 🎯 PHASE 9 — ATTACK PATH SET BY THE REVIEW LAP (2026-09-28, lap #8)

`DIRECTION.md` → CURRENT DIRECTIVE is binding.  Summary: **Lemma 3 stays a disclosed leaf** (it is
the `p`-adic Subspace Theorem; the review lap re-confirmed independently that the one-dimensional
route is vacuous — `∏_σ(σ(α)^N − k_N)` is a linear form in the `d` monomials `σ(α)^N`, and the
archimedean Liouville bound only re-derives `M(α) ≥ α`).  The objective is now **three leaves → one**.

**The new handle the earlier laps were missing: an UPPER bound on `den(U_N)`.**
`D α` is an algebraic integer for some positive integer `D` (`D ∣ a₀`), hence
`D^N · U_N = Tr((Dα)^N) ∈ ℤ`, i.e. `den(U_N) ∣ D^N`.  The sixth lap only had the *lower* bound
(`den ≍ D_v^N` in the unique-max case).  Pairing the upper bound with the already-proved
`tracePowSum_near_int` (for **all** large `n`, `2 U_(2^n)` is within `C r^(2^n)` of an integer,
`r = max(α⁻¹, ρ) < 1`) and `one_div_den_le_dist_int` gives

> **Cofiniteness dichotomy.**  For all large `n`, either `2 U_(2^n) ∈ ℤ`, or `(D r)^(2^n) ≥ 1/(2C)`.
> Hence **if `D · max(α⁻¹, ρ) < 1` then `2 U_(2^n) ∈ ℤ` for every large `n`** — the exact-integrality
> exponent set is COFINITE, which is precisely what the seventh lap identified as the missing input.

With a cofinite exponent set: (i) the Newton/Graeffe collapse applies at every tie size (item 1
below), so the local leaf closes; (ii) the degenerate descent iterates, because `{N | l N ∈ S}` is
cofinite too.  So **the whole sparsity obstruction upgrades to the single inequality
`D ≥ min(α, ρ⁻¹)`** — an assertion about the Mahler measure of a growth constant, which is a named,
attackable statement rather than "the index set might be a tower".

**Ordered work items — items 1-3 LANDED 2026-09-28 (lap 8); see the PROBE's eighth-lap sections**

✅ 1-3 done: `valuation_sum_unit_pow_mulClosed` (general-`k` Newton collapse, no nondegeneracy),
`false_of_bounded_den_tie_le` (closure only up to the TIE SIZE `K`; `K = 2` ⇒ mere doubling),
`isIntegral_of_bounded_den_mulClosed` (Lemma 4 with **no** `α^l ∈ ℚ` branch),
`exists_common_integral_multiple` + `exists_tracePowSum_den_dvd` (`den(U_N) ∣ D^N`),
`tracePowSum_int_of_near_int_of_den_lt` (the cofiniteness dichotomy), and the capstone
`isIntegral_of_tie_le_two_of_den_lt`.  `src/` went 3 disclosed `sorry`s → 2.

**Lap 9 (2026-09-30) — the doubling-closure frontier is now SHARP.**  Three new axiom-clean
theorems in `DubickasNoSubspace.lean`:

* `valuation_factorial_mul_esymm_le_of_closed` — the **refined Newton step**.  Only *some* power
  sums need to be small.  With `D = {j | v(p_j) ≤ ε}` and any `G` closed under
  `j ∈ G → j ∈ D ∧ ∀ 1 ≤ i < j, (i ∈ G ∨ j − i ∈ D)`, every `j ∈ G` has `v(j! e_j) ≤ ε`.
  (`valuation_factorial_mul_esymm_le` is the case `D = G = [1,k]`.)  This is the general machine
  for *sparse* exponent sets; it turns "which tie sizes does closure under `⋅2` kill?" into a
  finite combinatorial reachability question with `D = {1,2,4,…,2^s}`.
* `valuation_sum_unit_pow_card_four` — **tie size 4 closes from doubling alone.**  At `j = 4` the
  unavailable `p_3` is multiplied by `e_1 = p_1`, which is small; run `G = D = {1,2,4}`.
* `valuation_sum_unit_pow_of_common_pow` — if all `u ∈ U` share an `M`-th power and `M ∣ N` for
  `N ∈ S`, then `Σ u_i^N = |U| · w^(N/M)` has the fixed nonzero valuation `v(|U|)`: no decay.
  This is the **second half of attack (b)**: once the tie ratios are known to be `2^t`-th roots of
  unity, the tie closes immediately (no Graeffe tower needed).  Attack (b) is therefore reduced to
  its first half only: *are the p-adic tie ratios 2-power roots of unity?*

⚠ **REFUTED this lap**: the lap-8 hope "*if the tie size is a power of `2` the Graeffe tower closes
it*".  Running the reachability criterion with `D = {1,2,4,8}` at `k = 8`: `1, 2, 4 ∈ G` but
`3 ∉ G` (`3 ∉ D`) and then `j = 8` fails at `i = 3`, since `8 − 3 = 5 ∉ D` and `3 ∉ G`.  Equivalently
`p_3` multiplies `e_5` and `p_5` multiplies `e_3`, and neither `e_3` nor `e_5` is controlled by
`p_1, p_2, p_4`.  So the doubling-closed tie sizes that provably close are exactly `1, 2, 4`
(`k = 3` is *realized* by `u_i = ζ₃^i c`; `k = 5, 6, 7, 8` are open, and `6 = 2·3` is realized by
two `ζ₃`-triples).  **Any route through "the tie size is small" must therefore bound the tie size
by 4 — not by a power of 2.**

**Lap 9b — the local leaf is now COMPLETELY RESOLVED, and it is sharp.**  Kernel-checked
counterexample family: `sum_root_of_unity_pow_eq_zero` / `sum_root_of_unity_two_pow_eq_zero` /
`sum_cube_root_two_pow_eq_zero`.  For any `m > 1` that is **not a power of `2`**, `m ∤ 2^n` for every
`n`, so a full scaled set of `m`-th roots of unity (all of them `v`-units) has
`Σ_i u_i^(2^n) = 0` — valuation `0`, hence `≤ B r^(2^n)` vacuously.  Counterexamples are additive
over disjoint blocks (use distinct scalings), so the *realizable* tie sizes are exactly the sums of
parts that are not powers of `2`:

> `k` closes under doubling closure alone **iff `k ∈ {1, 2, 4}`**.
> `3` = a `ζ₃`-triple; `5` = `ζ₅`; `6` = two `ζ₃`-triples; `7` = `ζ₇`; **`8` = `ζ₃`-triple ⊎
> `ζ₅`-quintuple**; every `k ≥ 3` except `4` is a sum of non-powers-of-`2`.

`{1, 2, 4}` is exactly what `valuation_sum_unit_pow_mulClosed` (`k=1`),
`valuation_sum_unit_pow_card_two` and `valuation_sum_unit_pow_card_four` now prove.  **The
Newton/Graeffe direction is therefore exhausted — no cleverer symmetric-function identity can
help.**  Any further progress on Lemma 4's tie case must come from one of:

1. **Bound the tie size by `≤ 4`** at the offending prime (a Newton-polygon statement about
   `minpoly ℚ α` over `ℚ_p`), or
2. **Enlarge the exponent set** past `{2^n}` — e.g. get `3 · 2^n` into `S`.  Handle:
   `U_(3M) = e_1 U_(2M) − e_2 U_M + 3 e_3({w^M})` and `den(e_i({w^M})) ∣ D^(iM)`, so this needs a
   *joint* denominator bound, not just `den(U_M)`; or
3. **Show the tie ratios are `2`-power roots of unity** — then
   `valuation_sum_unit_pow_of_common_pow` closes it outright with no Newton at all (this is what
   makes route 3 attractive: the counterexamples above all need an ODD-order root of unity, and
   `norm_eq_of_pow_eq` already forces the *archimedean*-dominant conjugates to differ by `2`-power
   roots of unity).  **Route 3 is the recommended next attack**: the open half is purely
   "can a `p`-adic tie involve conjugates that are not archimedean-dominant?".

⚠ New hard fact (the `ζ₃` witness, PROBE eighth lap part 2): doubling closure canNOT be pushed past
tie size 2 — `u_i = ζ₃^i c` has `Σ u_i^(2^n) = 0` for every `n`.  So the residual is now exactly:
(a) `D ≥ min(α, ρ⁻¹)`, or (b) a triple tie at some prime, or (c) the sparsity of CZ Lemma 3's index
set.  **Next attack: (b).** A triple tie gives two conjugates with `w^3 = w'^3` at a *p-adic* place;
the archimedean-dominant conjugates are known to differ by `2`-power roots of unity
(`norm_eq_of_pow_eq`), so the question is whether a p-adic tie can involve conjugates that are not
archimedean-dominant — if not, all tie ratios are `2`-power roots of unity, the tie size is a power
of `2`, and the Graeffe tower closes it.  That is a concrete, local, checkable question.

**Superseded items (kept for the record)**
1. `valuation_sum_unit_pow_mulClosed` — general-`k` Newton collapse.  For `v`-units `u_1..u_k` and an
   exponent set closed under multiplication by `1..k`: set `x_i = u_i^N`; `multiset_mul_esymm_eq_sum`
   (in `MultisetNewton.lean`) gives `j e_j = (−1)^(j+1) Σ_{i<j} (−1)^i e_i p_(j−i)`; since
   `i! ∣ (j−1)!` one gets `v(j! e_j) ≤ max_{1 ≤ l ≤ k} v(p_l)` by induction (using `v(e_i) ≤ 1`, all
   terms being sums of products of units), and `e_k = ∏ u_i` is a unit, so
   `v(k!) = v(k! e_k) ≤ max_l v(p_l) → 0` — contradiction.  **No nondegeneracy hypothesis.**
   Generalizes `valuation_sum_unit_pow_card_two`; also covers `k = 1`.
2. `tracePowSum_den_dvd` — `∃ D > 0, ∀ N, (D^N * U_N).den = 1`, from `IsIntegral ℤ (D • α)`.
3. `tracePowSum_exact_int_of_lt` — the cofiniteness dichotomy above.
4. Re-route `corvajaZannier_lemma4` / `isIntegral_of_bounded_den_of_nondegenerate` through 1–3, and
   do the degenerate descent on the now-cofinite set.  What is left over is the recorded inequality
   `D ≥ min(α, ρ⁻¹)`.

## 🔭 PHASE 9 IN PROGRESS (2026-09-28) — `Dubickas2022` (Lemma 6) narrowed to the CZ dichotomy
The open `sorry`s in `src/` are deliberate and are the active crux, both in
`NumberTheory/Transcendence/DubickasNoSubspace.lean`:

* `corvajaZannier_dichotomy` — CZ 2004 main theorem, p. 177 (= Dubickas's Lemma 3).  **The wall**:
  the only `p`-adic-Subspace-Theorem step in the whole repo's Dubickas thread.
* `corvajaZannier_lemma4` — CZ 2004, Lemma 4.  **Not** subspace-strength: a valuation/trace
  argument in `ℚ(α)`; mathlib has `IsDedekindDomain.HeightOneSpectrum` + the number-field trace.
  **Attack this one next.**  The `d = 2` Newton-polygon analysis is written out in
  `PROBE-DUBICKAS-NOSUBSPACE.md`; its `hsmall` hypothesis (every conjugate inside the unit disc or
  of modulus `α`) is already proved at the call site, so a future proof may assume it.
  `ON-LINE-REQUEST.md` (2026-09-28) asks for CZ's own statements/proof before anything lands in
  `Literature/`.  Prerequisites for it that are now **proved** in the same file: `tracePowSum`
  (`= Tr_{ℚ(α)/ℚ}(α^N)`, the power sum over all conjugates), `tracePowSum_rat` (it is rational),
  `tracePowSum_recurrence` (`Σ_{k ≤ d} p_k U_(N+k) = 0` — the linear recurrence the valuation
  argument runs on) and `isIntegral_int_iff_minpoly_den` (the integrality bridge: `α` is an
  algebraic integer iff the coefficients of `minpoly ℚ α` have denominator 1 — the shape in which
  Lemma 4's conclusion arrives).  And the **non-archimedean core of the no-tie case is now proved**:
  `no_bounded_den_of_unique_max_valuation` — in any number field `L`, if one conjugate `z`
  strictly dominates the others at a prime `v` and `v z > 1`, then `q(z^N + Σ_w w^N)` cannot be a
  rational integer for infinitely many `N` (ultrametric equality ⇒ `v = v q · (v z)^N`, unbounded,
  while integers have valuation `≤ 1`); supporting `exists_one_lt_mul_pow`,
  `valuation_multiset_sum_lt`.  **(a) The bridge is now BUILT** (2026-09-28, fourth lap): `conjField α`
  (`adjoin ℚ ((minpoly ℚ α).rootSet ℂ)`) is a `NumberField` by *global* instances, `conjMultiset α`
  is the conjugate multiset there (via `Multiset.pmap` — no `Splits`/`aroots_map` needed),
  `conjMultiset_pow_sum_coe` pushes its power sums down to `tracePowSum`,
  `exists_valuation_one_lt` is the contrapositive of
  `HeightOneSpectrum.mem_integers_of_valuation_le_one`, and **`exists_tie_of_bounded_den`** (proved,
  axiom-clean) concludes: *if `q U_N ∈ ℤ` for infinitely many `N` and `α` is not an algebraic
  integer, then at some prime `v` two **distinct** conjugates share the maximal valuation, which
  is `> 1`.*  **(b) The tie case is therefore the entire residual, and it is now purely local**:
  with the dominant conjugates written `z u_i` (`u_i` a `v`-unit), the hypothesis forces
  `v(Σ_i u_i^N) → 0` along the infinite index set, and one must produce a root-of-unity ratio
  `u_i/u_j` (`p`-adic Skolem–Mahler–Lech).  **That reduction is now DONE too** (`false_of_bounded_den_of_nondegenerate`,
  `isIntegral_of_bounded_den_of_nondegenerate`): Lemma 4's first branch is proved whenever no two
  distinct conjugates of `α` share a power, modulo the **one** local leaf
  `valuation_sum_unit_pow_nondegenerate` (units `u_i`, `k ≥ 2`, no `u_i^l = u_j^l` ⇒ `v(Σ u_i^N)`
  cannot decay geometrically along an infinite exponent set).  **Next attack, ranked:**
  (1) the leaf — classical route is Strassmann's theorem on `ℤ_p` (mathlib has **no** Strassmann /
  `p`-adic Weierstrass preparation: that is the concrete prerequisite to build; for `N = 2^n` the
  tower-growth contradiction is easy once Strassmann is available);
  (1b) ⚠ **and Strassmann alone is NOT enough**: it forces the index set to grow like a tower, which
  an arbitrary infinite subset of `{2^n}` may do.  The fix now in `src/` is to make the index set
  *cofinite* at the price of near-integrality: `tracePowSum_near_int` / `tracePowSum_den_grows`
  (proved, axiom-clean) say that once one pseudo-Pisot exponent exists, `2 U_(2^n)` is within
  `C₂ r^(2^n)` (`r = max(α⁻¹, ρ) < 1`) of an integer for **all** large `n`, hence for every large `n`
  either `2 U_(2^n) ∈ ℤ` or its denominator is `≳ α^(2^n)`.  With the unique-dominant-valuation case
  this forces the local dominant valuation `D_v ≥ α` — the first constraint in this thread that bites
  on `α` itself (see the sixth-lap section of the PROBE);
  (1c) ✅ **the double tie now CLOSES elementarily** (seventh lap): the Graeffe identity
  `2(u₁u₂)^N = (u₁^N+u₂^N)² − (u₁^(2N)+u₂^(2N))` has valuation exactly `v 2` on the left, so
  `valuation_two_le_of_two_unit_pow_sums` / `false_of_two_unit_pow_sums_small` /
  `valuation_sum_unit_pow_card_two` prove the leaf for `card U = 2` (no nondegeneracy needed), and
  Newton's identities extend it to any tie size `k` once the exponent set is closed under
  multiplication by `1..k`.  **The residual is therefore SPARSITY of the pseudo-Pisot index set `S`,
  not `p`-adic analysis.**  Ranked next attack: make `S` cofinite (it comes out of CZ's Lemma 3 —
  see the seventh-lap section of the PROBE), which would make Lemma 4 elementary outright;
  (2) the **degenerate** branch, which is the other genuine gap — `w^l = w'^l` for distinct
  conjugates gives only `deg(α^l) < deg α` (a descent), and the descent cannot be iterated because
  the exponent set becomes `{N | l N ∈ S}`; CZ's own argument for their `α^l ∈ ℚ` branch is what
  `ON-LINE-REQUEST.md` asks for.

`exists_pisot_pow_pseudoPisot_core` is *proved* from exactly those two: Dubickas's Lemma 5 (both
branches), the `deg α^N ≤ deg α` bound and the "trace eventually nonzero" step are all formalized
(`isPisot_of_pseudoPisotMul`, `otherConj_eq_zero_of_pow_rat`, `eq_rat_of_otherConj_eq_zero`,
`card_otherConj_pow_le`).

**Advance this lap.**  Lemma 6 = Dubickas's Lemma 3 (Corvaja–Zannier's main theorem, subspace) ∨
Lemma 5 (elementary, given CZ's Lemma 4).  The *whole* rational-power case is now unconditional
from `Ridout1957`: new `Diophantine.mahler_mul_of_ridout1957` (Mahler 1957 II **with a positive
integer multiplier**, needed because our approximants are half-integers), then
`exists_pisot_pow_of_rat` / `exists_pisot_pow_of_pow_rat`.  So the residual core may assume
`α^(2^a) ∉ ℚ` for every `a`.

**Refuted this lap** (do not retry): the archimedean Liouville/norm route (it only re-derives
`M(α) ≥ α`, vacuous), and the Böttcher/Mahler-method route (`Φ_c` is not of Mahler-method shape).
Even *degree 1* is Mahler's `‖q(3/2)ⁿ‖` problem, which is why `Ridout1957` was needed there.

**Next attack:** state `CorvajaZannier2004` (pseudo-Pisot dichotomy, their p. 177) — proposal
written out in `PROBE-DUBICKAS-NOSUBSPACE.md`, *not* yet in `Literature/` per DIRECTION — and
split the core into that `Prop` + CZ Lemma 4 + Dubickas Lemma 5.  `hD` stays on the
`Dubickas.lean` headlines until the core is closed; never route a headline through the `sorry`.

## 🏁 THE FRONTIER IS OTHERWISE HYPOTHESES, NOT SORRIES (2026-09-28)
Apart from the phase-9 crux above, `src/` has **no `sorry`, no `admit`, no declared `axiom`**, and every headline is
`[propext, Classical.choice, Quot.sound]`.  So there is no leaf work left: the only fidelity debt
is the *literature hypotheses* carried by the conditional headlines.  Ranked (see
`DIRECTION.md` → CURRENT DIRECTIVE for the binding order):

| hypothesis | carried by | bucket | next prerequisite |
|---|---|---|---|
| `Dubickas2022` (his Lemma 6) | `Transcendence.Dubickas.{transcendental_growth_of_monic_quadratic,theorem1,oeis_constants}` | 🟠 generational | Corvaja–Zannier 2004 ⇒ `p`-adic Subspace Theorem (Schlickewei). mathlib has **nothing**. Chip a prerequisite: heights / places of a number field, or a Roth-shaped statement in the `Literature/Diophantine` idiom. |
| `BakerHarmanPintz2001`, `Matomaki2007` | `Mills.{transcendental_of_four_le,transcendental_or_pisot,irrational_of_ridout}` | 🟡 project-scale | primes in short intervals `[x, x+x^0.525]`; needs a sieve/zero-density layer mathlib lacks. |
| `PrimeBetweenCubesFrom` (Ingham) | `Mills.exists_least_of_primeBetweenCubes` | 🟡 project-scale | `θ(x+x^c)−θ(x) > 0` for `c > 5/8`; the PNTAnd dep is the natural home. |
| `Dubickas2022PisotGap` (his Lemma 8) | **nothing on the headline path any more** — only the paper-faithful `DubickasPisot.c_eq_zero_or_two`, kept for the audit trail | — | DISCHARGED-BY-BYPASS 2026-09-28: `c_eq_zero_or_two_noGap` gets the same conclusion without it. |
| `Ridout1957`, `Ridout1958` | `Diophantine.{mahler_of_ridout1957,ridoutSUnitDen_of_ridout1957,roth_of_ridout1958}` | 🟡 project-scale | same Subspace-Theorem family as Lemma 6; the *edges* off them are already proved (phase 5). |

Non-hypothesis frontiers still registered: **Saito Remark 4.4** (degree-3 Pisot, `Mills/`),
**Catalan phase 2** (probe-first, never claim `G ∉ ℚ`), **no-three-in-line all-`N` `(3/2−ε)N`**
(needs a prime in `[(1−ε)N/2, N/2]`), **Goodstein B4 at limit levels**.

## ✅ Dubickas 2022 phase 8 COMPLETE (2026-09-28) — Lemma 8 dropped, degree-uniform
`c_eq_zero_or_two_noGap` is proved from `Dubickas2022` alone for **every** degree, so
`hG : Dubickas2022PisotGap` is gone from all three `Dubickas.lean` headlines and from
`Comparator/Dubickas/Challenge.lean` (`scripts/comparator-probe Dubickas` → identical).
Route + file map: `PROBE-DUBICKAS-NOGAP.md`.  The decisive reframing: the exact recursion identity
`c = 2 βᴺ S_N + S_N² − S_(2N)` *is* the statement that `E₂(βᴺ's conjugates) = c/2` is **constant**
along the Graeffe tower, and eventual constancy of `E₂` alone forces `c/2 ∈ {0,1}` (via the
parity-weight induction + the `b`-recursion with finite support).  Lemma 8 was only ever supplying a
*lower* bound on `|S_N|`; nothing in the new route wants one.  Nothing to reopen.

## ✅ Dubickas 2022 phase 7 COMPLETE (2026-09-27) — `NumberTheory/Transcendence/` sorry-free, axiom-clean
`transcendental_growth_of_monic_quadratic`, `theorem1`, `oeis_constants` all
`[propext, Classical.choice, Quot.sound]`.  See `HANDOFF-2026-09-27-dubickas-phase7-complete.md`.
Nothing to reopen.  The crux that made it tractable: for `d = 2, a₀ = 1` the recursion is EXACT
(`y_{n+1} = y_n² − c`), so Lemmas 7/10 are unnecessary and (17)/(18) reduce to `c ∈ {0, 2}`; the
degree collapse is `Mills.pisot_degree_bound` at `μ = 1`.

## 🔢 Catalan salvage (branch `catalan`, 2026-09-04) — Phase 3 GREEN (all of Catalan/ sorry-free)
- **Done (lap 2, 2026-09-04):** `Frame.lean` 14/14 leaves, axiom-clean; sink edge
  `catalan_irrational_of_smallForms` kernel-checked.  E1/E2 statements corrected (`S ≤ B` added;
  frozen form refuted by exact probe at `B=0, S=7`).  See `HANDOFF-2026-09-04-catalan-phase3-green.md`.
- **Open (not a Lean question):** `SmallForms` is a `Prop`, numerically false for Sun's weights.
  A corrected construction would replace `resid`/`oddLcm` and re-run the ledger probe.

### (older) Phase 1 GREEN
- **Done:** Theorem 2.1 (`residual_rank`) and the 2-adic no-go (`sun_ledger_impossible`), all
  axiom-clean; see `HANDOFF-2026-09-04-catalan-phase1-green.md`.
- **Open (Phase 2, probe-first, no Lean discharges):** the frontier question — weakest open node on
  a path from A to the sink `Irrational catalanConst`.  N1 (`F_B`-free `N'_B` via binomial reference
  columns): extend `papers/sun-2026-catalan-twoadic-check.py` to report the real-place growth of
  `N'_B` in `B`; N2 (even normaliser): extend the probe first.  A node whose probe says the integer
  grows with `B` is refuted — record that, build no road.
- **⚠️ Nothing in the repo claims Catalan's constant is irrational.**


## 🎉 lap 14 — DONE: HJSW `3(p−1)` no-three-in-line COMPLETE & axiom-clean (`three_mul_pred_le_maxNoThreeInLine`)

The per-prime HJSW headline is **fully machine-checked** (commit `cd5a8ce`, trust base only). Found and
fixed the false lap-13 construction (below), built the genuine half-band pinwheel, and proved the
cross-class slope-`±1` diagonal crux (`pinwheel_diagonal_false`) across all 4 families. ITEM 1 below is
**CLOSED**. **Next frontier = the all-`N` `(3/2−ε)N` corollary** (needs PNT-grade primes near `N/2`;
Bertrand alone gives only ratio `3/4`). See STATUS.md → Short-term. Also minor: `p=2` witness to drop
the `Odd p` hypothesis.

## 🚨 lap 14 (HISTORY) — the lap-13 `pinwheel` construction was FALSE; rewrote to the real HJSW half-band form

**Brute-force discovery (2026-06-19 lap 14):** the lap-13 `Pinwheel.lean` construction — single
hyperbola, four `{0,p}²` translates per residue class, drop ONE corner (keep 3) — is **NOT
no-three-in-line for ANY drop rule**. Verified exhaustively (`/tmp/brute.py`): INFEASIBLE for `p=7`
(all `k`), `p=5` (`k∈{2,3}`). Root cause: the symmetric `{0,p}²` corner layout couples each class to a
`+1`-line partner AND a `−1`-line partner simultaneously, forcing it to break BOTH its `+1` and `−1`
diagonal with a single drop — impossible. So **`pinwheel_exists_noThree` as lap-13 stated it is FALSE**
(a `sorry` on a false statement is a landmine — it could be "closed" by any soundness slip).

**The fix = the genuine HJSW construction with the half-band shift.** The x-translate DIRECTION depends
on the half-band: a left-half class (`a ≤ h=(p−1)/2`) uses columns `{a, a+p}`, a right-half class uses
`{a−p, a}` — then a global `+h` shift lands everything in `[0,2p)`. The dropped corner is in the OUTER
column, opposite `b`'s band. Verified no-three + `card=3(p−1)` + grid `⊂[0,2p)²` for all primes `p≤17`,
all `k` (`/tmp/hjsw.py`). The reflection/general lemmas in `HyperbolaLine.lean` are UNAFFECTED (pure
ZMod p) and are reused verbatim. The no-three proof: slopes 0/∞ safe (residue-uniqueness); slope ±1 via
the σ-reflection — the partner class's three points sit on lines offset by exactly `±p` from the
diagonal, so none lands on it. THIS is the real, now-TRUE crux. See `Pinwheel.lean` rewrite (lap 14).

## 🧭 lap 13 — NO-THREE-IN-LINE: HJSW `3(p−1)` covering UNBLOCKED + scaffolded; crux narrowed to slope-±1 incidence (⚠️ construction was FALSE — see lap-14 note above)

**Findings harvested** (`archive/findings/ON-LINE-FINDINGS-2026-06-19-hjsw-3n2-construction.md`): the
real HJSW construction is a **12-of-16-block "pinwheel"** carved from a single hyperbola `H(k,p)` over
`2p×2p`, NOT stacked arcs. Grid side `N=2p`, `|N_set|=3(p−1)`. Crux is a slope-only argument.

**Done + committed this lap (build 🟢 8299 jobs, all axiom-clean — ONE disclosed crux `sorry`):**
- `HyperbolaLine.lean` (NEW) — **`hyperbola_line_two_congruent`** (the general HJSW Lemma: any
  collinear triple of the full hyperbola `xy≡k` has two CONGRUENT points; determinant collapse ported
  to arbitrary lattice points) + residue/x-residue forms. Plus **both reflection lemmas (HJSW Thm 2
  Step 2)**: `hyperbola_slope_one_reflection` (slope +1 ⇒ the two classes are anti-diagonal reflections
  `r'=−s, s'=−r`, `r·r'=−k`) and `hyperbola_slope_neg_one_reflection` (slope −1 ⇒ main-diagonal
  reflection `r'=s, s'=r`, `r·r'=k`). Pure ZMod p Vieta.
- `Pinwheel.lean` (NEW) — the construction, drop-rule-parametrized (`drop : ℕ → Fin 4` = which of the
  4 corners of each residue class to discard). **`pinwheel_card = 3(p−1)`** and **`pinwheel_grid ⊆
  [0,2p)²`** proved for ANY drop (mechanical, axiom-clean). **`pinCorner_not_collinear`** (3 distinct
  corners of one class are never collinear, `det3=±p²`) discharges the same-class no-three subcase.
  Headline `three_mul_pred_le_maxNoThreeInLine : 3(p−1) ≤ maxNoThreeInLine(2p)` STATED, reduced to the
  one crux below.

### ✅ CLOSED ITEM 1 — the no-three crux. DONE lap 14 (`pinwheel_noThree`, axiom-clean). Text below is HISTORY.
### OPEN ITEM 1 (HISTORY) — `pinwheel_exists_noThree` (the branch HEADLINE crux). STATUS: narrowed, unblocked.
The lone disclosed `sorry`: ∃ a drop-rule making the pinwheel no-three-collinear. **KEY STRUCTURE
(documented in `Pinwheel.lean`):** slopes 0/∞ are AUTOMATICALLY safe (each row/column residue belongs
to a unique class ⇒ ≤2 points), and the general Lemma reduces any collinear triple to "two congruent
(same class) + a third". The same-class subcase is killed by `pinCorner_not_collinear`. **So the crux
is ONLY the cross-class slope-±1 incidence:** choose `drop` so that each class's surviving ±1 diagonal
extends through no kept corner of the OTHER class on that line (the two classes are σ-reflections, by
the Step-2 lemmas already proved). Three attack paths:
1. **Define the HJSW family drop-rule + finish the slope-±1 incidence.** Drop-rule = family of residue
   `(x-half, y-half)` per findings §1.4–1.5 (in [0,2p)² frame: translate the centered HJSW pinwheel).
   Then the no-three proof: apply `hyperbola_line_two_congruent`, case on which corner-pair the two
   congruent points form (slope 0/∞/±1), discharge 0/∞ (unique-class — needs a small "same-y ⇒ same
   x-residue" lemma, ≈ `hyperbolaY_inj_residue` already in `Hyperbola.lean`) and same-class
   (`pinCorner_not_collinear`), then the ±1 case via the reflection lemmas + the family assignment
   forcing complementary slope-families (so only ONE of the two σ-paired classes keeps the on-line
   diagonal). The genuine remaining content; finite once the drop-rule is pinned.
2. **First prove the two reduction lemmas as standalone `Pinwheel` theorems** (slope-0/∞ ⇒ ≤2 pinwheel
   points on the line; the same-class one is done) to convert the monolithic `sorry` into a single
   narrow "±1 cross-class incidence" `sorry` — cheaper checkpoint, sets up path 1.
3. **Per-prime → all-N corollary** (independent, bankable): once item 1 lands, `(3/2−ε)N ≤
   maxNoThreeInLine N` for all large N via mathlib's PNT (pick prime `p≈N/2`); or state headline only
   at `N=2p`.

### OPEN ITEM 2 — Goodstein general limit-α B4 `H_{ω^α}(n)+1 = f_{α[n]}(n+1)`. STATUS: open, marginal.
Pattern proven at `ω^ω` (`hardy_omega_pow_omega`); finite-k done (`hardy_omega_pow_ofNat`). The
charter headline (`grows like f_{ε₀}`) is already delivered, so this is a sharpening. Three paths:
1. **Well-founded induction on α** with a non-uniform RHS index (succ vs limit α split): limit case
   peels `(ω^α)[n]=ω^{α[n]}` (brick `fundamentalSequence_omega_pow_limit`) → B4 at smaller `α[n]`;
   succ case is finite-B4's step via `hardy_oadd_coeff`. Fiddly; NB Hardy.lean edits re-run ~4–5 min
   `native_decide`.
2. **Next concrete level only** — B4 at `ω^{ω+1}` or `ω^{ω·2}` (specific limits past `ω^ω`),
   mirroring the `ω^ω` proof; cheaper, incremental.
3. **Inequality sandwich** instead of the exact (succ/limit-uniform) identity, if the exact form
   stays awkward.

### OPEN ITEM 3 — Goodstein strict domination (remove the `+2`). STATUS: open.
`f_o(m) ≤ goodsteinLength m + 2` → tighten. The `+2` is the Cichoń `H(2)−2` offset; A3 index
monotonicity is now CLOSED (`fastGrowing_bachmann_reach`), so the old "A3-hard" blocker is gone.
Paths: (1) trace where `+2` enters `GrowthStatement`/`TowerDomination` and see if a sharper seed
bound removes it; (2) prove a strict variant on a cofinal subsequence; (3) leave as-is (the
two-sided headline already holds with `+2`).

---

## 🎉🎉🎉 lap 11 — CICHOŃ'S LOWER BOUND COMPLETE TO ε₀: f_o(m) ≤ goodsteinLength m + 2 for EVERY o < ε₀

**Done + committed (`4856b9a` tower spine, `9b1e779` full ε₀); build 🟢 (8294 jobs).** New file
`src/LeanFormalizations/Logic/Goodstein/TowerDomination.lean`. The diagonal lower-bound headline —
the genuine Cichoń growth content — is now **complete for every ordinal below ε₀**:
- **`goodsteinLength_eventually_dominates_fastGrowing`** (`o.NF → ∃ N, ∀ m≥N, f_o(m) ≤ goodsteinLength m + 2`).
- `fastGrowing_towerO_le_goodsteinLength` (every tower level `ω↑↑k`); explicit threshold
  `goodsteinLength_dominates_fastGrowing_towerO` (`m ≥ towerN k (2^16+k)`).
- `fastGrowing_le_goodsteinLength_of_repr_le_tower` (any `o` with `repr o ≤ ω↑↑k`).

**The two general engines (each subsumes lap-10's per-level closures):**
1. **General length bootstrap** `two_mul_le_goodsteinLength_iter`: `goodsteinLength((log₂)^[k] m) ≥ 2m`
   for ALL `k`. The lap-10 worry ("needs `f_{ω^ω}`-strength deep-seed bound") was **FALSE** — the
   already-proved `o=ω` domination is strong enough at every depth. Carrier: the clean finite-level
   tower bound `towerN_le_fastGrowing` (`f_{k+2}(t) ≥ towerN(k+1)(t+1)`, induction on `k` via
   `f_{n+1}=(f_n)^[·]` + iterate-monotone), composed with `f_ω(t)=f_{t+1}(t) ≥ f_{k+2}(t)`. Plus the
   tower upper bound on the seed `succ_le_towerN_log_iter` (`m+1 ≤ towerN k ((log₂)^[k] m + 1)`).
2. **General ordinal bridge** `omegaTower_succ_le_seqONote_repr`: descent `≥ ω↑↑(k+1)` from the
   `k`-fold leading exponent in the large regime. Pure `toOrdinal` induction `omegaTower_le_toOrdinal`.
3. **Tower cofinality in ε₀** `exists_repr_lt_omegaTower` (axiom-clean): every NF `ONote` has
   `repr < ω↑↑k` for some `k` (structural induction + additive principality of `ω^·`). This is what
   lifts the tower-spine result to ALL of ε₀.

Crux discharged via the self-similarity tower `iterLeadExp_dominates` read at a fixed index
(`logSeq_iterate_apply`) feeding `n_le_goodsteinSeq` the bootstrap length bound. `#print axioms`:
trust base + finite-base-case `native_decide` (engines fully clean); no sorry.

**UPPER bound also landed this lap (two-sided "grows like f_{ε₀}" COMPLETE):**
- `hardy_le_fastGrowing` (`Logic/FastGrowing/Hardy.lean`, axiom-clean): `hardy o n ≤ fastGrowing o n`
  for `n≥2` — Hardy never outruns fast-growing at the same ordinal index (well-founded recursion on
  the notation; successor case `H_a(n+1) ≤ f_a(n+1) ≤ f_a(f_a n) = (f_a)^[2]n ≤ (f_a)^[n]n`).
- `goodsteinLength_le_fastGrowing_ordinal` (`GrowthStatement.lean`, **fully axiom-clean**, no
  native_decide): `goodsteinLength m + 2 ≤ f_{o_m}(2)` (`o_m = seqONote m 0`). Immediate from the
  Cichoń identity `hardy_seqONote_zero` + `hardy_le_fastGrowing`.
- C3 audit surface `GrowthStatement.lean` + faithfulness anchor `fastGrowingε₀_eq_towerO` (our
  `towerO` IS mathlib's ε₀ fundamental sequence: `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`).

### 🎯 NEXT FRONTIER — B4 (`H_{ω^α} = f_α`), the last charter ladder item — WALL MAPPED (lap 11)
The two-sided growth theorem is DONE; the charter ladder A–C is complete. The remaining explicit
charter target is **B4: the classical identity `H_{ω^α} = f_α`** (flagged "long-horizon trap under
mathlib's `ω[n]=n+1`"). **Lap 11 reconnaissance (measured with `native_decide`/`#eval`) pinned the
exact behavior — record before re-attacking:**

- **The offset is `+1`, and the clean form is `H_{ω^α}(n) + 1 = f_α(n+1)`.** MEASURED and CONFIRMED at
  α = 0, 1, 2 (finite):
  - α=0: `H_{ω^0}(n)=H_1(n)=n+1`, `f_0(n+1)=n+2` → `H+1 = f_0(n+1)` ✓.
  - α=1: `H_ω(n)=2n+1`, `f_1(n+1)=2n+2` → `2n+1+1 = 2n+2` ✓.
  - α=2: `H_{ω^2}(n) = 2^{n+1}(n+1)−1 = f_2(n+1)−1` ✓ (e.g. n=2: H=23, f_2(3)=24).
- **BUT THE CLEAN FORM IS FALSE AT LIMIT α.** MEASURED at α=ω (i.e. `ω^ω`): `H_{ω^ω}(1)+1 = 8` while
  `f_ω(2) = 2048` — NOT equal. Root cause (from the induction): for limit α with fund. seq. `q`,
  `H_{ω^α}(n) = H_{ω^{q n}}(n)` (index `n`) but `f_α(n+1) = f_{q(n+1)}(n+1)` (index `n+1`) — the
  `ω[n]=n+1` shift makes the two pick DIFFERENT tower levels (`q n` vs `q(n+1)`). So the naive offset
  identity does NOT generalize past successor exponents. This IS the charter's "trap."
- **Consequences / correct next attack:**
  - A *restricted* B4 `H_{ω^k}(n)+1 = f_k(n+1)` for FINITE k (α = ofNat k) is TRUE (measured) and is a
    legitimate bankable target — but even its successor step `k→k+1` needs the **coefficient lemma**
    `H_{ω^β·j}(n) = (H_{ω^β})^[j](n)` (since `(ω^{k+1})[n] = ω^k·(n+1)`). **This coefficient lemma is
    MEASURED+VERIFIED true** (lap 11: `H_{ω·2}=(H_ω)^[2]`, `H_{ω·3}=(H_ω)^[3]` exact). Its proof (by
    induction on j) needs, in the step, `H_{ω^β·(j-1)+(ω^β)[n]}(n) = H_{ω^β·(j-1)}(H_{ω^β}(n))` — i.e.
    the **Hardy additive law `H_{α+γ}(n) = H_α(H_γ(n))` for non-absorbing γ** (γ's CNF terms `≤` α's
    trailing term). NOTE the absorption caveat: the *general* `H_{α+β}=H_α∘H_β` is FALSE
    (`1+ω=ω` ⇒ `H_{1+ω}=H_ω` but `H_1∘H_ω ≠ H_ω`); only the non-absorbing form holds.
  - **ROOT BRICK = the non-absorbing Hardy additive law — ✅ DONE (lap 11, `5bf832f`, axiom-clean):**
    `hardy_oadd_tail (a m b n) : hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)` in
    `Logic/FastGrowing/Hardy.lean`. Tail-peeling by well-founded recursion on `b`; no ONote-addition
    machinery needed (the fund-seq def at `Notation.lean:922` already acts on the tail).
  - **✅ DONE (lap 11, `6a63e12`, all axiom-clean):** the coefficient lemma `hardy_oadd_coeff`
    (`H_{ω^β·j}=(H_{ω^β})^[j]`, β≠0) via `hardy_oadd_coeff_step`; the transfer `iterate_offset`; and
    **FINITE B4 `hardy_omega_pow_ofNat`: `H_{ω^k}(n)+1 = f_k(n+1)`** for every finite k. All in
    `Logic/FastGrowing/Hardy.lean`, with a `native_decide` anti-vacuity anchor (`H_{ω^2}(2)+1=24=f_2(3)`).
  - **B4 at LIMIT α — first limit DONE (`558e5bd`):** `hardy_omega_pow_omega`:
    `H_{ω^ω}(n)+1 = f_{n+1}(n+1)` (axiom-clean). The clean `H_{ω^α}(n)+1=f_α(n+1)` is FALSE at limit α
    (`H_{ω^ω}(1)+1=8≠f_ω(2)=2048`); the TRUE limit form reads off the fund seq: `(ω^ω)[n]=ω^{n+1}` ⇒
    `H_{ω^ω}(n)=H_{ω^{n+1}}(n) = f_{n+1}(n+1)−1` by finite B4. **General limit-α pattern (next lap if
    wanted):** `H_{ω^α}(n)+1 = f_{α[n]}(n+1)` for limit α (same `(ω^α)[n]=ω^{α[n]}` peel + finite/IH);
    a uniform B4 statement is non-uniform across succ/limit α — provable but fiddly, and the charter
    "grows like `f_{ε₀}`" is already delivered by finite B4 + the two-sided growth theorem.
  - For limit α, do NOT chase the clean identity (false). The honest general statement is likely an
    *inequality* sandwich or a statement along the successor-α cofinal subsequence only.
  - `hardy_le_fastGrowing` (lap 11, axiom-clean) already gives the `≤`-at-same-index half generally.
**Optional sharpenings** (lower priority): strict domination removing the `+2` (needs general index
monotonicity = A3-hard); a single ε₀ capstone via `ε₀ = sup_o repr o` (presentation).

---

## 🎉🎉 lap 10 — CLIMBED THE LIMIT LEVELS: o=ω, o=ω^j (all finite j), o=ω^ω all CLOSED
### (SUPERSEDED by lap 11's general `TowerDomination.lean` — kept for the engine writeup)

**Done + committed (`ca30077`, `69550cd`, `df89a28`, `1278df6`, `1fb59f8`); build 🟢 (8293 jobs).**
In one lap the diagonal domination `f_o(m) ≤ goodsteinLength m + 2` went from finite-`o`-only to
**every `o` up to `ω^ω`**, all unconditional + machine-checked:
- `fastGrowing_omega_le_goodsteinLength` (o=ω, m≥2^16) — `DominationOmega.lean`.
- `fastGrowing_omega_pow_le_goodsteinLength` (o=ω^j, all finite j≥1).
- `fastGrowing_omega_pow_omega_le_goodsteinLength` (o=ω^ω).

**The two engines (reusable):**
1. **The self-similarity TOWER** (`GoodsteinLike.lean`, axiom-clean): `GoodsteinLike a` (the Goodstein
   lower-bound recursion); `goodsteinLike_logSeq` (leading exponent of a Goodstein-like seq is
   Goodstein-like); `iterLeadExp_dominates m j` (the `j`-fold iterated leading exponent dominates
   `goodsteinSeq ((log₂)^[j] m)`). This is the precise self-reference: level-`j` leadExp ≥ a Goodstein
   value seeded at the `j`-fold log of `m`.
2. **The length BOOTSTRAP** (`two_mul_le_goodsteinLength_loglog`): `goodsteinLength ((log₂)^[2] m) ≥ 2m`,
   proved by bootstrapping `o=ω` against itself — `goodsteinLength t ≥ f_ω(t)−2 = f_{t+1}(t)−2 ≥
   f_3(t)−2 ≥ 2^{2^t·t}−2 ≥ 2(m+1)−2` (`fastGrowing_omega_eq` + `fastGrowing_ofNat_mono` +
   `two_pow_le_fastGrowing_ofNat_three`). The `f_ω` length bound is *tower-strength* — that's what
   lifts the leading exponent into the LARGE regime at the deep seed.

**Ordinal bridges built (`DominationOmega.lean`):** `omega_omega_le_seqONote_repr` (ω^ω from leadExp≥base),
`opow_le_toOrdinal` + `omega_pow_pow_le_seqONote_repr` (ω^{ω^j} from secondLeadExp≥j),
`omega_omega_le_toOrdinal` + `omega_pow_omega_le_seqONote_repr` (ω^{ω^ω} from secondLeadExp≥base).

### 🎯 NEXT FRONTIER — the FULL tower up to ε₀ (`ω^{ω^ω}`, …, `ε₀`)
The pattern is now self-propelling and should be made GENERAL (one induction, not per-level):
  - **General ordinal bridge:** `descent ≥ ω^β` from `β ≤ toOrdinal (base i) (leadExp_i)` (have the
    pieces: `opow_le_toOrdinal`, `omega_omega_le_toOrdinal`, `opow_toOrdinal_log_le`). Induct on
    ω-tower height `k` to get `descent ≥ ω↑↑(k+1)` from the `k`-th leadExp in the large regime.
  - **General length bootstrap:** `goodsteinLength ((log₂)^[k] m) ≥ 2m` by induction on `k`, using the
    previous level's domination as the length bound. The recursive crux is a fastGrowing lower bound
    `f_{tower_{k-1}}(t) ≥ 2m` — iterate `two_pow_le_fastGrowing_ofNat_three`/index-monotonicity. THIS
    is the genuinely hard recursive piece; everything else is mechanical.
  - Concrete next rung if not general: **o = ω^{ω^ω}** needs the THIRD leadExp in large regime, hence
    `goodsteinLength ((log₂)^[3] m) ≥ 2m` — bootstrap `o=ω^ω` (already proved) at the triple-log seed.
  - Good Aristotle candidate: the recursive fastGrowing lower bound (bounded, self-contained).

---

## 🎉 lap 9 — DIAGONAL DOMINATION CLOSED for all finite levels (the 8-lap crux)

**Done + committed (`da05776`, `9b186a8`); build 🟢 (8291 jobs).** The headline open problem —
`f_o(m) ≤ goodsteinLength m + 2` (sub-fact (ii), Cichoń's lower bound) — is **PROVED for every finite
`o`**: `fastGrowing_ofNat_le_goodsteinLength (16 ≤ m) (n+1 ≤ log₂ m)` and the qualitative
`goodsteinLength_dominates_fastGrowing_ofNat : ∀ n, ∃ N, ∀ m ≥ N, f_n(m) ≤ goodsteinLength m + 2`.

**The winning idea (what 8 laps were missing): SELF-SIMILARITY.** The leading-exponent sequence
`L_k = log_{base k}(G_k)` is itself a Goodstein-like descent (`L_{k+1} ≥ bump(base k) L_k − 1`,
`leadExp_step_ge`), so it **dominates the genuine Goodstein sequence seeded at `log₂ m`**
(`leadExp_ge_goodsteinSeq_log`, using `bump_mono` via the `toOrdinal` bridge). This converts "leadExp
stays `≥ n` for `m` steps" into "`goodsteinLength(log₂ m) ≥ m + n`" — one scale down. A strong
induction (`goodsteinLength_exp_lower`, step `exp_le_goodsteinLength_step`) makes the exponential
length bound `goodsteinLength m ≥ 2^{m+1}+m` **reproduce itself** at each scale; it bottoms out at the
finite computational base cases `goodsteinLength M ≥ 2^{M+1}+M` (`4≤M<16`) discharged by the
tail-recursive evaluator `gpos` under `native_decide`. General `o` from the small-regime termination
law (`goodsteinLength_le_of_small` → `n_le_goodsteinSeq`). Engine axiom-clean; unconditional closures
carry `Lean.ofReduceBool` (finite base computation).

### ❌ SUPERSEDED — do NOT pursue
- **The `ppCount` sparsity bound `ppCount m m ≤ log₂ m − 2`** (lap-8 "next brick"). The self-similarity
  recursion is a cleaner, COMPLETE route to the same `o=2` (and all finite `o`); the sparsity bound is
  no longer needed. `ppCount` + `leadExp_ge_sub_ppCount` remain in `Domination.lean` as harmless
  characterization lemmas but are off the closing path. Don't re-attack the sparsity bound.

### 🎯 NEXT FRONTIER — transfinite `o`, starting `o = ω` (toward `f_{ε₀}`)
The finite-`o` diagonal is closed. The expedition's destination (`goodsteinLength ~ f_{ε₀}`) now needs
**limit ordinals**. The smallest open instance: `f_ω(m) ≤ goodsteinLength m + 2`.

**The precise crux.** `f_ω` needs the descent ordinal `≥ ω^ω = (oadd ω 1 0).repr` at step `j ≈ m`,
i.e. `toOrdinal(base j)(G_j) ≥ ω^ω`. Since `toOrdinal b v = ω^(toOrdinal b (log_b v))·c + …`, this
requires `toOrdinal(base j)(leadExp_j) ≥ ω`, i.e. **`leadExp_j ≥ base j` at `j ≈ m`** — the leading
exponent must stay in the LARGE regime (`≥ base`) for `~m` steps, not just `≥ n`. Via self-similarity
`leadExp_k ≥ goodsteinSeq(log₂ m) k`, this needs the *lower* sequence's VALUE `≥ base k = k+2` at
`k ≈ m` — i.e. the lower Goodstein sequence (seed `log₂ m`) is itself still in its large regime at step
`m`. That is one more recursion of the SAME self-similarity (the lower sequence's leadExp dominates
`goodsteinSeq(log₂ log₂ m)`, …). Attack paths:
  (a) **Iterate self-similarity.** Generalize `leadExp_ge_goodsteinSeq_log` to a 2-level statement:
      `leadExp_k(m) ≥ goodsteinSeq(log₂ m) k`, and the value `goodsteinSeq(log₂ m) k ≥ base k` while
      `goodsteinSeq(log₂ m)` is in ITS large regime — bounded below by a length bound on
      `log₂ log₂ m`. Likely needs an `ω`-level analog of `goodsteinLength_exp_lower` (a doubly-iterated
      length bound). This is the natural continuation and reuses every brick built this lap.
  (b) **Direct CNF-height tracking.** Define a "second-level leading exponent" (the log of the leading
      exponent) and show it stays `≥ 2` for `~m` steps by the same self-similarity one level up. `ω^ω`
      ⟺ the CNF has a term `ω^(ω^0·c)` with the inner exponent ≥ ω, i.e. height-2 CNF persists.
  (c) **Bound `goodsteinLength m` below by `f_ω(m)` through the Cichoń identity** (`goodsteinLength m =
      H_{seqONote m 0}(2) − 2`, already proved) + a Hardy/`H_{ω^ω}` lower bound — may be cleaner than
      the leadExp route for limit levels. Cross-check against the `Logic/FastGrowing/Hardy` API.

Realistic: `o=ω` is a genuine multi-lap tier (the limit-ordinal half of Cichoń). Route (a) is the
most direct reuse of the lap-9 machinery; START there. Do NOT axiomatize — it IS the growth content.

---

## 🧘 Reflection — 2026-06-19 (lap 8, deep-reflection lap)

*Altitude pass over the whole expedition. Read STATUS/HANDOFF/PENDING/DIRECTION + git log; re-ran
`#print axioms` on all 12 headlines (every one = bare trust base, 0 math axioms) and re-audited the
growth-theory statements against the math (all faithful). This section is the lap's primary output.*

### Direction call: **SOUND — KEEP GOING.**
The expedition's destination (DIRECTION.md: build the mathlib-only growth theory behind Kirby–Paris,
"`goodsteinLength` grows like `f_{ε₀}`") is **right and substantially achieved**. What's DONE and
axiom-clean: **A1–A4** (fast-growing growth theory incl. `f_{ε₀}` domination, the Kirby–Paris growth
gap); **B1–B3** (Hardy hierarchy); **C1, C2** (the `toOrdinal ↔ ONote.repr` bridge + the Goodstein
descent on `ONote`); and **C3 — the Cichoń identity `goodsteinLength m = H_{seqONote m 0}(2) − 2`**,
whose borrowing crux `hstep_oadd_one_zero` (the heart of Cichoń's theorem) was genuinely discharged.
That is a coherent, novel, mathlib-PR-shaped body of formalization that did not exist anywhere. The
lap-over-lap record is **real forward motion, not circling**: C3 closed (lap 5) → headline reduced to
sub-fact (ii) (lap 6) → sub-fact (ii) at `o=1` + recursion machinery (lap 7).

The honest realistic endpoint: this is an *unbounded* expedition with no finish line. The valuable
artifact already exists; the ONE remaining headline — **diagonal domination `f_o(m) ≤ goodsteinLength
m + 2` for every fixed `o`** — is a genuine multi-lap crux (Cichoń's *lower* bound proper). It is
**not axiomatizable** (anti-smuggling: it *is* the growth content), so it stays a disclosed open
crux, kept off the `sorry` path by stating only the partial results actually proved. Keep banging.

### KEEP doing
- Attacking the **diagonal domination headline** via the reduction already machine-checked in lap 6
  (`goodstein_dominates_of_index` / `goodstein_dominates_of_index_le`): the headline ⟺ **sub-fact
  (ii)** = "the Goodstein descent stays `≥ ω^o` for `≥ m` steps." This reduction is correct and the
  norm-budget obstruction is resolved (`norm_seqONote_le`). Both natural routes (direct count; via
  the Cichoń identity + telescope to a high-budget step) provably collapse to sub-fact (ii) — it is
  irreducible (lap-6 analysis), so this IS the crux.
- Anti-vacuity `native_decide` anchors on every new computable lemma; `#print axioms` on every
  closed theorem; thin faithful headline statements. (All currently in good shape.)

### STOP doing
- **Stop producing further *non-diagonal* lower-bound refinements as the headline lap output.** The
  super-linear → NON-ELEMENTARY ladder (`fastGrowing_ofNat_log_le_goodsteinLength`) is a *complete,
  bankable* result — `goodsteinLength` outgrows every elementary function, proved clean. But it gives
  `f_n` at argument `~log₂ m`, NOT the diagonal `f_n(m)`; pushing it further (to multiply-recursive,
  to `f_ω`, etc.) would **simulate progress without advancing sub-fact (ii)**. That is the fixation
  trap to avoid: don't bag another non-diagonal leaf and call the lap a win.

### Single highest-value next target: **the `o=2` diagonal `f_2(m) ≤ goodsteinLength m + 2`.**
Reasoning: it is the **smallest open instance of the headline** (`o=1` is done), it is concrete and
checkable, and cracking it *forces* building the **steps-between-drops base case** — the technique
that then generalizes to all `o`. Concretely, via `fastGrowing_step_le_goodsteinLength` at a step
`j ≈ m`, the goal needs `(oadd 2 1 0).repr = ω² ≤ (seqONote m j).repr` at a step with budget `j+2 ≥
m`, i.e. **the leading CNF exponent stays `≥ 2` for `≥ m` steps** — equivalently a *super-polynomial
value lower bound* `goodsteinSeq m j ≥ (j+2)²` sustained to `j ≈ m`. The whole gap is the budget
`log₂ m → m`: lap 7's `omega_opow_le_seqONote_repr` already gives `≥ ω²` but only for `j ≤ log₂ m − 2`
(the per-step `leadExp drops ≤ 1` rate bound telescoped from `L₀ = log₂ m`). The truth is leadExp
drops are *rare* — the number of steps between consecutive drops of the leading exponent from level
`E` to `E−1` is itself a Goodstein length of the sub-structure (`≫ m`). The first concrete sub-lemma:
a `dropTime`-style count showing leadExp `≥ 2` persists for `≥ m` steps (induction mirroring
`hardy_oadd_iter`). **Feed Aristotle** a bounded, self-contained carve of this (a slot is free).

**Lap-8 proof progress (committed, axiom-clean):** the **per-step leading-exponent characterization**
is now COMPLETE, which is the prerequisite below the `dropTime` count:
- `log_bump_pred_of_not_pow` — at a NON-pure-power step (`b^{log_b n} < n`), the leading exponent is
  exactly preserved: `log_{b+1}(bump b n − 1) = bump b (log_b n)` (the `−1` is absorbed by lower terms).
- `log_bump_pred_of_pow` — at a pure power (`n = b^{log_b n}`, `log_b n ≥ 1`), it drops by EXACTLY one:
  `log_{b+1}(bump b n − 1) = bump b (log_b n) − 1` (the `−1` borrows from the top).
- `leadExp_ge_of_not_pow` — **unconditional non-decrease off pure powers** (no `≥ base` cap, unlike
  `leadExp_ge_of_base_le`): `L_k ≤ L_{k+1}` at every non-pure-power step. This is the lemma that, once
  paired with a bound on the number of pure-power events, lifts the `log₂ m`-step guarantee to `m` steps.
- `bump_eq_of_lt` (`bump b n = n` for `n < b`) + `leadExp_small_nonincreasing` — **the leadExp
  trajectory is now FULLY characterized**: it GROWS while `L_k ≥ base k` (large regime, `bump_gt`),
  then is **NON-INCREASING once `L_k < base k`** (small regime — off pure powers `bump` fixes the
  single-digit exponent, at pure powers it drops by 1). The `o = 2` difficulty lives entirely in the
  small regime; `leadExp_small_nonincreasing` is the tool for a value/quadratic-plateau induction there.
So the leading exponent bumps-itself/grows everywhere except at the **rare pure-power "borrow" events**.
- `ppCount m k` (new `def`) + `leadExp_ge_sub_ppCount` (the **sharpened telescope**):
  `log₂ m ≤ leadExp_k + ppCount m k` — the leading-exponent deficit is bounded by the *number of
  pure-power steps*, not the step index (sharper than `leadExp_ge_sub`).

**⟹ THE DIAGONAL CRUX IS NOW REDUCED TO ONE SPARSITY BOUND.** Since `ppCount` is monotone, the
implication is clean and CORRECT: **`ppCount m m ≤ log₂ m − 2` ⟹ `leadExp_k ≥ 2` for all `k ≤ m`**
⟹ `seqONote m (m−2) ≥ ω²` ⟹ `f_2(m) ≤ goodsteinLength m + 2` (via `fastGrowing_step_le_goodsteinLength`;
general `o` analogously with `ppCount m m ≤ log₂ m − o`). The sparsity hypothesis is *plausibly true*
(pure-power hits `G_i = (i+2)^e` are extremely sparse among the astronomically-large early terms) but
proving it rigorously **IS** the deep steps-between-drops content — the genuine remaining obligation.
**Next brick = the sparsity bound** `ppCount m m ≤ log₂ m − 2` (or its general-`o` form); cleanest
Aristotle carve too. ⚠ NOTE the telescope gives a LOWER bound on `ppCount` (`ppCount k ≥ log₂ m −
leadExp_k`), NOT the upper bound we need — so the sparsity bound is a genuinely separate fact. Routes:
(a) **bound the count directly** — show pure-power hits `G_i = (i+2)^e` among `i ≤ m` are `≤ log₂ m −
2`; since `G_i` is astronomically large and exact powers of base `i+2` are extremely sparse, this is
plausibly true (likely `O(1)` hits for large `m`), but proving it is the deep content. (b) **bypass
`ppCount` and lower-bound the value directly**: prove `G_k ≥ (k+2)²` for `k ≤ m` (⟺ `leadExp_k ≥ 2`)
by a quadratic-plateau induction — the difficulty is the same (it breaks at pure powers, where `G`
dips just below the square), but the per-step lemmas now characterize exactly those break points.
*(Do NOT claim "leadExp stays ≥ base for m steps" — that is FALSE; `leadExp ≥ base i = i+2` fails once
`i > log₂ m − 2`. The early large regime lasts only `~log₂ m` steps; the depth is the small regime.)*

*Detailed attack notes for sub-fact (ii) / the steps-between-drops recursion are in the lap-6/lap-7
sections below — unchanged and still the operative plan.*

---

## 🎯 ACTIVE FRONTIER (refreshed 2026-06-19 lap 2 — A4 CLOSED)

**Section A (growth theory of `ONote.fastGrowing`) is COMPLETE + axiom-clean.** A1
(`le_fastGrowing`), A2 (`fastGrowing_monotone`), A3 (`fastGrowing_bachmann_reach`), **A4
(`fastGrowing_lt_fastGrowingε₀`)** all proved. The A4 engine (`Domination.lean`): CNF `norm`,
`lt_fundamentalSequence_of_norm_le` (key cofinality bound), `reaches_of_lt` (general
reachability), `osucc` + strict step. General index monotonicity `fastGrowing_le_of_lt` /
`hardy_le_of_lt` added. `Logic/FastGrowing/*` is sorry-free.

### C2 — the semantic bridge `toOrdinal` ↔ `ONote.repr`  ✅ DONE (2026-06-19 lap 2)
`Logic/Goodstein/Growth.lean` (axiom-clean): `toONote b n` (the computable notation),
`repr_toONote : (toONote b n).repr = toOrdinal b n`, `toONote_NF`, and the descent on `ONote`:
`seqONote m k := toONote (k+2) (goodsteinSeq m k)`, `repr_seqONote = Engine.seqOrd m k`, and
**`seqONote_lt`** (`goodsteinSeq m k ≠ 0 ⟹ seqONote m (k+1) < seqONote m k`). The Goodstein
ε₀-descent now lives on the same `ONote` as the fast-growing growth theory.

### ✅ C3 — `goodsteinLength m = H_{seqONote m 0}(2) − 2`  (the Cichoń identity) — **DONE 2026-06-19 lap 5**
**FULLY PROVED + axiom-clean.** The lone disclosed `sorry` `hstep_oadd_one_zero` (the borrowing
predecessor of `ω^E` — the heart of Cichoń's theorem) is discharged. `goodsteinLength_eq_hardy`,
`hstep_toONote`, `hstep_oadd_one_zero` all have `#print axioms = [propext, Classical.choice,
Quot.sound]`. The close-out used the `Good`/`Canon` frontier invariant (base-`(b+1)` canonical
with ≤1 coeff `=b+1` at the active frontier): `canon_repr`/`canon_round_trip` (round-trip through
`evalNat` via the engine's `toOrdinal` strict monotonicity), `Canon_pred` (a `Good` successor's
predecessor is `Canon`), `Good_fundSeq` (limit descent preserves `Good`), and the general
`hstep_pred_pow` (WF recursion on `repr E`). `src/` is now sorry-free.

### ✅ Hardy ↔ fastGrowing BRIDGE — **DONE 2026-06-19 lap 5** (`Logic/Goodstein/Domination.lean`)
`fastGrowing_le_hardy_pow : NF α → fastGrowing α n ≤ hardy (oadd α 1 0) n` (`f_α ≤ H_{ω^α}`,
**matching args**), axiom-clean. Engine: `hardy_split` (`H_{ω^e·c+R}=H_{ω^e·c}∘H_R` for NF — the
NF condition `repr R < ω^(repr e)` IS the no-absorption side condition, sidestepping general
`ONote.add` additivity); `hardy_oadd_iter` (iteration law `H_{ω^e·(k+1)}=(H_{ω^e})^[k+1]`, via
`hardy_oadd_coeff_step_ne` + the lap-4 `fundSeq_oadd_coeff`); `hardy_finite`, `iterate_le_iterate`,
`succ_iterate`. Also `toOrdinal_two_cofinal` (`∀ NF β, ∃ N, repr β < toOrdinal 2 N`; via
`toOrdinal_pow` building ω-towers). All `#print axioms`-clean; native_decide anchors present.

### ✅ LAP 7 (2026-06-19) — `f_1` DOMINATED unconditionally + the recursion skeleton formalized

Six axiom-clean commits in `Goodstein/Domination.lean`. The growth attack moved from "fully
blocked on sub-fact (ii)" to "level `o = 1` CLOSED + the per-step recursion machinery built":

1. **Growth engine (`bump_gt`):** `b ≤ n → n + 1 ≤ bump b n` — one bump strictly grows a value
   above its base (leading power `b^L ↦ (b+1)^{bump b L} > b^L`). The first real growth fact.
2. **`goodsteinSeq_ge_init`:** `k + 1 ≤ m → m ≤ goodsteinSeq m k` — the value stays `≥ m` for the
   first `m` steps (non-decrease while `≥` base). ⟹ **`omega_le_seqONote_repr`:** the descent
   ordinal stays `≥ ω` for `~m` steps = **sub-fact (ii) at `o = 1`**.
3. **`goodstein_dominates_of_index_le`** (generalized reduction: any telescope step `j`, non-strict
   index, equality ⟹ `rfl`) ⟹ **`fastGrowing_one_le_goodsteinLength`**: `goodsteinLength`
   dominates `f_1` for every `m ≥ 2`, via the full Cichoń pipeline (NOT `native_decide`).
4. **`two_mul_sub_one_le_goodsteinLength`:** `goodsteinLength m ≥ 2m − 1` (value drops by `≤ 1`/step
   — `goodsteinSeq_sub_le` — from the `≥ m` plateau). Beats the old linear `≥ m`.
5. **Recursion skeleton (the path to `o ≥ 2`):** `log_bump` (`log_{b+1}(bump b n) = bump b(log_b n)`
   — *the leading exponent bumps itself*); `log_le_log_pred_succ` (a decrement lowers `Nat.log` by
   `≤ 1`); **`leadExp_drop_le_one`** (leading CNF exponent `L_k` drops by `≤ 1`/step) and
   **`leadExp_ge_of_base_le`** (`L_k` non-decreasing while `L_k ≥ base k`). The full per-step local
   structure of the leading-exponent descent.
6. **Telescope + ordinal bridge:** `leadExp_ge_sub` (`L_i ≥ log₂ m − i`, telescoping
   `leadExp_drop_le_one`); `opow_toOrdinal_log_le` (`ω^(L_i ordinal) ≤ seqOrd`); `opow_le_seqONote_repr`
   (`L_i ≥ k`, `k < base i` ⟹ `ω^k ≤ seqOrd`); **`omega_opow_le_seqONote_repr`** — the descent
   ordinal stays `≥ ω^k` for the first `log₂ m − k` steps (generalizes the `o=1` ordinal bound to
   every `k`). The `seqOrd ≥ ω^k` machinery is now fully built; the ONLY gap to sub-fact (ii) at
   `o = k` is upgrading the step-range from `log₂ m` to `m` — i.e. the steps-between-drops recursion.
7. **CAPSTONE — `goodsteinLength` is SUPER-LINEAR:** `fastGrowing_step_le_goodsteinLength` (the
   non-diagonal reduction: `seqOrd ≥ ω^o` at step `j` ⟹ `f_o(j+2) ≤ goodsteinLength m + 2`, no
   diagonal budget) instantiated at `o=2`, `j=log₂ m − 2` ⟹ **`fastGrowing_two_log_le_goodsteinLength`**:
   `f_2(log₂ m) ≤ goodsteinLength m + 2`, i.e. `goodsteinLength m ≳ m·log₂ m`. First proof it beats
   the polynomial regime. **✅ DONE — generalized to all `n`: `goodsteinLength` is NON-ELEMENTARY.**
   `fastGrowing_ofNat_log_le_goodsteinLength`: `fastGrowing (ofNat n) (L − n + 2) ≤ goodsteinLength
   m + 2` for `1 ≤ m`, `2n ≤ L = log₂ m` (helpers `norm_ofNat`, `ONote.repr_ofNat`, `(ofNat n).NF =
   inferInstance`). The budget is `L − n + 2` not `L` (leadExp ≥ n and budget trade off). Taking
   `n ≈ L/2` gives `goodsteinLength m ≥ f_{L/2}(L/2 + 2)` — a tower of height `~log₂ m`, so
   `goodsteinLength` outgrows every elementary function. Axiom-clean.

   **THE ONE REMAINING DEEP CRUX — the diagonal `f_n(m)` (true domination, the headline):** the gap
   is entirely the budget `L − n → m` (we have `f_n` at argument `~log m`; the headline wants
   argument `m`). This needs the descent to keep `leadExp ≥ n` for `≥ m` steps (not just `~log m`),
   i.e. the **steps-between-leading-exponent-drops = sub-Goodstein-length recursion**. All the local
   machinery (`leadExp_drop_le_one`, `leadExp_ge_of_base_le`, `log_bump`, the ordinal bridges) is the
   running start; the recursion itself (induction on the leading exponent mirroring `hardy_oadd_iter`)
   is the genuine multi-lap obligation.

**THE SHARPENED CRUX (what remains for `o ≥ 2`, i.e. the headline):** the per-step facts give only
a **`log m`-step** guarantee that `L_k ≥ 2` (rate-bound `drop ≤ 1`/step from `L_0 = log_2 m`; and
`leadExp_ge` only holds while `L_k ≥ base k = k+2`, i.e. `k ≲ log m`). The TRUTH is that `L_k`
*drops are RARE*: **the number of steps between consecutive drops of `L_k` from level `E` to `E−1`
is itself a Goodstein length of the sub-structure at level `E`** (astronomically `≫ m`). Formalizing
"steps-between-drops = sub-Goodstein-length" is the genuine recursive heart of Cichoń's lower bound
— the one remaining deep, multi-lap obligation. Concretely: define the drop-time function and prove
a recursion `dropTime(E) ≥` (Goodstein length at level `E−1`), then `L_k ≥ 2` for `≥ m` steps
follows. The local skeleton (lap 7) is the running start; next lap, attack the steps-between-drops
recursion (likely an induction on the leading exponent mirroring `hardy_oadd_iter`).

### 🎯 NEXT CRUX (refreshed 2026-06-19 lap 6): headline REDUCED to one descent-count fact

**Lap-6 result — the headline is now a machine-checked reduction to a single deep fact, and the
budget obstruction is RESOLVED.** Three axiom-clean additions in `Goodstein/Domination.lean`:

1. **`goodstein_dominates_of_index`** — the full Cichoń assembly, verified:
   `o.NF → norm o ≤ m → oadd o 1 0 < seqONote m m → fastGrowing o m ≤ goodsteinLength m + 2`.
   Chain (all banked): telescope at `j=m` (valid by `le_goodsteinLength`) + `hardy_seqONote_zero`
   give `goodsteinLength m + 2 = H_{seqONote m m}(m+2)`; `hardy_le_of_lt` (budget OK at `m+2`)
   lifts `H_{oadd o 1 0}(m+2) ≤ H_{seqONote m m}(m+2)`; bridge `fastGrowing_le_hardy_pow` +
   `fastGrowing_monotone`. **The ONLY open input is the index hypothesis `hidx`.**
2. **`norm_toONote_lt` / `norm_seqONote_le`** — `norm (seqONote m j) ≤ j+1` (a base-`(j+2)`
   numeral has all digits `< j+2`). ⟹ **the Hardy budget `norm ≤ argument` is AUTOMATIC at the
   telescope step `j+2`.** The old "norm obstruction" only ever bit at the *fixed* argument 2;
   evaluated on the descent at step `j+2` it is free, in BOTH comparison directions.
3. **`goodstein_dominates_or_hardy_bound`** (unconditional dichotomy) — for `norm o ≤ m`, EITHER
   `fastGrowing o m ≤ goodsteinLength m + 2` (A, dominates) OR
   `goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m+2)` (B, length Hardy-bounded). Proof: trichotomy
   of `seqONote m m` vs `oadd o 1 0`, budget free both ways.

**⟹ THE HEADLINE ⟺ "branch (B) is eventually empty" ⟺ sub-fact (ii) below.** Nothing else is
missing. native_decide anchors witness the inequality for `o∈{0,1}, m∈{2,3}` (computable regime).

**THE ONE REMAINING DEEP FACT — sub-fact (ii), `oadd o 1 0 < seqONote m m` for large `m`:**
the Goodstein descent stays above `ω^o` for at least `m` steps. Equivalent forms: (a) the drop
time `j*(m) = max{j : seqONote m j > oadd o 1 0}` satisfies `j*(m) ≥ m`; (b) branch (B) fails for
large `m`; (c) `goodsteinLength m + 2 > H_{ω^o}(m+2)` eventually.

**Why it is irreducible (lap-6 analysis — do NOT re-try these dead ends):**
- *Leading-exponent antitone is FREE and USELESS:* for ordinals `α<β ⟹ leadExp α ≤ leadExp β`
  (else `ω^{leadExp α} > β > α ≥ ω^{leadExp α}`), so "leading exp non-increasing on the descent"
  is just a corollary of the strict descent — it gives no step-COUNT.
- *The dichotomy cannot be bootstrapped from the linear bound:* branch (B) gives
  `goodsteinLength m + 2 ≤ H_{ω^o}(m+2)`; combined with `goodsteinLength m ≥ m` only yields
  `m+2 ≤ H_{ω^o}(m+2)` (always true). To kill (B) you need `goodsteinLength m` ABOVE `H_{ω^o}(m+2)`
  — i.e. a **super-linear lower bound on `goodsteinLength`**, which is the growth content itself.
- *`j*(m) → ∞` is provable but too weak:* for fixed `K`, `seqONote m K > oadd o 1 0` for large `m`
  (since `goodsteinSeq m K → ∞` as `m→∞` by bump-monotonicity, and `toOrdinal (K+2)` is cofinal),
  so `j*(m) ≥ K` eventually. But this only gives `f_o(K+2) ≤ goodsteinLength m + 2` (constant LHS)
  ⟹ `goodsteinLength → ∞`, NOT `f_o(m) ≤ goodsteinLength m`. The diagonal `j*(m) ≥ m` is the gap.

**Concrete next-lap attack (the genuine deep content):** a super-linear lower bound on
`goodsteinSeq m j` / on the descent ordinal. The real recursive structure: within one
leading-CNF-level the number of steps is itself a Hardy value (astronomically `>` 1 per level),
so the descent spends `≫ m` steps before the leading exponent falls below `repr o`. Formalizing
"steps-per-CNF-level" is Cichoń's lower bound proper — likely needs an induction on `o` mirroring
`f_{o+1} = f_o`-iterate, or a direct recursive count of `goodsteinLength` restricted to a
threshold. Multi-lap; decompose, checkpoint with a `sorry` only on the count itself.

**OLDER framing (lap 5) — superseded by the lap-6 reduction above but kept for the math:**
The identity gives `goodsteinLength m = H_{toONote 2 m}(2) − 2`; the headline (DIRECTION.md C3) is
"**`goodsteinLength` eventually dominates every `fastGrowing o`**". The diagonal `H_{toONote 2 m}(2)`
has a large *index* but the **argument is fixed at 2**.
**⚠ KEY OBSTRUCTION (found lap 5, the reason this is harder than it looks):** `hardy_le_of_lt`
carries a budget hypothesis `norm α ≤ x`, and Hardy index-monotonicity GENUINELY FAILS at small
fixed argument — measured: `H_ω(2)=5 < H_5(2)=7` although `ω > 5`. So you CANNOT dominate
`H_{toONote 2 m}(2)` by comparing it (via `hardy_le_of_lt`) to a big-coefficient notation like
`ω^o+(m+2)` at arg 2 (its `norm = m+2 > 2`). The naive arg-2 comparison is mathematically WRONG.

**Budget-aware attack paths (next laps):**
1. **Via fastGrowingε₀ + A4.** Relate `goodsteinLength m` to `fastGrowingε₀ m`, then A4
   (`fastGrowing_lt_fastGrowingε₀`, already proved) dominates every `f_o`. Needs the deep half of
   Cichoń: climb the index using the budget the descent itself provides (the bridge `f_α ≤ H_{ω^α}`
   at matching args is the easy half; the missing half converts index-size to argument-size).
2. **Hardy budget-climb.** `H_α(n+k) = H_{α+k}(n)` (finite additive shift — have `hardy_split` +
   `hardy_finite`). Apply `hardy_le_of_lt` only at points along the descent where `norm ≤ arg`
   already holds (the budget grows as the descent proceeds). Trace where the norm budget unlocks.
3. **The `H_{ω^α}=f_α`-style matching-budget correspondence** (the genuine "B4 trap"): mathlib's
   `ω[n]=n+1` shifts the classical identity (`H_ω(n)=2n+1` vs `f_1(n)=2n`; `H_{ω²}(2)=23` vs
   `f_2(2)=8`, not a constant shift). The one-sided `f_α ≤ H_{ω^α}` is done; a reverse bound
   `H_{ω^α}(n) ≤ f_{α+1}(n)` (matching args) would let the diagonal be squeezed.
Bank: bridge + cofinality are the prerequisites; this is a multi-lap crux.

**🔑 THE CONCRETE ENABLER (found lap 5) — the telescope unlocks the budget.** Already proved:
`hardy_seqONote_telescope : j ≤ goodsteinLength m → H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`.
Combined with `hardy_seqONote_zero`: **`goodsteinLength m + 2 = H_{seqONote m j}(j+2)` for ALL
`j ≤ goodsteinLength m`** — so we may evaluate the invariant at a HIGH-budget step `j+2` where
`norm` becomes available. Sketch to finish the headline `f_o(m) ≤ goodsteinLength m + 2`:
- pick `j` with budget `j+2 ≥ max(m, norm(oadd o 1 0))` and `j ≤ goodsteinLength m`;
- `H_{seqONote m j}(j+2) ≥ H_{oadd o 1 0}(j+2)` by `hardy_le_of_lt` (NOW norm-valid: `norm(ω^o)
  ≤ j+2`) **provided `oadd o 1 0 ≤ seqONote m j`** (index lower bound);
- `H_{oadd o 1 0}(j+2) ≥ f_o(j+2) ≥ f_o(m)` by the bridge + `fastGrowing_monotone` (need `j+2 ≥ m`).
**Sub-facts:**
  (i) ✅ **DONE lap 5** — `le_goodsteinLength : m ≤ goodsteinLength m` (`Domination.lean`, via
      `le_bump`+`goodsteinSeq_ge_sub`, axiom-clean). So any `j ≤ m` is a valid telescope step.
  (ii) **the real remaining depth — needs a STRONG term lower bound, NOT the linear one.**
       ⚠ Checked lap 5: at `j = m-2` (budget `m`), `goodsteinSeq m (m-2) ≥ m-(m-2) = 2` only, so
       `seqONote m (m-2)` reads as `finite 2` (repr 2) — FAR below `ω^o`. The linear bound (i) is
       insufficient for the index. **The sweet-spot tension:** small `j` ⇒ huge index but small
       budget (`< m`, bridge needs arg `≥ m`); large `j` ⇒ big budget but tiny index. The needed
       index bound `oadd o 1 0 ≤ seqONote m j` at a `j` with budget `≥ m` requires
       `goodsteinSeq m j ≥ (j+2)^(big)` — a **super-exponential** Goodstein-term lower bound (the
       term IS astronomically large early on). That strong term bound is essentially the growth
       content itself; it is the genuine deep crux. Next-lap target: prove a super-linear lower
       bound on `goodsteinSeq m j` for `j` in the early/middle range (e.g. via `bump b n ≥ n+...`
       or tracking the leading CNF term across steps), enough that `seqONote m j ≥ ω^o` at a
       budget-`≥m` step.

**OLD (pre-2026-06-19-lap5) C3 close-out notes — kept for reference, now all DONE:**
The whole C3 chain was built and the headline held modulo a single isolated lemma. Identity
(native_decide-confirmed): `hardy (seqONote m 0) 2 = goodsteinLength m + 2`. Done across laps 3–5:
- **Intrinsic Hardy machinery** (`FastGrowing/Hardy.lean`, axiom-clean): `hstep` (budget-
  incrementing Hardy step on `ONote`), `hardy_hstep : o≠0 → H_o(n)=H_{hstep o n}(n+1)`,
  `fundamentalSequence_inr_ne_zero`, `hstep_oadd_tail` (peel leading `oadd` term).
- **C3 assembly** (`Goodstein/Growth.lean`): `hstep_seqONote`, `hardy_seqONote_step` (per-step
  invariance), `hardy_seqONote_telescope`, `hardy_seqONote_zero`, `goodsteinLength_eq_hardy`
  (HEADLINE). Helpers `toONote_bump`, `toONote_oadd`, `toONote_single`,
  `fundamentalSequence_oadd_zero_zero`, `hstep_oadd_zero_zero`.
- **The crux `hstep_toONote`** (`hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`): strong
  induction on `p = c·b^L + r`. PROVED: `r≠0` (tail recursion via `hstep_oadd_tail` + IH +
  `toONote_oadd`/`toONote_bump`) and `r=0 ∧ L=0` (finite, `hstep_oadd_zero_zero`).

**THE LONE OPEN CORE: `hstep_oadd_one_zero` (general `L≥1`, `c=1`)** — predecessor of `ω^E`,
`E = toONote b L`. Target: `hstep (oadd (toONote b L) 1 0) b = toONote (b+1) ((b+1)^(bump b L) − 1)`.

**DONE 2026-06-19 lap 4 (4 commits) — crux narrowed `r=0,L≥1` ⟶ this single `c=1` lemma:**
1. **Lemma A (coefficient peel) — PROVED.** `hstep_oadd_coeff` (+ `fundSeq_oadd_coeff`): for
   `E≠0, c≥2`, `hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The `r=0,L≥1`
   branch of `hstep_toONote` is now FULLY PROVED modulo `hstep_oadd_one_zero` (c=1).
2. **Lemma B finite base case — PROVED.** `hstep_oadd_one_zero_finite`: `E = finite(d+1)`,
   `d≤b`, gives `(b+1)^(d+1)−1`. Validates the whole recursion engine end-to-end.
3. **Recursion primitives — PROVED.** `hstep_oadd_one_of_succ`/`_of_limit` (descent on
   `oadd E 1 0`), `fundSeq_oadd_one_of_succ`/`_of_limit`, `hstep_finite_pred`, `fundSeq_finite_succ`.
4. **`evalNat` linchpin — PROVED.** `evalNat b o` (= `repr o` read as base-`(b+1)` numeral);
   `evalNat_toONote : evalNat b (toONote b L) = bump b L`. The general answer is
   `toONote (b+1) ((b+1)^(evalNat b E) − 1)`.

**Remaining (next lap): the general recursion.** WF recursion on `repr E`:
- **Limit case CLEAN** (no reconstruction): `hstep_oadd_one_of_limit` → IH on `f b`, closes via
  `evalNat (f b) = evalNat E` (identity `evalNat_fundSeq`, TODO — at the fixed index `b`).
- **Successor case** needs `evalNat E = evalNat E' + 1` (`evalNat_succ`, TODO) AND the
  reconstruction `toONote (b+1) (evalNat E') = E'` for `E' = pred E`. Reconstruction is the
  real wall: it holds for base-`(b+1)`-CNF `E'` but the descent's `f b` introduces coefficient
  `b+1` (at index `b`). KEY OBSERVATION: that `b+1` is always immediately peeled by
  `hstep_oadd_coeff`, and `pred` of a reachable successor keeps coefficients `< b+1` at the
  decremented position — so a **coefficient-bound invariant** (≤ b+1, with the b+1 only where
  peelable) makes reconstruction go through. Formalize that invariant + the two `evalNat`
  identities, then the WF recursion closes `hstep_oadd_one_zero`.
3. **Aristotle: job `77c99f0e`** still RUNNING on the (pre-narrowing) general borrowing goal —
   if it returns a full proof, it subsumes everything; VERIFY + `#print axioms` before porting.

### Domination corollary (after the C3 identity closes)
With `goodsteinLength_eq_hardy` + A4 (`fastGrowing_lt_fastGrowingε₀`) + `hardy_le_of_lt`, derive
`goodsteinLength` eventually outgrows every `fastGrowing o`; then a thin audit-surface headline.

### B ladder (Hardy) — lower priority
B2/B3 done. **B4** (`H_{ω^α}=f_α`) is a trap under mathlib's `ω[n]=n+1` (measured: not a
constant shift, `H_{ω^2}(2)=23 ≠ f_2(2)+1=9`). Needs a reformulated statement; long-horizon.

---

## 🔭 OPEN-ITEM INVENTORY (refreshed 2026-06-17)

`src/` declares **no custom axioms** and has no `sorry`/`admit` (`lake build` green, 8274
jobs at the time of writing). Note this is not the same as "axiom-free": the Goodstein growth
closures carry `native_decide` artifacts, as `STATUS.md` records. Three threads are COMPLETE + axiom-clean — **do not reopen**: Curtis 1990
(no-Frobenius-formula), π/e-transcendence + squaring-the-circle (the `hermite_lindemann` axiom
was discharged + deleted 2026-06-16), and constructible numbers / Wantzel (full iff + 5 classical
impossibilities). Completion records below.

### ✅ COMPLETE (2026-06-18) — power-tower SHARP `iff` (the `0 < x < e^(-e)` divergence)
**DONE, axiom-clean.** The operator-directed target of the 2026-06-17 `DIRECTION.md` is
finished. `EngineLower.tower_diverges_lower` (`0<x<e^(-e) ⟹ ¬∃L`) + the headline
`Statement.tower_converges_iff_full` (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`) are
both proved; `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The proof followed
the planned route exactly: `fixedpoint_exists` (IVT fixed point `y`), `log_fixedpoint_lt_neg_one`
(the repelling seed `x<e^(-e) ⟹ log y < -1` — by contradiction, `log y ≥ -1 ⟹ y ≥ 1/e ⟹
-ye ≤ -1`, no `v·e^v` monotonicity lemma needed), `strict_two_cycle_exists` (IVT on `g-id`
both sides of `y`, where `g'>1` on a neighbourhood from continuity of `g'` + `g'(y)=(log y)²>1`),
and the even/odd-trapping bound (`a(2n) ≥ γ₀ > β₀ ≥ a(2n+1)`) ⟹ distinct limits ⟹ no limit.
The subsequence construction is now the shared `tower_subseq_limits` (used by both directions).
The Lóczi §3 reference was NOT needed (no `ON-LINE-REQUEST` filed).

### ✅ COMPLETE (2026-06-16) — π/e-transcendence, axiom-clean, `hermite_lindemann` DELETED
`Transcendence.transcendental_pi` proved from first principles, axiom-clean;
`squaring_the_circle_impossible_uncond` rewired to it; the cited axiom deleted → repo
math-axiom count = **0**. Assembly: `ETranscendental.lean` (`e_transcendental`, the Hermite
assembly of `exp_polynomial_approx`) → `PiLindemann.lean` (combinatorial reduction + non-monic
analytic engine) → `MonicRootSums.lean` (fact (a) `sum_aeval_roots_int`, Aristotle `9a19f72e`)
→ `SubsetSumEsymm.lean` (fact (b) `subsetSum_esymm_rational`, fundamental theorem of symmetric
polynomials, Aristotle `b7252abe`) → `PiTranscendental.lean`. Both Aristotle proofs independently
kernel-verified. (For the *alternative* path not taken — adopting mathlib PR #28013 on a future
bump — see `archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`.)

### 🧹 Deferred one-liner: a stale docstring in `PiLindemann.lean`

`PiLindemann.lean:48` still describes its two missing ingredients as "the isolated remaining crux
toward discharging `hermite_lindemann` at `π` (equivalently, adopting mathlib PR #28013 on the next
bump)".  **Both ingredients were supplied and the axiom was discharged and deleted** — verified
2026-09-04 by `#print axioms`: `transcendental_pi_axiomClean` and
`squaring_the_circle_impossible_uncond` are both `[propext, Classical.choice, Quot.sound]`.  The
docstring is a recorded plan that outlived the problem it solved, and it reads as an open TODO.
Rewrite it to describe what the file *does*.  Deferred only because editing a `.lean` file mid-run
contends with the treadmill's `lake` lock; it is a comment change, no proof content.

Same check settled the vendoring question: mathlib `v4.31.0` already ships
`NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` (`exp_polynomial_approx`, which this
repo uses), and `Analysis/Real/Pi/Irrational.lean` already has `irrational_pi`.  PR #28013 is still
OPEN (checked 2026-09-04, updated that same day) and its remaining files supply the *general*
Lindemann–Weierstrass theorem, which this repo does not need for `π`.  **Nothing to vendor.**


## ✅ COMPLETE (2026-06-14, operator-bounded run): Curtis verification hardening

All four items in `DIRECTION.md` are built, green, sorry-free, axiom-clean
(commits `ea89147`, `0498df8`). Every optional stretch part was also done:

1. ✅ `Boundary.n2_polynomial_relation_exists` — Sylvester hypersurface; n=2/n=3 line.
2. ✅ three new Lemma-2 anchors (⟨3,7,11⟩, ⟨3,13,14⟩, ⟨5,11,23⟩, one also direct) +
   ✅ stretch `frobeniusNumber_6_9_20` (McNugget 43, outside Curtis's family).
3. ✅ `symmetric_guess_not_a_formula` (worked) + ✅ stretch `no_single_polynomial_formula`.
4. ✅ `Curtis/FINDINGS.md` + fixed stale docstrings in `Engine.lean` / `Curtis/README.md`.

Run self-stopped on completion per `DIRECTION.md` (sentinel written). The PARKED targets
below remain Trevor's call for a future, separately-scoped run.

---

## ✅ COMPLETE (2026-06-14, power-tower LOWER half run)

Mandatory `tower_converges_of_mem` (convergence on the FULL Euler interval
`[e^(-e), e^(1/e)]`) is PROVED and **fully axiom-clean** (`[propext,
Classical.choice, Quot.sound]`). The lower-bound crux `two_cycle_collapse` (no
nontrivial 2-cycle of `t↦x^t` for `x ≥ e^(-e)`) is **machine-checked, no axiom** —
via the slope bound `g'(t) ≤ |log x|/e ≤ 1` (`EngineLower.lean`): contraction +
Banach for `x > e^(-e)`, antitone-on-interval for the boundary `x = e^(-e)`.
(The DIRECTION's "subtract the tangent-line inequalities" sketch is mathematically
invalid; the derivative/slope bound is the correct mechanism.)

### Sharp `iff` lower direction (`0 < x < e^(-e)` diverges) — NOW THE ACTIVE TARGET
`tower_converges_iff_full` was omitted as a stretch on the 6-14 run (the convergence half
`tower_converges_of_mem` + `tower_diverges` shipped; the lower divergence requires a *genuine
attracting 2-cycle*, multi-lap real analysis). **As of 2026-06-17 it is the directed goal —
see `DIRECTION.md` and "THE ONE ACTIVE ITEM" at the top.** NO `sorry` was ever left here.

---

## ✅ COMPLETE (2026-06-15): P1 Layer 1 — constructible-numbers algebraic core + all three classical impossibilities

`Geometry/Constructible/` — **PROVED, axiom-clean** (`[propext, Classical.choice,
Quot.sound]` on every headline). Exactly the Layer-1 plan below, and then some:
- `IsSqrtTower` / `IsConstructible` on `IntermediateField ℚ ℝ`; engine
  `IsSqrtTower.finrank_eq_pow_two` (degree `2ⁿ`) via tower law + quadratic step.
- **Doubling the cube**: `cbrt2_not_constructible` (`minpoly ℚ ∛2 = X³−2`,
  Kummer-irreducible; `[ℚ(∛2):ℚ]=3`).
- **Trisecting 60°**: `cos20_not_constructible` (triple-angle ⟹ `2cos20°` root of the
  monic `X³−3X−1`, irreducible by integral-root theorem; degree 3).
- **Squaring the circle**: `squaring_the_circle_impossible (hπ : Transcendental ℚ π)`
  via `IsConstructible.isAlgebraic`. Conditional on `π`-transcendence (mathlib gap).
- Constructibles form a **subfield closed under √** (`IsSqrtTower.sup_exists` +
  `IsConstructible.{add,sub,mul,neg,inv,sqrt}`, `isConstructible_ratCast`).

### ✅ DONE (2026-06-16): P1 Layer 2 + the full converse — Wantzel as an iff
The geometric faithfulness layer is COMPLETE and axiom-clean, and then some:
- `ConstructiblePoint : ℝ×ℝ → Prop` (inductive: `{(0,0),(1,0)}` closed under
  line∩line / line∩circle / circle∩circle). `ConstructiblePoint.isConstructible_coords`
  proves geometry ⟹ algebra via `line_meet_line` / `line_meet_circle` /
  `circle_meet_circle` (`ConstructiblePoint.lean`).
- **Converse** (`Converse.lean`): `AxisConstructible` closed under `+,−,·,⁻¹,/,√` by
  explicit compass constructions; tower induction `isSqrtTower_le_axisField` gives
  algebra ⟹ geometry. Headline `isConstructible_iff_constructiblePoint`.
- Geometric impossibility headlines (`cbrt2_point_not_constructible`,
  `heptagon_point_not_constructible`); positive `isConstructible_cos_pi_div_five`
  (pentagon); heptagon added (`Heptagon.lean`, 5th classical instance).

### ✅ DONE (2026-06-16): squaring-the-circle is now UNCONDITIONAL
`squaring_the_circle_impossible_uncond` no longer takes a hypothesis — it is wired to the
axiom-clean `Transcendence.transcendental_pi` (full Lindemann assembly; see the π completion
record at the top). The "multi-year wall" was discharged from first principles. No axiom remains.

### ✅ DONE (2026-06-16): regular heptagon / 7-gon
`Heptagon.lean` — `twoCosHept_not_constructible`, axiom-clean. Minpoly `X³+X²−2X−1`
derived from `cos(4θ)=cos(3θ)` at `θ=2π/7` (factor out the `c=1` root).

## 🅿️ PARKED — future runs, Trevor's call (NOT this run; do not start)

Preserved for a future, separately-scoped run. These are genuine extensions but are
**explicitly out of scope now** — do NOT treat them as "open frontier" when deciding to stop.

### P2. Upstream Curtis to `Mathlib.NumberTheory.FrobeniusNumber`
mathlib has the n=2 Chicken-McNugget theorem and notes it stops at n=2; Curtis's n=3
impossibility is the natural sequel. Needs a mathlib style pass (drop the bespoke
`IsAdmissible`/audit framing for an idiomatic statement) and an AI-contribution-policy check
(reference corpus: `2026-06-07-mathlib-ai-contribution-policy.md`). Web/CLA-gated.

### P3. Sharpen the "not algebraic" framing
State explicitly: `(s₁,s₂,s₃,g)` lies on no proper hypersurface of ℂ⁴ (graph Zariski-dense).
A short repackaging of `no_polynomial_relation`. (Item 4 of the active run *documents* this;
P3 would be a full theorem-level statement — defer.)

---

## Lemma2.lean lint warnings — LEAVE THEM
The unused-variable warnings on `lemma2`'s hypotheses (`h1,h2,h3,hk_hi,hr_hi`) are the
*mathematical* hypotheses of Curtis's Lemma 2, kept for the audit surface even though this
proof path doesn't consume all of them. Do not strip them. The two unused-simp-arg warnings
are inside Aristotle-verified tactic blocks — not worth the regression risk to touch.

## Aristotle
Nothing genuinely open → Aristotle correctly idle. The old Lemma-1 job (`80d9166c`) is
OBSOLETE (the proof needs no Lemma 1). Do not feed redundant cross-confirms. The verification
items 1–4 are all elementary and do NOT need Aristotle.

## Mills lane, phase 2 — COMPLETE (2026-09-27)

`src/LeanFormalizations/NumberTheory/Mills/` is **sorry-free and axiom-clean**.  Both phase-2
targets landed: `lower_bound_of_RH` (Caldwell–Cheng 2005 + `Schoenfeld1976`) and `irrational`
(Saito 2024 + `BakerHarmanPintz2001`/`Matomaki2007`/`Mahler1957`).  Every headline reports
`[propext, Classical.choice, Quot.sound]`.

Nothing is parked.  The literature `Prop`s in `Literature/Primes.lean` are the only remaining
debt, and discharging one (Schoenfeld under RH, BHP, Matomäki) is a research project in its own
right — a legitimate future lane, not a hole in this one.

## 2026-09-27 — Mills phase 6, lap 1: Saito Lemma 4.1 crux decomposed

`Mills/SaitoPisot.lean` (new). Attacked the route-decisive half of Saito Thm 1.5 first,
decoupled from the §3 `c`-generalisation grind: **`pisot_degree_bound`** is Saito's Claim
`(ℓ−1)·μ ≤ 1` for a Pisot `β` whose other-conjugate power sums decay like `β^(−μn)`.
It is PROVED from two named algebraic-number leaves. Proved along the way:
`le_of_pow_le_const_mul_pow` (Saito's "take k → ∞": `Mⁿ n^(−λ) ≤ K ρⁿ` ⇒ `M ≤ ρ`, via
`isLittleO_pow_const_const_pow_of_one_lt` after `n^λ ≤ n^⌈λ⌉₊`), `conjMax_pow_card_le`,
`Multiset.prod_le_pow_card_of_le`.

Open leaves (both standard ANT, neither Mills-specific):
1. `pisot_conjPowSum_add_mem_int` : `βⁿ + Σ_{j≥2} β_jⁿ ∈ ℤ` (trace of an algebraic integer).
   Route: `Algebra.trace_eq_sum_embeddings` over `ℚ⟮β⟯` + `Algebra.isIntegral_trace`.
2. `pisot_one_le_prod_norm` : `1 ≤ β·∏_{j≥2}|β_j|` = `|minpoly.coeff 0|` ≥ 1, via
   `minpoly.isIntegrallyClosed_eq_field_fractions` (ℚ-minpoly is the ℤ-minpoly mapped) and
   `prod_roots_eq_coeff_zero_of_monic_of_splits`.

**UPDATE (same lap): BOTH LEAVES PROVED.** `SaitoPisot.lean` is sorry-free and axiom-clean.
**Next attack**: the `b ≥ 5` arithmetic
(`μ = bθ_b ≥ 11/8 > 1`, `ℓ ≥ 2` ⇒ contradiction ⇒ Thm 1.1 modulo the §3 `c`-generalisation).
The §3 `c`-general Lemmas 3.5/3.6/3.8/3.9 (a known-shape generalisation of `Irrational.lean`)
are deliberately *later*: effort, not uncertainty.

### Same lap, later: the `c`-general §3 existence chain is DONE

* `Mills/BasicC.lean` — nested-interval construction for any `c ≥ 2`, sorry-free.
* `Mills/SaitoGeneral.lean` — `pow_succ_ge_add_mul` (binomial gap bound),
  `primeBetweenPows_of_BHP` (BHP ⇒ a prime in `(nᶜ,(n+1)ᶜ)` for `c ≥ 3`; the window fits because
  `21c/40 ≤ c−1` for `c ≥ 40/19`), `exists_millsC_of_BHP`, `exists_leastC_of_exists`
  (lower bound `2^(1/c)` replaces the hand-computed `5/4`), `exists_leastMillsC_of_BHP`.
* **`exists_minMillsC_of_BHP` is PROVED and axiom-clean** — the first of the three phase-6
  sorries is closed.

Remaining in `Mills/Transcendental.lean`: `transcendental_of_four_le`, `transcendental_or_pisot`.
Next attack: the `c`-general Saito Lemmas 3.5/3.6/3.8/3.9 supplying `pisot_degree_bound`'s
`hdecay` hypothesis (generalise `Irrational.lean`'s `mdigit`/`saito_lemma36/38/39`), then the
`b ≥ 5` arithmetic (`μ = bθ_b = 19c/40 − 1 ≥ 11/8 > 1` with `ℓ ≥ 2` contradicts the Claim).

### Same lap, later still: Saito Lemma 4.1 (case `μ > 1`) is COMPLETE

`Mills/SaitoLemma41.lean` — `transcendental_of_decay`, sorry-free and axiom-clean:

> If `A > 1`, `c ≥ 2`, `μ > 1`, `K > 0`, `|A^(cᵏ) − round(A^(cᵏ))| ≤ K·A^(−μcᵏ)` for all large
> `k`, and no `A^(cᵐ)` (`m ≥ 1`) is an integer, then `A` is transcendental.

Both branches of `Dubickas2022` are discharged: the separation branch by `ε := μ log A / 2`, the
Pisot branch by `pisot_degree_bound` + `card_otherConj_add_one` + `pisot_two_le_natDegree`.
Key design note: `le_of_pow_le_const_mul_pow` and `pisot_degree_bound` take `∃ᶠ`, not `∀ᶠ`,
because the decay for `β = A^(c^(m+1))` is only available along `n = c^j`.

**All that now separates Theorem 1.1 (`c ≥ 5`) from a proof is the §3 decay hypothesis**, i.e.
the `c`-general Saito Lemmas 3.5/3.6/3.8/3.9. For `c = 4` (and `c = 3`) one additionally needs
Lemmas 4.2/4.3, since there `μ = 19c/40 − 1 = 9/10 < 1` and the Claim only forces `ℓ = 2`.

**Next attack**: `c`-general Lemma 3.5 (`p_k^c < p_{k+1} < (p_k+1)^c − 1`) and Lemma 3.6
(minimality via Matomäki), generalising `Irrational.lean`. Lemma 3.6 is the long one.

### Same lap, final state: Theorem 1.1 for `c ≥ 5` reduced to ONE deep lemma

`Mills/SaitoDigits.lean` (new): `mdigitC`, Lemma 3.5 both halves, `le_add_rpow_of_pow_le`
(the (3.19) Bernoulli expansion), `decay_of_lemma36C`, `millsC_not_intCast`,
`transcendentalC_of_five_le`. All axiom-clean except for the one named `sorry`.

**The three remaining open obligations in `Mills/` are now exactly:**

1. `saito_lemma36C` (`SaitoDigits.lean:113`) — Saito Lemma 3.6 for general `c`, the Matomäki
   minimality step. The `c = 3` case IS proved (`saito_lemma36` in `Irrational.lean`, ~200
   lines); this is that argument with `3 → c` (`Rich`, `saito_lemma38`, `rich_chain`,
   `Chain.exists_shifted_of_chain` all generalise; Lemma 3.8's exponent `2/3` becomes `(c−1)/c`).
   **This is the whole remaining content of Theorem 1.1 for `c ≥ 5`.**
2. `transcendental_of_four_le`, the `c = 4` branch (`Transcendental.lean:70`) — needs Saito
   Lemmas 4.2 (`t_k = p_k`) and 4.3 (no degree-2 Pisot power), because there `μ = 9/10 < 1`
   and `pisot_degree_bound` only yields `ℓ = 2`. Lemma 4.3's `b = 4` case is the short one:
   `d_k` even ⇒ `β₂^(d_k) > 0` ⇒ `p_k = β₁^d + β₂^d > β₁^d = ξ^(C_k) ≥ p_k`.
3. `transcendental_or_pisot` (`Transcendental.lean:79`) — Theorem 1.2; same machinery at
   `c = 3` (`μ = 17/40`), where the Claim leaves `ℓ ∈ {2,3}` and Lemma 4.3's `b = 3` case
   (`p_k³ = p_{k+1} + 3x₁x₂p_k` ⇒ `p_k ∣ p_{k+1}`) kills `ℓ = 2`.

**Next attack**: item 2's Lemma 4.2/4.3 machinery (short, and shared by items 2 and 3), then
item 1 (long but mechanical).

### Same lap: THEOREM 1.1 IS COMPLETE (modulo `saito_lemma36C`)

`transcendental_of_four_le` is proved for **all** `c ≥ 4`. `#print axioms` shows `sorryAx`
solely from `saito_lemma36C`; every other ingredient is clean.

* `c ≥ 5`: `μ = 19c/40 − 1 > 1`, Lemma 4.1's Claim closes outright.
* `c = 4`: `μ = 9/10`, so the Claim forces `card (otherConj) = 1`, i.e. degree exactly 2 —
  killed by `not_pisot_two_of_even` (`Mills/SaitoDegreeTwo.lean`), axiom-clean.

The `c = 4` argument came out shorter than Saito's: **Lemma 4.2 is not needed as a separate
step.** With `n = cʲ` even, `wⁿ > 0`, so the integer `t = βⁿ + wⁿ` exceeds `βⁿ`, hence
`t ≥ ⌊βⁿ⌋ + 1` and `wⁿ = t − βⁿ > 1/2` as soon as `frac(βⁿ) < 1/2` — contradicting `|w| < 1`
directly. No `t_k = p_k` identification is required.
Also new and reusable: `exists_real_conj_of_natDegree_two` — a degree-2 Pisot number's other
conjugate is the *real* number `t₁ − β`, with no field theory (the `n = 1` trace over a
singleton multiset IS the conjugate), and `eventually_rpow_neg_lt`.

**Two obligations remain in `Mills/`:**
1. `saito_lemma36C` (`SaitoDigits.lean:114`) — general-`c` Matomäki minimality. Gates BOTH
   remaining items. The `c = 3` case is proved in `Irrational.lean`; this is `3 → c`.
2. `transcendental_or_pisot` (`Transcendental.lean:79`) — Theorem 1.2. At `c = 3`, `μ = 17/40`,
   so the Claim gives `card ≤ 40/17`, i.e. `card ∈ {1,2}` (degree 2 or 3). Degree 2 needs
   Lemma 4.3's `b = 3` case: `t_{3n} = t_n³ − 3(βw)ⁿ t_n` with `βw ∈ ℤ` gives `p_k ∣ p_{k+1}`,
   impossible for distinct primes. Degree 3 is Saito's open Remark 4.4 — it is the *disjunct*,
   so Theorem 1.2 needs only the degree-2 kill plus `IsPisot` + `natDegree = 3` extraction.
   **Prerequisite to add: `βw = (minpoly ℤ β).coeff 0 ∈ ℤ`** (extract from the proof of
   `pisot_one_le_prod_norm`, which already computes `Q.eval 0` both ways).

### 2026-09-27 — Mills phase 6 COMPLETE: Saito Theorems 1.1 and 1.2 are axiom-clean

`src/LeanFormalizations/NumberTheory/Mills/` is **sorry-free** again, and all three phase-6
headline theorems in `Mills/Transcendental.lean` report only
`[propext, Classical.choice, Quot.sound]`:

| theorem | content |
|---|---|
| `exists_minMillsC_of_BHP` | `ξ_c` exists for every integer `c ≥ 3` (Saito Cor 3.4) |
| `transcendental_of_four_le` | **Theorem 1.1**: `ξ_c` transcendental for every `c ≥ 4` |
| `transcendental_or_pisot` | **Theorem 1.2**: `ξ₃` transcendental, or some `ξ₃^(3^m)` is Pisot of degree 3 |

Two laps' worth of work, both landed here:

**`saito_lemma36C`** (Lemma 3.6 for general `c`) is proved, via two new sorry-free files:

* `ChainC.lean` — `exists_shifted_of_chainC`, `Chain.lean`'s shifted nested-interval engine for
  any `c ≥ 2`.
* `SaitoRich.lean` — `RichC`, the inner exponent `γ = 1 − 1/c` (`etaC`), and `saito_lemma38C`
  (Lemma 3.8 for general `c`).

The design point: at `c = 3` the inner Matomäki exponent and the outer window exponent coincide
(both `2/3`), so `Irrational.lean` could use one symbol.  Separating them is exactly what makes
the `c`-general lemma instantiable twice — at `η = 21/40` (window from Baker–Harman–Pintz) and at
`η = 1 − 1/c` (window from the previous chain step).  Since `2/3 − γ ≤ 0` for `c ≥ 3`, Matomäki's
count `D x^(2/3−γ)` collapses to the bare constant `D`.

Two elementary ingredients replaced the analytic estimates Saito leaves implicit:
`(1 + 1/(2c))^c ≤ 17/10` (from `1+t ≤ exp t` and `exp(1/2)² = e < 2.89`), which keeps the
window's `c`-th powers inside `[Xᶜ, 2Xᶜ]`; and `(u+1)ᶜ ≥ uᶜ + 2u^(c−1) + u^(c−2)` (split off
`(u+1)²` — no binomial theorem), which gives both the disjointness of the Matomäki windows and
the upper half of the chain condition.

**Theorem 1.2** then needed only Lemma 4.3 at `b = 3`, now `not_pisot_two_of_cube` in
`SaitoDegreeTwo.lean`.  The mechanism is the Dickson/Newton identity

    t_{3n} = t_n³ − 3 Pⁿ t_n,     t_n = βⁿ + wⁿ ∈ ℤ,  P = βw ∈ ℤ,

so `t_n ∣ t_{3n}`; along `n = 3ʲ` both are **digits of `A`**, hence primes, and
`t_{3n} > t_n³ > t_n` — a prime properly dividing a prime.  The missing prerequisite `βw ∈ ℤ` is
`pisot_two_prod_mem_int` (`βw = ∏(−root) = Q(0) = (minpoly ℤ β).coeff 0`, the same computation as
`pisot_one_le_prod_norm` but keeping the value instead of its modulus).  With `μ = 17/40` the
Claim gives `card ≤ 40/17 < 3`, so degree is 2 or 3; degree 2 dies, degree 3 *is* the disjunct
(Saito's open Remark 4.4).

Gotchas this lap: `gcongr` cannot discharge the `0 ≤ log(pᶜ)` side goal of a div-monotonicity
step — use `div_le_div_of_nonneg_right` with an explicit `Real.log_nonneg`.  `Nat.cast_sub` takes
`(R := ℝ)`, not `(α := ℝ)`.  A `set ... with h` does **not** fold occurrences created later by
`refine`, so re-`rw [← h]` before `omega`.  A transient `failed to open file ... .ir: Bad file
descriptor` from the mathlib build tree is spurious; rerun `lake build`.

## Phase 14 (2026-09-29): Mills transcendental under RH

- **`pisot_branch_otherConj_real` PROVED** (axiom-clean), i.e. Saito 2025 Thm 1.7's first half:
  in the Pisot branch the cubic Pisot number `β = A^(3^m)` has no complex pair of conjugates.
  Route actually used (all new, elementary, in `Mills/TranscendentalRH.lean`):
  1. `cube_re`: `Re(w³) = 4(Re w)³ − 3‖w‖²(Re w)` — the triple-angle formula with no trig, which
     turns the `×3` map on the circle into a *cubic recursion*.
  2. `eq_neg_one_of_triple_orbit`: `c_{j+1} = 4c_j³ − 3c_j`, all `c_j ∈ [−1,0)` ⟹ `c_0 = −1`.
     Mechanism: negativity forces `4c² > 3`, then `c+1 ↦ (c+1)(2c−1)²` with `(2c−1)² > 4`, so
     `c_j + 1 ≥ 4ʲ(c_0+1)` while `≤ 1`.  (Cleaner than the `mod 1` interval argument in the
     file header: no fractional parts, no `arg`.)
  3. `pair_pow_sum_re_neg`: trace = Mills prime (`eq_floor_of_abs_lt_half`) + Newton's cubic
     identity `p_k³ − p_{k+1} = 3s(x₁² + x₁s + x₂x₃)` ⟹ `s_i < 0` for all large `i`.
  4. `pisot_pow_two_of_pow_eq`: **the step the header left open.**  Once `u^N = v^N = y ∈ ℝ`,
     the *two* trace relations `β^N + 2y = t` and `β^{2N} + 2y² = T` give the explicit integer
     quadratic `3x² − 2tx + (t² − 2T) = 0` killed by `x = β^N`, so `deg β^N ≤ 2`; with
     `u^N ∈ otherConj(β^N)` that pins `deg = 2`, and `not_pisot_two_of_cube` (Saito 2024
     Lemma 4.3, already proved) finishes.  This *avoids* any Galois/embedding machinery
     (`range_eval_eq_rootSet_minpoly`, conjugate-transport of root sets) — worth remembering.

- **CLOSED (same lap): `transcendental_of_RH`.**  (Superseded text below kept for the route.)
  Both phase-14 theorems are proved and `#print axioms`-clean; `TranscendentalRH.lean` is
  sorry-free.  Final leaves: `digits_eq_gseq`, `gap_le_of_RH`, `real_case_contradiction`,
  `equal_norm_contradiction`.  Two notes worth keeping:
  * `equal_norm_contradiction` is *cheap*: equal moduli + real + distinct forces `v = −u`, and
    then `s_i = u^N + (−u)^N = 0` for the **odd** exponent `N = 3ⁱ`, contradicting `s_i < 0`
    straight from `pair_pow_sum_re_neg`.  No extra machinery at all.
  * `real_case_contradiction` works entirely with **squares** to dodge half-integer powers:
    `gap² ≥ (9/16)(‖u‖²)^N X⁴`, `gap² ≤ Y (log Y)⁴ ≤ X³ · 81 N⁴ L⁴`, divide by `X³` and fold
    `(‖u‖²)^N X = (β‖u‖²)^N ≥ ρ^N`.  Needs `set_option maxHeartbeats 1600000` and opaque
    `obtain`-introduced locals (not `set`) — `set`'s let-values blow the `isDefEq`/linarith
    budget in a context this large.

- **(superseded) the phase-14 crux: `transcendental_of_RH`.**  What remains is step 5, the real case:
  `|β₂| ≠ |β₃|`, `ρ = |β₂/β₃| > 1` ⟹ `p_{k+1} − p_k³ ≥ ρ^(N/2)·√(p_k³)`, against an RH gap
  bound.  **The missing prerequisite is a Schoenfeld-based least-prime-gap bound**, not yet in
  `Schoenfeld.lean`: `∃ C, ∀ y ≥ y₀, lpa y ≤ y + C·√y·(log y)²`.  Note the `log²`: with
  `g/log(y+g)` against error `√y log y/(8π)` on *each* side, `g ≍ √y log y` is **not** enough —
  one needs `g ≳ √y log²y/(4π)`.  That is still only polynomial in `N` (since
  `log p_k³ ≍ 3N log β`), so `ρ^(N/2)` beats it.  Next lap: prove that gap bound by the same
  route as `primeBetweenCubes_large`, then the `|β₂| ≠ |β₃|` dichotomy.

- **DONE (same lap): the gap bound.**  `exists_prime_short_interval` is proved: under
  `Schoenfeld1976 + RiemannHypothesis` there is a prime in `(y, y + √y (log y)²]` for every
  `y ≥ 41000`.  Helper `log_sq_le_sqrt` (`(log y)² ≤ √y` for `y ≥ 41000`, from
  `nine_log_sq_lt_sqrt` at `m = √y` plus `y^(1/4) ≥ 128/9`).  Margin is comfortable: main term
  `≥ √y log y / 2`, errors `≤ √y log y / (2π)`.
  **Next (the remaining crux of `transcendental_of_RH`):**
  1. `digits_eq_gseq`: for `A = minMills` under RH, `⌊A^(3^(k+1))⌋₊ = gseq k` — combine
     `gseq_le_digits` with `A ≤ A₀` from `exists_greedy_mills` + minimality.  Hence
     `p_{k+2} = lpa (p_{k+1}³)`, so `exists_prime_short_interval` caps the gap.
  2. `|u| ≠ |v|`: if `v = −u` then `s_N = 0` for odd `N = 3ⁱ`, contradicting
     `pair_pow_sum_re_neg` (`s_i < 0`).  So WLOG `|u| > |v|`, `ρ = |u|/|v| > 1`.
  3. Lower bound: `|s| ≥ |u|^N/2` for large `N`, and `|u|² ≥ ρ/β` from
     `pisot_one_le_prod_norm` (`β|u||v| ≥ 1`), so
     `gap = 3|s|(x₁² + x₁s + (uv)^N) ≥ (3/4) ρ^(N/2) β^(3N/2)`.
  4. Against step 5a's `√y log²y` at `y = p_k³ ≍ β^(3N)`: `ρ^(N/2)` exponential in `N` beats
     `(3N log β)²` polynomial.  Contradiction.


## Phase 16 (2026-09-29) — four/six exponentials: CLOSED, plus what it leaves behind

`NumberTheory/Transcendence/Exponentials.lean` is sorry-free and axiom-clean.  All six frozen
statements went through; **nothing was found underivable**.

**The one genuinely new idea** is the shape of "Schanuel ⇒ four exponentials", which is worth
keeping because it is not the case-analysis-on-dimension the textbooks sketch:

* `algebraicIndependent_of_exp_isAlgebraic` (reusable): Schanuel says *ℚ-linearly independent
  logarithms of algebraic numbers are algebraically independent* — apply Schanuel with `y = z`,
  since the exponentials are then already algebraic over `ℚ(z)`.  This is the only way Schanuel
  is used in the four-exponentials proof.
* `false_of_algebraicIndependent_mem` (reusable): **the rank obstruction.**  An algebraically
  independent family of `n` complex numbers cannot all lie in a field generated by fewer than
  `n` elements.  Encoded by handing it a *non-injective* `w : Fin n → ℂ`; the contradiction is
  that `algebraicIndependent_of_le_trdeg_adjoin w` would make `w` injective.  This replaces all
  the MvPolynomial coefficient-chasing the naive route needs.
* The proof is then four cases on how far `dim_ℚ span{λ_ij}` drops below 4.  In each case the
  relation `λ₀₀λ₁₁ = λ₀₁λ₁₀` puts one member of a maximal independent subfamily inside the
  *field* generated by the others (a single division — no polynomial identity), and the rank
  obstruction closes it.  The last case (`dim = 2`) is the only one needing a polynomial: `λ₀₁`
  becomes a root of a **monic** quadratic over `ℚ(λ₀₀)`, so `Monic.ne_zero` gives `≠ 0` for
  free.  Its degenerate sub-case (`λ₁₀ = α λ₀₀`) is killed by the linear independence of `x`,
  which is already packaged as `LinearIndependent ℚ ![λ₀₀, λ₁₀]` — no need to go back to `x`.

**Other reusable leaves:** `linearIndependent_const_mul` (scaling a ℚ-independent family by a
nonzero complex number), `ratCast_mem_adjoin`, `snoc3`/`snoc4` (`Fin.snoc v x = ![…]`, needed
to use `linearIndependent_finSnoc` to extract "the new element is in the span of the old"),
`transcendental_log_two`, `cexp_mul_ofReal_log` (`exp(t·log q) = q^t` across ℝ → ℂ),
`rpow_rat_pow_den`, `rat_eq_nat_of_prime_rpow` (one prime + unique factorisation already forces
a rational exponent to be a natural number — the three-primes hypothesis is only needed for the
*irrational* branch).

**Next attacks, in rough order of interest:**

1. **Sharpen the six-exponentials corollary to two primes.**  `eq_nat_of_three_primes_rpow`
   needs three primes only because the six exponentials *theorem* needs `y` of length 3.  With
   *four* exponentials (conjectural) two primes suffice; that statement is exactly what
   `FourExponentialsConjecture` buys, and it is one line from the existing proof.  Worth adding
   as a conditional companion.
2. **The strong four exponentials / sharp six exponentials conjecture.**  Its Schanuel
   derivation is the same rank obstruction with the algebraic-number "correction term"; a real
   test of whether the leaves above generalise.
3. **`e^e` and `π`, `e^π` and `e`, etc.** — more pairs from the same toolkit, cheap.
4. The Wright row of `Maze.lean` stays open (phase 15): every level `≥ 2` transcendental is
   consistent with every level sitting just above a prime.  Nothing in phase 16 moves it.


## Phase 17 (2026-09-29, same lap as 16) — `ExponentialsKnown.lean`: 3 of 4, and a real obstruction

Proved and axiom-clean: `two_three_five_rpow_transcendental` (unconditional: for irrational `t`
one of `2^t, 3^t, 5^t` is transcendental — the six-exponentials cousin of phase 16's
conditional two/three statement), `sixExponentials_of_shifted` (take every shift `β = 0`),
`sixExponentials_of_strong` (an algebraic `e^{xᵢyⱼ}` puts `xᵢyⱼ` in `LogAlgSpan` with `n = 1`,
`β = (0,1)`).

**`fiveExponentials_of_shifted` is a documented obstruction, not laziness.**  The reduction is
proved in full as `fiveExponentials_of_shifted_of_baker` (axiom-clean): apply the shifted six
exponentials theorem to `y = (y₀, y₁, γ/x₁)` with `β₁₂ = γ`, so the sixth exponential is
`e^{x₁·γ/x₁ − γ} = e⁰ = 1`.  The gap is the `ℚ`-linear independence of those three `y`, which
`FiveExponentials` does not supply; in the degenerate case `γ/x₁ ∈ span_ℚ{y₀,y₁}` the statement
*is* `BakerTwoLogs` — a nonzero algebraic number equal to a `ℚ`-linear combination of the two
logarithms `x₁y₀, x₁y₁`.  With one coefficient zero that is Hermite–Lindemann; with both nonzero
it is Baker's theorem on linear forms in two logarithms, strictly deeper than six exponentials.
`BakerTwoLogs` is defined in `ExponentialsKnown.lean` (not `Literature/`, which is frozen).

**UNBLOCKED CONDITIONALLY (same lap):** `bakerTwoLogs_of_schanuel` proves `BakerTwoLogs` from
Schanuel, so `fiveExponentials_of_shifted_of_schanuel` closes the five exponentials theorem from
the shifted six exponentials theorem + Schanuel.  Route: if the two logarithms are ℚ-linearly
independent, `algebraicIndependent_of_exp_isAlgebraic` makes them algebraically independent and
the relation `γ = r₀ℓ₀ + r₁ℓ₁` solves one of them out into the field generated by the other
(the same "solve out by a single division" move as the four-exponentials crux); if they are
ℚ-linearly dependent it collapses to `false_of_ratCast_smul_log`, which is Hermite–Lindemann
from Schanuel at the one-element family `z = (ℓ)`.  Only the **unconditional** form is still
open.

**Next:** the operator call is whether to add Baker to `Literature/` (then
`fiveExponentials_of_shifted` closes in one line from the reduction already proved), or to
restate the frozen `SixExponentialsShifted` with Waldschmidt's actual weaker independence
hypothesis.  Either is a one-line unblock; neither is this run's to make.  The fifth
bullet of the file header — a five-exponentials corollary — is now DONE, and the choice is worth
recording because the obvious candidates do not work.  `e^{π²}` and `2^{√2}` both come out as
*disjunctions already known by other means* (Gelfond gives `e^π`, Gelfond–Schneider gives
`2^{√2}`), so they are not new information.  What the five exponentials theorem actually buys
is a **special case of the four exponentials conjecture**: apply it with `x = (iπ, 1)` and
`γ = 1`, so its fifth number is `e^{γx₀/x₁} = e^{iπ} = −1`, algebraic, hence not the
transcendental one.  That leaves exactly the four numbers `e^{iπy₀}, e^{iπy₁}, e^{y₀}, e^{y₁}`
(`exists_transcendental_I_pi_row`).  The general recipe: the fifth number is killed whenever
`x₀/x₁` is a logarithm of an algebraic number divided by an algebraic `γ`.  Concrete
corollary at `y = (log 2, log 3)`: **one of `2^{iπ}`, `3^{iπ}` is transcendental**
(`two_or_three_cpow_I_pi`), unconditional.

### ⚠️ JUDGE-FLAG (2026-09-29): `Literature.StrongSixExponentials` is FALSE as stated

Found while setting up the Schanuel ⇒ Roy derivation below, and **machine-checked**:
`ExponentialsKnown.not_strongSixExponentials` (axiom-clean).  Roy's strong six exponentials
theorem requires `x` and `y` linearly independent over the field of **algebraic** numbers; the
frozen `Prop` asks only for `ℚ`-linear independence.  Witness: `x = (1, log 2)`,
`y = (1, √2, i)` are `ℚ`-linearly independent, but all six products `1, √2, i, log 2,
√2·log 2, i·log 2` lie in `𝓛̃` — the first three because `𝓛̃ ⊇ ℚ̄`, the last three because they
are `β·log 2` with `β` algebraic.  Over `ℚ̄` the triple `1, √2, i` is dependent, which is what
the real hypothesis excludes.

By-product proved on the way: `irrational_log_two`, **unconditionally** (`log 2 = num/den`
would make `e^num = 2^den`, so `e` would be a root of `X^num − 2^den`, against
`e_transcendental`).  Phase 16's `transcendental_log_two` needed Schanuel; this does not.

**Operator decision needed** (`Literature/` is frozen): change `StrongSixExponentials` (and, if
added later, any strong four exponentials) to take independence over `integralClosure ℚ ℂ`
rather than `ℚ`.  `sixExponentials_of_strong` remains a valid implication — its hypothesis is
now simply known to be unsatisfiable, so it carries no content until the `Prop` is fixed.
The same question should be asked of `FiveExponentials` and `SixExponentialsShifted`, which use
`ℚ`-independence too; there it is *correct* (those are not "strong" statements), but the
contrast is worth stating in `Literature/ExponentialsKnown.lean`'s docstring.

**Next (a genuine multi-lap target, now gated on the fix above): Schanuel ⇒ `StrongSixExponentials`.**  Roy's theorem from
Schanuel.  Sketch: choose a ℚ-basis `ℓ₁,…,ℓₙ` of the ℚ-span of all logarithms occurring in the
six `LogAlgSpan` witnesses; Schanuel (`algebraicIndependent_of_exp_isAlgebraic`) makes them
algebraically independent over ℚ, and `AlgebraicIndependent.extendScalars` upgrades that to
ℚ̄, so `ℚ̄[ℓ₁,…,ℓₙ]` is a genuine polynomial ring.  Each `xᵢyⱼ` is then a ℚ̄-linear form in the
`ℓ`, the relation `λ₀₀λ₁₁ = λ₀₁λ₁₀` is an identity between degree-≤2 polynomials, and UFD
factorisation of a product of linear forms forces the rank-1 shape that contradicts the
ℚ̄-linear independence of `x` and `y`.  Decompose into named leaves: (1) the basis-of-logs
reduction, (2) `extendScalars` to ℚ̄, (3) the polynomial-ring rank-1 lemma.  Step (3) is the
only one with real content and should be attacked first.  **Note the refutation above is
exactly what the naive degree count predicts**: with only `ℚ`-independence, `λ = 1`, `s = √2`,
`r = log 2` makes `λ, λs, λr, λrs` all of degree ≤ 1 in the logarithms, so no contradiction is
available; the ℚ̄-independence hypothesis is what forces a degree-2 term and kills it.

## Phase 26 (2026-09-29): Leopoldt stress tests — DONE; stretch recorded as blocked

`NumberTheory/Leopoldt/StressTests.lean` and `NumberTheory/Transcendence/SharpSixVariants.lean`
are sorry-free; `leopoldt_of_rank_zero`, `not_leopoldtNoIndep_rat`, `shiftedAlg_of_sharp`,
`witness_not_algIndep` all `#print axioms`-clean (`propext/choice/Quot.sound` only).

**No counterexample.**  The Leopoldt statement survived both tests, so the ~75% faithfulness
argument in `Literature/Leopoldt.lean` stands unrefuted.  Two facts learned:
- the rank-0 positive test is *degenerate* — the multiplicative-independence hypothesis forces
  `r = 0` outright (via `isOfFinOrder_of_rank_zero`, Dirichlet with an empty fundamental system),
  so it tests only that the statement is not accidentally false, not that it says anything.
- the negative test is sharp: `ε = −1, mₙ ≡ 2, a = 2` over `ℚ` kills `LeopoldtNoIndep` for
  *every* prime `p`, so the independence clause is load-bearing.

**Stretch (real quadratic, unit rank 1) is BLOCKED on missing mathlib infrastructure, not on
mathematics.**  It reduces to: `ε` the fundamental unit of `ℚ(√2)`, `mₙ → a` in `ℤ_7`,
`ε^{mₙ} → 1` in `K_v` ⟹ `a = 0`.  The only known routes need the ℤ_p-module structure of the
principal units `U₁ ⊂ (v.adicCompletion K)ˣ` — either the p-adic logarithm (`log_p ε ≠ 0`,
i.e. Baker/Brumer in the rank-1 case) or `U₁ ≅ μ × ℤ_p^d` torsion-freeness.  At our pin mathlib
has NEITHER: `Mathlib/NumberTheory/Padics/` has no `padicLog`, and there is no development of the
unit group of `HeightOneSpectrum.adicCompletion`.  Next attack, in order:
1. the `ℤ_p`-action `ℤ_p × U₁ → U₁` by continuity from `ℤ`-powers (needs `U₁` complete + the
   `ε^{m} ≡ ε^{m'} mod p^k` congruence);
2. torsion-freeness of `U₁` for `p` odd and unramified, via `(1+x)^p = 1 + px + … ` valuation;
3. only then the rank-1 Leopoldt statement.
This is a multi-lap infrastructure build and was explicitly "not frozen" in the phase-26 directive.


## Phase 27 (2026-09-29): Leopoldt in unit rank ≤ 1 — DONE; the rank-2 wall located

`NumberTheory/Leopoldt/RankOne.lean` is sorry-free; `rank_cyclotomic_eight` and
`leopoldt_cyclotomic_eight_seven` are `#print axioms`-clean.  The phase-26 "blocked on missing
mathlib infrastructure" verdict was **wrong**: neither the `ℤ_p`-action on `U⁽¹⁾` nor a `p`-adic
logarithm is needed in rank `≤ 1`.  What landed instead, in
`NumberTheory/Leopoldt/PrincipalUnits.lean`:

- `valuation_zpow_sub_one` — on a principal unit at `v` (`W (θ−1) < 1`), an exponent prime to the
  residue characteristic leaves `W (θ − 1)` **exactly** unchanged.  This is the whole engine.
- `exists_principal_exponent` — `N = card (𝓞 K ⧸ v)ˣ` is prime to `p` (Cauchy + freshman's dream
  in a finite domain of char `p`) and makes any unit principal.  Since `N` is a `ℤ_p`-unit,
  proving `N·a = 0` suffices, so the header's residue-class subsequence is avoidable.
- `eq_zero_of_local_tendsto_one` — the rank-one local obstruction, unconditional in `K` and `p`.
- `card_le_rank`, `exists_prime_above`, `leopoldt_of_rank_le_one`.

**Where the wall actually is.**  For `r ≥ 2` the local argument fails for a structural reason
worth recording: it bounds the `p`-part of *one* exponent, while a relation among `r` units mixes
the `p`-parts.  There is no valuation-only substitute — the statement for `r ≥ 2` really does
imply `ℚ_p`-linear independence of `p`-adic logarithms, i.e. Baker–Brumer.  Next attack, in
order: (1) `padicLog` on the principal units of `v.adicCompletion K` (the only step with real
content), (2) Brumer's `p`-adic Baker theorem as a `Literature/` axiom with a faithfulness
argument, (3) rank-2 Leopoldt for ℚ(ζ₇) from it.

### Phase 28 step (1) started (2026-09-29, same lap)

`PrincipalUnits.lean` now has the **exact** filtration formula, which is what `padicLog` and
genuine torsion-freeness need (`valuation_pow_sub_one_le` only gave the inequality):

- `valuation_pow_char_sub_one` — for `θ` principal at `v` and `p` the residue characteristic,
  `W (θ^p − 1) = max (W p · W (θ−1)) (W (θ−1)^p)` **whenever those two differ**.  Proof: the
  binomial decomposition `θ^p − 1 = p·x + B + x^p` with `B = ∑_{2 ≤ k ≤ p−1} C(p,k) x^k`; every
  `C(p,k)` there is divisible by `p`, so `W B ≤ W p · W x² < W p · W x`, and the two extremes are
  distinguished exactly by the hypothesis.
- `pow_char_ne_one_of_principal` — hence no `p`-torsion in `U⁽¹⁾` away from the tie
  `W p = W (θ−1)^(p−1)`.

**The tie is not an artefact.**  `θ = −1` in `ℚ₂` has `ν(θ−1) = 1 = ν(2)` and `(p−1)·1 = 1`, and
it *is* a genuine `2`-torsion element of `U⁽¹⁾`.  So the hypothesis is sharp; it is automatic for
`p` odd at an unramified `v` (`ν p = 1`, `ν x ≥ 1`, `1 = (p−1)ν x` impossible).

### Phase 28 step (2) DONE (2026-09-29, same lap): the deep regime

The iteration does **not** need unramifiedness — it needs only that `θ` sit *above* the tie, which
is the classical `log`/`exp` convergence range `ν x > e/(p−1)` and is **self-propagating**:

- `valuation_pow_pow_char_sub_one` — if `W (θ−1)^(p−1) < W p` then for every `j`,
  `W (θ^(p^j) − 1) = W p ^ j · W (θ − 1)`.  Exact, all `j`, any `p`, any ramification.
- `pow_pow_char_ne_one_of_deep` — hence `U^(m)` for `m > e/(p−1)` is genuinely **torsion-free**
  (one of the two things the phase-26 plan wanted), and `θ^(p^j) → 1` at the *known* rate
  `W p ^ j`, which is the quantitative input `padicLog` needs.

Why the deep condition propagates: if `W x^(p−1) < W p` then `W x' = W p · W x` and
`W x'^(p−1) = W p^(p−1) W x^(p−1) < W p^(p−1) · W p ≤ W p`, using `W p ≤ 1`.  The `x^p` binomial
term is then dominated by `p·x` at every level, so the tie never recurs and the max in
`valuation_pow_char_sub_one` is always the left one.

### Phase 28 step (3a) DONE (2026-09-29, same lap): the Cauchy estimate

- `valuation_zpow_sub_one_le` — the `ℤ`-exponent version of `valuation_pow_sub_one_le`.
- `valuation_zpow_sub_one_le_of_dvd` — on a deep `θ`, `p^j ∣ m` gives
  `W (θ^m − 1) ≤ W p ^ j · W (θ − 1)`.
- `valuation_zpow_sub_zpow_le` — **the uniform continuity of `k ↦ θ^k`**: `p^j ∣ k − l` gives
  `W (θ^k − θ^l) ≤ W p ^ j · W (θ − 1)`.  Via the factorisation `θ^k − θ^l = θ^l (θ^{k−l} − 1)`
  and `W (θ^l) = 1`.

All in `K`, no completeness used, all axiom-clean.

**Next leaf (step 3b) — the extension itself.**  `valuation_zpow_sub_zpow_le` says
`k ↦ algebraMap K (v.adicCompletion K) (θ^k)` is uniformly continuous for the `p`-adic uniformity
on `ℤ`; `v.adicCompletion K` is complete, so it extends to `zpowExtend θ : ℤ_[p] → (v.adicCompletion K)`.
Shape of the build: (1) show the map is Cauchy along any `ℤ`-sequence converging in `ℤ_[p]`
(the estimate gives it directly, since `‖(k : ℤ_[p]) − l‖ ≤ p^{-j}` iff `p^j ∣ k − l` by
`PadicInt.norm_int_le_pow_iff_dvd`), (2) define the extension by `CauSeq`/`UniformSpace.Completion`
or, more cheaply, by `DenseInducing.extend` from `ℤ` dense in `ℤ_[p]`, (3) `map_mul` and continuity
transfer, (4) injectivity from `pow_pow_char_ne_one_of_deep`.  Then `padicLog` (or in fact the
`ℤ_p`-module structure alone, which is all Ax's reduction needs) and Brumer.

Note the rank-≤1 theorem needs **none** of this — steps 1–3 are pure phase-28 (rank ≥ 2) machinery.

### Phase 28 step (4) (2026-09-29, same lap): the rank-≥2 wall is a residue-field cancellation

Two new axiom-clean lemmas in `PrincipalUnits.lean` give the tool that reaches past rank 1:

- `valuation_prod_one_add_sub_one_lt` — a product of principal units `∏ (1 + xᵢ)` stays strictly
  inside any ball `W · < c ≤ 1` containing all the `xᵢ`.
- `valuation_prod_one_add_sub_one` — **the leading term survives**: if `W (x i₀)` is strictly the
  largest (additively, `ν xᵢ₀` strictly the smallest), then `W (∏ (1 + xᵢ) − 1) = W (x i₀)`
  *exactly*, because every cross term `xᵢxⱼ` is strictly smaller.

**What this settles about the wall.**  Put `θᵢ = εᵢ^N`, deep, with levels `tᵢ = ν(θᵢ − 1)`.  By the
step-2 exact growth plus the prime-to-`p` invariance of step 1,
`ν(θᵢ^{mᵢ} − 1) = tᵢ + v_p(mᵢ)·e` **exactly**.  If `aᵢ ≠ 0` then `v_p(mₙᵢ) = v_p(aᵢ)` eventually;
if `aᵢ = 0` then `v_p(mₙᵢ) → ∞`.  So eventually the minimum of the levels is attained inside
`S = {i : aᵢ ≠ 0}` at the fixed value `M = min_{i∈S} (tᵢ + v_p(aᵢ)·e)`.  **If that minimum is
uniquely attained**, `valuation_prod_one_add_sub_one` gives
`ν(∏ θᵢ^{mₙᵢ} − 1) = M` for all large `n` — a fixed finite value, contradicting `→ 1`.  Hence
Leopoldt holds for every `r` whenever the minimum is unique.

So the **entire** remaining content of Leopoldt is the *tie* case: two or more leading terms at the
same level `M`, whose residue-field leading coefficients may cancel, letting `ν` jump.  That is
exactly the linear-forms-in-`p`-adic-logarithms problem, i.e. Baker/Brumer.  **The wall is a
residue-field cancellation problem, not a missing construction** — which is worth knowing, because
it means no amount of further valuation-theoretic infrastructure will close it.

### Phase 28 step (5) DONE (2026-09-29, same lap): Leopoldt's mechanism at arbitrary rank

Three more axiom-clean lemmas; the arbitrary-rank theorem is now **proved** modulo the tie.

- `false_of_tendsto_one_of_valuation_ge` — the topology endgame, factored out: if `f n → 1` in
  `K_v` then `W (f n − 1)` cannot stay `≥` a fixed nonzero value.  (Reusable; the rank-1 proof has
  the same block inline.)
- `valuation_zpow_sub_one_eq` — **the exact level formula**: on a deep principal unit, splitting
  `m = p^j · t` with `p ∤ t`, `W (θ^m − 1) = W p ^ j · W (θ − 1)` exactly, with **no dependence on
  `t`**.  (Step 2 for the `p`-part, step 1's prime-to-`p` invariance for the rest.)
- `false_of_unique_leading_level` — **arbitrary `r`**: if the exponents are in split form
  `m n i = p^(j i) · t n i` with the `p`-part `j i` *fixed in `n`*, all `θ i` deep principal and
  `≠ 1`, and the leading level `W p ^ (j i) · W (θ i − 1)` is *uniquely* maximised at `i₀`, then
  `∏ θ i ^ (m n i) → 1` is impossible.

So the valuation-theoretic side of Leopoldt is **complete at every rank**.  Exactly two gaps
remain, and both are bookkeeping-or-Baker, not construction:

1. *(bookkeeping, tractable)* deriving the split form from the real hypotheses: `a i ≠ 0` makes
   `v_p(m n i)` eventually constant `= v_p(a i)` (this is already done for `r = 1` inside
   `eq_zero_of_local_tendsto_one`), and `a i = 0` makes `v_p(m n i) → ∞` so those indices
   eventually leave the leading level.  Needs a `Fin r`-indexed "eventually" intersection and a
   `PadicInt` valuation function; then `false_of_unique_leading_level` applies verbatim.
2. *(the wall)* the **tie**: two or more indices realising the same leading level.  Then the
   leading coefficients live in the residue field and can cancel, letting `ν` jump — which is
   precisely a nonvanishing statement for a linear form in `p`-adic logarithms, i.e. Baker/Brumer.
   Nothing in the valuation calculus can decide it; it must be imported as a `Literature/`
   statement.

**Next leaf**: gap (1) — `leopoldt_of_unique_level` in terms of `a`, i.e. replace the split-form
hypothesis by `∀ i, a i ≠ 0 → (unique leading level)`.  Then gap (2) as `Literature/Brumer.lean`.

---

## ⚠️ Operator note on the phase-28 "tie" (2026-09-29, Ren)

The phase-28 handoff proposes importing Brumer (the p-adic Baker theorem) as `Literature/Brumer.lean` to close the rank ≥ 2 tie.  **That does not close general Leopoldt.**
- Brumer (1967) gives `ℚ̄`-linear independence of `ℚ`-independent p-adic logarithms of algebraic numbers, i.e. linear forms with *algebraic* coefficients.
- Leopoldt's kernel condition is a linear form with arbitrary `ℤ_p` coefficients `a`.
- In the abelian case the p-adic regulator factors (a Frobenius group determinant) into forms with algebraic coefficients, which is Ax's 1965 reduction.  That is the *only* reason Brumer proves the abelian case.
- So the tie at rank ≥ 2 **is** the open conjecture.  A `Literature/Brumer.lean` would give general rank-≥2 Leopoldt only via a false implication.

What is honest and tractable:
- **Specific (K, p) instances by certificate.**  Leopoldt at a given `(K, p)` is certified by a finite computation: choose a unit basis whose local images have *separated* leading levels after a unimodular change of basis, then apply `false_of_unique_leading_level`.  A rank-2 instance, e.g. `ℚ(ζ₇)` or a totally real cubic at a small prime, is a finite, checkable test.
- **The abelian theorem** as a Literature statement (Ax 1965 + Brumer 1967: Leopoldt holds for abelian `K/ℚ`), stated directly, with no fake derivation through the tie.

Status: statement validated nontrivially (`leopoldt_of_rank_le_one`, all K, all p).  Leopoldt work is paused here pending Trevor's call.

## Phase 41 (CoveringEngine.lean) — CLOSED 2026-09-30 (`be4d97a`)
All four frozen statements proved, file sorry-free, axiom-clean.  Notes for the next lap:
* The route's suggested Gauss-type descent `V(c^(k+1)) ≡ V(c^k) (mod c^(k+1))` was **not needed**:
  `lucasV_mul_odd` at `m = c^n` gives the exact composition `V(c^(n+d)) = V_(c^d)(V(c^n))`, and
  `lucasV_neg_one_growth` applies verbatim with `c` replaced by `c^d` (it only ever used
  *odd and ≥ 3*).  The single-index certificate closes in one comparison.
* `covering_of_mech` is the assembly with the `glCard 2` hard-coding removed (abstract predicate
  `G : ℕ → ℕ → Prop`); `dvd_linearMap_of_entries` is what lets entries and the trace share one
  proof.  Both are ready for roadmap §1 Theorems A and B — only the certificate is missing there.
* `DIRECTION.md` still lists phase 41 as CURRENT; an altitude lap owns marking it DONE.

## 2026-10-01 — Erdős #385 E1 DONE
`Erdos385/Rigidity.lean` sorry-free, axiom-clean (Lemma R by strong induction over primes; R′ small
case `n < y+2` via Lemma R at `y' = n−2` + Bertrand ⇒ `n = 2p`, pair `(p, p)`).  Next: E1b
(`FunctionField.lean`, `Graph.lean` edges), then E2 `card_bad_le`, then plant E3.

## 2026-10-01 Erdős #385 E1b (FunctionField half) DONE
`FunctionField.lean` sorry-free, axiom-clean: degeneracy finding (`T^q − T ∣ f` for bad `f`),
`ffGood_of_natDegree_lt_card`, and the BBR wiring edge `ffWitness_of_BBR` (count ≥ 2 via
`q^{m+1} = q^{m+1/2}·√q`; coefficient-injectivity picks a shift with `g ≠ f`).
Next: `Graph.lean` edges (`noCarrier_of_bad`, repulsion ⇒ (i), FGKMT ⇒ sieve sibling), then E2 `Count.lean`.

## 2026-10-01 Erdős #385 E2b DONE — `BrunUniformGap` discharged
`brunUniformGap_holds` axiom-clean (C = 20000), so `card_bad_le` is now unconditional via
`card_bad_le brunUniformGap_holds`.  Files `Erdos385/Brun/{GLower,Density,Selberg,PairSieve}.lean`:
Selberg Λ² with optimal weights on top of mathlib's `SelbergSieve` scaffolding.  Reusable ideas:
- G(z) lower bound without Euler products: `g(p) ≥ g₁(p)+g₂(p)` ⇒ `g ≥ g₁*g₂` on squarefree, then
  decouple coprimality with `∑_{a∈S} F ≤ (∑_{d∣m sqfree} F d)·∑_{(a,m)=1} F` (costs `m/φ(m)`),
  and `∑_{a≤t sqfree} 1/a ≥ log t / 2` via `n = b²a`.
- |w_d| ≤ g(d)/ν(d) ≤ d crude bound suffices with level y², y = t², t = ⌊X^{1/16}⌋ (error ≤ y⁶).

## 2026-10-01 E2c DONE
Discharge.lean sorry-free, axiom-clean (see HANDOFF-2026-10-01-erdos385-E2c-discharge-complete.md).
Reusable: positivity of the Fejér transform is NOT needed — only `|J| ≤ min(T, 1/(Tλ²))`
plus pointwise `w ≥ 1_{[0,T]}`; the single row weight `2TN²/(T²k²+N²)` absorbs the min.

## 2026-10-01 E2d lap 1 — Plancherel crux CLOSED
`Erdos385/Parseval/Plancherel.lean`: `plancherel_lintegral` (∫⁻‖𝓕f‖ₑ² = ∫⁻‖f‖ₑ² for f integrable,
bounded, a.e. continuous), axiom-clean.  Gaussian regularization + multiplication formula
(`integral_sesq_fourierIntegral_eq_neg_flip`) + `Real.tendsto_integral_gaussian_smul'`.
Route decision (refines header): SHARP bands are fine — every function Plancherel is applied to is
bounded/integrable/a.e.-continuous: Φ itself, F_lo = Φ̂·1_lo, F_mid = A·1_mid.  The high part needs
no integrability of Φ_hi: ‖Φ−P‖² = ‖Φ‖² − 2Re⟨Φ,P⟩ + ‖P‖² with P = 𝓕⁻(Φ̂·1_{|ξ|≤T₁}) and
⟨Φ,P⟩ = ∫|Φ̂|²1 (multiplication formula), giving ∫|Φ̂|²1_hi.  No convolution, no kernels.
Next: Φ and 𝓕Φ = A(1+2πiξ)/(1+2πiξ); a.e. identity for shortSumC; low/mid/high bounds.

## 2026-10-01 E2d DONE — `mr16Lemma14_holds` proved, axiom-clean (C = 500)
`Erdos385/Parseval/Assembly.lean` (`mr16_core`) assembles the bands: a.e. identity
shortSumC = winDelta Φ off ℕ; Φ = P_lo + P_mid + Φ_hi with Φ_hi := Φ − P_lo − P_mid (so the
split is `ring`, only P_lo+P_mid = 𝓕⁻(1_all 𝓕Φ) needs 𝓕⁻-additivity via
`VectorFourier.fourierIntegral_add`); ‖u+v+w‖² ≤ 3Σ in ENNReal; lo ≤ 9/T₀ pointwise, mid via
`integral_winDif_mid_le` + `t = 2πξ` change of variables, hi via `integral_norm_sub_proj` +
`integral_tail_le` (lintegral change of variables through `Real.map_volume_mul_left`).
Band-indicator a.e. continuity: `ae_continuousAt_indicator` (locally constant off a null set).
Next: remaining lit inputs of `almost_all_F385`: `MontgomeryVaughanMVT`, `VKZeroFreeLogDeriv`,
`MediumPNTStatement` (wire PNT+ `MediumPNT`).
## Erdős #385 E3 (2026-10-01): headline wired; leaves W3d/e/f + VK edge + VK control open
See HANDOFF-2026-10-01-erdos385-E3-W3-assembled.md.  Next attack: W3e/W3f (MVT), then W3d, then VK edge.

## Erdős #385 E3 crux (2026-10-01): `smoothPrimeSumVK_of_VKZ` decomposed
Edge now PROVED from three named leaves in `AlmostAll.lean` (all other AlmostAll sorries closed this lap:
W3d/W3e/W3f + control 3d).  Proved helpers: `xDeriv`, `mellin_xDeriv` (M[xf'] = −s M[f]),
`mellin_strip_bound`, **`mellin_strip_decay`** (‖s‖^k |F(s)| bounded on strips, by induction via xDeriv),
`exists_support_Icc`.  Open leaves:
- V6 `smoothTwist_smallP` (aP<1: finite sum, all O(1)) — easy.
- V4 `smoothTwist_sub_main_eq` (Perron at Re s = 2 minus main term, H = ζ'/ζ + 1/(w−1)) — moderate:
  `mellinInv_mellin_eq`, Fubini, `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, ∫_1^∞ x^{-s-it}.
- V5 `vertical_integral_bound` (contour shift under VK) — THE crux.  Next: split into
  (i) H(·) holomorphic on VK rectangle (removable sing. at 1 via boundedness from hypothesis,
  `Complex.differentiableOn_update_limUnder_of_bddAbove`), (ii) rectangle identity
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), (iii) left side / horizontals / tails
  bounds via `mellin_strip_decay` k=3, (iv) width comparison c₀/(L^{2/3}(log L)^{1/3}) ≥ L^{−2/3−ε}.
- 2026-10-01 later: **V5 `vertical_integral_bound` PROVED** (contour shift via `rect_shift_norm` on
  F(s)P^s·Ĥ(s+it), Ĥ = removable-singularity update of zetaH at 1; tails via k=4 decay; left side
  P^{σ₁} ≤ P e via `vk_width_eventually`; bounded T via trivial P² bound).  Remaining: V4, V6.

## Erdős #385 E3 DONE (2026-10-01, review lap, `e819725`)
`AlmostAll.lean` sorry-free; `almost_all_F385` = trust base + 4 literature Props.  V4 closed by
`twist_inversion` + `smoothTwist_eq_vertical` (Fubini via `integral_tsum_of_summable_integral_norm`,
dominated by `‖term Λ 2 n‖ · P² ∫‖F(2+iy)‖`) + `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
Remaining Erdős-385 open items (outside E3 scope): the five Literature controls `not_…` in
`Literature/Erdos385AlmostAll.lean` (teeth tests: each refutes a wrong transcription), and E4
(paper only).  Discharge candidates for the 🟡 hypotheses: `MediumPNTStatement` from PNT+ `MediumPNT`
(olean unbuilt at this pin); `MontgomeryVaughanMVT` (Hilbert inequality, elementary but long).


## Erdős #385 E3c DONE (2026-10-01)
`Erdos385/Rate.lean` sorry-free: `almost_all_F385_rate` (count ≤ C X exp(−c (log X)^{1/10})) =
trust base + the same 4 literature Props.  Mechanism: `card_le_of_windows` (covering count with
N₀ uniform in E and η), apply it to E ∩ [2√X, ∞) where every window Z ≥ √X has the single rate
η = A exp(−c'(log √X)^{1/10}); head n < 2√X absorbed by `sqrt_le_rate`.  Next: exponent 1/3−ε
needs Vinogradov–Korobov-strength long average (new phase), or the Literature `not_…` controls.

## E2e lap 1 (2026-10-01)
Landau.lean: both frozen statements now proved modulo two named halves —
`vk_large_height` (crux: Landau's method from Richert) and `vk_small_height` (compactness,
unconditional).  Gluing (vkW antitone, constants) proved.  PNT+ check: `FinalBound`
(local zero-sum formula for f'/f from Borel–Carathéodory) is sorry-free and generic; its
`ZeroInequality` (classical region) IS sorried — so the 3-4-1 argument must be built here.
Next: split `vk_large_height` into (a) growth `|ζ| ≤ (log t)^K` on σ ≥ 1−θ(t), (b) rescaled
FinalBound for ζ at centre 1+θ+it, (c) 3-4-1 zero-free, (d) log-deriv bound.

## E2e lap 2 (2026-10-01)
`vk_large_height` PROVED from five named interfaces in `Erdos385/Landau/Basic.lean`:
`vk_asymp` (elementary asymptotics), `logDeriv_zeta_dirichlet_bound` (D3),
`three_four_one` (D2), `landau_neg_re_upper` (Z1), `landau_logderiv_bound` (Z2).
`Landau/ZeroFree.lean` (sorry-free modulo those): `vk_zero_free` (3-4-1 ⇒ β < 1 − c·vkW|γ|,
c = 3/(104(1+6K))) and `vk_large_height_of`.  Remaining crux = Z1/Z2 (FinalBound rescaled for ζ
at centre 1+θ+it, radius 2θ; growth via Richert + PNT+ ZetaUpperBnd; lower via ZetaLowerBound3).
Plus `vk_small_height` (PNT+ ZetaNoZerosInBox + riemannZetaLogDerivResidue + compactness).
- lap 3: `Landau/Local.lean` `local_landau` PROVED (FinalBound+ZerosBound rescaled to any disc;
  multiplicities ≥ 1 via finiteness).  Interfaces adjusted: zero ball 15/8·θ, Z2 needs σ ≥ 1−θ/4,
  disc = closedBall(1+θ+it, 3θ).  Next: Zeta.lean deriving Z1/Z2 from local_landau + growth
  (Richert + ZetaUpperBnd) + lower (ZetaLowerBound3) + finiteness of ζ-zeros in a disc.
- lap 4: `Landau/Zeta.lean`: `zeta_local`, Z1, Z2 PROVED from `local_landau` + 3 leaves.
  Open leaves now (7): Zeta.lean `zeta_zeros_finite`, `zeta_disc_growth` (Richert+ZetaUpperBnd),
  `zeta_center_lower` (ZetaLowerBound3); Basic.lean `vk_asymp`, D3, D2; Landau.lean `vk_small_height`.
  Everything left is classical/elementary — the Landau crux itself is assembled.
- E2e DONE 2026-10-01: Landau.lean sorry-free + axiom-clean (see HANDOFF-2026-10-01-erdos385-E2e-done.md).

## E9 (2026-10-01, erdos-385-c): Hyperbola.lean DONE; PowerSaving reduced to the per-window crux
`almost_all_F385_powerSaving` ⇐ `badWindowPowerSaving_of_lit` (sorry, the near/far split) via
`PowerSaving/Assembly.lean` `almost_all_of_badWindowPowerSaving` (proved). `badCount_powerSaving` proved.
Next attack: decompose `badWindowPowerSaving_of_lit` along `Gen.badWindow_rate`: (i) `card_badWindow_le`
reuse with T₀ = Z^{c₀}; (ii) long average via ShortIntervalPrimesLower; (iii) far mean square;
(iv) near pointwise via NearOneLargeValues. Also `nearOneLargeValues_of_density` open.
- (later, same day) `badWindowPowerSaving_of_lit` PROVED from two named leaves via
  `PowerSaving/Split.lean` `badWindowPowerSaving_of_leaves` + `PowerSaving/Window.lean`
  `card_badWindow_le_of_split` (W2 against an arbitrary majorant G). Open leaves (PowerSaving.lean):
  `longAveragePower_of_lit` (ShortIntervalPrimesLower ⇒ long avg ≥ c₁δ/log²Z at H = X/Z^{3c₀}),
  `differenceSplit_of_lit` (D within 1/log³Z of D_far, ∫D_far² ≤ C X Z^{−c}), `nearOneLargeValues_of_density`.
  Next: longAveragePower (copy Gen.longAverage_lower/qcount_lower with power-scale H).
- Step 1 `longAveragePower_of_lit` PROVED axiom-clean (PowerSaving/{LongAverage,Primes,LongAveragePower}.lean:
  free-h₂ copy of the W2′ double count + greedy tiling of (y,y+H] by (t,t+t^e]). Hyperbola.lean axiom-clean.
  Remaining: `differenceSplit_of_lit` (crux), `nearOneLargeValues_of_density`.
- Step 2 route FIXED in Lean (2026-10-01): near set = finite union of intervals Icc(s−r,s+r) around a
  1-separated large-value set S (from NearOneLargeValues). D_far := D − Re winDif(𝓕⁻(1_E F)).
  * `Parseval.norm_winDif_fourierInv_le` (PowerSaving/Near.lean) PROVED: |D_near(x)| ≤ 2∫_E|Â|.
  * `Parseval.mr16_masked` (PowerSaving/Masked.lean) sorry 85%: rerun mr16_core with masked mid/tail.
  * Still to state: coeffA-level analytic inputs — (i) ∫_E|Â| ≤ 1/(4 log³Z) [NearOneLargeValues +
    VK η_min]; (ii) mid∖E and block integrals ≤ C Z^{−c} [|P| ≤ Z^{−η₀/2} off E + MVT for Q; T>4X
    via coeffC_meanSquare]; then assemble DifferenceSplit. Insight: near part only needs
    exp(−(log Z)^{1/3}) pointwise (≪ μ/2), far part gets the power saving in mean square.
- `Parseval.mr16_masked` PROVED axiom-clean (PowerSaving/Masked.lean). Remaining for step 2: the
  coeffA-level inputs (near integral ∫_E|Â| small; masked mid/blocks ≤ C Z^{−c}) + DifferenceSplit
  assembly (D_far := D − Re winDif(𝓕⁻(1_E F)), real/complex bridge via coeffC, a.e. x ∉ ℕ).
- `Parseval.far_split` (PowerSaving/Bridge.lean) PROVED axiom-clean: D = D_far + D_near for real coeffs, |D_near| ≤ ∫_{Et}|A|, ∫D_far² ≤ 500X(1/T₀+M_masked+B). Left: coeffA analytic inputs (NearFarInput) + DifferenceSplit wiring.
- E9 HEADLINE DONE 2026-10-01: `largeValueCount_of_zeroDetect` PROVED (ZeroCount.lean: zc_count_core +
  ev_loglog_small + nearOneZeroDensity_nonneg; η := log(2/u)/log P, η₀ = s₀²/16, s₀ = 1/(48(B+1))).
  `almost_all_F385_powerSaving`, `badCount_powerSaving`: #print axioms = [propext, Classical.choice,
  Quot.sound] (mod the literature Props as hypotheses). Only scoped sorry left:
  `nearOneLargeValues_of_density` (frozen, OFF headline, DIRECTION forbids; stated acceptable finish).

## phase 61 (2026-10-05, branch `mills-eplus`): Theorem E+
A (edge) and B (Saito wiring) PROVED axiom-clean.  Node C decomposed in `Mills/ShiftRigidity.lean`;
`rigidity_generic` (Step 4) PROVED: 3-cycle automorphism over L + circulant Fourier argument + the
equilateral exclusion (centroid c = ω/tr(β^s) ∈ ℚ; one-zero vertex ⇒ 3c² = 1).  No √−3 needed.
Open in node C: `not_primeTraces_of_cube`, `exists_spectral` (the transfer: window for 3^n+s,
T^(Q+1)=T with type-specific Q ∈ {2,8,26}, U·C^(s⁻)=T·C^(s⁺), y·(T∓1)_ab = 1), `eq_one_or_neg_one_of_const`,
`not_mem_cycField_{two,eight}`, `e1_empty` (Frobenius coherence P(h(C)) = P(C)^3 + rank certificate).
Node D untouched.

## 2026-10-05 phase 64b DONE
cm3_check and cert_all kernel-checked (E1CertCore Fast form + 6 table modules); headline xi_shift_transcendental_classical axioms = propext, Classical.choice, Quot.sound.

## Phase 65 lap 1 (2026-10-05): EDGE PROVED
`SaitoTypeBTheta.xi_shift_transcendental_of_degree` is axiom-clean (propext/choice/Quot.sound).
`μ > 1/3` was used only for the degree bound: `records_pisot_theta` never used it (dropped);
`eventually_record_shift_theta` and `saitoTypeB_shift_theta` now take
`1/3 < μ ∨ (degree ≤ 3)`.  No second node: the record step (`DominantPair.lower_along_records`,
`record_gap_bounded`) is degree-free given `card otherConj ≤ 2`.
The whole 5/9 wall is now the single node `shiftPisotDegreeLeThree_holds`.
Next: ξ-free obstruction; mechanism 1 (sign along `n ↦ 3n+d`) tested on the `X⁴ − aX³ − 1` control.
Lap 1 cont.: ξ-free node stated, `Mills/ShiftRigidityDeg.lean`: `ShiftTraceRigidityDeg ℓ`
(degree-ℓ form of `not_primeTraces`), ℓ = 3 proved (`shiftTraceRigidityDeg_three`), ℓ ≥ 4 sorry
(`shiftTraceRigidityDeg_holds`, ~75%).  Second half of the node still unstated: trace = floor at
ALL large k without `card otherConj ≤ 2` (eventual-records in degree ≥ 4).  Next: read
`exists_spectral_solution_shift` / `rigidity_generic` for what generalizes; state the eventual-
records half and wire both into `shiftPisotDegreeLeThree_holds`.
