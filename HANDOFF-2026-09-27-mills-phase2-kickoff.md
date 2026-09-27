# HANDOFF 2026-09-27 — Mills phase 2 kickoff (planted by Ren)

Phase 1 closed in one lap (Wright, conditional Mills, least Mills; merged to main `f53701b`).

Planted, compiling, 4 named sorries:
- `Literature/Primes.lean` — `primesIn`, `BakerHarmanPintz2001`, `Matomaki2007`, `Mahler1957`,
  `Schoenfeld1976` (no sorries; these are hypotheses).  Hand-checked against Saito Thm 2.1/2.5/3.7
  and Caldwell–Cheng Lemma 4.  `Schoenfeld1976` is deliberately WEAKENED (li(2) as ∃ C).
- `Mills/RH.lean` — `primeBetweenCubes_of_schoenfeld`, `minMills_mem_Ioo_of_primeBetweenCubes`.
- `Mills/Irrational.lean` — `primeBetweenCubes_of_BHP`, `irrational`.

Operator triage:
- Digits: b₄ = 2521008887; b₄^(1/81) ≈ 1.30637788386308, (b₄+1)^(1/81) ≈ 1.30637788386948 —
  inside (1.3063778838, 1.3063778839), so b₁..b₄ suffice.  Checked host-side with mpmath.
- Schoenfeld leaf needs ∫ 1/log t ≥ (b−a)/log b on [a,b] (monotone integrand) and a
  real-analysis inequality at n ≥ 14; mathlib has no `logIntegral`, hence the ∫₂ˣ form.
- Saito for c = 3 only: every "c_{k+1} = b" condition is automatic; `I_b = ℕ`, `B = 3`.
- Mahler contradiction needs: ξ^(3^k) is never an integer (else p_{k+1} = p_k³, not prime).

Next: DIRECTION.md phase 2, `lower_bound_of_RH` first.
