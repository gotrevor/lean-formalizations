# HANDOFF phase 64a lap 2 (2026-10-05)

Advance on the crux (θ ∈ [5/9, 2/3) branch): a **control** showing decay alone cannot close it.
- New `Mills/DecayDegreeFour.lean`: `decay_admits_degree_four` (sorry, ~90%, English proof in docstring).
  For every μ < 1/3 a quartic Pisot β (root of X⁴ − aX³ − 1, a large) has ‖β^n‖ ≤ 3β^(−μn) at **every** n.
  So `ShiftPisotDegreeLeThree` needs an input other than decay plus Pisot-ness: the prime/greedy structure,
  or the orbit n ↦ 3n − d used arithmetically (e.g. a p-adic Skolem step as in `E2Skolem`).
- Maze row for the 5/9 wall now cites it in evidence and reopenIf.
- The frozen sorry is unchanged.  θ < 5/9 is proved (`xi_shift_transcendental_of_shortInterval'`), as the directive's fallback requires.

## Next attack
Find an arithmetic constraint the orbit puts on the quartic case: for a quartic β with all three small
conjugates near modulus β^(−1/3), decay μ close to 1/3 along n_k forces |Σγ_i^(n_k)| ≈ R^(n_k) cancellation-free unless
arguments align; try a dominant-triple analogue of `lower_along_records` (u_i^(n_k) phases under n ↦ 3n − d).
