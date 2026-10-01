# HANDOFF 2026-10-01 — Erdős #385 E3d DONE
`almost_all_F385_rate_VK` (RateVK.lean) proved, `#print axioms` = {propext, Classical.choice, Quot.sound}:
from VKZeroFreeLogDeriv + DLVPStatement, #bad n ≤ X is ≤ C X exp(−(log X)^{1/3−ε}).

How: `RateVK/General.lean` is the E3 pipeline (AlmostAll.lean) copied into namespace `Gen` with the
scale `(log Z)^{1/10}` replaced by `(log Z)^a`, `[Fact (0<a)] [Fact (a<1/3)]` instance hypotheses (so
call sites need only `(a := a)`), VK slack ε_vk = (1/3−a)/2.  `RateVK/RateGen.lean` copies Rate.lean's
assembly.  Final step picks a = 1/3 − min(ε,1/6)/2, absorbs c L^a ≥ L^{1/3−ε} eventually and small X
by a finite sum.  Build note: cold wide builds hit "Too many open files"; build ≤3 targets per call.
Next (other branch): E2e Landau.lean (VK from Richert).
