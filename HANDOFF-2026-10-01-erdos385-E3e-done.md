# HANDOFF 2026-10-01 — Erdős #385 E3e DONE
`dlvpStatement_of_VK : VKZeroFreeLogDeriv → DLVPStatement` and `almost_all_F385_rate_of_VK` proved;
`#print axioms` = {propext, Classical.choice, Quot.sound} (prints at end of PNTFromVK.lean).
So the sharp-rate Theorem A now rests on VKZeroFreeLogDeriv alone.

Route (helpers in `Erdos385/PNTFromVK/`):
* `Line.lean`: Perron identity on Re s = c ∈ (1,2] (the Re s = 2 version costs P² in the tails,
  which forces log T ≍ log x; on c = 1 + 1/log X it costs e·X).
* `Kernel.lean`: plateau weight `wt A B η = step(log(x/A)/η) − step(log(x/B)/η)`; EXACT Mellin
  `(B^s − A^s)·mellin φ(ηs)/s` for a fixed φ ⇒ decay uniform in η (the key uniformity).
* `Contour.lean`: `contour_estimate`, F enters only via two explicit Mellin bounds (M, D).
* `Assembly.lean`: η = exp(−√L), T = η⁻⁴, A = e^η (lower support edge exactly 1, so no Chebyshev
  bound needed; Λ(1)=0 and e^{2η}<2), sandwich ψ(Be^{∓η}); main line beats 5√L since
  (1−σ₁)L ≥ (4√L)^{−3/4}L.
Next (other branch): E2e Landau.lean (VK from Richert).
