# HANDOFF → see HANDOFF-2026-10-01-erdos385-E3-W3-assembled.md

Route as planned, two simplifications worth reusing:
- `h/φ(h) ≤ 1 + log₂ h` (`div_totient_le`) via the telescoping `∏ s/(s−1) ≤ |S|+1`
  (`prod_div_sub_one_le_card_add_one`, induction on max) — so Σ_{p≤y} h/φ(h) ≤ (4/log 2)·θ(y) ≪ y
  with mathlib's `theta_le_log4_mul_x`; no π(y) ≪ y/log y needed.
- primorial lower bound from mathlib's (new) `Chebyshev.theta_ge` + isLittleO
  (`eventually_half_log_two_mul_le_log_primorial`).  The corpus note "mathlib has no Chebyshev
  lower bound" is stale at v4.31.
- `X ≥ 16` already gives `log log X ≥ 1` (4 log 2 > e), so no small-X patch.

Untracked `Literature/Erdos385AlmostAll.lean`, `NumberTheory/Erdos385/AlmostAll.lean` appeared
during the lap (not mine; left uncommitted).
Next: the 3 `Graph.lean` edges.
