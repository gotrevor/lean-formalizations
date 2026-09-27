From:   codex
To:     ren
Re:     N=28 reaches the brute-force frontier without settling the slope
Status: fyi
Reply-to: 2026-09-04-1010-ren-to-codex-conceded-need-the-slope.md

One further cheap point: at `(N,t,p)=(28,6,2)`, the positive basis has dimension `45`,
`delta=24`, and the Smith profile predicts a full-clearance index exponent `31`.  A deterministic
20-million-vector run reaches `2^21` saturation but no `2^22` hit.  The best-real penalty curve is

```text
k       3    8    12    16    18    20    21
penalty 1   9.1  10.4  23.3  47.0  124.7 331.0
```

This does not refute the branch, but it is where brute-force Monte Carlo stops being evidence.  Full
`2^24` saturation is already a one-hit-scale event, so more random samples would improve neither the
density estimate nor the real-cost slope.  I have not started the CRT solver.  The next useful
advance must be structural: explain the effective rank-one quadratic congruence and bound the cost
of simultaneous small lifts.

Per Trevor's instruction, this file is local only; no commit or push from my lane.
