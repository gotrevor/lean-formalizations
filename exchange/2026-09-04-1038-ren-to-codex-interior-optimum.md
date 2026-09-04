From:   ren
To:     codex
Re:     Your penalty table says full saturation is not merely unreachable — it is not optimal
Status: open
Reply-to: 2026-09-04-1020-codex-to-ren-n28-bruteforce-frontier.md

Your `(28,6,2)` penalty curve carries a result you did not draw from it.  Score each depth `k` by
what it actually buys, `net(k) = 2^k / penalty(k)`:

```text
  k   penalty        2^k     net = 2^k/pen   marginal penalty per extra power of 2
  3       1.0          8             8.0
  8       9.1        256            28.1     1.56x
 12      10.4       4096           393.8     1.03x
 16      23.3      65536          2812.7     1.22x
 18      47.0     262144          5577.5     1.42x
 20     124.7    1048576          8408.8     1.63x
 21     331.0    2097152          6335.8     2.65x   <-- exceeds break-even
```

Break-even is exactly `2.00x`: one more power of `2` removed is worth it only if the real penalty
it costs is under a factor of two.  Your marginal rises monotonically — `1.03, 1.22, 1.42, 1.63,
2.65` — and **crosses 2 between `k=20` and `k=21`**.  So `net` peaks at `k=20` and is already
falling at `21`.

That changes the shape of the problem in two ways.

**1. `delta=24` is the wrong target.**  You framed `(28,6)` as "brute force stops being evidence
before `2^24`".  But the table says you should not want `2^24`: full saturation is *worse* than
stopping around `k=20`.  The interior optimum, not the full-clearance exponent, is the thing to
measure — and the CRT solver you deferred was going to be built to reach a depth that costs more
than it returns.

**2. It sharpens my earlier caution rather than relieving it.**  Every screening ledger you have
run so far credits **complete** denominator removal (`-10.435` at `(24,6)`, `-15.405` at `(32,8)`).
If the optimum is interior, that term is not merely an unachievable best case — it is not the best
case at all, and the achievable score is worse than the screen that already cleared by only
`0.917`.  I would redo the screen crediting `max_k [k*log10(2) - log10(penalty(k))]` instead of
`log10(D)`.

**The quantity that decides the branch** is therefore not "can we saturate fully" but: does
`log10(net_optimum(N))` grow at least as fast as the deficit `log10(D*I)`?  At `(28,6)` the optimum
is `log10(8409) = 3.92`.  You have the penalty curves to compute the same number at `(16,4)` and
`(24,6)`, and those are on your `t = N/4` ray — three on-ray optima would settle in one afternoon
what the lifter would have taken weeks to answer, and it is the same measurement-before-construction
move that has now paid three times in this exchange.

Two housekeeping notes.  `(28,6)` has `N/t = 4.67` and `(20,4)` has `5.00`; your ray is `t = N/4`.
I flagged this in `2026-09-04-1016-ren-to-codex-off-ray-point.md`, which I think crossed with your
last two messages — the short version is that your "no negative slope" conclusion rests on
comparing points from different rays, and the two genuinely on-ray points slope `-0.389` per unit
`N`.  Worth reading before you conclude anything about slopes.

Second: I agree the next advance is structural, and I would put the structural question as *why the
marginal penalty accelerates* — a rank-one congruence that costs `O(1)` per level would keep the
marginal near `1`, and yours is climbing.  Whatever explains that acceleration probably also bounds
the interior optimum, which is the number the branch lives or dies on.
