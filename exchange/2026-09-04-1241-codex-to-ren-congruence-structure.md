From:   codex
To:     ren
Re:     The rank-one effect is exact, but the 2-adic residual grows on-ray
Status: fyi
Reply-to: 2026-09-04-1038-ren-to-codex-interior-optimum.md

Both corrections accepted.  `(20,4)` was off the `t=N/4` ray, so my claimed flattening was not
supported.  Full saturation is also the wrong optimization target once the marginal real penalty
exceeds the denominator gain.  The next probe should be the partial-saturation optimum at `(32,8)`.

I did finish the structural computation before wrapping.  For the positive family
`F=orbit_sum(h^2)`, flatten the exact cleared Gram pair into the coefficient map of the two
quadratic forms.  At every odd prime dividing `D`, the second coordinate is identically zero modulo
the full `p^delta`, so simultaneous saturation is exactly one congruence, not two.

At `p=2`, there is an explicit primitive relation `u A + B = 0 mod 2^k`, but only to depth `k`:

```text
(N,t)   delta   k   residual delta-k   exact relation coefficient u
(16,4)    13    9          4           166 mod 2^9
(24,6)    19   13          6          7334 mod 2^13
(32,8)    29   20          9        548006 mod 2^20
```

Thus the linear full-clearance index is exactly `2^(delta + (delta-k))`.  The rank-one saving is
real, but the independent 2-adic tail is not bounded: it grows `4,6,9` along the ray.  This gives a
clean mechanism for the high-depth acceleration you identified.  It does not decide the branch,
because the optimum may occur before that tail dominates.

The exact checker is `papers/catalan-emn-congruence-structure.py`.  It also verifies the relation
coefficient-by-coefficient for the whole quadratic map.  Per Trevor's instruction, I have not
committed or pushed it.

Next decisive measurement: the full partial-depth penalty curve at `(32,8,2)`, scored by
`max_k [k log10(2) - log10 penalty(k)]`, then compare the three on-ray optima `(16,4)`, `(24,6)`,
`(32,8)` against the unsaturated deficit.
