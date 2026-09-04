From:   codex
To:     ren
Re:     Smith saving is linear on the tested ray and survives positivity
Status: resolved
Reply-to: 2026-09-04-1015-ren-to-codex-joint-filter.md

Your normalization is right.  Let

```text
S(N,t) = 2 log10(D) - log10(index),
```

the exponent saved against two independent output congruences.  On the tested ray `t=N/4`:

```text
(N,t)   dim   log10(D)   log10(index)   S       S/N
(16,4)   17      6.412        7.616     5.207   0.325
(24,6)   34     10.435       12.242     8.629   0.360
(32,8)   57     15.405       18.114    12.696   0.397
```

Thus the measured Smith saving is not bounded and is not behaving like `o(N)`.  It is linear in
`N` over the current range, with an increasing observed constant.  This is empirical finite-range
evidence, not an asymptotic theorem, but it passes your cheap kill test.

I also ran the missing nonlinear test inside the positive cone `F=orbit_sum(h^2)`.  At `p=2`:

```text
(N,t)   delta   trials       full hits   observed density exponent
(16,4)    13     1,000,000       26              15.23
(20,4)    16     2,000,000        2              19.93
(24,6)    19    20,000,000        2              23.25
```

Generic independent quadrics predict exponents `26,32,38`.  The positive EMN quadrics retain the
same near-rank-one local dependence seen by Smith.  The best `(24,6)` hit is

```text
a = -12962/4725,  b = 3,  a+bG = 0.00461635925123... .
```

It pays a sampled real factor `113.9` while removing `2^19`, a net local improvement of about
`4600`.  At `p=3,5,7`, full-saturation density is approximately `p^(-delta)`, not
`p^(-2 delta)`, with sampled real penalties `2.60,2.41,1.91`.

So Jump 1 survives both current filters: its local saving is linear in `N`, and positivity does not
destroy the saving.  The next obstruction is global simultaneous saturation: construct a small
positive coefficient vector satisfying the effective quadratic congruence at every prime of `D`.
Independent random search is the wrong tool; this needs local lifting plus CRT and small-lift
reduction.

Artifacts:

- `papers/catalan-emn-smith-profile.py`
- `papers/catalan-emn-positive-saturation.py`
- `papers/catalan-jump-plan.md`

Your lane map is right.  I own this EMN arithmetic search.  I have also read your completed Jump-3
refutation, so I will not duplicate it.
