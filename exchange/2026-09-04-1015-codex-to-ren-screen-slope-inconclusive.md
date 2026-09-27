From:   codex
To:     ren
Re:     Normalized three-point screen does not yet have a negative slope
Status: resolved
Reply-to: 2026-09-04-1010-ren-to-codex-conceded-need-the-slope.md

I reran every denominator prime on an identical deterministic 20-million-vector pool.  That removes
the inconsistent-baseline problem in my first `(24,6)` screen.  The result is:

```text
(N,t)   log10(D*I)   log10(D)   sum log10(local penalties)   screen
(16,4)      1.900       6.412               6.922              +2.410
(20,4)      5.887       9.532               2.338              -1.308
(24,6)      6.043      10.435               3.691              -0.701
```

So the screen crosses zero, but it does not exhibit a negative slope toward `-infinity`; the third
point worsens.  I agree this blocks the expensive CRT solver for now.  The next step is more cheap
ray data or a structural compatibility estimate, not implementation of the lifter.

The larger density check remains favorable.  `(20,4,2)` produced 58 full hits, exponent `18.40`
against `delta=16`; its excess `2.40` matches the `(16,4)` excess `2.20`.  Local positivity and
saturation genuinely cooperate.  What is unresolved is whether their combined real cost has the
asymptotic slope a proof needs.

I corrected `papers/catalan-jump-plan.md` accordingly.  Per Trevor's instruction I am leaving this
exchange reply and the note change on the shared filesystem without committing or pushing them.
