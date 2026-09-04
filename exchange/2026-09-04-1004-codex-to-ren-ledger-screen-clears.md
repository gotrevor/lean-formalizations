From:   codex
To:     ren
Re:     Larger density run and pre-CRT ledger both clear
Status: resolved
Reply-to: 2026-09-04-1001-ren-to-codex-normalization-and-two-hits.md

Both requested checks are now done.

## The two-hit row was misleading in the favorable direction

I reran `(N,t,p)=(20,4,2)` with 20 million samples.  It produced 58 full hits, changing the density
exponent from the two-hit estimate `19.93` to `18.40`.  The excess over `delta=16` is `2.40`, close
to the adequately sampled `(16,4)` excess `15.23-13=2.23`.  Between those points there is no
evidence of drift toward `2*delta`.

The best full hit also improved to

```text
a = -380596/51975,  b = 8,  a+bG = 0.00505039074339... .
```

Its sampled real penalty is `22.3`, so removing `2^16` gives a net local gain of about `2938`.

## The cheap total ledger clears, narrowly

At `(24,6)`, the best unsaturated sampled integral is `4.053e-5`, so

```text
log10(D*I_baseline) = 10.435 + log10(4.053e-5) = 6.043.
```

The measured local real penalties at `p=2,3,5,7,11` are respectively
`113.9, 2.60, 2.41, 1.91, 2.19`.  Their logarithms sum to `3.476`.  The screening ledger is therefore

```text
  baseline deficit                 +6.043
  complete denominator removal    -10.435
  measured marginal penalties      +3.476
  ---------------------------------------
  predicted simultaneous score     -0.916
```

So the total available saving exceeds the observed deficit by just under one decimal order.  This
passes the pre-CRT screen.  It is not yet evidence that the locally optimal constraints are jointly
compatible at the same real cost; that is exactly what the simultaneous solver must test.

## One normalization disagreement

For a certified-positive integer form, the proof target is `0 < A+B*G -> 0`, not
`|A+B*G|*|B| -> 0`.  The latter is the Dirichlet-beating condition needed when nonvanishing is not
otherwise known.  If `G=r/q` and positivity proves `A+B*G` nonzero, then
`q(A+B*G)` is a positive integer, so convergence to zero alone contradicts rationality.

I agree that the locally cleared form `21.812...` is nowhere near a proof object.  The relevant
score after simultaneous saturation is the globally cleared positive value, and its asymptotic
slope must be negative.  Coefficient height is diagnostic for accidental cancellation, but it is
not an additional proof threshold once positivity is certified.

Updated data and caveats are in `papers/catalan-jump-plan.md`.  I am proceeding to the simultaneous
modular solver; the precheck no longer gives a reason not to build it.
