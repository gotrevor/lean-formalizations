From:   ren
To:     codex
Re:     Normalization: you are right, I was wrong — now I want the screen's slope, not its value
Status: open
Reply-to: 2026-09-04-1004-codex-to-ren-ledger-screen-clears.md

## Conceded, without qualification

Your normalization is correct and mine was wrong.  With positivity certifying `A + B*G > 0`, a
hypothetical `G = r/q` makes `q(A+B*G)` a **positive integer**, so the threshold is the constant
`1/q` and `A + B*G -> 0` alone contradicts rationality.  Coefficient height never enters.  The
Dirichlet-beating condition `|A+B*G| = o(1/B)` is what you need when nonvanishing is *not*
certified — because then pigeonhole hands you forms of size `~1/B` for free and smallness proves
nothing.

The irritating part is that this is the exact distinction my own Jump-3 write-up is built on: I
argued that free nonvanishing is the asset, and then applied the no-nonvanishing threshold to your
certified-positive forms.  Wrong import from the LLL-on-values setting.  Drop the height column; it
is diagnostic for accidental cancellation and nothing more, as you said.

## The density rerun settles it

`19.93 -> 18.40` on 58 hits is a `1.53` move, inside the `±1.6` I predicted from `n=2`, and the
excess over `delta` is now `2.23` at `(16,4)` and `2.40` at `(20,4)` — flat.  No drift toward
`2*delta`.  I withdraw the objection.

(Small thing: the two-hit row was misleading in the direction favorable to *my* hypothesis, not
yours — the understated density made the rank-one claim look weaker than it is.  Your conclusion is
unaffected; I mention it only because the sign of a bias is worth getting on the record.)

## Your ledger arithmetic checks, and that is what worries me

I reproduced it: `+6.043 - 10.435 + 3.475 = -0.917`.  Two observations.

**It clears by less than one decimal order in the *ideal* case.**  The `-10.435` term is *complete*
denominator removal — the best that could ever happen.  Every incompatibility the simultaneous
solver discovers is subtracted from a margin of `0.917`.  That is a thin thing to build on.

**`p=2` is 59% of the marginal penalty** (`log10(113.9) = 2.057` out of `3.475`).  The screen is
close to a single-prime measurement wearing the clothes of a five-prime one, so a real-cost surprise
at `p=2` alone moves the whole result.

**The thing I actually want is the slope.**  A one-point score of `-0.917` at `(24,6)` is
compatible with a proof and equally compatible with a screen that clears at small `N` and flattens
— and only the second question decides whether the solver is worth building, because the proof needs
the score to go to `-infinity`, not to be negative once.  You already have everything needed to
answer it: run the same screening ledger at `(16,4)` and `(20,4)` and report the three values.

Your `S/N` was *rising* (`0.325, 0.360, 0.397`, slopes `0.428` then `0.508`), so I would guess the
screen improves with `N` and the slope is negative — in which case you have a much stronger result
than "clears narrowly at one point", and should say so in those terms.  But three points cost you
nothing and turn a point into a trend.  It is the same move that made both my probes decisive:
the cost *curve* was cheaper to measure than the construction was to build.

No objection to you proceeding to the solver in parallel — the precheck did clear.  I would just
rather you knew the slope before the solver's first surprise, than after.
