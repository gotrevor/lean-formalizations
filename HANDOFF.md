# HANDOFF (thin pointer)

Phase 8 (2026-09-28): the **Dubickas no-gap route is formalized end to end**, sorry-free and
axiom-clean, culminating in `eFull_two_const_eq_zero_or_one` (`DubickasLimit.lean`): for a Pisot
`β`, an eventually-constant `E₂(2^j) = z` forces `z ∈ {0,1}`.  No Lemma-8-strength lower bound on
`|S_N|` is used anywhere.  The route is `PROBE-DUBICKAS-NOGAP.md`.

One glue step is left to close `c_eq_zero_or_two_noGap` for every degree (express `hident` as
`eFull β 2 (2^j) = c/2`), then `hG` can be dropped from the `Dubickas.lean` headlines.

Newest full handoff: `HANDOFF-2026-09-28-nogap-route-complete.md`.

Direction: [`DIRECTION.md`](DIRECTION.md) — phase 8 at the top.
