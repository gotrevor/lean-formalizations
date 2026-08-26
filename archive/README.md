# archive/ - the unedited session log 🗂️

These are **point-in-time snapshots, published as written.** Nothing in this directory has been
revised after the fact, and much of it is wrong in ways the repo later fixed. That is the point:
it is the working record of how the mathematics actually got made, not a retrospective account
of it.

Two things follow, and both matter if you quote from here.

**Any claim in this directory is scoped to its own date.** Several handoffs print
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound, kakeya_subresolution_content]`.
That was true on that day. It is not true now, because that axiom turned out to be **false** and
was removed. For the current position, read [`../STATUS.md`](../STATUS.md) and re-run
`#print axioms` yourself - never a file in here.

**The mistakes are load-bearing.** The most useful documents in this directory are the ones
recording a retraction:

- `axiom kakeya_subresolution_content` was introduced as "true but deep", then **proved false**.
  It was deleted and replaced with a kernel-checked refutation,
  `Kakeya2D.Engine.kakeya_subresolution_content_is_unsound`, which is still in `src/` today as a
  permanent guard so the axiom cannot come back.
- A `pinwheel_exists_noThree` construction was asserted, then found to be false as stated
  (*"a sorry on a false statement = landmine"*).
- `Kakeya2D/CASE_B_ANALYSIS.md` carries an invalidation banner over its own conclusion.

**Timestamps are approximate.** Filenames carry the wall-clock the writing session believed it
had. Several sessions ran in a sandbox whose clock drifted, so a few filenames disagree with
their commit times and with each other. Trust `git log`, not the filename.

**On the repetition.** A long run of near-identical re-verification handoffs sits in here from
2026-06-20. An autonomous loop kept re-confirming a finished result instead of stopping; it
eventually diagnosed that itself, in `HANDOFF-2026-06-20-1657` and its neighbours, and the run
was stopped by hand. Left in, because a log that quietly deleted its own dead ends would not be
worth much as a record.
