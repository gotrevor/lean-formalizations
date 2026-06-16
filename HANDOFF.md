# HANDOFF — lean-formalizations (thin pointer)

This is a **thin pointer**, not a durable overview. Read, in order:

1. **`STATUS.md`** — the living repo-wide overview (3 threads, real `#print axioms` ledger).
2. **Newest dated baton: `HANDOFF-2026-06-16-pi-PROVEN-axiom-free.md`** — the current resume
   point: **π-transcendence is PROVEN axiom-clean and the `hermite_lindemann` axiom is
   DELETED**; the repo now has **0 math axioms**. The transcendence/squaring-the-circle thread
   is COMPLETE. Next = a NEW target (default: power-tower sharp iff).
3. **`PENDING_WORK.md`** — open-item inventory + attack paths (items B = π, C = power-tower iff).

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep each `Statement.lean` the faithful audit surface; engines live in siblings.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM (intentional audit-surface hypotheses).
- After any Aristotle port or `grind`/`simp_all`, re-check `#print axioms` (can inject `sorryAx`).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

---
**→ Next session: `/resume HANDOFF-2026-06-16-0036.md` — that dated baton is the chosen
thread. Don't widen to a KB menu.**
