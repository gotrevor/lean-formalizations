# HANDOFF — lean-formalizations (thin pointer)

This is a **thin pointer**, not a durable overview. Read, in order:

1. **`STATUS.md`** — the living repo-wide overview (3 threads, real `#print axioms` ledger).
2. **Newest dated baton: `HANDOFF-2026-06-18-power-tower-SHARP-iff.md`** — the current resume
   point: the **power-tower SHARP `iff` is PROVEN axiom-clean** (`tower_converges_iff_full`:
   `x>0` converges ⟺ `x ∈ [e^-e, e^1/e]`). That bounded operator-directed target is COMPLETE;
   the transcendence/squaring-the-circle thread was already complete (repo has **0 math axioms**).
   Next = a NEW target (default: general Hermite–Lindemann for arbitrary algebraic α).
3. **`PENDING_WORK.md`** — open-item inventory + attack paths.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep each `Statement.lean` the faithful audit surface; engines live in siblings.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM (intentional audit-surface hypotheses).
- After any Aristotle port or `grind`/`simp_all`, re-check `#print axioms` (can inject `sorryAx`).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

---
**→ Next session: `/resume HANDOFF-2026-06-18-power-tower-SHARP-iff.md`. The power-tower thread
is DONE (sharp iff, axiom-clean) — do NOT reopen it. Start a NEW target.**
