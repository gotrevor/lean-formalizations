# HANDOFF — lean-formalizations (thin pointer)

This is a **thin pointer**, not a durable overview.

## ⛔ Current run: read `DIRECTION.md` FIRST — bounded Goodstein run
The active directed target is **Goodstein's theorem (termination)**, scaffolded in
`src/LeanFormalizations/Logic/Goodstein/`. `DIRECTION.md` is authoritative: prove
`goodstein_terminates` (replace the stub `goodsteinSeq`, discharge the `Anchors`,
prove the headline, keep it axiom-clean), then **self-stop**. Touch ONLY
`Logic/Goodstein/`. Do NOT reopen the four complete threads. Do NOT start any other
new target — when Goodstein is done, the run is OVER.

Then, in order:
1. **`DIRECTION.md`** — the operator directive for THIS run (Goodstein).
2. **`STATUS.md`** — living repo-wide overview (now 4 complete threads + Goodstein in progress).
3. **`HANDOFF-2026-06-18-goodstein-START.md`** — the resume baton for this run.
4. **`PENDING_WORK.md`** — older open-item inventory (all OUT OF SCOPE this run).

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep each `Statement.lean` the faithful audit surface; engines live in siblings.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM (intentional audit-surface hypotheses).
- After any Aristotle port or `grind`/`simp_all`, re-check `#print axioms` (can inject `sorryAx`).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

---
**→ Next session: read `DIRECTION.md` and work the Goodstein target. The four prior
threads (Curtis, transcendence/squaring-the-circle, Constructible, power-tower) are
DONE + axiom-clean — do NOT reopen them.**
