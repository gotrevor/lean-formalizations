# HANDOFF — lean-formalizations (thin pointer)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

This file is a **thin pointer**. The durable overview is **`STATUS.md`**; the per-lap baton
is the newest **`HANDOFF-<date>.md`**; open items/attack paths live in **`PENDING_WORK.md`**.

## Where things stand (2026-06-19 lap 9 — 🎉 FINITE DIAGONAL CLOSED; newest baton: `HANDOFF-2026-06-19-1215.md`)
- **DONE + axiom-clean:** A1–A4 (fast-growing growth theory); B1–B3 (Hardy); C1–C3 (Cichoń identity);
  and **🎉 THE FINITE-LEVEL DIAGONAL DOMINATION** `f_n(m) ≤ goodsteinLength m + 2` for every finite
  `n` (`fastGrowing_ofNat_le_goodsteinLength`, hyps `16≤m ∧ n+1≤log₂m`) — the 8-lap open crux
  (Cichoń's lower bound, sub-fact (ii)). `src/` **sorry-free**; build 🟢 green (8292 jobs). Math
  engine axiom-clean; unconditional closures carry `Lean.ofReduceBool` (finite base-case `native_decide`).
- **The winning idea: SELF-SIMILARITY** (`leadExp_ge_goodsteinSeq_log` — leadExp seq dominates the
  Goodstein seq one scale down) + strong-induction exponential length bound (`goodsteinLength_exp_lower`)
  + small-regime termination (`n_le_goodsteinSeq`). The lap-8 `ppCount` sparsity route is
  **SUPERSEDED — do not reopen.** Full writeup: `PENDING_WORK.md` top + `STATUS.md` lap-9 entry.

## Next (the lap-9 frontier — START HERE)
1. **`o=ω` diagonal `f_ω(m) ≤ goodsteinLength m + 2`** — the transfinite tier toward `f_{ε₀}`. Already
   FRAMED: `DominationOmega.lean` has the `ω^ω` bridge + `fastGrowing_omega_le_goodsteinLength_of_largeRegime`
   reducing it to ONE open hypothesis `hreg : base(m-2) ≤ leadExp_{m-2}` (leading exponent stays in the
   LARGE regime ~m steps). **Crux = discharge `hreg`** via route (a): iterate the self-similarity so
   the one-level-down value stays `≥ base` at `k≈m` (a doubly-iterated length bound). Three attack
   paths in `PENDING_WORK.md` → "NEXT FRONTIER". Genuinely multi-lap.
2. **DO NOT** reopen the `ppCount` sparsity bound (superseded) or chase non-diagonal refinements.
3. B4 (`H_{ω^α}=f_α`) — long-horizon trap under mathlib's `ω[n]=n+1`. Lower priority.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` clean on closed theorems.
- Work only in `Logic/FastGrowing/*` + `Logic/Goodstein/{Length,Growth}`; don't touch the five frozen threads.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
