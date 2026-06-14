# DIRECTION — read FIRST (operator directive, 2026-06-14)

## Doctrine: hardest-first. Spike the crux; don't dress up scaffolding.

**Default to trying the hardest, most-likely-to-fail sub-problem FIRST.** The value of
this proof is **binary-gated on ONE lemma**. Easy things fall easily; hard things often
don't — so the only number that decides the project is "does the crux close?" Resolve
that uncertainty before investing anywhere else. Going hardest-first is to resolve the
crux's *feasibility*, not necessarily to solve it in one lap.

## Where we are (2026-06-14)
The tractable work is **done**: Step B (`half_le_totalDegree`), Lemma 2 (Brauer–Shockley,
via Aristotle), the spine, the corollary, the finite-bad-prime lemma — all machine-checked.
But **none of it is a deliverable**: every headline is still `sorryAx` transitively, because
it all consumes the one open crux. There is exactly **one open `sorry`**, and it IS the crux:

### THE CRUX: `substCurve_eq_zero` (Step A, `Engine.lean`)
Two remaining long poles — spike the riskier first:
1. **Lemma 1 — the Dirichlet + Farey witness** (riskiest; OUT TO ARISTOTLE, job
   `80d9166c`). prime `x ≡ i`, `y ≡ j` (mod p), `gcd=1`, `|α − y/x| < ε`. Engine: mathlib
   Dirichlet (HAVE) + Farey adjacency `|rs − qt| = 1`. Verify Aristotle's result in our
   kernel + `#print axioms` before trusting; port onto the real defs.
2. **The limit argument** — `G(xₙ,yₙ)=0`, `yₙ/xₙ → α` ⟹ `G*(1,α,0)=0` for all irrational
   α in an interval ⟹ univariate poly with ∞ roots ⟹ `Z ∣ G*`. Mostly mathlib
   (`MvPolynomial` homogenization + univariate root-finiteness). Build it now, independent
   of Lemma 1, against Lemma 1's *statement*.

## Keep banging — advance the crux, do NOT bail to easy leaves
The crux is the whole game. Attack it EVERY lap. Do not retreat to easier work because
it's hard — there are no easy leaves left to hide in here, and there wouldn't be an excuse
if there were.
- **Advance the attack each lap** (decompose to the narrowest open core, read the paper,
  formalize the next prerequisite, feed Aristotle, mine the reference corpus). Banging ≠
  repeating a failed attempt; it means pushing the attack forward from a new angle. A
  disclosed `sorry` on the crux is a CHECKPOINT to resume from next lap — never a stopping
  point.
- **Document the obstacle precisely** in `PENDING_WORK.md` (what you tried, the exact
  blocking gap, the next angle) — as a continuation aid for the next lap, NOT a verdict that
  licenses quitting. "Needs deep machinery / infeasible" is a hypothesis to test by trying,
  not a verdict to file.
- **Parking/abandoning Curtis is TREVOR's call** after sustained multi-lap effort — never
  your lap-level excuse.
- NEVER report "spine/corollary/Step B proved" as deliverable progress without stating they
  remain `sorryAx` until the crux closes.
