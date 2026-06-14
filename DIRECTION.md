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

## Feasibility gate — report honestly each lap
Write a VERDICT into `PENDING_WORK.md`/`STATUS.md`: is the crux reachable with current
mathlib, or is there a genuine gap (name it precisely)?
- A disclosed `sorry` + a **named gap** is a SUCCESS — it's the feasibility signal Trevor
  needs. A failed honest attempt that maps the wall beats a confident "done."
- This is an **umbrella repo**: if the crux is a confirmed wall, **park Curtis** (disclosed
  sorry + documented gap) and redirect to a target with a reachable crux. Parking-with-gap
  is correct; grinding a confirmed wall forever is not.
- NEVER report "spine/corollary/Step B proved" as deliverable progress without stating they
  remain `sorryAx` until the crux closes.
