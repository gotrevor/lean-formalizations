# ⭐ CLOSED-FORM SELECTION RULE FOUND — the HJSW crux is cracked (2026-06-19)

For months the open crux of `hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)` was the
*lift-selection rule* for the sheared-hyperbola construction. The prior baton believed it was
intrinsically **non-uniform** ("3,2,3,1,3,4,3", deficit-of-3, p-mod-4 split, size-3 classes). That
was an artifact of an unlucky search. **A clean closed form exists.**

## The construction (final)

Let `p` prime, `pl = (p−1)/2` (the pole: `2·pl+1 ≡ 0 mod p`).

- **Base points**: for each `x ∈ {0,…,p−1}`, `(r,s) = (x, y(x))` where `y(x) = (2x+1)⁻¹ mod p`
  (and `y(pl)=0`, the convention `0⁻¹=0` in `ZMod p`). Curve: `(2x+1)·y ≡ 1 (mod p)`.
- **Drop the pole** base point `x = pl` entirely.
- For every other base point keep **3 of its 4 lifts** into `[0,2p)²`
  `{(r,s),(r+p,s),(r,s+p),(r+p,s+p)}`, dropping the single lift

  > **`dropped(r,s) = ( r + p·[r ≤ pl],  s + p·[s ≤ pl] )`**

  (i.e. shift a coordinate up by `p` exactly when its residue is `≤ pl` — geometrically: **drop the
  lift nearest the grid centre `(p,p)`**, ties broken by `≤`).

`|S| = 3(p−1)`. **Verified card + distinct + grid-bound + NoThree (exact integer determinant) for
EVERY prime `3 ≤ p ≤ 109`.** (`/tmp/shear_verify_big.py`.)

## Why it works (proof sketch — the next formalization target)

Each non-pole base point `(r,s)` keeps either its **diagonal pair** `{A=(r,s), D=(r+p,s+p)}`
(slope +1) or its **antidiagonal pair** `{B=(r+p,s), C=(r,s+p)}` (slope −1):

- dropped corner is `B` or `C` ⟺ `r,s` on **opposite** sides of `pl` ⟹ keep diagonal pair `{A,D}`;
- dropped corner is `A` or `D` ⟺ `r,s` on the **same** side of `pl` ⟹ keep antidiagonal pair `{B,C}`.

Geometry (already formalized, axiom-clean, `Hyperbola.lean`):
`shear_hyperbola_lift_share_residue` ⟹ any collinear triple of lifts has two lifts of one base
point; `lift_triple_noncollinear` ⟹ three lifts of one base point are never collinear. So every
collinear triple is **two lifts of one base point + one lift of another**, forced onto a **slope ±1**
line. The remaining (open) lemma: with this explicit rule, **no slope ±1 integer line carries 3 kept
points**. Reduces to modular arithmetic via `coord_diff_of_residue_eq`.

This is now the sole remaining obligation for an axiom-clean `hjsw_lower`.

## Status of the old "2 stubborn triples"

The pure "drop nearest centre" rule (strict `<`) left exactly **2** collinear triples for every `p`,
both sharing the `D`-corner of base point `(pl−1, pl)`; the `≤` tie-break (used above) removes both
with no new collisions. Confirmed `0` bad triples for all primes ≤ 109.
