# STATUS — lean-formalizations 📊
**Umbrella for solved-but-unformalized impossibility / no-formula meta-theorems.** · **Build**: 🟢 green (8255 jobs) · **Updated**: review lap · 2026-06-14 · `fe18f0a`

## Where it stands
**Curtis 1990 is COMPLETE and axiom-clean** — verified this lap by real `#print axioms`, not just inherited from the baton. All 7 headline results reduce to the pure trust base `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms anywhere in `src/`). The single deep crux (`substCurve_eq_zero`) was closed in the prior session by a reformulation that bypassed Curtis's Lemma 1 / limit argument entirely. The repo's one directed target is therefore done; the only remaining Curtis items are outward-facing (mathlib upstream — Trevor's call) or trivial (a Zariski-dense repackaging).

**Next target chosen this lap (pivot):** open a *new* impossibility target in the umbrella — **compass-and-straightedge impossibility** (constructible numbers / doubling the cube). It is genuinely absent from mathlib (the `Constructible.lean` files there are all topology/spectra), on-theme, and has a provable axiom-clean algebraic core plus a hard geometric→algebraic bridge to chip across laps. No proof code written yet — design + mathlib-tooling recon done (see PENDING_WORK).

## What's happened (newest first)
- **2026-06-14 (review lap):** Verified Curtis complete & axiom-clean from real `#print axioms` on all 7 headlines. Confirmed Liouville/Lindemann/Abel–Ruffini are already in mathlib, but constructible-number theory is **not**. Chose the next umbrella target: compass-and-straightedge impossibility (doubling the cube). De-risked the mathlib tooling (tower `finrank`, `adjoin.finrank`, Eisenstein/`X_pow_sub_C` irreducibility). Created this STATUS.md.
- **2026-06-14 1511:** Closed the crux `substCurve_eq_zero`; repo went `sorry`-free + axiom-clean. Added extensions: faithfulness anchors (`⟨3,7,8⟩`), the ℤ/ℚ (any ℂ-algebra) corollary, the n≥3 generalization, and `grid_vanish` generalized to any infinite field.
- **2026-06-14 1423 & earlier:** Built the Curtis engine spine, Step B, Lemma 2 (Brauer–Shockley, via Aristotle, verified), the corollary, the finite-bad-prime lemma — all under the then-open crux.

## Outstanding
### Short-term (mirror PENDING_WORK top)
- Build Layer 1 of the constructible-numbers target: define a quadratic/sqrt tower predicate, prove **constructible ⟹ `[ℚ(a):ℚ]` is a power of 2**, prove `∛2` has degree 3, conclude `∛2` not constructible ⟹ the cube cannot be doubled. Aim: axiom-clean.
### Long-term
- Layer 2 (the hard wall): a faithful *geometric* definition (points/lines/circles + intersections) and the bridge **geometric-constructible ⟹ lies in a quadratic tower**. This is the multi-lap crux of the new target.
- Cheap follow-ons once Layer 1 lands: angle trisection (`cos 20°` has degree 3), regular n-gon constructibility (Gauss–Wantzel), squaring the circle (π transcendental — already in mathlib via Lindemann).
- Curtis: mathlib upstream of `FrobeniusNumber` n≥3 impossibility — **Trevor's outward-facing call**, not autonomous.
### To completion
- Curtis 1990: ✅ done (axiom-clean). Constructible-numbers target: just opening; "done" = Layer 1 + Layer 2 both axiom-clean with a geometric headline.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `no_polynomial_relation` | Curtis 1990 (Frobenius of a triple not algebraic over generators), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ trust-base only — **0 math axioms** |
| `no_finite_polynomial_formula` | ℂ corollary (no finite formula list), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_of_algebra` | any ℂ-algebra coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_int` | ℤ coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_rat` | ℚ coeffs, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `no_finite_polynomial_formula_multivar` | n≥3 (paper's full title), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Anchors.frobeniusNumber_3_7_8` | faithfulness witness (Frobenius⟨3,7,8⟩=5) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |

**Math-axiom count (🟢+🟡+🟠) across all headlines: 0.** Every base is the bare trust base — no 🔴 anywhere, correct since every Curtis headline is unconditional. The constructible-numbers target has no headlines yet.

## Pointers
- Newest baton: `HANDOFF-2026-06-14-1545.md` (this lap) · prior: `HANDOFF-2026-06-14-1511.md`
- Open items / attack paths: `PENDING_WORK.md`
- Historical directive (now mostly stale — crux closed): `DIRECTION.md`
