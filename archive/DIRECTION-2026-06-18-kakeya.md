# DIRECTION — read FIRST (operator directive, 2026-06-18, Trevor via Ren)

## ♾️ UNBOUNDED EXPEDITION. Prove the planar Kakeya conjecture (Davies 1971) in Lean.

This is an **open-ended research run**, not a bounded "do X then stop" task. There is NO
self-stop sentinel and `--allow-stop` stays OFF until the crux is genuinely closed. Keep
going, lap after lap, until Trevor stops the treadmill. Slow, steady, real progress is the point.

### The target
`davies_kakeya_2d : KakeyaSetConjectureDim 2` — *every Kakeya set in `ℝ²` has Hausdorff
dimension `2`* — lives in `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`. It is
**assembled** from two halves:
- `dimH_le_two` (the `≤ 2` upper bound) — **already proven, axiom-clean**. Do not touch.
- `two_le_dimH` (the `≥ 2` lower bound, Davies' real content) — **the open crux, one `sorry`.**

So the entire job is closing `two_le_dimH`. The defs (`IsKakeya`, `KakeyaSetConjectureDim`) mirror
`google-deepmind/formal-conjectures` **verbatim** — do NOT change them (faithfulness + portability).

### The plan
`src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/PLAN.md` has the full ladder. The shape:
1. **K1 (do first, it's free):** reduce `two_le_dimH` to `∀ d : ℝ≥0, ↑d < 2 → μH[d] S ≠ 0` via
   mathlib's `le_dimH_of_hausdorffMeasure_ne_zero`. Pure mathlib, no analysis — turns the analytic
   `sorry` into a concrete one.
2. **K2:** δ-tube geometry + the two-tube overlap bound `vol(Tᵥ ∩ T_w) ≲ δ²/(θ+δ)` (the geometric heart).
3. **K3:** δ-discretize a Kakeya set into ~δ⁻¹ tubes of distinct directions.
4. **K4:** Córdoba `L²`/Cauchy–Schwarz ⟹ `vol(Sδ) ≳ 1/log(1/δ)`.
5. **K5:** Minkowski-content → Hausdorff-positivity bridge ⟹ close K1's concrete sorry.

This is a single-paper harmonic-analysis result. **It is hard and will take many laps.** A lap that
advances the crux by one honest prerequisite — even leaving a disclosed `sorry` on it — is a
**successful lap**. Do not retreat to easy unrelated work.

## Lane discipline
- Work ONLY in `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`. Wire every new file into
  `src/LeanFormalizations.lean` (the lib only builds files reachable from that root).
- **DO NOT TOUCH** any other thread (`NumberTheory/Transcendence/`, `Geometry/Constructible/`,
  `NumericalSemigroups/Curtis/`, `RealAnalysis/PowerTower/`, `Logic/`, `Combinatorics/`). Read them
  for technique if useful, but do not modify, reopen, or re-axiomatize them.
- Do NOT start an unrelated result to "keep busy." The Kakeya ladder is a deep, many-lap runway.

## Anti-vacuity locks (non-negotiable)
- **The headline is the audit surface.** Keep `davies_kakeya_2d` / `KakeyaSetConjectureDim` faithful
  and thin; delegate proof content to engine siblings.
- **No axiom-smuggling.** This crux is *constructible in mathlib* — never introduce an `axiom` for a
  tube/overlap/content bound and call it done. A disclosed `sorry` on an open crux is fine; a bare
  `axiom` standing in for the actual content is NOT.
- **Every new computable helper gets `native_decide` anchors** (small explicit cases), as standalone
  `example`s off any headline axiom path. `native_decide` MUST NOT leak onto the headline's axiom path.
- Run `#print axioms two_le_dimH` whenever you close a real sub-lemma; the goal end-state is
  `[propext, Classical.choice, Quot.sound]` with zero `sorryAx`.

## Rules (same as every autonomous run here)
- **Commit every green build** from a real `lake build` you actually saw succeed. **NEVER push** (the host pushes).
- A `sorry` is a disclosed checkpoint, never a faked proof. Never claim green you didn't see.
- Verify lemma names against THIS repo's mathlib (`v4.29.1`). `push_neg` is deprecated → `push Not at h`.
- **Reference corpus** (cross-lap memory, NOT auto-loaded): `ls`
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` at lap start, and
  `grep -rl <keyword>` it before re-deriving any Hausdorff-measure / `dimH` / geometry friction.
- **Aristotle:** keep one job in flight only while a genuinely-open lemma exists to feed it (the
  two-tube overlap bound or an `L²`/Cauchy–Schwarz lemma are good candidates). Verify any returned
  proof in-kernel + `#print axioms` before trusting; never re-submit something already proved locally.
- **Blocked needing the open web** (Córdoba's argument, a textbook content→dimension lemma, an
  existing formalization to port)? First check answered `ON-LINE-FINDINGS-*.md`; else append a dated,
  specific item to `ON-LINE-REQUEST.md` and continue on another brick. Do not block.
- Keep `HANDOFF.md` current; on the governor's budget signal, `/handoff` and end the lap (you'll be
  relaunched fresh, resumed from the HANDOFF).

## NOT a stop condition
No completion sentinel until `two_le_dimH` is genuinely closed and axiom-clean. Do NOT stop because a
brick landed, "to take stock," or because the next step is hard. Trevor ends the run.
