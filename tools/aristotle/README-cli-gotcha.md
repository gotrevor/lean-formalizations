# Aristotle CLI submit gotcha (discovered 2026-06-16)

`aristotle submit "<prompt>"` (prompt-only) calls `Path(args.prompt).is_file()` to detect
whether the prompt is a file path. Python pathlib does NOT catch `OSError ENAMETOOLONG`
(errno 36), so **any prompt containing a 255+ character run with no `/` raises**
`OSError: File name too long` BEFORE the request is sent.

- A prompt works iff every path-component (text between `/` chars, newlines do NOT split)
  is < 255 chars. The monic-leaf prompt worked only because it said "Lean 4 / mathlib"
  (an early `/`) and had short slash-free runs.
- Lean theorem statements are usually one long slash-free block → they trip this.

**Workarounds (next lap):**
1. Sprinkle `/` into the NL prose so no slash-free run exceeds ~200 chars (keep the Lean
   statement compact / reference mathlib files with slashes like `RingTheory/Polynomial/Vieta.lean`).
2. Or use `--project-dir <dir>` (skips the `is_file` check entirely) — but Aristotle pins
   Lean v4.28 so project-dir risks a mathlib build mismatch; use a minimal self-contained dir.
3. Or prove the lemma locally.

The pending leaf `pi-conjugate-poly-symmetric-prompt.txt` (subsetSum_esymm_rational) hit
this; submit it next lap with workaround (1).
