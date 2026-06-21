#!/usr/bin/env -S uv run --quiet python3
"""
check_dm_transcription.py — pre-submission faithfulness gate for planar Kakeya.

Confirms the *verbatim* transcription of DeepMind formal-conjectures' Kakeya
definitions in  src/.../Kakeya2D/DeepMindBridge.lean  still matches their actual
source in the local Reservoir mirror. The Lean side (DeepMindBridge.lean) already
proves `ours ≡ this-transcription` by `Iff.rfl`; this script closes the last link:
`this-transcription == DeepMind's real source`.

Modes:
  (default)   print BOTH sides (annotated) + a PASS/FAIL verdict; exit 0/1.
  --dm        print ONLY DeepMind's source side (de-annotated).
  --ours      print ONLY our transcription side (de-annotated).
  --quiet     de-annotate (drop the per-piece sub-labels) in the both-sides view.

The section header (════ THEIR … ════ / ════ OUR … ════) is ALWAYS printed, so

    diff <(check_dm_transcription.py --dm) <(check_dm_transcription.py --ours)

shows *only the header line* when the bodies match (a clean 1-line diff == PASS).

NB the Reservoir mirror is a shallow clone and can lag upstream — refresh it
(`reservoir-clone --update`) before trusting a PASS for an actual PR submission.

git-ignored: hardcodes the machine-local Reservoir mirror path.
"""
from __future__ import annotations

import argparse
import difflib
import os
import re
import sys
from pathlib import Path

HOME = Path.home()
FC = Path(os.environ.get("FC", HOME / "src/reservoir/google-deepmind/formal-conjectures"))
REPO = Path(__file__).resolve().parent.parent
BRIDGE = REPO / "src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/DeepMindBridge.lean"
EUCLIDEAN = FC / "FormalConjecturesForMathlib/Geometry/Euclidean.lean"
KAKEYA = FC / "FormalConjectures/Wikipedia/Kakeya.lean"

HEADER = {
    "dm": "════════ THEIR SOURCE (Reservoir mirror) ════════",
    "ours": "════════ OUR TRANSCRIPTION (DeepMindBridge.lean) ════════",
}

# (regex anchored at col 0 so it skips indented docstring prose; n = trailing lines to also grab)
NOTATION = (r'^scoped\[EuclideanGeometry\] notation "ℝ', 0)
ISKAKEYA = (r'^def IsKakeya \{', 1)
CONJDIM = (r'^def KakeyaSetConjectureDim ', 1)


def _grab(path: Path, pattern: str, extra: int) -> list[str]:
    """First line matching `pattern`, plus `extra` following lines (all rstripped)."""
    lines = path.read_text().splitlines()
    rx = re.compile(pattern)
    for i, ln in enumerate(lines):
        if rx.match(ln):
            return [s.rstrip() for s in lines[i : i + 1 + extra]]
    sys.exit(f"check_dm_transcription: pattern not found in {path}: {pattern!r}")


def their_pieces() -> list[tuple[str, list[str]]]:
    return [
        ("Euclidean.lean (ℝ^n notation)", _grab(EUCLIDEAN, *NOTATION)),
        ("Kakeya.lean (IsKakeya)", _grab(KAKEYA, *ISKAKEYA)),
        ("Kakeya.lean (KakeyaSetConjectureDim)", _grab(KAKEYA, *CONJDIM)),
    ]


def our_pieces() -> list[tuple[str, list[str]]]:
    return [
        ("DeepMindBridge.lean (ℝ^n notation)", _grab(BRIDGE, *NOTATION)),
        ("DeepMindBridge.lean (IsKakeya)", _grab(BRIDGE, *ISKAKEYA)),
        ("DeepMindBridge.lean (KakeyaSetConjectureDim)", _grab(BRIDGE, *CONJDIM)),
    ]


def render(pieces, *, annotated: bool) -> list[str]:
    out: list[str] = []
    for label, lns in pieces:
        if annotated:
            out.append(f"── {label} ──")
        out.extend(lns)
    return out


def body(pieces) -> list[str]:
    """The normative lines only (no labels), for comparison."""
    out: list[str] = []
    for _, lns in pieces:
        out.extend(lns)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--dm", action="store_true", help="print only DeepMind's source side (de-annotated)")
    g.add_argument("--ours", action="store_true", help="print only our transcription side (de-annotated)")
    ap.add_argument("--quiet", action="store_true", help="de-annotate the both-sides view (drop sub-labels)")
    args = ap.parse_args()

    if args.dm or args.ours:
        side, pieces = ("dm", their_pieces()) if args.dm else ("ours", our_pieces())
        print(HEADER[side])
        print("\n".join(render(pieces, annotated=False)))  # single-side ⇒ always de-annotated
        return 0

    tp, op = their_pieces(), our_pieces()
    annotated = not args.quiet
    print(HEADER["dm"])
    print("\n".join(render(tp, annotated=annotated)))
    print()
    print(HEADER["ours"])
    print("\n".join(render(op, annotated=annotated)))
    print()
    if body(tp) == body(op):
        print("✅ PASS — the 5 normative lines match DeepMind's source verbatim.")
        return 0
    print("❌ DRIFT — DeepMindBridge.lean no longer matches DeepMind's source:")
    for d in difflib.unified_diff(body(tp), body(op), "deepmind", "ours", lineterm=""):
        print(d)
    return 1


if __name__ == "__main__":
    sys.exit(main())
